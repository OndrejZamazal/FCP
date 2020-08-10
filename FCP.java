package cz.vse.swoe.fcatpowo;

import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.HashSet;
import java.util.Iterator;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.MissingImportHandlingStrategy;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataExactCardinality;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDataHasValue;
import org.semanticweb.owlapi.model.OWLDataMaxCardinality;
import org.semanticweb.owlapi.model.OWLDataMinCardinality;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLDataSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectExactCardinality;
import org.semanticweb.owlapi.model.OWLObjectHasSelf;
import org.semanticweb.owlapi.model.OWLObjectHasValue;
import org.semanticweb.owlapi.model.OWLObjectMaxCardinality;
import org.semanticweb.owlapi.model.OWLObjectMinCardinality;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.parameters.Imports;
import org.semanticweb.owlapi.reasoner.Node;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.OWLReasonerConfiguration;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;
import org.semanticweb.owlapi.reasoner.SimpleConfiguration;
import org.semanticweb.owlapi.search.EntitySearcher;

import uk.ac.manchester.cs.jfact.JFactFactory;

/**
 * Created by Ondřej Zamazal on 2016-2020.
 */

public class FCP {
	
	protected OWLOntology ontology;
	protected OWLOntologyManager manager;
	protected OWLDataFactory factory;
	
	//get categorization options for each ontology
	//first there is black list generation
	//then categorization options detection itself
	//onto is the URI of ontology, imports either true (including imports) or false (without imports)
	private void getCategorizationOptions(String onto, boolean imports) {
		try {
			//init for each ontology
			this.manager = OWLManager.createOWLOntologyManager();
			this.manager.getOntologyConfigurator().setMissingImportHandlingStrategy(MissingImportHandlingStrategy.SILENT);
			this.manager.getOntologyConfigurator().setConnectionTimeout(500);			
			//09-08-20, START silent missing imports handling
			//this.manager.getOntologyConfigurator().setMissingImportHandlingStrategy(MissingImportHandlingStrategy.SILENT);
			//09-08-20, END silent missing imports handling
			this.ontology=this.manager.loadOntology(IRI.create(onto));
			this.factory=manager.getOWLDataFactory();
			
			//System.out.println(this.ontology.getClassesInSignature().size());
			
			//the black list
			//black list construction strategy
			//the combination (anchor class, property, thing) 
			//this is created from the cases where the filler Thing
			//the combination (anchor class, property, filler) 
			//this is created from the cases where the filler is the class or instance
			//there is always the combination (anchor class, property) added to the black list for pruning
			HashSet<String> ACpropertyFillerBlist = new HashSet<String>();
			
			//19-12-19, creation class expressions corresponding to cases v2,v3,v4 (p1,p2,p3) for checking whether they are not already counted in v1 (p1) - kind of experiment implemention
			HashSet<OWLClassExpression> all_created_class_expressions = null;			
			
			//use the reasoner
			this.factory= manager.getOWLDataFactory();
			//since 2019 I use JFact reasoner
			OWLReasonerFactory reasonerFactory = new JFactFactory();
			OWLReasonerConfiguration config = new SimpleConfiguration(5000);
			OWLReasoner reasoner = reasonerFactory.createReasoner(ontology, config);
			//System.out.println("to precompute inferences...");
			reasoner.precomputeInferences();
			
			//1. black list generation
			//iteration over all classes either with imports Imports.INCLUDED or without imports Imports.EXCLUDED
			Imports considerImport;
			if(imports)
				considerImport=Imports.INCLUDED;
			else
				considerImport=Imports.EXCLUDED;			
			//10-08-20, Java8 for stream
			Iterator<OWLClass> iter = this.ontology.classesInSignature(considerImport).iterator();
			
			while(iter.hasNext()) {
			
				OWLClass cls = iter.next();
				
				//the iteration over all partial definitions and checking of different types of anonymous expressions
				//10-08-20, Java8 for stream
				Iterator<OWLClassExpression> iter1 = EntitySearcher.getSuperClasses(cls, this.ontology).iterator();
				
				while(iter1.hasNext()) {
					OWLClassExpression exp = iter1.next();
				
					//System.out.println("   "+cls+" rdfs:subClassOf:"+exp);
					if(exp.isAnonymous()) {
						if (exp instanceof OWLObjectSomeValuesFrom) {							
							String p = ((OWLObjectSomeValuesFrom) exp).getProperty().toString();
		
							ACpropertyFillerBlist.add(cls.toString()+";"+p.toString()+";"+((OWLObjectSomeValuesFrom) exp).getFiller());
							ACpropertyFillerBlist.add(cls.toString()+";"+p.toString());
							
							Iterator<Node<OWLClass>> it1 = reasoner.getSubClasses(cls, false).nodes().iterator(); 
								
							while(it1.hasNext()) {
								Node<OWLClass> n = it1.next();
								
								for(OWLClass cls1 : n.getEntitiesMinusTop()) {									
									//the propagation to the subclasses
									if(!cls1.isBottomEntity()) {
										ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString()+";"+((OWLObjectSomeValuesFrom) exp).getFiller());
										ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString());
									}
								}
							}
						}
						
						if (exp instanceof OWLDataSomeValuesFrom) {							
							String p = ((OWLDataSomeValuesFrom) exp).getProperty().toString();
							ACpropertyFillerBlist.add(cls.toString()+";"+p.toString());							
							
							Iterator<Node<OWLClass>> it2 = reasoner.getSubClasses(cls, false).nodes().iterator();
							
							while(it2.hasNext()) {
								Node<OWLClass> n = it2.next();
							
								for(OWLClass cls1 : n.getEntitiesMinusTop()) {
									//the propagation to the subclasses
									if(!cls1.isBottomEntity()) {
										ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString());
									}
								}
							}
						}
					
						if (exp instanceof OWLObjectHasValue) {							
							String p = ((OWLObjectHasValue) exp).getProperty().toString();
							ACpropertyFillerBlist.add(cls.toString()+";"+p.toString()+";"+((OWLObjectHasValue) exp).getFiller());
							ACpropertyFillerBlist.add(cls.toString()+";"+p.toString());
							
							Iterator<Node<OWLClass>> it3 = reasoner.getSubClasses(cls, false).nodes().iterator();
							
							while(it3.hasNext()) {
								Node<OWLClass> n = it3.next();
								
								
								for(OWLClass cls1 : n.getEntitiesMinusTop()) {
									//the propagation to the subclasses
									if(!cls1.isBottomEntity()) {
										ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString()+";"+((OWLObjectHasValue) exp).getFiller());
										ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString());
									}
								}
							}
						}
						
						if (exp instanceof OWLDataHasValue) {							
							String p = ((OWLDataHasValue) exp).getProperty().toString();
							ACpropertyFillerBlist.add(cls.toString()+";"+p.toString());
							
							Iterator<Node<OWLClass>> it4 = reasoner.getSubClasses(cls, false).nodes().iterator();
							
							while(it4.hasNext()) {
								
								Node<OWLClass> n = it4.next();
								for(OWLClass cls1 : n.getEntitiesMinusTop()) {
									//the propagation to the subclasses
									if(!cls1.isBottomEntity()) {
										ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString());
									}
								}
							}
						}
						
						if (exp instanceof OWLObjectHasSelf) {							
							String p = ((OWLObjectHasSelf) exp).getProperty().toString();
							ACpropertyFillerBlist.add(cls.toString()+";"+p.toString());
							
							Iterator<Node<OWLClass>> it5 = reasoner.getSubClasses(cls, false).nodes().iterator();
							
							while(it5.hasNext()) {
								Node<OWLClass> n = it5.next();
								
								for(OWLClass cls1 : n.getEntitiesMinusTop()) {
									//the propagation to the subclasses
									if(!cls1.isBottomEntity()) {
										ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString());
									}
								}
							}
						}
						
						if (exp instanceof OWLObjectMinCardinality) {							
							if(((OWLObjectMinCardinality) exp).getCardinality()>=0) {
								String p = ((OWLObjectMinCardinality) exp).getProperty().toString();
								ACpropertyFillerBlist.add(cls.toString()+";"+p.toString()+";"+((OWLObjectMinCardinality) exp).getFiller());
								ACpropertyFillerBlist.add(cls.toString()+";"+p.toString());
								
								Iterator<Node<OWLClass>> it6 = reasoner.getSubClasses(cls, false).nodes().iterator();
								
								while(it6.hasNext()) {
									Node<OWLClass> n = it6.next();
									
									for(OWLClass cls1 : n.getEntitiesMinusTop()) {
										//the propagation to the subclasses
										if(!cls1.isBottomEntity()) {
											ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString()+";"+((OWLObjectMinCardinality) exp).getFiller());
											ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString());
										}
									}
								}
							}
						}
						
						if (exp instanceof OWLDataMinCardinality) {							
							if(((OWLDataMinCardinality) exp).getCardinality()>=0) {
								String p = ((OWLDataMinCardinality) exp).getProperty().toString();
								ACpropertyFillerBlist.add(cls.toString()+";"+p.toString());
								
								Iterator<Node<OWLClass>> it7 = reasoner.getSubClasses(cls, false).nodes().iterator();
								
								while(it7.hasNext()) {
									Node<OWLClass> n = it7.next();
									
									for(OWLClass cls1 : n.getEntitiesMinusTop()) {
										//the propagation to the subclasses
										if(!cls1.isBottomEntity()) {
											ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString());
										}
									}
								}
							}
						}
						
						if (exp instanceof OWLObjectMaxCardinality) {							
							if(((OWLObjectMaxCardinality) exp).getCardinality()>=0) {
								String p = ((OWLObjectMaxCardinality) exp).getProperty().toString();
								ACpropertyFillerBlist.add(cls.toString()+";"+p.toString()+";"+((OWLObjectMaxCardinality) exp).getFiller());
								ACpropertyFillerBlist.add(cls.toString()+";"+p.toString());
								
								Iterator<Node<OWLClass>> it8 = reasoner.getSubClasses(cls, false).nodes().iterator();
								
								while(it8.hasNext()) {
									Node<OWLClass> n = it8.next();
									
									for(OWLClass cls1 : n.getEntitiesMinusTop()) {
										//the propagation to the subclasses
										if(!cls1.isBottomEntity()) {
											ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString()+";"+((OWLObjectMaxCardinality) exp).getFiller());
											ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString());
										}
									}
								}
							}
						}

						if (exp instanceof OWLDataMaxCardinality) {							
							if(((OWLDataMaxCardinality) exp).getCardinality()>=0) {
								String p = ((OWLDataMaxCardinality) exp).getProperty().toString();
								ACpropertyFillerBlist.add(cls.toString()+";"+p.toString());

								Iterator<Node<OWLClass>> it9 = reasoner.getSubClasses(cls, false).nodes().iterator();
								
								while(it9.hasNext()) {
									Node<OWLClass> n = it9.next();
									
									for(OWLClass cls1 : n.getEntitiesMinusTop()) {
										//the propagation to the subclasses
										if(!cls1.isBottomEntity()) {
											ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString());
										}
									}
								}
							}
						}
						
						if (exp instanceof OWLObjectExactCardinality) {
							if(((OWLObjectExactCardinality) exp).getCardinality()>=0) {
								String p = ((OWLObjectExactCardinality) exp).getProperty().toString();
								ACpropertyFillerBlist.add(cls.toString()+";"+p.toString()+";"+((OWLObjectExactCardinality) exp).getFiller());
								ACpropertyFillerBlist.add(cls.toString()+";"+p.toString());
								
								Iterator<Node<OWLClass>> it10 = reasoner.getSubClasses(cls, false).nodes().iterator();
								
								while(it10.hasNext()) {
									Node<OWLClass> n = it10.next();
									
									for(OWLClass cls1 : n.getEntitiesMinusTop()) {
										//the propagation to the subclasses
										if(!cls1.isBottomEntity()) {
											ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString()+";"+((OWLObjectExactCardinality) exp).getFiller());
											ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString());
										}
									}
								}
							}
						}
						
						if (exp instanceof OWLDataExactCardinality) {
							if(((OWLDataExactCardinality) exp).getCardinality()>=0) {
								String p = ((OWLDataExactCardinality) exp).getProperty().toString();
								ACpropertyFillerBlist.add(cls.toString()+";"+p.toString());
								
								Iterator<Node<OWLClass>> it11 = reasoner.getSubClasses(cls, false).nodes().iterator();
								
								while(it11.hasNext()) {
									Node<OWLClass> n = it11.next();
									
									for(OWLClass cls1 : n.getEntitiesMinusTop()) {
										//the propagation to the subclasses
										if(!cls1.isBottomEntity()) {
											ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString());
										}
									}
								}
							}
						}
					}
				}
				//the iteration over all complete definitions
				Iterator<OWLClassExpression> iter2 = EntitySearcher.getEquivalentClasses(cls, this.ontology).iterator();
				
				while(iter2.hasNext()) {
					OWLClassExpression exp = iter2.next();
								
					if(exp.isAnonymous()) {
						
						if (exp instanceof OWLObjectSomeValuesFrom) {							
							String p = ((OWLObjectSomeValuesFrom) exp).getProperty().toString();
							ACpropertyFillerBlist.add(cls.toString()+";"+p.toString()+";"+((OWLObjectSomeValuesFrom) exp).getFiller());
							ACpropertyFillerBlist.add(cls.toString()+";"+p.toString());
							
							Iterator<Node<OWLClass>> it1 = reasoner.getSubClasses(cls, false).nodes().iterator();
							
							while(it1.hasNext()) {
								Node<OWLClass> n = it1.next();
								
								for(OWLClass cls1 : n.getEntitiesMinusTop()) {
									//the propagation to the subclasses
									if(!cls1.isBottomEntity()) {
										ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString()+";"+((OWLObjectSomeValuesFrom) exp).getFiller());
										ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString());
									}
								}
							}
						}
						
						if (exp instanceof OWLDataSomeValuesFrom) {							
							String p = ((OWLDataSomeValuesFrom) exp).getProperty().toString();
							ACpropertyFillerBlist.add(cls.toString()+";"+p.toString());
							
							Iterator<Node<OWLClass>> it2 = reasoner.getSubClasses(cls, false).nodes().iterator();
							
							while(it2.hasNext()) {
								Node<OWLClass> n = it2.next();
								
								for(OWLClass cls1 : n.getEntitiesMinusTop()) {
									//the propagation to the subclasses
									if(!cls1.isBottomEntity()) {
										ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString());
									}
								}
							}
						}
					
						if (exp instanceof OWLObjectHasValue) {							
							String p = ((OWLObjectHasValue) exp).getProperty().toString();
							ACpropertyFillerBlist.add(cls.toString()+";"+p.toString()+";"+((OWLObjectHasValue) exp).getFiller());
							ACpropertyFillerBlist.add(cls.toString()+";"+p.toString());
							
							Iterator<Node<OWLClass>> it3 = reasoner.getSubClasses(cls, false).nodes().iterator();
							
							while(it3.hasNext()) {
								Node<OWLClass> n = it3.next();
								
								for(OWLClass cls1 : n.getEntitiesMinusTop()) {
									//the propagation to the subclasses
									if(!cls1.isBottomEntity()) {
										ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString()+";"+((OWLObjectHasValue) exp).getFiller());
										ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString());
									}
								}
							}
						}
						
						if (exp instanceof OWLDataHasValue) {							
							String p = ((OWLDataHasValue) exp).getProperty().toString();
							ACpropertyFillerBlist.add(cls.toString()+";"+p.toString());

							Iterator<Node<OWLClass>> it4 = reasoner.getSubClasses(cls, false).nodes().iterator();
							
							while(it4.hasNext()) {
								Node<OWLClass> n = it4.next();
								
								for(OWLClass cls1 : n.getEntitiesMinusTop()) {
									//the propagation to the subclasses
									if(!cls1.isBottomEntity()) {
										ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString());
									}
								}
							}
						}
						
						if (exp instanceof OWLObjectHasSelf) {							
							String p = ((OWLObjectHasSelf) exp).getProperty().toString();
							ACpropertyFillerBlist.add(cls.toString()+";"+p.toString());
							
							Iterator<Node<OWLClass>> it5 = reasoner.getSubClasses(cls, false).nodes().iterator();
							
							while(it5.hasNext()) {
								Node<OWLClass> n = it5.next();
								
								for(OWLClass cls1 : n.getEntitiesMinusTop()) {
									//the propagation to the subclasses
									if(!cls1.isBottomEntity()) {
										ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString());
									}
								}
							}
						}
						
						if (exp instanceof OWLObjectMinCardinality) {							
							if(((OWLObjectMinCardinality) exp).getCardinality()>=0) {
								String p = ((OWLObjectMinCardinality) exp).getProperty().toString();
								ACpropertyFillerBlist.add(cls.toString()+";"+p.toString()+";"+((OWLObjectMinCardinality) exp).getFiller());
								ACpropertyFillerBlist.add(cls.toString()+";"+p.toString());
								
								Iterator<Node<OWLClass>> it6 = reasoner.getSubClasses(cls, false).nodes().iterator();
								
								while(it6.hasNext()) {
									Node<OWLClass> n = it6.next();
									
									for(OWLClass cls1 : n.getEntitiesMinusTop()) {
										//the propagation to the subclasses
										if(!cls1.isBottomEntity()) {
											ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString()+";"+((OWLObjectMinCardinality) exp).getFiller());
											ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString());
										}
									}
								}
							}
						}
						
						if (exp instanceof OWLDataMinCardinality) {		
							if(((OWLDataMinCardinality) exp).getCardinality()>=0) {
								String p = ((OWLDataMinCardinality) exp).getProperty().toString();
								ACpropertyFillerBlist.add(cls.toString()+";"+p.toString());
								
								Iterator<Node<OWLClass>> it7 = reasoner.getSubClasses(cls, false).nodes().iterator();
								
								while(it7.hasNext()) {
									Node<OWLClass> n = it7.next();
									
									for(OWLClass cls1 : n.getEntitiesMinusTop()) {
										//the propagation to the subclasses
										if(!cls1.isBottomEntity()) {
											ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString());
										}
									}
								}
							}
						}
						
						if (exp instanceof OWLObjectMaxCardinality) {							
							if(((OWLObjectMaxCardinality) exp).getCardinality()>=0) {
								String p = ((OWLObjectMaxCardinality) exp).getProperty().toString();
								ACpropertyFillerBlist.add(cls.toString()+";"+p.toString()+";"+((OWLObjectMaxCardinality) exp).getFiller());
								ACpropertyFillerBlist.add(cls.toString()+";"+p.toString());
								
								Iterator<Node<OWLClass>> it8 = reasoner.getSubClasses(cls, false).nodes().iterator();
								
								while(it8.hasNext()) {
									Node<OWLClass> n = it8.next();
									
									for(OWLClass cls1 : n.getEntitiesMinusTop()) {
										//the propagation to the subclasses
										if(!cls1.isBottomEntity()) {
											ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString()+";"+((OWLObjectMaxCardinality) exp).getFiller());
											ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString());
										}
									}
								}
							}
						}
						
						if (exp instanceof OWLDataMaxCardinality) {		
							if(((OWLDataMaxCardinality) exp).getCardinality()>=0) {
								String p = ((OWLDataMaxCardinality) exp).getProperty().toString();
								ACpropertyFillerBlist.add(cls.toString()+";"+p.toString());
								
								Iterator<Node<OWLClass>> it9 = reasoner.getSubClasses(cls, false).nodes().iterator();
								
								while(it9.hasNext()) {
									Node<OWLClass> n = it9.next();
									
									for(OWLClass cls1 : n.getEntitiesMinusTop()) {
										//the propagation to the subclasses
										if(!cls1.isBottomEntity()) {
											ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString());
										}
									}
								}
							}
						}
						
						if (exp instanceof OWLObjectExactCardinality) {			
							if(((OWLObjectExactCardinality) exp).getCardinality()>=0) {
								String p = ((OWLObjectExactCardinality) exp).getProperty().toString();
								ACpropertyFillerBlist.add(cls.toString()+";"+p.toString()+";"+((OWLObjectExactCardinality) exp).getFiller());
								ACpropertyFillerBlist.add(cls.toString()+";"+p.toString());
								
								Iterator<Node<OWLClass>> it10 = reasoner.getSubClasses(cls, false).nodes().iterator();
								
								while(it10.hasNext()) {
									Node<OWLClass> n = it10.next();
									
									for(OWLClass cls1 : n.getEntitiesMinusTop()) {
										//the propagation to the subclasses
										if(!cls1.isBottomEntity()) {
											ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString()+";"+((OWLObjectExactCardinality) exp).getFiller());
											ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString());
										}
									}
								}
							}
						}
						
						if (exp instanceof OWLDataExactCardinality) {
							if(((OWLDataExactCardinality) exp).getCardinality()>=0) {
								String p = ((OWLDataExactCardinality) exp).getProperty().toString();
								ACpropertyFillerBlist.add(cls.toString()+";"+p.toString());
								
								Iterator<Node<OWLClass>> it11 = reasoner.getSubClasses(cls, false).nodes().iterator();
								
								while(it11.hasNext()) {
									Node<OWLClass> n = it11.next();
									
									for(OWLClass cls1 : n.getEntitiesMinusTop()) {
										//the propagation to the subclasses
										if(!cls1.isBottomEntity()) {
											ACpropertyFillerBlist.add(cls1.toString()+";"+p.toString());
										}
									}
								}
							}
						}
					}
				}
			}
			//black list generation end
			System.out.println("blist:");
			System.out.println(ACpropertyFillerBlist);
			//control output to the text file
			PrintWriter toFileBL = new PrintWriter(new FileWriter("blackList", true));
			toFileBL.println(onto);
			for(String s : ACpropertyFillerBlist) {
				toFileBL.println(s);
			}
			toFileBL.println();
			toFileBL.close();
			
			//2. categorization options detection itself - variants v1, v2, v3, v4 (v5 is skipped for now)
			PrintWriter toFile = new PrintWriter(new FileWriter("FCP-options.csv", true));
			toFile.println(onto);

			//19-12-19
			//all_created_class_expressions - work in progress
			all_created_class_expressions = new HashSet<OWLClassExpression>();
			
			//fist go for variants v2, v3, v4
			Iterator<OWLObjectProperty> iter3 = this.ontology.objectPropertiesInSignature(considerImport).iterator();
					
			while(iter3.hasNext()) {
				
				OWLObjectProperty op = iter3.next();
			
				Iterator<Node<OWLClass>> it1 = reasoner.getObjectPropertyDomains(op, false).nodes().iterator();
				
				while(it1.hasNext()) {
					Node<OWLClass> n = it1.next();
					
					//it does not consider Nothing
					if(n.isBottomNode()) break;
					for(OWLClass cls1 : n.getEntitiesMinusTop()) {
						//v2
						if(ACpropertyFillerBlist.contains(cls1.toString()+";"+op.toString())) {
							System.out.println("blist applied:"+cls1.toString()+";"+op.toString());
							continue; //pruning
						}
						System.out.println("$v2 exists "+op+".owl:Thing rdfs:SubClassOf "+cls1);
						toFile.println("$v2 exists "+op+".owl:Thing rdfs:SubClassOf "+cls1);
						
						//19-12-19, creation corresponding class expression
						OWLClassExpression clsExpr1 = this.factory.getOWLObjectSomeValuesFrom(op, factory.getOWLThing());
						all_created_class_expressions.add(clsExpr1);
						OWLClassExpression clsExpr3 = this.factory.getOWLObjectSomeValuesFrom(op, factory.getOWLThing());
						OWLClassExpression clsExpr4 = factory.getOWLObjectIntersectionOf(cls1, clsExpr3);
						if (reasoner.isSatisfiable(clsExpr4)==false) {
							System.out.println(reasoner.isConsistent());
							System.out.println(clsExpr4);
							System.out.println("Found CE which is not satisfiable");
							System.exit(1);						
						}
						
						System.out.println("");
						
						//start v3
						HashSet<String> subclasses = new HashSet<String>();
						HashSet<String> individuals = new HashSet<String>();
						
						Iterator<OWLClassExpression> iter4 = EntitySearcher.getRanges(op, this.ontology).iterator();
						
						while(iter4.hasNext()) {
							OWLClassExpression exp = iter4.next();
						
							if(exp instanceof OWLClass) {
								OWLClass cls2 = (OWLClass) exp; 
								
								
								Iterator<Node<OWLClass>> it2 = reasoner.getSubClasses(cls2, false).nodes().iterator();
									
								while(it2.hasNext()) {
									Node<OWLClass> n2 = it2.next();
									
									for(OWLClass cls3 : n2.getEntitiesMinusBottom()) {
										if(ACpropertyFillerBlist.contains(cls1.toString()+";"+op.toString()+";"+cls3.toString())) {
											System.out.println("blist applied:"+cls1.toString()+";"+op.toString()+";"+cls3.toString());
											continue; //pruning
										}
										subclasses.add(cls3.toString());
									}
								}
								//start v4								
									
								Iterator<Node<OWLNamedIndividual>> it3 = reasoner.getInstances(cls2, false).nodes().iterator();
									
								while(it3.hasNext()) {
									Node<OWLNamedIndividual> n2 = it3.next();
									
									Iterator<OWLNamedIndividual> it4 = n2.entities().iterator(); 
									
									while(it4.hasNext()) {
										OWLNamedIndividual ind = it4.next();
										
										if(ACpropertyFillerBlist.contains(cls1.toString()+";"+op.toString()+";"+ind.toString())) {
											System.out.println("blist applied:"+cls1.toString()+";"+op.toString()+";"+ind.toString());
											continue; //pruning
										}
										individuals.add(ind.toString());
									}
								}								
								//end v4
							}							
						}
						if(!subclasses.isEmpty()) {
							//System.out.println("$v3 "+subclasses+" classification option (via op "+op+") for anchor class:"+cls1);;
							for(String x : subclasses) {
								System.out.println("$v3 exists "+op+"."+x+" rdfs:SubClassOf "+cls1);
								toFile.println("$v3 exists "+op+"."+x+" rdfs:SubClassOf "+cls1);
								toFile.println("");
								System.out.println("");
								//19-12-19, start, corresponding class expression
								clsExpr1 = this.factory.getOWLObjectSomeValuesFrom(op, this.factory.getOWLClass(IRI.create(x.replaceAll("<", "").replaceAll(">", ""))));
								all_created_class_expressions.add(clsExpr1);
								clsExpr3 = this.factory.getOWLObjectSomeValuesFrom(op, this.factory.getOWLClass(IRI.create(x.replaceAll("<", "").replaceAll(">", ""))));
								clsExpr4 = factory.getOWLObjectIntersectionOf(cls1, clsExpr3);
								if (reasoner.isSatisfiable(clsExpr4)==false) {
									System.out.println(reasoner.isConsistent());
									System.out.println(clsExpr4);
									System.out.println("Found CE which is not satisfiable");
									System.exit(1);						
								}
							}
							
						}
						if(!individuals.isEmpty())
							for(String x : individuals) {
								System.out.println("$v4 exists "+op+".{"+x+"} rdfs:SubClassOf "+cls1);;
								System.out.println("");
								toFile.println("$v4 exists "+op+".{"+x+"} rdfs:SubClassOf "+cls1);;
								toFile.println("");
								//19-12-19, start, corresponding class expression
								clsExpr1 = this.factory.getOWLObjectSomeValuesFrom(op, (this.factory.getOWLObjectOneOf(this.factory.getOWLNamedIndividual(IRI.create(x.replaceAll("<", "").replaceAll(">", ""))))));
								all_created_class_expressions.add(clsExpr1);
								clsExpr3 = this.factory.getOWLObjectSomeValuesFrom(op, (this.factory.getOWLObjectOneOf(this.factory.getOWLNamedIndividual(IRI.create(x.replaceAll("<", "").replaceAll(">", ""))))));
								clsExpr4 = factory.getOWLObjectIntersectionOf(cls1, clsExpr3);
								if (reasoner.isSatisfiable(clsExpr4)==false) {
									System.out.println(reasoner.isConsistent());
									System.out.println(clsExpr4);
									System.out.println("Found CE which is not satisfiable");
									System.exit(1);						
								}
							}
						//end v3
					}
				}
			}
			
			//for dp compute v2
				
			Iterator<OWLDataProperty> iter5 = this.ontology.dataPropertiesInSignature(considerImport).iterator();
				
			while(iter5.hasNext()) {
					
				OWLDataProperty dp = iter5.next();
				
				Iterator<Node<OWLClass>> it1 = reasoner.getDataPropertyDomains(dp, false).nodes().iterator();
					
				while(it1.hasNext()) {
					Node<OWLClass> n = it1.next();
					
					//if domain is Nothing not considering this
					if(n.isBottomNode()) break;
					for(OWLClass cls1 : n.getEntitiesMinusTop()) {
						if(ACpropertyFillerBlist.contains(cls1.toString()+";"+dp.toString())) {
							System.out.println("blist applied:"+cls1.toString()+";"+dp.toString());
							continue; //pruning
						}
						System.out.println("$v2 (dp) exists "+dp+".owl:Thing rdfs:SubClassOf "+cls1);
						System.out.println("");
						toFile.println("$v2 (dp) exists "+dp+".owl:Thing rdfs:SubClassOf "+cls1);
						toFile.println("");
						//19-12-19, start, corresponding odpovidajici class expression for dp owl:Thing not possible
						//end dp v2
					}
				}
			}
			//end categorization options detection itself v2, v3, v4 but v1 is in the following iteration
			
			//3. compute v1			
			
			Iterator<OWLClass> iter6 = this.ontology.classesInSignature(considerImport).iterator();
				
			while(iter6.hasNext()) {
				
				OWLClass cls = iter6.next();	
				
				if(cls.isTopEntity())
					continue;
				//compute and print v1
				HashSet<String> subclasses = new HashSet<String>();
				HashSet<OWLClass> subclasses1 = new HashSet<OWLClass>();
								
				Iterator<Node<OWLClass>> it1 = reasoner.getSubClasses(cls, false).nodes().iterator();
					
				while(it1.hasNext()) {
					Node<OWLClass> n = it1.next();	
					
					if(n.getEntitiesMinusBottom().size()>0) {
						subclasses.add(n.getEntitiesMinusBottom().toString());
						//19-12-19, because of finding CE already as equivalence for subclasses)
						for(OWLClass cls1 : n.getEntitiesMinusBottom()) {
							subclasses1.add(cls1);
						}				
						//19-12-19, end
					}
				}
				if(subclasses.size()>0) {
					System.out.println("$v1 "+cls+" "+subclasses);
					toFile.println("$v1 "+cls+" "+subclasses);
					//19-12-19, checking whether named subclass  is not the same as cases from v2, v3, v4
					//if so then it is output but not counted
					//this part is in progress
					System.out.println(subclasses1);
					//toFile.println(subclasses1);
					//the following work in progress
					for(OWLClassExpression owlExpr1 : all_created_class_expressions) {						
						//system control output
						//Iterator<Node<OWLNamedIndividual>> it3 = reasoner.getInstances(cls2, false).nodes().iterator();
						Iterator<OWLClass> itt = reasoner.getEquivalentClasses(owlExpr1).entities().iterator();
						while(itt.hasNext()) {
							System.out.println(itt.next());
						}													
					}
					//19-12-19, end
				}
				
				toFile.println();
			}
			
			toFile.close();
			
			System.out.println("done");
		}
		catch(Exception e) {
			e.printStackTrace();
		}
	}
	
	public static void main(String[] args) {
		//ArrayList<String> ontologies = new ArrayList<String>();
		
		//for OntoFarm
		String OntoFarmCollectionList = "117810, 148595, 22715, 338585, 444843, 705423, 706664, 802652, 812819, 849686, 863124, 882174, 921432, 941140, 969223, 997991";
		//String OntoFarmCollectionList = "117810";
		String ontologies[] = OntoFarmCollectionList.split(",");
		
		//System.exit(1);
		
		FCP fcp = new FCP();
		
		try {
			/*
			for(String s : ontologies) {
				System.out.println(s);
				fcp.getCategorizationOptions("https://owl.vse.cz/ontologies/"+s.trim()+".owl", true);
			}
			*/
			//run for one ontology
			//String onto = "https://owl.vse.cz/ontologies/117810.owl"; //cmt.owl
			//String onto = "http://lod.nl.go.kr/ontology/"; //nlon ontology this url does not work it needs redirection to the ontology file
			//String onto = "http://lod.nl.go.kr/data/ontology/?output=rdfxml"; //this does not work
			//https://lov.linkeddata.es/dataset/lov/vocabs/nlon/versions/2015-11-23.n3
			//String onto = "https://w3id.org/arco/ontology/location"; //this works		
			String onto = "https://lov.linkeddata.es/dataset/lov/vocabs/nlon/versions/2015-11-23.n3"; //unloadable imports issue - okay with silent imports			
			//String onto = "https://lov.linkeddata.es/dataset/lov/vocabs/opmo/versions/2015-01-11.n3";
			//String onto = "https://lov.linkeddata.es/dataset/lov/vocabs/vra/versions/2003-10-14.n3";
			//fcp.getCategorizationOptions(onto, true);
			fcp.getCategorizationOptions(onto, true);
		}
		catch (Exception e) {
			e.printStackTrace();
		}
	}
}
