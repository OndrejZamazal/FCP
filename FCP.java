package cz.vse.swoe.fcatpowo;

import java.io.FileWriter;
import java.io.PrintWriter;
import java.util.HashSet;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
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
			for(OWLClass cls : this.ontology.getClassesInSignature(considerImport)) {
				
				//the iteration over all partial definitions and checking of different types of anonymous expressions
				for(OWLClassExpression exp : EntitySearcher.getSuperClasses(cls, this.ontology)) {
					//System.out.println("   "+cls+" rdfs:subClassOf:"+exp);
					if(exp.isAnonymous()) {
						if (exp instanceof OWLObjectSomeValuesFrom) {							
							String p = ((OWLObjectSomeValuesFrom) exp).getProperty().toString();
		
							ACpropertyFillerBlist.add(cls.toString()+";"+p.toString()+";"+((OWLObjectSomeValuesFrom) exp).getFiller());
							ACpropertyFillerBlist.add(cls.toString()+";"+p.toString());
							
							for(Node<OWLClass> n : reasoner.getSubClasses(cls, false).getNodes()) {
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
							
							for(Node<OWLClass> n : reasoner.getSubClasses(cls, false).getNodes()) {
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
							
							for(Node<OWLClass> n : reasoner.getSubClasses(cls, false).getNodes()) {
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
							for(Node<OWLClass> n : reasoner.getSubClasses(cls, false).getNodes()) {
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
							for(Node<OWLClass> n : reasoner.getSubClasses(cls, false).getNodes()) {
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
								
								for(Node<OWLClass> n : reasoner.getSubClasses(cls, false).getNodes()) {
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
								for(Node<OWLClass> n : reasoner.getSubClasses(cls, false).getNodes()) {
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
								
								for(Node<OWLClass> n : reasoner.getSubClasses(cls, false).getNodes()) {
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
								for(Node<OWLClass> n : reasoner.getSubClasses(cls, false).getNodes()) {
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
								
								for(Node<OWLClass> n : reasoner.getSubClasses(cls, false).getNodes()) {
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
								for(Node<OWLClass> n : reasoner.getSubClasses(cls, false).getNodes()) {
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
				for(OWLClassExpression exp : EntitySearcher.getEquivalentClasses(cls, this.ontology)) {
					if(exp.isAnonymous()) {
						
						if (exp instanceof OWLObjectSomeValuesFrom) {							
							String p = ((OWLObjectSomeValuesFrom) exp).getProperty().toString();
							ACpropertyFillerBlist.add(cls.toString()+";"+p.toString()+";"+((OWLObjectSomeValuesFrom) exp).getFiller());
							ACpropertyFillerBlist.add(cls.toString()+";"+p.toString());
							
							for(Node<OWLClass> n : reasoner.getSubClasses(cls, false).getNodes()) {
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
							for(Node<OWLClass> n : reasoner.getSubClasses(cls, false).getNodes()) {
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
							
							for(Node<OWLClass> n : reasoner.getSubClasses(cls, false).getNodes()) {
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
							for(Node<OWLClass> n : reasoner.getSubClasses(cls, false).getNodes()) {
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
							for(Node<OWLClass> n : reasoner.getSubClasses(cls, false).getNodes()) {
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
								
								for(Node<OWLClass> n : reasoner.getSubClasses(cls, false).getNodes()) {
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
								for(Node<OWLClass> n : reasoner.getSubClasses(cls, false).getNodes()) {
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
								
								for(Node<OWLClass> n : reasoner.getSubClasses(cls, false).getNodes()) {
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
								for(Node<OWLClass> n : reasoner.getSubClasses(cls, false).getNodes()) {
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
								
								for(Node<OWLClass> n : reasoner.getSubClasses(cls, false).getNodes()) {
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
								for(Node<OWLClass> n : reasoner.getSubClasses(cls, false).getNodes()) {
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
			for(OWLObjectProperty op : this.ontology.getObjectPropertiesInSignature(considerImport)) {
				for(Node<OWLClass> n : reasoner.getObjectPropertyDomains(op, false).getNodes()) {
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
						for(OWLClassExpression exp : EntitySearcher.getRanges(op, this.ontology)) { 
							if(exp instanceof OWLClass) {
								OWLClass cls2 = (OWLClass) exp; 
								for(Node<OWLClass> n2 : reasoner.getSubClasses(cls2, false).getNodes()) {
									for(OWLClass cls3 : n2.getEntitiesMinusBottom()) {
										if(ACpropertyFillerBlist.contains(cls1.toString()+";"+op.toString()+";"+cls3.toString())) {
											System.out.println("blist applied:"+cls1.toString()+";"+op.toString()+";"+cls3.toString());
											continue; //pruning
										}
										subclasses.add(cls3.toString());
									}
								}
								//start v4
								for(Node<OWLNamedIndividual> n2 : reasoner.getInstances(cls2, false).getNodes()) {
									for(OWLNamedIndividual ind : n2.getEntities()) {
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
			for(OWLDataProperty dp : this.ontology.getDataPropertiesInSignature(considerImport)) {
				for(Node<OWLClass> n : reasoner.getDataPropertyDomains(dp, false).getNodes()) {
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
			for(OWLClass cls : this.ontology.getClassesInSignature(considerImport)) {
				if(cls.isTopEntity())
					continue;
				//compute and print v1
				HashSet<String> subclasses = new HashSet<String>();
				HashSet<OWLClass> subclasses1 = new HashSet<OWLClass>();
				
				for(Node<OWLClass> n : reasoner.getSubClasses(cls, false).getNodes()) {
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
						if (!reasoner.getEquivalentClasses(owlExpr1).getEntities().isEmpty()) {
							System.out.println(reasoner.getEquivalentClasses(owlExpr1).getEntities());
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
			
			for(String s : ontologies) {
				System.out.println(s);
				fcp.getCategorizationOptions("https://owl.vse.cz/ontologies/"+s.trim()+".owl", true);
			}
			
			//run for one ontology
			//String onto = "https://owl.vse.cz/ontologies/117810.owl"; //cmt.owl
			//fcp.getCategorizationOptions(onto, true);
		}
		catch (Exception e) {
			e.printStackTrace();
		}
	}
}