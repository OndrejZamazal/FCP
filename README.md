# FCP
This program is implementation of detection of classification options for focus classes.

Notice: The code is still experimental and some parts are "work in progress".

Currently, the implemenation find categorization options and compute frequencies for each class how many times they are focus class - the output file FOCanalysisReport-ontology.csv

The file, blackList, contains generated black list.

External java libraries
- https://osdn.net/projects/sfnet_owlapi/downloads/OWL%20API%20%28for%20OWL%202.0%29/4.0.1/owlapi-osgidistribution-4.0.1.jar/
- https://sourceforge.net/projects/jfact/files/jfact-4.0.0.jar%20%28OWLAPI%204%20and%20Protege%20plugin%29/download

You can run it for ontology stored in OOSP from https://owl.vse.cz/ontologies/117810.owl or you can use any ontology with its URI using String onto line (need to be uncommented) in main method.
