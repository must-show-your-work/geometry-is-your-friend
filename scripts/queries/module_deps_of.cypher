// Every Geometry module transitively required by a target module's decls.
// Edit the module name in the WHERE clause to retarget.
// Useful when shaking imports: anything the term-graph reaches must be in
// the import closure; anything else can be dropped.
MATCH (root:Decl)-[:DECLARED_IN]->(rm:Module {name: 'Geometry.Ch3.Prop.Pasch'})
MATCH (root)-[:USES*1..]->(d:Decl)-[:DECLARED_IN]->(m:Module)
WHERE m.name STARTS WITH 'Geometry' AND m.name <> 'Geometry.Ch3.Prop.Pasch'
RETURN DISTINCT m.name AS module
ORDER BY module;
