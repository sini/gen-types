# Fixture for the purity walk's recursion. Never imported and never part of the purity
# subject: the tree importer ignores path components beginning with an underscore, and the
# scan's subject is lib/ alone. The tether below is planted on purpose.
{
  planted = mkOption { type = "string"; };
}
