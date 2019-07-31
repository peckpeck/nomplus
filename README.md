# nomplus

Nomplus is an extension to nom 5.

It provides some parsers and combinators that I find useful in parsing languages, such as:

* sp! and sp1! for adding whitespace around a parser
* sequence! and wsequence! for replacing the deprecated do_parse
* cut_with to transform an error into a specific failure

To use it just add this line to you Cargo.toml dependencies:
  nomplus = { version="0.1", path = "/checkout/path/nomplus" }

And add this to your code (or use things selectively):
   use nomplus::*;

To generate the documentation in target/doc/nomplus/all.html:
   cargo doc
