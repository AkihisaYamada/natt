XML Input Format of NaTT
====
Input method is XML.

### CLASS ***term***
 A term is either: 
* **Option**  A constant or variable symbol; or 
    * **ELEMENT** `sym`
      * **TEXT**
* **Option**  A function application. 
    * **ELEMENT** `app`
      * **ELEMENT** `sym`
        * **TEXT**
      * ***term***<sup>+</sup>
## Main Content

* **ELEMENT** `trs`
  * **ATTRIBUTE** `problem`<sup>?</sup>
  * **ELEMENT** `syms`<sup>?</sup> 
   This element declares symbols. 
    * **CHOICE**\*
      * **ELEMENT** `var` 
       variable symbol 
        * **TEXT**
      * **ELEMENT** `sym` 
       function symbol 
        * **ATTRIBUTE** `theory`<sup>?</sup> (`AC?|C`)
        * **TEXT**
  * **CHOICE**\* 
   These elements declare rewrite rules. 
    * **ELEMENT** `rule`
      * ***term***
      * ***term***
      * **ELEMENT** `cond`\*
        * ***term***
        * ***term***
    * **ELEMENT** `relative`
      * ***term***
      * ***term***
  * **ELEMENT** `infeasibility`<sup>?</sup> 
   The presense of this element indicates NaTT to check the infeasibility problem. 
    * **ELEMENT** `cond`\*
      * ***term***
      * ***term***