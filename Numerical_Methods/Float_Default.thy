(* Shared default-class instance for IEEE floats.

   The scalar float fields of the various zstores need IEEE.float to be an
   instance of the `default` class.  That instance is GLOBAL, so it may be
   declared in exactly one place; declaring it separately in each algorithm
   theory clashes as soon as two of them are imported together (e.g. by the
   cap theory Verified_Numerical_Methods).  It therefore lives here, and the
   algorithm theories import this theory instead of re-declaring it. *)
theory Float_Default
  imports
    "ITree_Numeric_VCG.ITree_Numeric_VCG"
    "IEEE_Floating_Point.IEEE_Properties"
begin

instantiation IEEE.float :: (len, len) default
begin
definition "default_float = (0 :: ('a, 'b) IEEE.float)"
instance ..
end

end
