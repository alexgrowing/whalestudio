import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IntegralExtensionOfRegR1
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PlusRec
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra NumberField IsDedekindDomain Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

abbrev NormDatum (B : WeightFamilies.Prov D) := GlobalTheory.RunIn.SecNorm B

def NormDatum.sup (B : WeightFamilies.Prov D) : NormDatum B := GlobalTheory.RunIn.SecNorm.sup B
namespace NormDatum
variable (n : NormDatum B)

abbrev B' : WeightFamilies.Prov D := GlobalTheory.RunIn.SecNorm.base n

abbrev X' (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E) : PJ D n.B' P j := xplusN n.N n.h0 n.h1 n.h2 n.h3 n.h4 X E hM

abbrev S' (S : Scal B) : Scal n.B' := scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S

abbrev G' {ka wL wF : WeightFamilies.Wt D j} {X : PJ D B P j} (G : GlobalFamilyData X ka wL wF) (E : PtExt X) (hM : IntAtExt X E) :
    GlobalFamilyData (n.X' X E hM) ka wL wF := gd2XplusN n.N n.h0 n.h1 n.h2 n.h3 n.h4 G E hM

end NormDatum

def Generates (X : PJ D B P j) (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) {n : ℕ} (gens : Fin n → B.Cusp j w) : Prop :=
  Submodule.span (𝓞 B.KO) (Set.range gens) = X.WWc s w

example (B : WeightFamilies.Prov D) :
    NormDatum.B' (B := B) ⟨B.l2NormAlt, B.l2Norm_nonneg_bis, B.l2Norm_eq_zero_iff, B.l2Norm_smul_alt, B.l2Norm_add_le', B.l2Norm_le_supNorm_alt⟩ = B := rfl

example (B : WeightFamilies.Prov D) : (NormDatum.sup B).B'.l2NormAlt = (NormDatum.sup B).B'.supN := rfl
end GlobalTheory.PlusRec
