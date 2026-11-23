import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeIntoDeRhamInjectiveImports
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOnAff

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.LieVB

namespace GlobalTheory.HodgeSub

theorem exists_proj : ∀ {T : Scheme.{0}} (A : Over T) [GrpObj A] (V V' : T.Opens) (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') (h : V' ≤ V),
    letI := resAlg h
    ∃ (φ : (onAff A hV').left ⟶ (onAff A hV).left)
      (_ : IsGrpPullback (onAff A hV') (onAff A hV) (spMap (algebraMap Γ(T, V) Γ(T, V'))) φ),
      φ ≫ pullback.fst A.hom hV.fromSpec = pullback.fst A.hom hV'.fromSpec := by
  intro T A _ V V' hV hV' h
  letI := resAlg h
  obtain ⟨φ, hφ, hc⟩ := GlobalTheory.DeRhamSheaf.VB.exists_transition A hV hV' h
  exact ⟨φ, hφ, hc⟩

end GlobalTheory.HodgeSub
