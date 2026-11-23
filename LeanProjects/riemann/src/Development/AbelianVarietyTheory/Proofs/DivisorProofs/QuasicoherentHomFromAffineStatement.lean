import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasicoherentHomFromAffine
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeIntoDeRhamInjectiveImports
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.LieVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasicoherent_hom_from_affine : ∀ (T : Scheme.{0}) (F G : T.Modules)
    (j : ∀ V : T.Opens, IsAffineOpen V → Γ(F, V) →ₗ[Γ(T, V)] Γ(G, V)),
    (∀ (V V' : T.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V) (s : Γ(F, V)),
      j V' hV' (GlobalTheory.Twist.resM F h s) = GlobalTheory.Twist.resM G h (j V hV s)) →
    ∃ i : F ⟶ G, ∀ (V : T.Opens) (hV : IsAffineOpen V), GlobalTheory.QCoh.appLinear i V = j V hV := by
  first | exact @GlobalTheory.hom_of_affine_compatible | exact GlobalTheory.hom_of_affine_compatible | (intros; apply GlobalTheory.hom_of_affine_compatible <;> assumption)
