import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.SubLift

theorem factor_of_frame : ∀ (X : Scheme.{0}) [IsIntegral X] (A : X.Opens) (G G' E : X.Modules) (i : G ⟶ E) (f : G' ⟶ E) (n : ℕ) (t : Fin n → Γ(G', A)), genericPoint X ∈ A → IsSubbundle i → IsFrame t → (∀ j, ∃ u : Γ(G, A), i.app A u = f.app A (t j)) → ∃ a : G' ⟶ G, a ≫ i = f := by
  intro X _ A G G' E i f n t hA hi ht hu
  have := hi.mono
  have htf : IsTorsionFree (cokernel i) := hi.isSaturated
  have hz : ∀ j, (f ≫ cokernel.π i).app A (t j) = 0 := fun j => by
    obtain ⟨u, hu⟩ := hu j
    rw [← QCoh.app_app, ← hu, QCoh.app_app, cokernel.condition]
    rfl
  have hst : QCoh.stalkLinear (f ≫ cokernel.π i) (genericPoint X) = 0 := by
    refine (ht.stalkBasis _ hA).ext fun j => ?_
    rw [IsFrame.stalkBasis_apply, QCoh.stalkLinear_germ, LinearMap.zero_apply, hz j, map_zero]
  refine ⟨Abelian.monoLift i f ?_, Abelian.monoLift_comp i f _⟩
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  ext s
  change (f ≫ cokernel.π i).app W s = (0 : G' ⟶ cokernel i).app W s
  rw [show (0 : G' ⟶ cokernel i).app W s = 0 from rfl]
  by_cases hW : genericPoint X ∈ W
  · exact htf W hW _ (by rw [← QCoh.stalkLinear_germ, hst, LinearMap.zero_apply])
  · exact QCoh.section_eq_zero_of_germ _ fun x hx => absurd (genericPoint_mem hx) hW

end GlobalTheory.SubLift
