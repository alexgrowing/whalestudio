import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.WeilPairing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVariety
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfMemChart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PairingLawsCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.WeilPairingLaws

theorem theta_pt_pow {S : Scheme.{0}} (P : PolAV S) (k : ℕ) {T : Over S}
    (θ : ThetaGrp P.A P.L (k : ℤ) T) : θ.pt ^ k = 1 := by
  refine ((GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube
    GlobalTheory.AbLaw.CubeAssembly.cube_and_sections.1).1).1 S P k T θ.pt).1 ?_
  intro p
  refine ⟨⊤, trivial, (GlobalTheory.KerPow.pull_iff _ _ _).2 ?_⟩
  exact GlobalTheory.KerPow.HasGen.pull ⟨θ.φ, θ.isGen⟩ _ fun _ => rfl

theorem pow_eq_one_of_local_lift {S : Scheme.{0}} (P : PolAV S) (k : ℕ) {T : Over S} (x : T ⟶ P.A)
    (h : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : ThetaGrp P.A P.L (k : ℤ) (overRes V), θ.pt = overResι V ≫ x) : x ^ k = 1 := by
  ext1
  refine Scheme.hom_ext_of_forall _ _ fun p => ?_
  obtain ⟨V, hV, θ, hθ⟩ := h p
  refine ⟨V, hV, ?_⟩
  have e : overResι V ≫ (x ^ k) = overResι V ≫ (1 : T ⟶ P.A) := by
    rw [MonObj.comp_pow, MonObj.comp_one, ← hθ, theta_pt_pow]
  exact congrArg (fun q => q.left) e

theorem mem_tors_of_weilIs {S : Scheme.{0}} (P : PolAV S) (k : ℕ) {T : Over S} {x y : T ⟶ P.A}
    {c : Γ(T.left, ⊤)ˣ} (h : WeilIs P.A P.L (k : ℤ) x y c) :
    x ∈ tors P T k ∧ y ∈ tors P T k := by
  constructor
  · refine pow_eq_one_of_local_lift P k x fun p => ?_
    obtain ⟨V, hV, ⟨θx, θy, hx, -⟩, -⟩ := h p
    exact ⟨V, hV, θx, hx⟩
  · refine pow_eq_one_of_local_lift P k y fun p => ?_
    obtain ⟨V, hV, ⟨θx, θy, -, hy⟩, -⟩ := h p
    exact ⟨V, hV, θy, hy⟩

section Clauses

variable {S : Scheme.{0}} (P : PolAV S) (k : ℕ) (T : Over S)

end Clauses

def unitSpecEquiv (K : Type) [CommRing K] : Kˣ ≃* Γ(Spec (CommRingCat.of K), ⊤)ˣ :=
  Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.toMulEquiv

end GlobalTheory.PairingLawsCompare
