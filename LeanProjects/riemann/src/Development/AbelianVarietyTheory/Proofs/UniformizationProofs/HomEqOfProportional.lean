import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomEqOfPullSections
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ProjUniq

theorem hom_eq_of_proportional : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (f : Z ⟶ Spec (CommRingCat.of R)) (H : LB Z) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (T : Scheme.{0}) (φ ψ : T ⟶ Z), φ ≫ f = ψ ≫ f → (∀ z k k' i i', φ z ∈ H.U k → ψ z ∈ H.U k' → gs φ z (H.U k) ((s i).f k) * gs ψ z (H.U k') ((s i').f k') = gs φ z (H.U k) ((s i').f k) * gs ψ z (H.U k') ((s i).f k')) → φ = ψ := by
  intro R _ Z f H n s hH hs T φ ψ hf h
  choose r hr hsurj using fun i => (hs.2 i).2
  have hm : ∀ i z, φ z ∈ nonzeroLocus (s i) → ψ z ∈ nonzeroLocus (s i) := fun i z hz => by
    obtain ⟨k, hk⟩ := exists_chart hH (φ z)
    obtain ⟨k', hk'⟩ := exists_chart hH (ψ z)
    obtain ⟨i', hi'⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show ψ z ∈ ⨆ i, nonzeroLocus (s i) by rw [hs.1]; trivial)
    rw [AmpleSpan.mem_nonzeroLocus_iff_gs (s i) φ z hk] at hz
    rw [AmpleSpan.mem_nonzeroLocus_iff_gs (s i') ψ z hk'] at hi'
    rw [AmpleSpan.mem_nonzeroLocus_iff_gs (s i) ψ z hk']
    have hu := hz.mul hi'
    rw [h z k k' i i' hk hk'] at hu
    exact isUnit_of_mul_isUnit_right hu
  refine MapUniq.hom_ext_of_gs (fun i => nonzeroLocus (s i)) (fun i => (hs.2 i).1) hs.1 φ ψ hm
    fun i z hz a => ?_
  obtain ⟨k, hk⟩ := exists_chart hH (φ z)
  obtain ⟨k', hk'⟩ := exists_chart hH (ψ z)
  have hz' := hm i z hz
  have hrr : ∀ j, gs φ z _ (r i j) = gs ψ z _ (r i j) := fun j => by
    have e₁ := AmpleSpan.IsRatio.gs (s := s j) (t := s i) (r := r i j) (hr i j) φ z hz hk
    have e₂ := AmpleSpan.IsRatio.gs (s := s j) (t := s i) (r := r i j) (hr i j) ψ z hz' hk'
    have u₁ := (AmpleSpan.mem_nonzeroLocus_iff_gs (s i) φ z hk).1 hz
    have u₂ := (AmpleSpan.mem_nonzeroLocus_iff_gs (s i) ψ z hk').1 hz'
    have e := h z k k' j i hk hk'
    rw [e₁, e₂] at e
    refine (u₁.mul u₂).mul_right_cancel ?_
    linear_combination e
  obtain ⟨p, rfl⟩ := hsurj i a
  induction p using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.eval₂Hom_C, MapUniq.gs_cst f φ z _ hz, MapUniq.gs_cst f ψ z _ hz', hf]
  | add p q hp hq => rw [map_add, gs_add φ z _ hz, gs_add ψ z _ hz', hp, hq]
  | mul_X p j hp => rw [map_mul, MvPolynomial.eval₂Hom_X', gs_mul φ z _ hz, gs_mul ψ z _ hz', hp, hrr]

end GlobalTheory.ProjUniq
