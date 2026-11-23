import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem single_mem_span_iff_of_selfDual : ∀ (O R K La I : Type) [CommRing O] [CommRing R] [Field K] [Algebra R K] [AddCommGroup La] [Module O La] [Fintype I] [DecidableEq I] (τ₀ : O →+* R) (h : La → La → O) (ev dv : La → I → K) (n : ℕ) (x y : Fin n → La), (∀ a b, algebraMap R K (τ₀ (h a b)) = ∑ i, ev a i * dv b i) → (∀ a, ev a = ∑ m, algebraMap R K (τ₀ (h a (y m))) • ev (x m)) → Submodule.span K (Set.range ev) = ⊤ → ∀ (i : I) (t : K), Pi.single i t ∈ Submodule.span R (Set.range ev) ↔ ∀ b, t * dv b i ∈ (algebraMap R K).range := by
  intro O R K La I _ _ _ _ _ _ _ _ τ₀ h ev dv n x y hh hev hspan i t
  have hsum : ∀ b, ∑ j, (Pi.single i t : I → K) j * dv b j = t * dv b i := by
    intro b
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  constructor
  · intro hm b
    rw [← hsum b]
    generalize (Pi.single i t : I → K) = v at hm
    induction hm using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, rfl⟩ := hv
      exact ⟨_, hh a b⟩
    | zero => simp
    | add u w _ _ hu hw =>
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      exact add_mem hu hw
    | smul r u _ hu =>
      have : ∑ j, (r • u) j * dv b j = algebraMap R K r * ∑ j, u j * dv b j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Pi.smul_apply, Algebra.smul_def, _root_.mul_assoc]
      rw [this]
      exact mul_mem ⟨r, rfl⟩ hu
  · intro hb
    have key : ∀ v : I → K, v = ∑ m, (∑ j, v j * dv (y m) j) • ev (x m) := by
      intro v
      have hv : v ∈ Submodule.span K (Set.range ev) := hspan ▸ Submodule.mem_top
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨a, rfl⟩ := hv
        simp only [← hh]
        exact hev a
      | zero => simp
      | add u w _ _ hu hw =>
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, add_smul]
        rw [← hu, ← hw]
      | smul r u _ hu =>
        simp only [Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, ← Finset.mul_sum, mul_smul,
          ← Finset.smul_sum]
        rw [← hu]
    rw [key (Pi.single i t)]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [hsum]
    obtain ⟨r, hr⟩ := hb (y m)
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end GlobalTheory.CM
