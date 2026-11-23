import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark

theorem finite_bilinForm_abs_le (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (B : X → X → ℤ) :
    {x : LinearMap.BilinForm ℤ X | ∀ a b, |x a b| ≤ B a b}.Finite := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := X)
  let f : LinearMap.BilinForm ℤ X → (s × s → ℤ) := fun x p => x p.1 p.2
  have hf : Function.Injective f := fun x y h =>
    LinearMap.ext_on hs fun a ha => LinearMap.ext_on hs fun b hb => congrFun h (⟨a, ha⟩, ⟨b, hb⟩)
  have hfin : (Set.pi Set.univ fun p : s × s => Set.Icc (-B p.1 p.2) (B p.1 p.2)).Finite :=
    Set.Finite.pi' (fun p : s × s => Set.finite_Icc (-B p.1 p.2) (B p.1 p.2)) |>.subset fun g hg p => hg p trivial
  exact (hfin.preimage hf.injOn).subset fun x hx p _ => abs_le.1 (hx p.1 p.2)

theorem abs_le_of_indec {X : Type} [AddCommGroup X] {m : ℕ} (τ : Fin m → LinearMap.BilinForm ℤ X)
    {x : LinearMap.BilinForm ℤ X} (hx : InRCone τ x)
    (hind : ∀ y z, InRCone τ y → InRCone τ z → y ≠ 0 → z ≠ 0 → y + z ≠ x) (a b : X) :
    |x a b| ≤ ∑ j, |τ j a b| := by
  classical
  obtain ⟨c, hc, h⟩ := hx
  have hv : ∀ a b, ((x a b : ℤ) : ℝ) = ∑ i, c i * (τ i a b : ℝ) := fun a b => by
    have := LinearMap.congr_fun₂ h a b
    simpa [toReal, LinearMap.sum_apply] using this
  by_cases hex : ∃ j, τ j ≠ 0 ∧ 1 ≤ c j
  · obtain ⟨j, hj, hcj⟩ := hex
    have hin : InRCone τ (x - τ j) := by
      refine ⟨c - Pi.single j 1, fun i => ?_, LinearMap.ext₂ fun a b => ?_⟩
      · by_cases hi : i = j
        · subst hi; simpa using hcj
        · simpa [Pi.single_apply, hi] using hc i
      · simp [toReal, LinearMap.sum_apply, sub_mul, Finset.sum_sub_distrib, Pi.single_apply, hv]
    have hx0 : x - τ j = 0 := by
      by_contra h0
      exact hind _ _ hin (inRCone_self τ j) h0 hj (by simp)
    rw [sub_eq_zero.1 hx0]
    exact Finset.single_le_sum (f := fun j => |τ j a b|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  · push Not at hex
    have : ((|x a b| : ℤ) : ℝ) ≤ ((∑ j, |τ j a b| : ℤ) : ℝ) := by
      push_cast
      rw [hv]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      by_cases hi : τ i = 0
      · simp [hi]
      · rw [abs_mul, abs_of_nonneg (hc i)]
        exact mul_le_of_le_one_left (abs_nonneg _) (hex i hi).le
    exact_mod_cast this

theorem finite_indec_inRCone (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (m : ℕ)
    (τ : Fin m → LinearMap.BilinForm ℤ X) :
    {x : LinearMap.BilinForm ℤ X | InRCone τ x ∧ x ≠ 0 ∧
      ∀ y z, InRCone τ y → InRCone τ z → y ≠ 0 → z ≠ 0 → y + z ≠ x}.Finite :=
  (finite_bilinForm_abs_le X fun a b => ∑ j, |τ j a b|).subset fun _ hx => abs_le_of_indec τ hx.1 hx.2.2

end GlobalTheory.PolFan.Mark
