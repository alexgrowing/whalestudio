import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open NumberField IsDedekindDomain GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier AlgebraicGeometry CategoryTheory

namespace GlobalTheory.HtDiff

theorem abs_finsum_sub_le {V : Type} (f₁ f₂ b : V → ℝ) (S : Finset V) (c : ℝ)
    (hS : ∀ v ∉ S, f₁ v = f₂ v) (hb : ∀ v, |f₁ v - f₂ v| ≤ c * b v) :
    |∑ᶠ v, f₁ v - ∑ᶠ v, f₂ v| ≤ max 0 (c * ∑ v ∈ S, b v) := by
  have hsub : Function.support (fun v => f₁ v - f₂ v) ⊆ (S : Set V) := by
    intro v hv
    by_contra h
    exact hv (by simp [hS v h])
  have h12 : Function.support f₁ ⊆ Function.support f₂ ∪ (S : Set V) := by
    intro v hv
    by_cases h : v ∈ S
    · exact Or.inr h
    · exact Or.inl (by rw [Function.mem_support, ← hS v h]; exact hv)
  have h21 : Function.support f₂ ⊆ Function.support f₁ ∪ (S : Set V) := by
    intro v hv
    by_cases h : v ∈ S
    · exact Or.inr h
    · exact Or.inl (by rw [Function.mem_support, hS v h]; exact hv)
  by_cases h1 : (Function.support f₁).Finite
  · have h2 : (Function.support f₂).Finite := (h1.union S.finite_toSet).subset h21
    rw [← finsum_sub_distrib h1 h2, finsum_eq_sum_of_support_subset _ hsub]
    refine le_max_of_le_right ((Finset.abs_sum_le_sum_abs _ _).trans ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun v _ => hb v
  · have h2 : ¬ (Function.support f₂).Finite := fun h2 => h1 ((h2.union S.finite_toSet).subset h12)
    rw [finsum_of_infinite_support h1, finsum_of_infinite_support h2]
    simp

theorem abs_finsum_mem_sub_le {Z : Type} (p : Z → Prop) (hp : Finite {z // p z}) (φ₁ φ₂ : Z → ℝ) (b : ℝ)
    (hb : ∀ z, |φ₁ z - φ₂ z| ≤ b) :
    |(∑ᶠ (z) (_ : p z), φ₁ z) - ∑ᶠ (z) (_ : p z), φ₂ z| ≤ (Nat.card {z // p z} : ℝ) * b := by
  have hs : ({z | p z} : Set Z).Finite := Set.finite_coe_iff.1 hp
  change |(∑ᶠ (z) (_ : z ∈ {z | p z}), φ₁ z) - ∑ᶠ (z) (_ : z ∈ {z | p z}), φ₂ z| ≤
    (Nat.card ({z | p z} : Set Z) : ℝ) * b
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, finsum_mem_eq_finite_toFinset_sum _ hs,
    Nat.card_eq_card_finite_toFinset hs, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun z _ => hb z).trans ?_
  simp

end GlobalTheory.HtDiff

open GlobalTheory.HtDiff in

theorem GlobalTheory.TrueGeo.Adl.abs_ht_sub_ht_with_lg_le {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}
    (A : Adl C Y) (g : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) (x : Y.X)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (b : HeightOneSpectrum (𝓞 F) → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hS : ∀ v ∉ S, ∀ e y, A.lg v e y = g v e y) (hb : ∀ v e y, |A.lg v e y - g v e y| ≤ b v)
    (hsum : ∑ v ∈ S, b v ≤ ((A.n : ℕ) : ℝ) * (Module.finrank ℚ F : ℝ) * K) :
    |A.ht x - ({ A with lg := g } : Adl C Y).ht x| ≤ K := by
  classical
  set c : ℕ := Nat.card {y : AlgPt Y // below y.1 = x} with hc
  set f₁ : HeightOneSpectrum (𝓞 F) → ℝ := fun v => if h : Nonempty (Ext v) then
      ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), A.lg v h.some y else 0 with hf₁
  set f₂ : HeightOneSpectrum (𝓞 F) → ℝ := fun v => if h : Nonempty (Ext v) then
      ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), g v h.some y else 0 with hf₂
  set I : ℝ := ∑ σ : F →+* ℂ, ∑ᶠ (z : Pts Y σ) (_ : under z = x),
      (Real.log (C.pn Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D x)⁻¹ : Y.Fnˣ)) z) / 2 -
        (A.n : ℕ) * A.ci (InfinitePlace.mk σ)) with hI
  have e₁ : A.ht x = -(I + ∑ᶠ v, f₁ v) / (((A.n : ℕ) : ℝ) * (Module.finrank ℚ F : ℝ) * (c : ℝ)) := rfl
  have e₂ : ({ A with lg := g } : Adl C Y).ht x =
      -(I + ∑ᶠ v, f₂ v) / (((A.n : ℕ) : ℝ) * (Module.finrank ℚ F : ℝ) * (c : ℝ)) := rfl
  rw [e₁, e₂]
  by_cases hc0 : c = 0
  · simp [hc0, hK]
  have hfin : Finite {y : AlgPt Y // below y.1 = x} := Nat.finite_of_card_ne_zero hc0
  have hbv : ∀ v, |f₁ v - f₂ v| ≤ (c : ℝ) * b v := by
    intro v
    simp only [hf₁, hf₂]
    split_ifs with h
    · exact abs_finsum_mem_sub_le (fun y : AlgPt Y => below y.1 = x) hfin _ _ _ fun y => hb v _ y
    · exact absurd (Ext.instNonempty v) h
  have hSv : ∀ v ∉ S, f₁ v = f₂ v := by
    intro v hv
    have : A.lg v = g v := funext fun e => funext fun y => hS v hv e y
    simp only [hf₁, hf₂, this]
  have key := abs_finsum_sub_le f₁ f₂ b S (c : ℝ) hSv hbv
  have hd : 0 < ((A.n : ℕ) : ℝ) * (Module.finrank ℚ F : ℝ) * (c : ℝ) := by
    have h1 : 0 < ((A.n : ℕ) : ℝ) := by exact_mod_cast (A.n).pos
    have h2 : 0 < (Module.finrank ℚ F : ℝ) := by exact_mod_cast Module.finrank_pos
    have h3 : 0 < (c : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hc0
    positivity
  rw [← sub_div, abs_div, abs_of_pos hd, div_le_iff₀ hd]
  have e : -(I + ∑ᶠ v, f₁ v) - -(I + ∑ᶠ v, f₂ v) = -(∑ᶠ v, f₁ v - ∑ᶠ v, f₂ v) := by ring
  rw [e, abs_neg]
  refine key.trans (max_le (by positivity) ?_)
  have hc' : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  calc (c : ℝ) * ∑ v ∈ S, b v ≤ c * (((A.n : ℕ) : ℝ) * (Module.finrank ℚ F : ℝ) * K) :=
        mul_le_mul_of_nonneg_left hsum hc'
    _ = K * (((A.n : ℕ) : ℝ) * (Module.finrank ℚ F : ℝ) * (c : ℝ)) := by ring
