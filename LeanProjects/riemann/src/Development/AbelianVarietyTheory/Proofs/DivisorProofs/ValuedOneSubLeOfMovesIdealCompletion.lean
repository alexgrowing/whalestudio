import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IpEqZeroOfHeisEigen

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

namespace GlobalTheory.CosetOrth

theorem exists_single_adele {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E) :
    ∃ s : FiniteAdeleRing (𝓞 E) E, s w = x ∧ ∀ u, u ≠ w → s u = 0 := by
  refine ⟨⟨Pi.single w x, ?_⟩, ?_, ?_⟩
  · refine Filter.eventually_cofinite.2 ((Set.finite_singleton w).subset fun u hu => ?_)
    by_contra hne
    apply hu
    rw [Pi.single_eq_of_ne hne]
    exact zero_mem _
  · exact Pi.single_eq_same (M := fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletion E) w x
  · intro u hu
    exact Pi.single_eq_of_ne (M := fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletion E) hu x

theorem row_bound {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (hv : Function.Surjective v) {ι : Type} [Fintype ι] (δ h : ι → K) (hδ : ∀ k, v (δ k) ≤ 1) {C : Γ} (hC : 1 < C)
    (H : ∀ x, v x ≤ C → (∀ k, v (x * h k) ≤ C) → ∀ j, v (x * (δ j - h j)) ≤ 1) (j : ι) :
    v (δ j - h j) ≤ C⁻¹ := by
  have hC0 : 0 < C := zero_lt_one.trans hC
  have hint : ∀ k, v (h k) ≤ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨k₀, hk₀⟩ := hcon
    obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun k => v (h k)) ⟨k₀, Finset.mem_univ _⟩
    have h1 : 1 < v (h k) := hk₀.trans_le (hk k₀ (Finset.mem_univ _))
    have h0 : 0 < v (h k) := zero_lt_one.trans h1
    obtain ⟨x, hx⟩ := hv (C * (v (h k))⁻¹)
    have hxk : v x * v (h k) = C := by rw [hx, mul_assoc, inv_mul_cancel₀ h0.ne', mul_one]
    have key := H x (by rw [← hxk]; exact le_mul_of_one_le_right' h1.le)
      (fun l => by rw [map_mul, ← hxk]; gcongr; exact hk l (Finset.mem_univ _)) k
    rw [map_mul, v.map_sub_eq_of_lt_right ((hδ k).trans_lt h1), hxk] at key
    exact absurd hC (not_lt.2 key)
  obtain ⟨x, hx⟩ := hv C
  have key := H x hx.le (fun l => by rw [map_mul, hx]; exact mul_le_of_le_one_right' (hint l)) j
  rw [map_mul, hx] at key
  calc v (δ j - h j) = C⁻¹ * (C * v (δ j - h j)) := by rw [← mul_assoc, inv_mul_cancel₀ hC0.ne', one_mul]
    _ ≤ C⁻¹ * 1 := by gcongr
    _ = C⁻¹ := mul_one _

theorem valued_one_sub_le_of_moves_integral : ∀ {E : Type} [Field E] [NumberField E] (I : FractionalIdeal (𝓞 E)⁰ E) (w : HeightOneSpectrum (𝓞 E)) (c : ℤ) (n : E)
  {a : ℕ} (H : Matrix (Fin a) (Fin a) (FiniteAdeleRing (𝓞 E) E)), w.valuation E n = 1 → FractionalIdeal.count E w I = -c → 1 ≤ c →
  (∀ (s : FiniteAdeleRing (𝓞 E) E) (i j : Fin a), InHat I s → (∀ k, InHat I (s * H i k)) →
    InHat 1 (algebraMap E (FiniteAdeleRing (𝓞 E) E) n * (s * (1 - H) i j))) →
  ∀ i j, Valued.v ((1 - H) i j w) ≤ WithZero.exp (-c) := by
  intro E _ _ I w c n a H hn hI hc hH i j
  have hsub : ∀ l, (1 - H) i l w = (1 : Matrix (Fin a) (Fin a) (FiniteAdeleRing (𝓞 E) E)) i l w - H i l w :=
    fun l => rfl
  rw [hsub, WithZero.exp_neg]
  refine row_bound Valued.v (w.valuedAdicCompletion_surjective E)
    (fun l => (1 : Matrix (Fin a) (Fin a) (FiniteAdeleRing (𝓞 E) E)) i l w) (fun l => H i l w) (fun k => ?_) ?_ ?_ j
  · by_cases hik : i = k
    · subst hik
      rw [Matrix.one_apply_eq]
      have : (1 : FiniteAdeleRing (𝓞 E) E) w = 1 := rfl
      rw [this, map_one]
    · rw [Matrix.one_apply_ne hik]
      have : (0 : FiniteAdeleRing (𝓞 E) E) w = 0 := rfl
      rw [this, map_zero]; exact zero_le
  · rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  · intro x hx hxh l
    obtain ⟨s, hsw, hsu⟩ := exists_single_adele w x
    have h1 : InHat I s := fun u => by
      by_cases hu : u = w
      · subst hu; rw [hsw, hI, neg_neg]; exact hx
      · rw [hsu u hu, map_zero]; exact zero_le
    have h2 : ∀ k, InHat I (s * H i k) := fun k u => by
      have : (s * H i k) u = s u * H i k u := rfl
      rw [this]
      by_cases hu : u = w
      · subst hu; rw [hsw, hI, neg_neg]; exact hxh k
      · rw [hsu u hu, zero_mul, map_zero]; exact zero_le
    have key := (inHat_one_iff _).1 (hH s i l h1 h2) w
    have e : (algebraMap E (FiniteAdeleRing (𝓞 E) E) n * (s * (1 - H) i l)) w =
        (n : w.adicCompletion E) * (s w * (1 - H) i l w) := rfl
    rw [e, map_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hn, one_mul, hsw, hsub] at key
    exact key

end GlobalTheory.CosetOrth
