import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIntegersTensorEqLetterwiseProductAinf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SeedSec

theorem eq_of_pow_eq_self {R K : Type} [CommRing R] [Field K] [CharZero K] (θ : R →+* K)
    (hθ : ∀ y, θ y ≠ 0 → IsUnit y) {n : ℕ} (hn : 2 ≤ n) {u v : R} (hu : u ^ n = u) (hv : v ^ n = v)
    (h : θ u = θ v) : u = v := by
  set S := ∑ i ∈ Finset.range n, u ^ i * v ^ (n - 1 - i) with hS
  have h1 : S * (u - v) = u - v := by rw [hS, geom_sum₂_mul, hu, hv]
  have hc : θ u ^ n = θ u := by rw [← map_pow, hu]
  have e : θ S = n * θ u ^ (n - 1) := by
    rw [hS, map_sum, Finset.sum_congr rfl (g := fun _ => θ u ^ (n - 1)) (fun i hi => by
      have := Finset.mem_range.1 hi
      rw [map_mul, map_pow, map_pow, ← h, ← pow_add]
      congr 1
      omega)]
    simp
  have h2 : θ (S - 1) ≠ 0 := by
    rw [map_sub, map_one, e]
    by_cases h0 : θ u = 0
    · rw [h0, zero_pow (by omega)]
      simp
    · have h3 : θ u ^ (n - 1) = 1 := by
        refine mul_right_cancel₀ h0 ?_
        rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul, hc]
      rw [h3, mul_one, sub_ne_zero]
      exact_mod_cast (show n ≠ 1 by omega)
  have h4 : (S - 1) * (u - v) = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  exact sub_eq_zero.1 ((hθ _ h2).mul_right_eq_zero.1 h4)

theorem exists_om_of_pow_eq_self (l : ℕ) [Fact l.Prime] {n : ℕ} (hn : 2 ≤ n) (c : ℂ_[l]) (hc : c ^ n = c) :
    ∃ x : Om l, algebraMap (Om l) ℂ_[l] x = c := by
  have hs : (Polynomial.X ^ n - Polynomial.X : Polynomial (Om l)).Splits := IsAlgClosed.splits _
  have h0 : (Polynomial.X ^ n - Polynomial.X : Polynomial (Om l)) ≠ 0 := fun h => by
    have := congrArg (Polynomial.coeff · 1) h
    simp [Polynomial.coeff_X_pow, show (1 : ℕ) ≠ n by omega] at this
  obtain ⟨x, hx⟩ := hs.mem_range_of_isRoot h0 (i := algebraMap (Om l) ℂ_[l]) (x := c) (by simp [hc])
  exact ⟨x, hx⟩

private theorem padicInt_hom_apply_eq {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R]
    (hR : IsHausdorff (Ideal.span {(l : R)}) R) (f g : ℤ_[l] →+* R) (z : ℤ_[l]) : f z = g z := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus hR _ fun n => ?_
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨f c - g c, ?_⟩
  have hf := congrArg f hc
  have hg := congrArg g hc
  simp only [map_mul, map_pow, map_natCast, map_sub] at hf hg
  linear_combination hf - hg

theorem exists_sec (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Core l) (w : Wq l a) :
    ∃ x : Om l, ((Per.θ l (wA l a w) : OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] x ∧
      C.o x = aDp l (wA l a w) := by
  have hspan : w ∈ Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l a → Wq l a)) := by
    rw [span_teich]; trivial
  induction hspan using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, rfl⟩ := hy
    have hq : 2 ≤ l ^ a := one_lt_pow_l l a
    have hw : (WittVector.teichmuller l z) ^ (l ^ a) = WittVector.teichmuller l z := by
      rw [← map_pow, Fq.pow_card]
    set A := wA l a (WittVector.teichmuller l z) with hAdef
    have hA : A ^ (l ^ a) = A := by rw [hAdef, ← map_pow, hw]
    have hc : ((Per.θ l A : OC l) : ℂ_[l]) ^ (l ^ a) = ((Per.θ l A : OC l) : ℂ_[l]) := by
      rw [← SubmonoidClass.coe_pow, ← map_pow, hA]
    obtain ⟨x, hx⟩ := exists_om_of_pow_eq_self l hq _ hc
    have hxq : x ^ (l ^ a) = x := (algebraMap (Om l) ℂ_[l]).injective (by rw [map_pow, hx, hc])
    refine ⟨x, hx.symm, eq_of_pow_eq_self (Per.θD l) (thetaD_props l).2.2.1 hq
      (by rw [← map_pow, hxq]) (by rw [← map_pow, hA]) ?_⟩
    rw [C.o_sec.th, (thetaD_props l).2.2.2.1]
    exact hx
  | zero => exact ⟨0, by simp, by simp⟩
  | add y y' _ _ hy hy' =>
    obtain ⟨x, hx1, hx2⟩ := hy
    obtain ⟨x', hx1', hx2'⟩ := hy'
    refine ⟨x + x', ?_, ?_⟩
    · rw [map_add, map_add, map_add, Subring.coe_add, hx1, hx1']
    · rw [map_add, map_add, map_add, hx2, hx2']
  | smul r y _ hy =>
    obtain ⟨x, hx1, hx2⟩ := hy
    have e : wA l a (r • y) = algebraMap ℤ_[l] (Ainf l) r * wA l a y := by
      rw [map_smul, Algebra.smul_def]
    refine ⟨algebraMap ℚ_[l] (Om l) (r : ℚ_[l]) * x, ?_, ?_⟩
    · rw [e, map_mul, Subring.coe_mul, hx1, map_mul]
      congr 1
      exact GlobalTheory.UnramIdem.ringHom_eq ((Per.θ l).comp (algebraMap ℤ_[l] (Ainf l))) r
    · rw [e, map_mul, map_mul, hx2, C.o_sec.z r]
      have hA : IsAdicComplete (Ideal.span {(l : Ainf l)}) (Ainf l) := inferInstance
      rw [padicInt_hom_apply_eq hA.toIsHausdorff (Per.zA l) (algebraMap ℤ_[l] (Ainf l)) r]

theorem o_eq_aDp_wA : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Core l) (w : Wq l a) (x : Om l),
    ((Per.θ l (wA l a w) : OC l) : ℂ_[l]) = (x : ℂ_[l]) → C.o x = aDp l (wA l a w) := by
  intro l _ a _ C w x hx
  obtain ⟨y, hy1, hy2⟩ := exists_sec l a C w
  have hxy : x = y := (algebraMap (Om l) ℂ_[l]).injective (hx.symm.trans hy1)
  rw [hxy, hy2]

end GlobalTheory.SeedSec
