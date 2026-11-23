import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StSmallGenHeightsNonneg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

namespace SmallGenHeightsNonneg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def killBlocksBelow (j : ℕ) : MRing ι →+* MRing ι :=
  eval₂Hom C fun p ↦ if ((Fintype.equivFin K p.1 : Fin _) : ℕ) < j then 0 else X p

theorem killBlocksBelow_X (j : ℕ) (p : Σ k, ι k) :
    killBlocksBelow j (X p : MRing ι) =
      if ((Fintype.equivFin K p.1 : Fin _) : ℕ) < j then 0 else X p := by
  simp [killBlocksBelow]

theorem killBlocksBelow_C (j : ℕ) (c : ℤ) : killBlocksBelow j (C c : MRing ι) = C c := by
  simp [killBlocksBelow]

theorem killBlocksBelow_monomial (j : ℕ) (m : (Σ k, ι k) →₀ ℕ) (c : ℤ) :
    killBlocksBelow j (monomial m c : MRing ι) =
      if ∀ p ∈ m.support, ¬ ((Fintype.equivFin K p.1 : Fin _) : ℕ) < j then monomial m c else 0 := by
  rw [killBlocksBelow, coe_eval₂Hom, eval₂_monomial]
  split_ifs with h
  · rw [monomial_eq, Finsupp.prod, Finsupp.prod]
    congr 1
    refine Finset.prod_congr rfl fun p hp ↦ ?_
    rw [if_neg (h p hp)]
  · push Not at h
    obtain ⟨p, hp, hlt⟩ := h
    rw [Finsupp.prod, Finset.prod_eq_zero hp, mul_zero]
    rw [if_pos hlt, zero_pow (Finsupp.mem_support_iff.mp hp)]

theorem killBlocksBelow_of_isMultiHomog (j : ℕ) {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    killBlocksBelow j f = f ∨ killBlocksBelow j f = 0 := by
  by_cases h : ∀ k, ((Fintype.equivFin K k : Fin _) : ℕ) < j → a k = 0
  · left
    conv_rhs => rw [f.as_sum]
    conv_lhs => rw [f.as_sum, map_sum]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    rw [killBlocksBelow_monomial, if_pos]
    intro p hp hlt
    have hsum := hf m hm p.1
    rw [h p.1 hlt, Finset.sum_eq_zero_iff] at hsum
    exact Finsupp.mem_support_iff.mp hp (hsum p.2 (Finset.mem_univ _))
  · right
    push Not at h
    obtain ⟨k, hk, hak⟩ := h
    conv_lhs => rw [f.as_sum, map_sum]
    refine Finset.sum_eq_zero fun m hm ↦ ?_
    rw [killBlocksBelow_monomial, if_neg]
    push Not
    have hsum := hf m hm k
    rw [← hsum] at hak
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hak
    exact ⟨⟨k, i⟩, Finsupp.mem_support_iff.mpr hi, hk⟩

theorem le_comap_killBlocksBelow (j : ℕ) {V : Ideal (MRing ι)} (hV : IsMultiHomogIdeal V) :
    V ≤ V.comap (killBlocksBelow j) := by
  obtain ⟨S, hS, rfl⟩ := hV
  rw [Ideal.span_le]
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  rcases killBlocksBelow_of_isMultiHomog j ha with h | h
  · rw [SetLike.mem_coe, Ideal.mem_comap, h]
    exact Ideal.subset_span hf
  · rw [SetLike.mem_coe, Ideal.mem_comap, h]
    exact zero_mem _

theorem killBlocksBelow_comp {j j' : ℕ} (hj : j ≤ j') :
    (killBlocksBelow j' : MRing ι →+* MRing ι).comp (killBlocksBelow j) = killBlocksBelow j' := by
  refine MvPolynomial.ringHom_ext (fun c ↦ ?_) fun p ↦ ?_
  · simp
  · rw [RingHom.comp_apply, killBlocksBelow_X j p]
    split_ifs with h1
    · rw [map_zero, killBlocksBelow_X, if_pos (by omega)]
    · rfl

theorem killBlocksBelow_card (f : MRing ι) :
    killBlocksBelow (Fintype.card K) f = C (constantCoeff f) := by
  have : (killBlocksBelow (Fintype.card K) : MRing ι →+* MRing ι) = C.comp constantCoeff := by
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) fun p ↦ ?_
    · simp
    · rw [killBlocksBelow_X, if_pos (Fin.isLt _)]
      simp
  rw [this, RingHom.comp_apply]

def chainIdeal (V : Ideal (MRing ι)) (j : ℕ) : Ideal (MRing ι) :=
  if j ≤ Fintype.card K then V.comap (killBlocksBelow j)
  else (Ideal.span {(2 : ℤ)}).comap (constantCoeff : MRing ι →+* ℤ)

theorem chainIdeal_isPrime {V : Ideal (MRing ι)} (hV : V.IsPrime) (j : ℕ) : (chainIdeal V j).IsPrime := by
  have : (Ideal.span {(2 : ℤ)}).IsPrime := (Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two
  unfold chainIdeal
  split_ifs
  · exact Ideal.comap_isPrime _ _
  · exact Ideal.comap_isPrime _ _

theorem comap_card_le_even {V : Ideal (MRing ι)} (hVm : IsMultiHomogIdeal V) (hh : IsHorizontal V) :
    V.comap (killBlocksBelow (Fintype.card K)) ≤ (Ideal.span {(2 : ℤ)}).comap (constantCoeff : MRing ι →+* ℤ) :=
  fun f hf ↦ by
    rw [Ideal.mem_comap, killBlocksBelow_card] at hf
    have h0 : constantCoeff f ∈ V.comap (C : ℤ →+* MRing ι) := hf
    rw [hh, Ideal.mem_bot] at h0
    rw [Ideal.mem_comap, h0]
    exact zero_mem _

theorem le_chainIdeal {V : Ideal (MRing ι)} (hVm : IsMultiHomogIdeal V) (hh : IsHorizontal V) (j : ℕ) :
    V ≤ chainIdeal V j := by
  unfold chainIdeal
  split_ifs
  · exact le_comap_killBlocksBelow j hVm
  · exact (le_comap_killBlocksBelow _ hVm).trans (comap_card_le_even hVm hh)

theorem comap_killBlocksBelow_le_succ {V : Ideal (MRing ι)} (hVm : IsMultiHomogIdeal V) (j : ℕ) :
    V.comap (killBlocksBelow j) ≤ V.comap (killBlocksBelow (j + 1)) := by
  intro f hf
  have h := le_comap_killBlocksBelow (j + 1) hVm hf
  rw [Ideal.mem_comap, ← RingHom.comp_apply, killBlocksBelow_comp (Nat.le_succ j)] at h
  exact h

theorem X_mem_comap_killBlocksBelow_succ {V : Ideal (MRing ι)} {j : ℕ} (hj : j < Fintype.card K)
    (i : ι ((Fintype.equivFin K).symm ⟨j, hj⟩)) :
    (X ⟨(Fintype.equivFin K).symm ⟨j, hj⟩, i⟩ : MRing ι) ∈ V.comap (killBlocksBelow (j + 1)) := by
  rw [Ideal.mem_comap, killBlocksBelow_X, if_pos]
  · exact zero_mem _
  · simp only [Equiv.apply_symm_apply]
    exact Nat.lt_succ_self j

theorem X_mem_comap_killBlocksBelow_iff {V : Ideal (MRing ι)} {j : ℕ} (hj : j < Fintype.card K)
    (i : ι ((Fintype.equivFin K).symm ⟨j, hj⟩)) :
    (X ⟨(Fintype.equivFin K).symm ⟨j, hj⟩, i⟩ : MRing ι) ∈ V.comap (killBlocksBelow j) ↔
      (X ⟨(Fintype.equivFin K).symm ⟨j, hj⟩, i⟩ : MRing ι) ∈ V := by
  rw [Ideal.mem_comap, killBlocksBelow_X, if_neg]
  simp only [Equiv.apply_symm_apply]
  exact lt_irrefl j

theorem chainIdeal_lt_succ_of_lt {V : Ideal (MRing ι)} (hV : IsMultiProjPrime V) {j : ℕ}
    (hj : j < Fintype.card K) : chainIdeal V j < chainIdeal V (j + 1) := by
  obtain ⟨-, hVm, hVr⟩ := hV
  rw [chainIdeal, chainIdeal, if_pos hj.le, if_pos (Nat.succ_le_of_lt hj)]
  refine lt_of_le_of_ne (comap_killBlocksBelow_le_succ hVm j) fun h ↦ ?_
  obtain ⟨i, hi⟩ := hVr ((Fintype.equivFin K).symm ⟨j, hj⟩)
  have h1 := X_mem_comap_killBlocksBelow_succ (V := V) hj i
  rw [← h, X_mem_comap_killBlocksBelow_iff hj i] at h1
  exact hi h1

theorem chainIdeal_card_lt {V : Ideal (MRing ι)} (hV : IsMultiProjPrime V) (hh : IsHorizontal V) :
    chainIdeal V (Fintype.card K) < chainIdeal V (Fintype.card K + 1) := by
  obtain ⟨-, hVm, -⟩ := hV
  rw [chainIdeal, chainIdeal, if_pos le_rfl, if_neg (Nat.not_succ_le_self _)]
  refine lt_of_le_of_ne (comap_card_le_even hVm hh) fun h ↦ ?_
  have h2 : (C (2 : ℤ) : MRing ι) ∈ (Ideal.span {(2 : ℤ)}).comap (constantCoeff : MRing ι →+* ℤ) := by
    rw [Ideal.mem_comap, constantCoeff_C]
    exact Ideal.mem_span_singleton_self 2
  rw [← h, Ideal.mem_comap, killBlocksBelow_C] at h2
  have h0 : (2 : ℤ) ∈ V.comap (C : ℤ →+* MRing ι) := h2
  rw [hh, Ideal.mem_bot] at h0
  exact two_ne_zero h0

theorem chainIdeal_lt_succ {V : Ideal (MRing ι)} (hV : IsMultiProjPrime V) (hh : IsHorizontal V) {j : ℕ}
    (hj : j ≤ Fintype.card K) : chainIdeal V j < chainIdeal V (j + 1) := by
  rcases lt_or_eq_of_le hj with hj | rfl
  · exact chainIdeal_lt_succ_of_lt hV hj
  · exact chainIdeal_card_lt hV hh

theorem card_add_one_le_ringKrullDim {V : Ideal (MRing ι)} (hV : IsMultiProjPrime V)
    (hh : IsHorizontal V) :
    ((Fintype.card K + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι ⧸ V) := by
  rw [ringKrullDim_quotient]
  let p : LTSeries (PrimeSpectrum.zeroLocus (R := MRing ι) (V : Set (MRing ι))) :=
    { length := Fintype.card K + 1
      toFun := fun i ↦ ⟨⟨chainIdeal V i, chainIdeal_isPrime hV.1 i⟩,
        show (V : Set (MRing ι)) ⊆ chainIdeal V i from le_chainIdeal hV.2.1 hh i⟩
      step := fun i ↦ by
        show chainIdeal V i.castSucc < chainIdeal V i.succ
        rw [Fin.val_succ, Fin.coe_castSucc]
        exact chainIdeal_lt_succ hV hh (Nat.lt_succ_iff.mp i.isLt) }
  exact Order.LTSeries.length_le_krullDim p

theorem not_isHorizontal_of_mem_divSupp {W : Ideal (MRing ι)} {A : HermLine ι} {s : MRing ι}
    (hW : IsArithVar W 1) (hs : IsSectionOn W A s) {V : Ideal (MRing ι)} (hV : V ∈ divSupp W s) :
    ¬ IsHorizontal V := by
  intro hh
  obtain ⟨-, hVm, hVh, hdim⟩ := (divSuppArith K ι W 0 A s V hW hs hV).1 hh
  have key := card_add_one_le_ringKrullDim hVm hVh
  rw [hdim, zero_add] at key
  have : Fintype.card K + 1 ≤ Fintype.card K := by exact_mod_cast key
  omega

theorem finsum_mem_nonpos' {α : Type*} (S : Set α) (f : α → ℝ) (h : ∀ x ∈ S, f x ≤ 0) :
    ∑ᶠ x ∈ S, f x ≤ 0 := by
  have : 0 ≤ -∑ᶠ x ∈ S, f x := by
    rw [← finsum_neg_distrib]
    refine finsum_nonneg fun x ↦ ?_
    rw [← finsum_neg_distrib]
    exact finsum_nonneg fun hx ↦ neg_nonneg.mpr (h x hx)
  linarith

theorem maDensity_fin_zero (φ : Fin 0 → (Fin 0 → ℂ) → ℝ) (z : Fin 0 → ℂ) : maDensity φ z = 1 := by
  simp [maDensity, mixedDisc]

theorem arInt_nonpos {W : Ideal (MRing ι)} {A : HermLine ι} {s : MRing ι}
    (hsm : ∀ z ∈ mcPts W, ‖eval z (map (Int.castRingHom ℂ) s)‖ ≤ A.h z) :
    arInt W s A (Fin.elim0 : Fin 0 → HermLine ι) ≤ 0 := by
  unfold arInt ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    refine integral_nonpos fun y ↦ ?_
    refine finsum_mem_nonpos' _ _ fun w _ ↦ ?_
    unfold sheetDensity
    split_ifs with hγ
    · have hz : hγ.choose y ∈ mcPts W := hγ.choose_spec.2.self_of_nhds.2.1
      rw [maDensity_fin_zero, mul_one]
      unfold logNorm
      have hpos := A.pos _ hz.1
      exact Real.log_nonpos (div_nonneg (norm_nonneg _) hpos.le)
        ((div_le_one hpos).mpr (hsm _ hz))
    · exact le_rfl
  · exact le_rfl

end SmallGenHeightsNonneg

open SmallGenHeightsNonneg in

theorem SmallGenHeightsNonneg.proof : SmallGenHeightsNonneg.Statement := by
  intro K _ ι _ P A II q w hII hA hAnn hw hgen hsmall W hW hPW
  obtain ⟨j, hj⟩ := hgen W hW.2.1 hPW
  set a : K → ℕ := fun k ↦ (A.a k).toNat
  have ha : ∀ k, A.a k = a k := fun k ↦ (Int.toNat_of_nonneg (hAnn k)).symm
  have hR := (hII K ι).2.2 W 0 (Fin.elim0 : Fin 0 → HermLine ι) A (w j) a hW
    (fun i ↦ i.elim0) hA ha (hw j) hj
  have e : (Fin.snoc (α := fun _ ↦ HermLine ι) (Fin.elim0 : Fin 0 → HermLine ι) A : Fin 1 → HermLine ι) =
      ![A] := by
    funext i
    fin_cases i
    rfl
  have key : II K ι W 1 ![A] = recR (II K ι) W (Fin.elim0 : Fin 0 → HermLine ι) A (w j) := by
    rw [← e]
    exact hR
  rw [key, recR]
  have hsm : ∀ z ∈ mcPts W, ‖eval z (map (Int.castRingHom ℂ) (w j))‖ ≤ A.h z := fun z hz ↦
    hsmall j z ⟨hz.1, fun f hf ↦ hz.2 f (hPW hf)⟩
  refine sub_nonneg.mpr ((arInt_nonpos hsm).trans ?_)
  refine finsum_nonneg fun V ↦ finsum_nonneg fun hV ↦ ?_
  rw [if_neg (not_isHorizontal_of_mem_divSupp hW ⟨a, ha, hw j, hj⟩ hV)]
  have hg : (0 : ℝ) ≤ geoNum 0 V (fun i ↦ ((Fin.elim0 : Fin 0 → HermLine ι) i).a) := by
    unfold geoNum
    split_ifs <;> positivity
  exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hg (Real.log_natCast_nonneg _))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
