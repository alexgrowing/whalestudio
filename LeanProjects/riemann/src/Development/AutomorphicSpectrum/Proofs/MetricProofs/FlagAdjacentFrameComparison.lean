import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DetFacChange
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Move

section Minors

open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

variable {N j : ℕ}

theorem minor_w_mul (S : Matrix (Fin N) (Fin N) ℂ) {h : Matrix (Fin N) (Fin N) ℂ} (hh : IsBlockDiag j h) :
    minorIJ (S * h) (wIdx N j) (wIdx N j) = minorIJ S (wIdx N j) (wIdx N j) * minorIJ h (wIdx N j) (wIdx N j) :=
  minorIJ_mul_of_support S h _ _ (support_wIdx hh)

theorem minor_om_mul (S : Matrix (Fin N) (Fin N) ℂ) {h : Matrix (Fin N) (Fin N) ℂ} (hh : IsBlockDiag j h) :
    minorIJ (S * h) (omIdx N j) (omIdx N j) = minorIJ S (omIdx N j) (omIdx N j) * minorIJ h (omIdx N j) (omIdx N j) :=
  minorIJ_mul_of_support S h _ _ (support_omIdx hh)

theorem minor_one (C : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) C C = 1 := by
  rw [minorIJ_self_of_triangular 1 Matrix.blockTriangular_one]
  simp

theorem minor_ne {S : Matrix (Fin N) (Fin N) ℂ} (hS : IsBlockDiag j S) (hd : S.det ≠ 0) :
    minorIJ S (wIdx N j) (wIdx N j) ≠ 0 ∧ minorIJ S (omIdx N j) (omIdx N j) ≠ 0 := by
  have hu : IsUnit S.det := isUnit_iff_ne_zero.2 hd
  have hi := hS.inv hu
  have e : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hu
  have e1 := minor_w_mul S hi
  have e2 := minor_om_mul S hi
  rw [e, minor_one] at e1 e2
  exact ⟨left_ne_zero_of_mul (e1 ▸ one_ne_zero), left_ne_zero_of_mul (e2 ▸ one_ne_zero)⟩

theorem detFac_ne {S : Matrix (Fin N) (Fin N) ℂ} (hS : IsBlockDiag j S) (hd : S.det ≠ 0) (i : Fin N) :
    detFac j i S ≠ 0 := by
  obtain ⟨h1, h2⟩ := minor_ne hS hd
  unfold detFac
  split_ifs <;> simp [h1, h2]

theorem minor_empty {C : Finset (Fin N)} (hC : C = ∅) (S : Matrix (Fin N) (Fin N) ℂ) : minorIJ S C C = 1 := by
  subst hC
  unfold minorIJ
  rw [dif_pos rfl]
  haveI : IsEmpty (Fin (∅ : Finset (Fin N)).card) := inferInstanceAs (IsEmpty (Fin 0))
  exact det_isEmpty

theorem blockDiag_transv (hj : j ≤ N) {a b ca cb : Fin N} (hb : (b : ℕ) = a + 1) (hc : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := by
  have same : ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) := by
    have := b.2
    unfold lastCol at hca
    split_ifs at hca <;> omega
  intro r s hrs
  have e1 : r ≠ s := fun e => hrs (by rw [e])
  rw [Matrix.add_apply, Matrix.one_apply_ne e1, zero_add, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hrs same.symm

end Minors

section Sums

variable {Ψ : Type} [DecidableEq Ψ] {N j : ℕ}

theorem sum_xi (τ : Ψ) (a b : Fin N) (hb : (b : ℕ) = a + 1) (g : Fin N → ℝ) :
    ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * g i =
      (if h : 1 ≤ (a : ℕ) then g ⟨a - 1, by have := a.2; omega⟩ else 0) + g b - 2 * g a := by
  have e : ∀ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * g i =
      (if (i : ℕ) + 1 = a then g i else 0) + (if i = b then g i else 0) - (if i = a then 2 * g i else 0) := by
    intro i
    have hib : (i : ℕ) = a + 1 ↔ i = b := by rw [← hb]; exact Fin.ext_iff.symm
    simp only [xiCoef, if_true, hib]
    split_ifs <;> push_cast <;> ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  congr 2
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨a - 1, by have := a.2; omega⟩ : Fin N)]
    · rw [if_pos]
      show (a : ℕ) - 1 + 1 = a
      omega
    · intro i _ hi
      rw [if_neg]
      intro e'
      exact hi (Fin.ext (by show (i : ℕ) = a - 1; omega))
    · exact fun h' => absurd (Finset.mem_univ _) h'
  · exact Finset.sum_eq_zero fun i _ => if_neg (by omega)

theorem sum_g (τ : Ψ) (hj : j ≤ N) (a b : Fin N) (hb : (b : ℕ) = a + 1) (hc : (b : ℕ) < j ∨ j ≤ (a : ℕ)) (w o : ℝ)
    (hw : j = 0 → w = 0) (ho : j = N → o = 0) :
    ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) *
      ((if IsProperStep N j i then 0 else
          (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then w else 0) else o)) -
        ((if j ≤ (i : ℕ) + 1 then w else 0) + (if (i : ℕ) + 1 = N then o else 0))) = 0 := by
  let G : ℕ → ℝ := fun n => (if n + 1 ≠ j ∧ n + 1 ≠ N then 0 else
      (if n + 1 = j then (if (a : ℕ) < j then w else 0) else o)) -
    ((if j ≤ n + 1 then w else 0) + (if n + 1 = N then o else 0))
  have hg : ∀ i : Fin N, ((if IsProperStep N j i then 0 else
      (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then w else 0) else o)) -
        ((if j ≤ (i : ℕ) + 1 then w else 0) + (if (i : ℕ) + 1 = N then o else 0))) = G i := by
    intro i
    by_cases h : IsProperStep N j i
    · rw [if_pos h]
      simp only [G]
      rw [if_pos (show (i : ℕ) + 1 ≠ j ∧ (i : ℕ) + 1 ≠ N from h)]
    · rw [if_neg h]
      simp only [G]
      rw [if_neg (show ¬ ((i : ℕ) + 1 ≠ j ∧ (i : ℕ) + 1 ≠ N) from h)]
  rw [Finset.sum_congr rfl fun i _ => by rw [hg i], sum_xi τ a b hb fun i => G i]
  have hbN := b.2
  have haN := a.2
  have hlow : ∀ n, n + 1 < j → G n = 0 := fun n hn => by
    simp only [G]
    rw [if_pos ⟨by omega, by omega⟩, if_neg (by omega), if_neg (by omega)]
    simp
  have hhigh : ∀ n, j ≤ n + 1 → (n + 1 = j → ¬ (a : ℕ) < j) → n + 1 < N → G n = -w := fun n hn h1 h2 => by
    simp only [G]
    rw [if_pos hn, if_neg (by omega : ¬ n + 1 = N)]
    by_cases e : n + 1 = j
    · rw [if_neg (by omega), if_pos e, if_neg (h1 e)]
      simp
    · rw [if_pos ⟨e, by omega⟩]
      simp
  rcases hc with hc | hc
  · rw [hlow a (by omega)]
    have e0 : G b = 0 := by
      by_cases e : (b : ℕ) + 1 = j
      · simp only [G]
        rw [if_neg (by omega), if_pos e, if_pos (by omega), if_pos (by omega)]
        by_cases e' : (b : ℕ) + 1 = N
        · rw [if_pos e', ho (by omega)]
          simp
        · rw [if_neg e']
          simp
      · exact hlow b (by omega)
    rw [e0]
    split_ifs with h
    · rw [hlow _ (by show (a : ℕ) - 1 + 1 < j; omega)]
      simp
    · simp
  · rw [hhigh a (by omega) (by omega) (by omega)]
    have e0 : G b = -w := by
      by_cases e : (b : ℕ) + 1 = N
      · simp only [G]
        rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_pos e]
        ring
      · exact hhigh b (by omega) (by omega) (by omega)
    rw [e0]
    split_ifs with h
    · rw [show G ((⟨(a : ℕ) - 1, by omega⟩ : Fin N) : ℕ) = -w from hhigh _ (by show j ≤ (a : ℕ) - 1 + 1; omega)
        (by intro e; show ¬ (a : ℕ) < j; omega) (by show (a : ℕ) - 1 + 1 < N; omega)]
      ring
    · rw [hw (by omega)]
      ring

end Sums

section Fs

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem log_fs_smul (d : K → ℤ) (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log ((fsHerm ι d).h fun q => c q.1 * z q) =
      ∑ k, (d k : ℝ) * Real.log ‖c k‖ + Real.log ((fsHerm ι d).h z) := by
  have hp := (fsHerm ι d).pos z hz
  have hne : ∀ k, ‖c k‖ ^ d k ≠ 0 := fun k => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [(fsHerm ι d).smul c z hc]
  show Real.log ((∏ k, ‖c k‖ ^ d k) * _) = _
  rw [Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => hne k) hp.ne', Real.log_prod (fun k _ => hne k)]
  simp only [Real.log_zpow]

theorem log_norm_prod_zpow {σ : Type} [Fintype σ] (x : σ → ℤ) (e : σ → ℂ) (he : ∀ i, e i ≠ 0) :
    Real.log ‖∏ i, e i ^ x i‖ = ∑ i, (x i : ℝ) * Real.log ‖e i‖ := by
  have hne : ∀ i, ‖e i‖ ^ x i ≠ 0 := fun i => zpow_ne_zero _ (norm_ne_zero_iff.2 (he i))
  rw [norm_prod]
  simp only [norm_zpow]
  rw [Real.log_prod (fun i _ => hne i)]
  simp only [Real.log_zpow]

theorem sum_dite_subtype {P : K → Prop} [DecidablePred P] [Fintype {k // P k}] (f : {k // P k} → ℝ) :
    ∑ k, (if h : P k then f ⟨k, h⟩ else 0) = ∑ k : {k // P k}, f k := by
  calc ∑ k, (if h : P k then f ⟨k, h⟩ else 0)
      = ∑ k ∈ Finset.univ.filter P, (if h : P k then f ⟨k, h⟩ else 0) :=
        (Finset.sum_filter_of_ne fun k _ hk => by
          by_contra h
          exact hk (dif_neg h)).symm
    _ = ∑ k : {k // P k}, (if h : P k.1 then f ⟨k.1, h⟩ else 0) :=
        Finset.sum_subtype _ (by simp) fun k => if h : P k then f ⟨k, h⟩ else 0
    _ = _ := Finset.sum_congr rfl fun k _ => dif_pos k.2

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem sum_dy (M : FlagModel y Ψ N j) (p : Ψ × Fin N) (l : K → ℝ) :
    ∑ k, (M.dy p k : ℝ) * l k = -∑ k : NonPluckerBlocks M.blk, (M.b p k : ℝ) * l k.1 + (M.blk p).elim 0 l := by
  have e : ∀ k, (M.dy p k : ℝ) * l k =
      (if h : ∀ p', M.blk p' ≠ some k then -((M.b p ⟨k, h⟩ : ℝ) * l k) else 0) +
        (if M.blk p = some k then l k else 0) := by
    intro k
    unfold FlagModel.dy
    by_cases h : ∀ p', M.blk p' ≠ some k
    · rw [dif_pos h, dif_pos h, if_neg (h p)]
      push_cast
      ring
    · rw [dif_neg h, dif_neg h]
      split_ifs <;> simp
  simp only [e, Finset.sum_add_distrib]
  congr 1
  · refine (sum_dite_subtype (P := fun k => ∀ p', M.blk p' ≠ some k) fun k => -((M.b p k : ℝ) * l k.1)).trans ?_
    rw [Finset.sum_neg_distrib]
  · cases hb : M.blk p with
    | none => simp
    | some k => simp [eq_comm]

def cc (M : FlagModel y Ψ N j) (τ : Ψ) (ζ : NonPluckerBlocks M.blk → ℂ) (S : Matrix (Fin N) (Fin N) ℂ) : K → ℂ := fun k =>
  if h : ∀ p, M.blk p ≠ some k then ζ ⟨k, h⟩
  else if h' : ∃ i, M.blk (τ, i) = some k then (detFac j h'.choose S)⁻¹ * ∏ k', ζ k' ^ M.b (τ, h'.choose) k'
  else 1

theorem cc_base (M : FlagModel y Ψ N j) (τ : Ψ) (ζ : NonPluckerBlocks M.blk → ℂ) (S : Matrix (Fin N) (Fin N) ℂ)
    (k : NonPluckerBlocks M.blk) : cc M τ ζ S k.1 = ζ k := dif_pos k.2

theorem cc_step (M : FlagModel y Ψ N j) (τ : Ψ) (ζ : NonPluckerBlocks M.blk → ℂ) (S : Matrix (Fin N) (Fin N) ℂ) {i : Fin N}
    {k : K} (hk : M.blk (τ, i) = some k) :
    cc M τ ζ S k = (detFac j i S)⁻¹ * ∏ k', ζ k' ^ M.b (τ, i) k' := by
  have h : ¬ ∀ p, M.blk p ≠ some k := fun h => h _ hk
  have h' : ∃ i, M.blk (τ, i) = some k := ⟨i, hk⟩
  have e : h'.choose = i := congrArg Prod.snd (M.blk_inj _ _ k h'.choose_spec hk)
  unfold cc
  rw [dif_neg h, dif_pos h', e]

theorem cc_ne (M : FlagModel y Ψ N j) (τ : Ψ) {ζ : NonPluckerBlocks M.blk → ℂ} {S : Matrix (Fin N) (Fin N) ℂ}
    (hζ : ∀ k, ζ k ≠ 0) (hd : ∀ i, detFac j i S ≠ 0) (k : K) : cc M τ ζ S k ≠ 0 := by
  unfold cc
  split_ifs with h h'
  · exact hζ _
  · exact mul_ne_zero (inv_ne_zero (hd _)) (Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (hζ k'))
  · exact one_ne_zero

theorem chart_ne {M : FlagModel y Ψ N j} {F : FrameData ι Ψ N M.Ω M.blk} {zb : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hF : M.GoodAt F (mCoordIdeal zb)) (k : NonPluckerBlocks M.blk) : zb ⟨k, F.c k⟩ ≠ 0 := fun h => hF.1 k (by
  show mConeMap zb (X ⟨k, F.c k⟩) = 0
  rw [mConeMap, aeval_X, h, map_zero, zero_mul])

theorem val_ups_ne {M : FlagModel y Ψ N j} {F : FrameData ι Ψ N M.Ω M.blk} {zb : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hz : zb ∈ mcPts (mCoordIdeal M.x)) (hF : M.GoodAt F (mCoordIdeal zb)) {p : Ψ × Fin N} (hp : M.blk p = none) :
    valAt M.x (F.υ p) zb ≠ 0 := by
  obtain ⟨h0, h1, h2⟩ := hF.2.2 p hp
  have e := (reg_mul hz h1 h2).2
  rw [mul_inv_cancel₀ h0, (ValRing.regAt_valAt_ring _ _ _ M.x zb hz).2.2.2.1] at e
  exact left_ne_zero_of_mul (e ▸ one_ne_zero)

def zeta (M : FlagModel y Ψ N j) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk) :
    NonPluckerBlocks M.blk → ℂ := fun k => zb ⟨k, F₂.c k⟩ / zb ⟨k, F₁.c k⟩

theorem val_move {M : FlagModel y Ψ N j} {zb : (Σ k, baseIdx ι M.blk k) → ℂ} (hz : zb ∈ mcPts (mCoordIdeal M.x))
    {ζ : NonPluckerBlocks M.blk → ℂ} (hζ : ∀ k, ζ k ≠ 0) {c : K → ℂ} (hc : ∀ k : NonPluckerBlocks M.blk, c k.1 = ζ k)
    {z : (Σ k, ι k) → ℂ} (hb : basePart M.blk z = zb) (s : M.Ω) :
    valAt M.x s (basePart M.blk fun q : Σ k, ι k => c q.1 * z q) = valAt M.x s zb := by
  have e : basePart M.blk (fun q : Σ k, ι k => c q.1 * z q) = fun q : Σ k, baseIdx ι M.blk k => ζ q.1 * zb q := by
    subst hb
    funext q
    show c q.1.1 * z ⟨q.1.1, q.2⟩ = ζ q.1 * z ⟨q.1.1, q.2⟩
    rw [hc]
  rw [e]
  exact ((GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main _ _ _ M.x zb ζ hζ).2 hz).2 s

theorem exact_move {M : FlagModel y Ψ N j} {F₁ F₂ : FrameData ι Ψ N M.Ω M.blk}
    {zb : (Σ k, baseIdx ι M.blk k) → ℂ} (hz : zb ∈ mcPts (mCoordIdeal M.x)) (h1 : ∀ k, zb ⟨k, F₁.c k⟩ ≠ 0)
    (h2 : ∀ k, zb ⟨k, F₂.c k⟩ ≠ 0) (τ : Ψ) (i : Fin N) {S h' : Matrix (Fin N) (Fin N) ℂ} {z : (Σ k, ι k) → ℂ}
    (hd : detFac j i S ≠ 0) (hb : basePart M.blk z = zb)
    (hs : ∀ k, M.blk (τ, i) = some k → ∀ m : ι k, detFac j i S * plk M F₁ zb i ⟨k, m⟩ (S * h') =
      (∏ k', zeta M zb F₁ F₂ k' ^ M.b (τ, i) k') * plk M F₂ zb i ⟨k, m⟩ h')
    (hex : M.ExactAt F₂ (τ, i) z h') :
    M.ExactAt F₁ (τ, i) (fun q => cc M τ (zeta M zb F₁ F₂) S q.1 * z q) (S * h') := by
  have hζ : ∀ k, zeta M zb F₁ F₂ k ≠ 0 := fun k => div_ne_zero (h2 k) (h1 k)
  refine ⟨fun k => ?_, fun k hk m => ?_⟩
  · show cc M τ _ S k.1 * z ⟨k.1, F₁.c k⟩ = 1
    have e1 : z ⟨k.1, F₁.c k⟩ = zb ⟨k, F₁.c k⟩ := congrFun hb ⟨k, F₁.c k⟩
    have e2 : zb ⟨k, F₂.c k⟩ = 1 := by
      rw [← hb]
      exact hex.1 k
    rw [cc_base, e1, zeta, div_mul_cancel₀ _ (h1 k), e2]
  · have e := hex.2 k hk m
    have hv := val_move hz hζ (cc_base M τ (zeta M zb F₁ F₂) S) hb
    show cc M τ _ S k * z ⟨k, m⟩ = _
    simp only [hv]
    rw [hb] at e
    have h3 := hs k hk m
    unfold plk at h3
    rw [cc_step M τ _ S hk, e, mul_assoc, ← h3, inv_mul_cancel_left₀ hd]

end Fs

section Norm

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def rFac (j : ℕ) (a : Fin N) (h : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) : ℂ :=
  if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ h (wIdx N j) (wIdx N j) else 1)
    else minorIJ h (omIdx N j) (omIdx N j)

def baseF (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (F : FrameData ι Ψ N M.Ω M.blk)
    (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (h : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) : ℂ :=
  if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) zb * rFac j a h i

def eFac (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (ζ : NonPluckerBlocks M.blk → ℂ) (S : Matrix (Fin N) (Fin N) ℂ)
    (i : Fin N) : ℂ :=
  if IsProperStep N j i then 1 else (∏ k', ζ k' ^ M.b (τ, i) k') * (detFac j i S)⁻¹ * rFac j a S i

theorem rFac_mul (a : Fin N) (S : Matrix (Fin N) (Fin N) ℂ) {h : Matrix (Fin N) (Fin N) ℂ} (hh : IsBlockDiag j h)
    (i : Fin N) : rFac j a (S * h) i = rFac j a S i * rFac j a h i := by
  unfold rFac
  rw [minor_w_mul S hh, minor_om_mul S hh]
  split_ifs <;> simp

theorem rFac_ne (a : Fin N) {h : Matrix (Fin N) (Fin N) ℂ} (hh : IsBlockDiag j h) (hd : h.det ≠ 0) (i : Fin N) :
    rFac j a h i ≠ 0 := by
  obtain ⟨h1, h2⟩ := minor_ne hh hd
  unfold rFac
  split_ifs <;> simp [h1, h2]

theorem blk_none_of_not {M : FlagModel y Ψ N j} {τ : Ψ} {i : Fin N} (hp : ¬ IsProperStep N j i) :
    M.blk (τ, i) = none := (M.blk_none (τ, i)).2 hp

theorem exists_blk_of_proper {M : FlagModel y Ψ N j} {τ : Ψ} {i : Fin N} (hp : IsProperStep N j i) :
    ∃ k, M.blk (τ, i) = some k := by
  rcases e : M.blk (τ, i) with _ | k
  · exact absurd hp ((M.blk_none (τ, i)).1 e)
  · exact ⟨k, rfl⟩

theorem baseF_move {M : FlagModel y Ψ N j} (τ : Ψ) (a : Fin N) {F₁ F₂ : FrameData ι Ψ N M.Ω M.blk}
    {zb : (Σ k, baseIdx ι M.blk k) → ℂ} {ζ : NonPluckerBlocks M.blk → ℂ} {S h : Matrix (Fin N) (Fin N) ℂ}
    (hS : IsBlockDiag j S) (hSd : S.det ≠ 0) (hh : IsBlockDiag j h)
    (hs : ∀ i : Fin N, M.blk (τ, i) = none → valAt M.x (F₂.υ (τ, i)) zb * (∏ k', ζ k' ^ M.b (τ, i) k') =
      detFac j i S * valAt M.x (F₁.υ (τ, i)) zb) (i : Fin N) :
    baseF M τ a F₁ zb (S * h) i = baseF M τ a F₂ zb h i * eFac M τ a ζ S i := by
  unfold baseF eFac
  by_cases hp : IsProperStep N j i
  · rw [if_pos hp, if_pos hp, if_pos hp, one_mul]
  · rw [if_neg hp, if_neg hp, if_neg hp, rFac_mul a S hh]
    have hd := detFac_ne hS hSd i
    have e := hs i (blk_none_of_not hp)
    have e' : valAt M.x (F₁.υ (τ, i)) zb =
        valAt M.x (F₂.υ (τ, i)) zb * (∏ k', ζ k' ^ M.b (τ, i) k') * (detFac j i S)⁻¹ := by
      rw [e, mul_comm (detFac j i S), mul_inv_cancel_right₀ hd]
    rw [e']
    ring

theorem baseF_ne {M : FlagModel y Ψ N j} (τ : Ψ) (a : Fin N) {F : FrameData ι Ψ N M.Ω M.blk}
    {zb : (Σ k, baseIdx ι M.blk k) → ℂ} (hz : zb ∈ mcPts (mCoordIdeal M.x)) (hF : M.GoodAt F (mCoordIdeal zb))
    {h : Matrix (Fin N) (Fin N) ℂ} (hh : IsBlockDiag j h) (hd : h.det ≠ 0) (i : Fin N) :
    baseF M τ a F zb h i ≠ 0 := by
  unfold baseF
  split_ifs with hp
  · exact one_ne_zero
  · exact mul_ne_zero (val_ups_ne hz hF (blk_none_of_not hp)) (rFac_ne a hh hd i)

theorem eFac_ne (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) {ζ : NonPluckerBlocks M.blk → ℂ} (hζ : ∀ k, ζ k ≠ 0)
    {S : Matrix (Fin N) (Fin N) ℂ} (hS : IsBlockDiag j S) (hSd : S.det ≠ 0) (i : Fin N) :
    eFac M τ a ζ S i ≠ 0 := by
  unfold eFac
  split_ifs with hp
  · exact one_ne_zero
  · exact mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hζ k))
      (inv_ne_zero (detFac_ne hS hSd i))) (rFac_ne a hS hSd i)

theorem prod_part (x : Fin N → ℤ) {B₁ B₂ e : Fin N → ℂ} {t : ℂ} (ht : t ≠ 0) (h : ∀ i, B₁ i = B₂ i * e i)
    (h2 : ∀ i, B₂ i ≠ 0) (he : ∀ i, e i ≠ 0) :
    Real.log ‖t * ∏ i, B₁ i ^ x i‖ = Real.log ‖t * ∏ i, B₂ i ^ x i‖ + ∑ i, (x i : ℝ) * Real.log ‖e i‖ := by
  simp only [h, mul_zpow, Finset.prod_mul_distrib]
  rw [← mul_assoc, norm_mul, Real.log_mul
    (norm_ne_zero_iff.2 (mul_ne_zero ht (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (h2 i))))
    (norm_ne_zero_iff.2 (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (he i))), log_norm_prod_zpow x e he]

theorem sum_xi_p (τ : Ψ) (a : Fin N) (f : Ψ × Fin N → ℝ) :
    ∑ p, (xiCoef τ a p : ℝ) * f p = ∑ i, (xiCoef τ a (τ, i) : ℝ) * f (τ, i) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · intro τ' _ hn
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [xiCoef, hn]
  · simp

theorem fs_part (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) {c : K → ℂ} (hc : ∀ k, c k ≠ 0)
    {z₀ z₁ : (Σ k, ι k) → ℂ} (hn₀ : ∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) (hn₁ : ∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0) :
    ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h fun q => c q.1 * z₀ q) +
        Real.log ((fsHerm ι (M.dy p)).h fun q => c q.1 * z₁ q)) =
      ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁)) +
        2 * ∑ i, (xiCoef τ a (τ, i) : ℝ) * ∑ k, (M.dy (τ, i) k : ℝ) * Real.log ‖c k‖ := by
  rw [← sum_xi_p τ a fun p => ∑ k, (M.dy p k : ℝ) * Real.log ‖c k‖, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [log_fs_smul _ c hc z₀ hn₀, log_fs_smul _ c hc z₁ hn₁]
  ring

theorem log_detFac {S : Matrix (Fin N) (Fin N) ℂ} (hS : IsBlockDiag j S) (hd : S.det ≠ 0) (i : Fin N) :
    Real.log ‖detFac j i S‖ = (if j ≤ (i : ℕ) + 1 then Real.log ‖minorIJ S (wIdx N j) (wIdx N j)‖ else 0) +
      (if (i : ℕ) + 1 = N then Real.log ‖minorIJ S (omIdx N j) (omIdx N j)‖ else 0) := by
  obtain ⟨h1, h2⟩ := minor_ne hS hd
  unfold detFac
  split_ifs <;> simp [Real.log_mul, h1, h2]

theorem log_rFac (a : Fin N) (S : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    Real.log ‖rFac j a S i‖ = if (i : ℕ) + 1 = j then
      (if (a : ℕ) < j then Real.log ‖minorIJ S (wIdx N j) (wIdx N j)‖ else 0)
      else Real.log ‖minorIJ S (omIdx N j) (omIdx N j)‖ := by
  unfold rFac
  split_ifs <;> simp

theorem step_sum (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) {ζ : NonPluckerBlocks M.blk → ℂ} (hζ : ∀ k, ζ k ≠ 0)
    {S : Matrix (Fin N) (Fin N) ℂ} (hS : IsBlockDiag j S) (hSd : S.det ≠ 0) (i : Fin N) :
    ∑ k, (M.dy (τ, i) k : ℝ) * Real.log ‖cc M τ ζ S k‖ + Real.log ‖eFac M τ a ζ S i‖ =
      (if IsProperStep N j i then 0 else
          (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then Real.log ‖minorIJ S (wIdx N j) (wIdx N j)‖ else 0)
            else Real.log ‖minorIJ S (omIdx N j) (omIdx N j)‖)) -
        ((if j ≤ (i : ℕ) + 1 then Real.log ‖minorIJ S (wIdx N j) (wIdx N j)‖ else 0) +
          (if (i : ℕ) + 1 = N then Real.log ‖minorIJ S (omIdx N j) (omIdx N j)‖ else 0)) := by
  have hd := detFac_ne hS hSd i
  have hP : (∏ k', ζ k' ^ M.b (τ, i) k') ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hζ k)
  have hA := log_norm_prod_zpow (M.b (τ, i)) ζ hζ
  rw [sum_dy, ← log_detFac hS hSd i]
  simp only [cc_base]
  rw [← hA]
  unfold eFac
  by_cases hp : IsProperStep N j i
  · obtain ⟨k, hk⟩ := exists_blk_of_proper (M := M) (τ := τ) hp
    rw [if_pos hp, if_pos hp, hk]
    simp only [Option.elim]
    rw [cc_step M τ ζ S hk, norm_mul, norm_inv, Real.log_mul (inv_ne_zero (norm_ne_zero_iff.2 hd))
      (norm_ne_zero_iff.2 hP), Real.log_inv, norm_one, Real.log_one]
    ring
  · rw [if_neg hp, if_neg hp, blk_none_of_not hp, ← log_rFac a S i]
    simp only [Option.elim]
    rw [norm_mul, norm_mul, norm_inv, Real.log_mul (mul_ne_zero (norm_ne_zero_iff.2 hP)
      (inv_ne_zero (norm_ne_zero_iff.2 hd))) (norm_ne_zero_iff.2 (rFac_ne a hS hSd i)),
      Real.log_mul (norm_ne_zero_iff.2 hP) (inv_ne_zero (norm_ne_zero_iff.2 hd)), Real.log_inv]
    ring

theorem norm_move {M : FlagModel y Ψ N j} (τ : Ψ) (a b : Fin N) (hb : (b : ℕ) = a + 1)
    (hc : (b : ℕ) < j ∨ j ≤ (a : ℕ)) {F₁ F₂ : FrameData ι Ψ N M.Ω M.blk} {zb : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hz : zb ∈ mcPts (mCoordIdeal M.x)) (hG₂ : M.GoodAt F₂ (mCoordIdeal zb)) {ζ : NonPluckerBlocks M.blk → ℂ}
    (hζ : ∀ k, ζ k ≠ 0) {S h : Matrix (Fin N) (Fin N) ℂ} (hS : IsBlockDiag j S) (hSd : S.det ≠ 0)
    (hh : IsBlockDiag j h) (hd : h.det ≠ 0) {t : ℂ} (ht : t ≠ 0) {z₀ z₁ : (Σ k, ι k) → ℂ}
    (hb₀ : basePart M.blk z₀ = zb) (hn₀ : ∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) (hn₁ : ∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0)
    (hs : ∀ i : Fin N, M.blk (τ, i) = none → valAt M.x (F₂.υ (τ, i)) zb * (∏ k', ζ k' ^ M.b (τ, i) k') =
      detFac j i S * valAt M.x (F₁.υ (τ, i)) zb) :
    normRhs M τ a F₁ (fun q => cc M τ ζ S q.1 * z₀ q) (fun q => cc M τ ζ S q.1 * z₁ q) (S * h) t =
      normRhs M τ a F₂ z₀ z₁ h t := by
  have hcc := cc_ne M τ hζ (detFac_ne hS hSd)
  have hv := val_move hz hζ (cc_base M τ ζ S) hb₀
  have n₁ : normRhs M τ a F₁ (fun q => cc M τ ζ S q.1 * z₀ q) (fun q => cc M τ ζ S q.1 * z₁ q) (S * h) t =
      Real.log ‖t * ∏ i : Fin N, baseF M τ a F₁ zb (S * h) i ^ xiCoef τ a (τ, i)‖ +
        (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h fun q => cc M τ ζ S q.1 * z₀ q) +
          Real.log ((fsHerm ι (M.dy p)).h fun q => cc M τ ζ S q.1 * z₁ q)) := by
    unfold normRhs baseF rFac
    simp only [hv]
  have n₂ : normRhs M τ a F₂ z₀ z₁ h t =
      Real.log ‖t * ∏ i : Fin N, baseF M τ a F₂ zb h i ^ xiCoef τ a (τ, i)‖ +
        (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) +
          Real.log ((fsHerm ι (M.dy p)).h z₁)) := by
    unfold normRhs baseF rFac
    rw [hb₀]
  rw [n₁, n₂, prod_part _ ht (baseF_move τ a hS hSd hh hs) (baseF_ne τ a hz hG₂ hh hd)
    (eFac_ne M τ a hζ hS hSd), fs_part M τ a hcc hn₀ hn₁]
  have key : ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * Real.log ‖eFac M τ a ζ S i‖ +
      ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ∑ k, (M.dy (τ, i) k : ℝ) * Real.log ‖cc M τ ζ S k‖ = 0 := by
    rw [← Finset.sum_add_distrib, ← sum_g τ M.j_le a b hb hc (Real.log ‖minorIJ S (wIdx N j) (wIdx N j)‖)
      (Real.log ‖minorIJ S (omIdx N j) (omIdx N j)‖) ?_ ?_]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← step_sum M τ a hζ hS hSd i]
      ring
    · intro e
      rw [minor_empty _ S]
      · simp
      · subst e
        ext c
        simp [wIdx]
    · intro e
      rw [minor_empty _ S]
      · simp
      · subst e
        ext c
        simp [omIdx]
  linear_combination key

end Norm

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk) (z₀ z₁ : (Σ k, ι k) → ℂ) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) → (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) → (∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0) → basePart M.blk z₁ = basePart M.blk z₀ → M.IsFrame F₁ → M.IsFrame F₂ → M.GoodAt F₁ (mCoordIdeal (basePart M.blk z₀)) → M.GoodAt F₂ (mCoordIdeal (basePart M.blk z₀)) → IsBlockDiag j h → h.det ≠ 0 → t ≠ 0 → (∀ i, M.ExactAt F₂ (τ, i) z₀ h) → (∀ i, M.ExactAt F₂ (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → ∃ (z₀' z₁' : (Σ k, ι k) → ℂ) (S : Matrix (Fin N) (Fin N) ℂ), SameOrbit z₀' z₀ ∧ SameOrbit z₁' z₁ ∧ IsBlockDiag j S ∧ S.det ≠ 0 ∧ (∀ i, M.ExactAt F₁ (τ, i) z₀' (S * h)) ∧ (∀ i, M.ExactAt F₁ (τ, i) z₁' (S * h * (1 + Matrix.single cb ca t))) ∧ normRhs M τ a F₁ z₀' z₁' (S * h) t = normRhs M τ a F₂ z₀ z₁ h t := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a b k₀ ca cb hb hc hblk hca hcb F₁ F₂ z₀ z₁ h t hz hn₀ hn₁ hbase hF₁ hF₂ hG₁ hG₂
    hh hdet ht hE₀ hE₁
  obtain ⟨hS, hsc⟩ := GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Scal.main K ι Φ y Ψ N j M (basePart M.blk z₀) F₁ F₂ hz hF₁ hF₂ hG₁ hG₂
  have h1 := chart_ne hG₁
  have h2 := chart_ne hG₂
  have hζ : ∀ k, zeta M (basePart M.blk z₀) F₁ F₂ k ≠ 0 := fun k => div_ne_zero (h2 k) (h1 k)
  have hd := detFac_ne (hS τ).1 (hS τ).2
  have hcc := cc_ne M τ hζ hd
  have hT := blockDiag_transv M.j_le hb hc hca hcb t
  refine ⟨_, _, _, ⟨_, hcc, rfl⟩, ⟨_, hcc, rfl⟩, (hS τ).1, (hS τ).2, fun i => ?_, fun i => ?_, ?_⟩
  · exact exact_move hz h1 h2 τ i (hd i) rfl (fun k hk m => (hsc (τ, i)).1 k hk h hh m) (hE₀ i)
  · rw [Matrix.mul_assoc]
    exact exact_move hz h1 h2 τ i (hd i) hbase (fun k hk m => (hsc (τ, i)).1 k hk _ (hh.mul hT) m) (hE₁ i)
  · exact norm_move τ a b hb hc hz hG₂ hζ (hS τ).1 (hS τ).2 hh hdet ht rfl hn₀ hn₁ fun i hi => (hsc (τ, i)).2 hi

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Move
