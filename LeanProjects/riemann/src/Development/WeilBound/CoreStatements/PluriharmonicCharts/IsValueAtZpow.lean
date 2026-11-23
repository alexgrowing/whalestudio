import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ValueConstantOnOrbit
import Development.WeilBound.CoreStatements.PluriharmonicCharts.MinorIJConjTranspose
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc GlobalTheory.CompanionTheory.Ar.PB.CPts GlobalTheory.CompanionTheory.Ar.PB.ValRing
open scoped ComplexOrder Classical

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_hom

section Val

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {x : (Σ k, ι k) → Ω} {w : (Σ k, ι k) → ℂ}

theorem isValueAt_zpow (hw : w ∈ mcPts (mCoordIdeal x)) {s : Ω} {v : ℂ} (h : IsValueAt x s w v) (hv : v ≠ 0)
    (n : ℤ) : IsValueAt x (s ^ n) w (v ^ n) := by
  have hs : s ≠ 0 := fun h0 => hv (isValueAt_zero hw (h0 ▸ h))
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using isValueAt_pow h m
  · simpa using isValueAt_pow (isValueAt_inv h hs hv) m

theorem isValueAt_prod {α : Type} (S : Finset α) (f : α → Ω) (v : α → ℂ)
    (h : ∀ i ∈ S, IsValueAt x (f i) w (v i)) : IsValueAt x (∏ i ∈ S, f i) w (∏ i ∈ S, v i) := by
  induction S using Finset.induction_on with
  | empty => simpa using isValueAt_one_self x w
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact isValueAt_mul (h a (Finset.mem_insert_self a S)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isValueAt_mon (hw : w ∈ mcPts (mCoordIdeal x)) {c c' : ∀ k, ι k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0)
    (hc' : ∀ k, w ⟨k, c' k⟩ ≠ 0) (b : K → ℤ) :
    IsValueAt x ((∏ k, x ⟨k, c k⟩ ^ b k) / ∏ k, x ⟨k, c' k⟩ ^ b k) w (∏ k, (w ⟨k, c k⟩ / w ⟨k, c' k⟩) ^ b k) := by
  rw [← Finset.prod_div_distrib]
  refine isValueAt_prod _ _ _ fun k _ => ?_
  rw [← div_zpow]
  exact isValueAt_zpow hw (isValueAt_ratio (coord_ne hw (hc' k)) (hc' k)) (div_ne_zero (hc k) (hc' k)) _

theorem log_mon {c c' : ∀ k, ι k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (hc' : ∀ k, w ⟨k, c' k⟩ ≠ 0) (b : K → ℤ) :
    Real.log ‖∏ k, (w ⟨k, c k⟩ / w ⟨k, c' k⟩) ^ b k‖ =
      ∑ k, (b k : ℝ) * Real.log ‖w ⟨k, c k⟩‖ - ∑ k, (b k : ℝ) * Real.log ‖w ⟨k, c' k⟩‖ := by
  rw [norm_prod, Real.log_prod fun k _ => norm_ne_zero_iff.2 (zpow_ne_zero _ (div_ne_zero (hc k) (hc' k))),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_zpow, Real.log_zpow, norm_div, Real.log_div (norm_ne_zero_iff.2 (hc k)) (norm_ne_zero_iff.2 (hc' k))]
  ring

theorem ne_of_notMem {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal w) : w q ≠ 0 := fun h0 => h (by
  show mConeMap w (X q) = 0
  rw [mConeMap, aeval_X, h0, map_zero, zero_mul])

theorem eval_conj (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    eval (conjVec z) (map (Int.castRingHom ℂ) f) = starRingEnd ℂ (eval z (map (Int.castRingHom ℂ) f)) := by
  rw [eval_map, eval_map, eval₂_comp_left]
  exact congrArg (fun g => MvPolynomial.eval₂ g _ f) (RingHom.ext_int _ _)

theorem isValueAt_conj {s : Ω} {v : ℂ} (h : IsValueAt x s w v) : IsValueAt x s (conjVec w) (starRingEnd ℂ v) := by
  obtain ⟨d, g, f, hg, hf, hy, heq, hz0, rfl⟩ := h
  refine ⟨d, g, f, hg, hf, hy, heq, ?_, ?_⟩
  · rw [eval_conj]; exact (map_ne_zero _).2 hz0
  · rw [eval_conj, eval_conj, map_div₀]

theorem valAt_conj (hw : w ∈ mcPts (mCoordIdeal x)) (hw' : conjVec w ∈ mcPts (mCoordIdeal x)) {s : Ω}
    (hs : RegAt x (mCoordIdeal w) s) : valAt x s (conjVec w) = starRingEnd ℂ (valAt x s w) := by
  obtain ⟨v, hv⟩ := exists_isValueAt hw hs
  rw [valAt_eq hw hv, valAt_eq hw' (isValueAt_conj hv)]

end Val

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j)

theorem change_gen {F F' : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) (hF' : M.IsFrame F') {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) (m : ι k) {I' : Finset (Fin N)} (hI : IsStepRows N j p.2 I') :
    detFac j p.2 ((F.T p.1)⁻¹ * F'.T p.1) * (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') *
      ∑ I, F.u ⟨k, m⟩ I * minorIJ ((F.T p.1)⁻¹ * F'.T p.1) I I' =
      (∏ k', M.x ⟨k', F'.c k'⟩ ^ M.b p k') * F'.u ⟨k, m⟩ I' := by
  obtain ⟨h, bh, hh⟩ := exists_selector M.Ω M.j_le p.2 hI
  have hu : IsUnit (F.T p.1).det := (hF.1 p.1).2.isUnit
  set R := (F.T p.1)⁻¹ * F'.T p.1 with hR
  have bR : IsBlockDiag j R := ((hF.1 p.1).1.inv hu).mul (hF'.1 p.1).1
  have eT : F'.T p.1 = F.T p.1 * R := by rw [hR, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  have e1 := hF.2.1 p k hp m (R * h) (bR.mul bh)
  have e2 := hF'.2.1 p k hp m h bh
  have e3 : ∀ I, minorIJ (R * h) I (stepCols N j p.2) = minorIJ R I I' := fun I => by
    rw [minorIJ_mul]; simp [hh]
  simp only [e3] at e1
  rw [eT, detFac_mul _ bR, Matrix.mul_assoc] at e2
  simp only [hh, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e2
  linear_combination e2 - detFac j p.2 R * e1

theorem change_base {F F' : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) (hF' : M.IsFrame F') {p : Ψ × Fin N}
    (hp : M.blk p = none) :
    detFac j p.2 ((F.T p.1)⁻¹ * F'.T p.1) * (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') * F.υ p =
      (∏ k', M.x ⟨k', F'.c k'⟩ ^ M.b p k') * F'.υ p := by
  have hu : IsUnit (F.T p.1).det := (hF.1 p.1).2.isUnit
  set R := (F.T p.1)⁻¹ * F'.T p.1 with hR
  have bR : IsBlockDiag j R := ((hF.1 p.1).1.inv hu).mul (hF'.1 p.1).1
  have eT : F'.T p.1 = F.T p.1 * R := by rw [hR, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  have e1 := hF.2.2.2 p hp
  have e2 := hF'.2.2.2 p hp
  rw [eT, detFac_mul _ bR] at e2
  linear_combination e2 - detFac j p.2 R * e1

theorem left_inv_val {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {w : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hw : w ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal w)) {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) {f : Matrix (Fin N) (Fin N) ℂ} (bf : IsBlockDiag j f) {I : Finset (Fin N)}
    (hI : IsStepRows N j p.2 I) :
    ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) w * ∑ I', valAt M.x (F.u ⟨k, m⟩ I') w * minorIJ f I' (stepCols N j p.2) =
      minorIJ f I (stepCols N j p.2) := by
  let uA : (Σ k, ι k) → Finset (Fin N) → regRing M.x w := fun q I => ⟨F.u q I, exists_isValueAt hw (hG.2.1 q I).1⟩
  let vA : Finset (Fin N) → (Σ k, ι k) → regRing M.x w := fun I q => ⟨F.u' I q, exists_isValueAt hw (hG.2.1 q I).2⟩
  have rel : ∀ I', IsStepRows N j p.2 I' →
      ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) w * valAt M.x (F.u ⟨k, m⟩ I') w = if I = I' then 1 else 0 := fun I' hI' => by
    have e : ∑ m : ι k, vA I ⟨k, m⟩ * uA ⟨k, m⟩ I' = if I = I' then 1 else 0 := by
      apply Subtype.ext
      have := hF.2.2.1 p k hp I I' hI hI'
      split_ifs at this ⊢ <;> simpa [uA, vA] using this
    have e' := congrArg (regVal hw) e
    rw [map_sum] at e'
    simp only [map_mul] at e'
    refine e'.trans ?_
    split_ifs <;> simp
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul]
  rw [Finset.sum_eq_single I]
  · rw [rel I hI, if_pos rfl, one_mul]
  · intro I' _ hne
    by_cases h : IsStepRows N j p.2 I'
    · rw [rel I' h, if_neg hne.symm, zero_mul]
    · rw [minor_stepCols_eq_zero M.j_le f I' bf h, mul_zero]
  · simp

def Rel (Gr : FrameData ι Ψ N M.Ω M.blk → Ψ → ((Σ k, baseIdx ι M.blk k) → ℂ) → Matrix (Fin N) (Fin N) ℂ → Prop)
    (p : Ψ × Fin N) (z : (Σ k, ι k) → ℂ) (r : ℝ) : Prop :=
  ∃ F G, Gr F p.1 (basePart M.blk z) G ∧ ∃ h : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j h ∧ h.det ≠ 0 ∧ ∃ t : ℝ,
    ((∃ k a, M.blk p = some k ∧ a ≠ 0 ∧ (∀ m : ι k, z ⟨k, m⟩ =
        a * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (basePart M.blk z) * minorIJ h I (stepCols N j p.2)) ∧ t = Real.log ‖a‖) ∨
      (M.blk p = none ∧ t = -Real.log ‖valAt M.x (F.υ p) (basePart M.blk z)‖)) ∧
    r = t + blockPot j p.2 G h - ∑ k', (M.b p k' : ℝ) * Real.log ‖basePart M.blk z ⟨k', F.c k'⟩‖

variable {M}
variable {Gr : FrameData ι Ψ N M.Ω M.blk → Ψ → ((Σ k, baseIdx ι M.blk k) → ℂ) → Matrix (Fin N) (Fin N) ℂ → Prop}

theorem Rel.unique
    (hgood : ∀ F τ w G, Gr F τ w G → M.IsFrame F ∧ w ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal w) ∧
      IsBlockDiag j G ∧ G.PosDef)
    (hcomp : ∀ F F' τ w G G', Gr F τ w G → Gr F' τ w G' → ∃ Rz : Matrix (Fin N) (Fin N) ℂ,
      (∀ a b, IsValueAt M.x (((F.T τ)⁻¹ * F'.T τ) a b) w (Rz a b)) ∧ Rz.det ≠ 0 ∧ G' = Rzᴴ * G * Rz)
    {p : Ψ × Fin N} {z : (Σ k, ι k) → ℂ} {r r' : ℝ} (h1 : Rel M Gr p z r) (h2 : Rel M Gr p z r') : r = r' := by
  obtain ⟨F, G, hG, h, bh, dh, t, ht, rfl⟩ := h1
  obtain ⟨F', G', hG', h', bh', dh', t', ht', rfl⟩ := h2
  obtain ⟨Rz, hRz, dR, rfl⟩ := hcomp _ _ _ _ _ _ hG hG'
  obtain ⟨hF, hw, gd, bG, pG⟩ := hgood _ _ _ _ hG
  obtain ⟨hF', -, gd', -, -⟩ := hgood _ _ _ _ hG'
  generalize basePart M.blk z = w at *
  have hc : ∀ k, w ⟨k, F.c k⟩ ≠ 0 := fun k => ne_of_notMem (gd.1 k)
  have hc' : ∀ k, w ⟨k, F'.c k⟩ ≠ 0 := fun k => ne_of_notMem (gd'.1 k)
  have hμ := isValueAt_mon hw hc hc' (M.b p)
  have lμ := log_mon hc hc' (M.b p)
  have μ0 : (∏ k, (w ⟨k, F.c k⟩ / w ⟨k, F'.c k⟩) ^ M.b p k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (div_ne_zero (hc k) (hc' k))
  have m0 : (∏ k, M.x ⟨k, F'.c k⟩ ^ M.b p k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (coord_ne hw (hc' k))
  generalize (∏ k, (w ⟨k, F.c k⟩ / w ⟨k, F'.c k⟩) ^ M.b p k) = μ at *
  let RA : Matrix (Fin N) (Fin N) (regRing M.x w) := Matrix.of fun a b => ⟨_, _, hRz a b⟩
  let μA : regRing M.x w := ⟨_, _, hμ⟩
  have eμ : regVal hw μA = μ := valAt_eq hw hμ
  have e1 : RA.map (regRing M.x w).subtype = (F.T p.1)⁻¹ * F'.T p.1 := by ext a b; rfl
  have e2 : RA.map (regVal hw) = Rz := by ext a b; exact valAt_eq hw (hRz a b)
  have bR : IsBlockDiag j Rz := by
    have : IsBlockDiag j RA := fun a b hab =>
      Subtype.ext ((((hF.1 p.1).1.inv (hF.1 p.1).2.isUnit).mul (hF'.1 p.1).1) a b hab)
    exact e2 ▸ this.map _
  rcases ht with ⟨k, a, hk, ha, hz, rfl⟩ | ⟨hk, rfl⟩ <;> rcases ht' with ⟨k', a', hk', ha', hz', rfl⟩ | ⟨hk', rfl⟩
  · obtain rfl : k = k' := Option.some.inj (hk.symm.trans hk')
    have hi : IsProperStep N j p.2 := by
      by_contra hn
      rw [(M.blk_none p).2 hn] at hk
      cases hk
    have ch : ∀ m I', IsStepRows N j p.2 I' → detFac j p.2 Rz * μ *
        ∑ I, valAt M.x (F.u ⟨k, m⟩ I) w * minorIJ Rz I I' = valAt M.x (F'.u ⟨k, m⟩ I') w := by
      intro m I' hI'
      let uA : Finset (Fin N) → regRing M.x w := fun I => ⟨F.u ⟨k, m⟩ I, exists_isValueAt hw (gd.2.1 _ I).1⟩
      let vA : regRing M.x w := ⟨F'.u ⟨k, m⟩ I', exists_isValueAt hw (gd'.2.1 _ I').1⟩
      have e : detFac j p.2 RA * μA * ∑ I, uA I * minorIJ RA I I' = vA := by
        apply (regRing M.x w).subtype_injective
        simp only [map_mul, map_sum, ← detFac_map, ← minorIJ_map, e1]
        have := change_gen M hF hF' hk m hI'
        show _ * (_ / _) * ∑ I, F.u ⟨k, m⟩ I * _ = F'.u ⟨k, m⟩ I'
        rw [← mul_div_assoc, div_mul_eq_mul_div, this, mul_div_cancel_left₀ _ m0]
      have e' := congrArg (regVal hw) e
      simp only [map_mul, map_sum, ← detFac_map, ← minorIJ_map, e2, eμ] at e'
      exact e'
    have ch2 : ∀ m, ∑ I, valAt M.x (F'.u ⟨k, m⟩ I) w * minorIJ h' I (stepCols N j p.2) = detFac j p.2 Rz * μ *
        ∑ I, valAt M.x (F.u ⟨k, m⟩ I) w * minorIJ (Rz * h') I (stepCols N j p.2) := by
      intro m
      simp only [minorIJ_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun I' _ => ?_
      by_cases hs : IsStepRows N j p.2 I'
      · rw [← ch m I' hs, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun I _ => by ring
      · simp [minor_stepCols_eq_zero M.j_le h' I' bh' hs]
    have fin : ∀ I, a * minorIJ h I (stepCols N j p.2) =
        a' * detFac j p.2 Rz * μ * minorIJ (Rz * h') I (stepCols N j p.2) := by
      intro I
      by_cases hs : IsStepRows N j p.2 I
      · rw [← left_inv_val M hF hw gd hk bh hs, ← left_inv_val M hF hw gd hk (bR.mul bh') hs, Finset.mul_sum,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        have := (hz m).symm.trans (hz' m)
        rw [ch2] at this
        linear_combination (valAt M.x (F.u' I ⟨k, m⟩) w) * this
      · rw [minor_stepCols_eq_zero M.j_le h I bh hs, minor_stepCols_eq_zero M.j_le _ I (bR.mul bh') hs]
        simp
    have := pot_step M.j_le p.2 hi pG bG bR dR dh dh' ha ha' μ0 fin
    linarith
  · rw [hk] at hk'; cases hk'
  · rw [hk] at hk'; cases hk'
  · have hi := (M.blk_none p).1 hk
    obtain ⟨v, hv⟩ := exists_isValueAt hw (gd.2.2 p hk).2.1
    obtain ⟨v', hv'⟩ := exists_isValueAt hw (gd.2.2 p hk).2.2
    have v0 : v ≠ 0 := by
      have := isValueAt_mul hv hv'
      rw [mul_inv_cancel₀ (gd.2.2 p hk).1] at this
      have e := (valAt_eq hw this).symm.trans (valAt_eq hw (isValueAt_one_self M.x w))
      exact left_ne_zero_of_mul_eq_one e
    let uA : regRing M.x w := ⟨F.υ p, v, hv⟩
    let vA : regRing M.x w := ⟨F'.υ p, exists_isValueAt hw (gd'.2.2 p hk).2.1⟩
    have e : detFac j p.2 RA * μA * uA = vA := by
      apply (regRing M.x w).subtype_injective
      simp only [map_mul, ← detFac_map, e1]
      have := change_base M hF hF' hk
      show _ * (_ / _) * F.υ p = F'.υ p
      rw [← mul_div_assoc, div_mul_eq_mul_div, this, mul_div_cancel_left₀ _ m0]
    have e' := congrArg (regVal hw) e
    simp only [map_mul, ← detFac_map, e2, eμ] at e'
    have e'' : detFac j p.2 Rz * μ * v = valAt M.x (F'.υ p) w := by
      rw [← valAt_eq hw hv]; exact e'
    have d0 := detFac_ne_zero M.j_le p.2 bR dR
    rw [pot_base M.j_le p.2 hi h h' pG bG bR dR, ← e'', valAt_eq hw hv, norm_mul, norm_mul,
      Real.log_mul (mul_ne_zero (norm_ne_zero_iff.2 d0) (norm_ne_zero_iff.2 μ0)) (norm_ne_zero_iff.2 v0),
      Real.log_mul (norm_ne_zero_iff.2 d0) (norm_ne_zero_iff.2 μ0)]
    linarith

end PositivityTheory.Xgp.c_bm_exists_hom
