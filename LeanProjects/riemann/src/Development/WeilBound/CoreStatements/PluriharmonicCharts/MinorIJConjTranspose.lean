import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc GlobalTheory.CompanionTheory.Ar.PB.CPts
open scoped ComplexOrder Classical

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_hom

variable {N j : ℕ}

theorem exists_selector (R : Type) [CommRing R] (hj : j ≤ N) (i : Fin N) {I' : Finset (Fin N)}
    (hI : IsStepRows N j i I') : ∃ h : Matrix (Fin N) (Fin N) R, IsBlockDiag j h ∧
      ∀ I, minorIJ h I (stepCols N j i) = if I = I' then 1 else 0 := by
  refine ⟨Matrix.of fun a b => if ∃ s, a = I'.orderEmbOfFin hI.1 s ∧ b = (stepCols N j i).orderEmbOfFin rfl s
    then 1 else 0, fun a b hab => ?_, fun I => ?_⟩
  · rw [Matrix.of_apply, if_neg]
    rintro ⟨s, rfl, rfl⟩
    have h1 := hI.2 (I'.orderEmbOfFin_mem hI.1 s)
    have h2 := mem_stepCols_block hj ((stepCols N j i).orderEmbOfFin_mem rfl s)
    apply hab
    split_ifs at h1 h2 with h
    · simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at h1
      omega
    · simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at h1
      exact ⟨fun _ => h2, fun _ => h1⟩
  · by_cases e : I = I'
    · subst e
      rw [if_pos rfl, minorIJ, dif_pos hI.1]
      refine Eq.trans (congrArg Matrix.det ?_) Matrix.det_one
      ext s t
      simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq]
      refine if_congr ⟨?_, ?_⟩ rfl rfl
      · rintro ⟨u, rfl, rfl⟩; rfl
      · rintro rfl; exact ⟨s, rfl, rfl⟩
    · rw [if_neg e]
      by_cases c : I.card = (stepCols N j i).card
      · have hs : ¬ I ⊆ I' := fun hs => e (Finset.eq_of_subset_of_card_le hs (by rw [c, hI.1]))
        obtain ⟨a, ha, has⟩ := Finset.not_subset.mp hs
        refine minorIJ_eq_zero_of_row _ ha fun b _ => ?_
        rw [Matrix.of_apply, if_neg]
        rintro ⟨s, rfl, -⟩
        exact has (I'.orderEmbOfFin_mem hI.1 s)
      · exact minorIJ_of_card_ne _ c

theorem minorIJ_conjTranspose (h : Matrix (Fin N) (Fin N) ℂ) (I J : Finset (Fin N)) :
    minorIJ hᴴ J I = star (minorIJ h I J) := by
  by_cases e : I.card = J.card
  · rw [minorIJ_eq_det h I J _ e rfl, minorIJ_eq_det hᴴ J I _ rfl e, ← Matrix.det_conjTranspose]
    rfl
  · rw [minorIJ_of_card_ne h e, minorIJ_of_card_ne hᴴ (Ne.symm e), star_zero]

theorem gram_minor {G h g : Matrix (Fin N) (Fin N) ℂ} {C : Finset (Fin N)} {a l : ℂ}
    (e : ∀ I, a * minorIJ h I C = l * minorIJ g I C) :
    ‖a‖ ^ 2 * (minorIJ (hᴴ * G * h) C C).re = ‖l‖ ^ 2 * (minorIJ (gᴴ * G * g) C C).re := by
  have key : ∀ (b : ℂ) (f : Matrix (Fin N) (Fin N) ℂ), star b * b * minorIJ (fᴴ * G * f) C C =
      ∑ I', ∑ I, star (b * minorIJ f I C) * minorIJ G I I' * (b * minorIJ f I' C) := by
    intro b f
    rw [minorIJ_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I' _ => ?_
    rw [minorIJ_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [minorIJ_conjTranspose, star_mul]
    ring
  have h1 := key a h
  simp only [e] at h1
  rw [← key l g] at h1
  have n : ∀ b : ℂ, star b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := fun b => by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  rw [n, n] at h1
  simpa only [Complex.re_ofReal_mul] using congrArg Complex.re h1

theorem minor_pos {G : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (C : Finset (Fin N)) : 0 < minorIJ G C C := by
  rw [minorIJ, dif_pos rfl]
  exact (hG.submatrix (C.orderEmbOfFin rfl).injective).det_pos

theorem detFac_pos {G : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (i : Fin N) : 0 < (detFac j i G).re := by
  have : 0 < detFac j i G := by
    unfold detFac
    refine mul_pos ?_ ?_ <;> split_ifs
    exacts [minor_pos hG _, one_pos, minor_pos hG _, one_pos]
  exact (Complex.pos_iff.1 this).1

theorem gram_pos {G h : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (hh : h.det ≠ 0) (C : Finset (Fin N)) :
    0 < (minorIJ (hᴴ * G * h) C C).re := by
  have : (hᴴ * G * h).PosDef := hG.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det h).2 hh.isUnit))
  exact (Complex.pos_iff.1 (minor_pos this C)).1

theorem detFac_conjTranspose (i : Fin N) (h : Matrix (Fin N) (Fin N) ℂ) :
    detFac j i hᴴ = star (detFac j i h) := by
  unfold detFac
  rw [minorIJ_conjTranspose, minorIJ_conjTranspose, star_mul']
  split_ifs <;> simp

theorem log_detFac (hj : j ≤ N) (i : Fin N) {G R : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (bG : IsBlockDiag j G)
    (bR : IsBlockDiag j R) (hR : R.det ≠ 0) :
    (1 / 2) * Real.log (detFac j i (Rᴴ * G * R)).re =
      (1 / 2) * Real.log (detFac j i G).re + Real.log ‖detFac j i R‖ := by
  have h0 := norm_ne_zero_iff.2 (detFac_ne_zero hj i bR hR)
  have e : detFac j i (Rᴴ * G * R) = ((‖detFac j i R‖ ^ 2 : ℝ) : ℂ) * detFac j i G := by
    rw [detFac_mul i bR, detFac_mul i bG, detFac_conjTranspose, mul_right_comm, Complex.star_def, Complex.conj_mul']
    push_cast; rfl
  rw [e, Complex.re_ofReal_mul, Real.log_mul (pow_ne_zero _ h0) (detFac_pos hG i).ne', Real.log_pow]
  push_cast; ring

theorem pot_step (hj : j ≤ N) (i : Fin N) (hi : IsProperStep N j i) {G R h h' : Matrix (Fin N) (Fin N) ℂ}
    (hG : G.PosDef) (bG : IsBlockDiag j G) (bR : IsBlockDiag j R) (hR : R.det ≠ 0) (hh : h.det ≠ 0)
    (hh' : h'.det ≠ 0) {a a' μ : ℂ} (ha : a ≠ 0) (ha' : a' ≠ 0) (hμ : μ ≠ 0)
    (e : ∀ I, a * minorIJ h I (stepCols N j i) = a' * detFac j i R * μ * minorIJ (R * h') I (stepCols N j i)) :
    Real.log ‖a‖ + blockPot j i G h = Real.log ‖a'‖ + Real.log ‖μ‖ + blockPot j i (Rᴴ * G * R) h' := by
  have h0 := detFac_ne_zero hj i bR hR
  have h1 := gram_minor (G := G) e
  have p1 := gram_pos hG hh (stepCols N j i)
  have p2 := gram_pos hG (h := R * h') (by rw [Matrix.det_mul]; exact mul_ne_zero hR hh') (stepCols N j i)
  have h2 := congrArg Real.log h1
  rw [Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 ha)) p1.ne',
    Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 (mul_ne_zero (mul_ne_zero ha' h0) hμ))) p2.ne',
    Real.log_pow, Real.log_pow, norm_mul, norm_mul,
    Real.log_mul (mul_ne_zero (norm_ne_zero_iff.2 ha') (norm_ne_zero_iff.2 h0)) (norm_ne_zero_iff.2 hμ),
    Real.log_mul (norm_ne_zero_iff.2 ha') (norm_ne_zero_iff.2 h0)] at h2
  have e2 : h'ᴴ * (Rᴴ * G * R) * h' = (R * h')ᴴ * G * (R * h') := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  unfold blockPot
  rw [if_pos hi, if_pos hi, log_detFac hj i hG bG bR hR, e2]
  push_cast at h2
  linarith

theorem pot_base (hj : j ≤ N) (i : Fin N) (hi : ¬ IsProperStep N j i) {G R : Matrix (Fin N) (Fin N) ℂ}
    (h h' : Matrix (Fin N) (Fin N) ℂ) (hG : G.PosDef) (bG : IsBlockDiag j G) (bR : IsBlockDiag j R) (hR : R.det ≠ 0) :
    blockPot j i (Rᴴ * G * R) h' = blockPot j i G h + Real.log ‖detFac j i R‖ := by
  unfold blockPot
  rw [if_neg hi, if_neg hi, log_detFac hj i hG bG bR hR]
  ring

theorem detFac_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (i : Fin N) (A : Matrix (Fin N) (Fin N) R) :
    detFac j i (A.map f) = f (detFac j i A) := by
  unfold detFac
  rw [minorIJ_map, minorIJ_map, map_mul]
  split_ifs <;> simp

theorem pot_conj (i : Fin N) (G h : Matrix (Fin N) (Fin N) ℂ) :
    blockPot j i (G.map (starRingEnd ℂ)) (h.map (starRingEnd ℂ)) = blockPot j i G h := by
  have e : (h.map (starRingEnd ℂ))ᴴ * G.map (starRingEnd ℂ) * h.map (starRingEnd ℂ) =
      (hᴴ * G * h).map (starRingEnd ℂ) := by
    rw [Matrix.map_mul, Matrix.map_mul]
    rfl
  unfold blockPot
  rw [e, detFac_map, minorIJ_map, Complex.conj_re, Complex.conj_re]

end PositivityTheory.Xgp.c_bm_exists_hom
