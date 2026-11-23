import Development.WeilBound.CoreStatements.MultihomogeneousSquares.SingSt
import Development.WeilBound.CoreStatements.PluriharmonicCharts.MinorIJConjTranspose

noncomputable section

namespace HeightCancellation.C4

open Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB SquareStatements.Sing
open scoped ComplexOrder

theorem jacobi_blocks {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A B : Matrix (m ⊕ n) (m ⊕ n) ℂ) (h : A * B = 1) : A.det * B.toBlocks₂₂.det = A.toBlocks₁₁.det := by
  have e : A * fromBlocks 1 B.toBlocks₁₂ 0 B.toBlocks₂₂ = fromBlocks A.toBlocks₁₁ 0 A.toBlocks₂₁ 1 := by
    rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply, ← fromBlocks_one,
      fromBlocks_inj] at h
    conv_lhs => rw [← fromBlocks_toBlocks A, fromBlocks_multiply]
    rw [h.2.1, h.2.2.2]
    simp
  have := congrArg det e
  rwa [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_one, det_one, one_mul, mul_one] at this

theorem jacobi {k l : ℕ} (O : Matrix (Fin (k + l)) (Fin (k + l)) ℂ) (hO : O.det ≠ 0) :
    O.det * ((revDual O).submatrix (Fin.castLE (Nat.le_add_left l k)) (Fin.castLE (Nat.le_add_left l k))).det =
      (O.submatrix (Fin.castLE (Nat.le_add_right k l)) (Fin.castLE (Nat.le_add_right k l))).det := by
  have h : O.submatrix finSumFinEquiv finSumFinEquiv * O⁻¹.submatrix finSumFinEquiv finSumFinEquiv = 1 := by
    rw [submatrix_mul_equiv, mul_nonsing_inv _ hO.isUnit, submatrix_one_equiv]
  have h1 := jacobi_blocks _ _ h
  rw [det_submatrix_equiv_self] at h1
  have e : (revDual O).submatrix (Fin.castLE (Nat.le_add_left l k)) (Fin.castLE (Nat.le_add_left l k)) =
      ((O⁻¹.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ᵀ).submatrix Fin.revPerm Fin.revPerm := by
    ext a b
    have r : ∀ a : Fin l, Fin.rev (Fin.castLE (Nat.le_add_left l k) a) = Fin.natAdd k (Fin.rev a) := fun a =>
      Fin.ext (by have := a.2; simp [Fin.rev]; omega)
    simp only [revDual, submatrix_apply, r, ← transpose_nonsing_inv, transpose_apply, toBlocks₂₂, of_apply,
      finSumFinEquiv_apply_right, Fin.revPerm_apply]
  rw [e, det_submatrix_equiv_self, det_transpose, h1]
  rfl

theorem re_mul_pos {a b : ℂ} (ha : 0 < a) : (a * b).re = a.re * b.re := by
  rw [Complex.mul_re, ← (Complex.pos_iff.1 ha).2]
  simp

theorem jacobi_lead {q : ℕ} (O : Matrix (Fin q) (Fin q) ℂ) (hO : O.PosDef) {k l : ℕ} (e : k + l = q) :
    O.det.re * leadMinor (revDual O) l = leadMinor O k := by
  subst e
  unfold leadMinor
  rw [dif_pos (Nat.le_add_left l k), dif_pos (Nat.le_add_right k l), ← jacobi O hO.det_pos.ne',
    re_mul_pos hO.det_pos]

theorem grN_rev {q : ℕ} (O : Matrix (Fin q) (Fin q) ℂ) (hO : O.PosDef) {k l : ℕ} (e : k + l + 1 = q) :
    (grN (revDual O) l)⁻¹ = grN O k := by
  have h0 : O.det.re ≠ 0 := (Complex.pos_iff.1 hO.det_pos).1.ne'
  unfold grN
  rw [← jacobi_lead O hO (k := k + 1) (l := l) (by omega), ← jacobi_lead O hO (k := k) (l := l + 1) (by omega),
    mul_div_mul_left _ _ h0, ← Real.sqrt_inv, inv_div]

theorem log_grN {r : ℕ} {Γ : Matrix (Fin r) (Fin r) ℂ} (hΓ : Γ.PosDef) {k : ℕ} (hk : k < r) :
    0 < grN Γ k ∧ Real.log (grN Γ k) =
      (1 / 2) * Real.log (leadMinor Γ (k + 1)) - (1 / 2) * Real.log (leadMinor Γ k) := by
  have a := leadMinor_pos_of_posDef hΓ (s := k + 1) hk
  have b := leadMinor_pos_of_posDef hΓ (s := k) hk.le
  unfold grN
  refine ⟨Real.sqrt_pos.2 (div_pos a b), ?_⟩
  rw [Real.log_sqrt (div_pos a b).le, Real.log_div a.ne' b.ne']
  ring

theorem minor_emb {R : Type} [CommRing R] {N k : ℕ} (T : Matrix (Fin N) (Fin N) R) (C : Finset (Fin N))
    (f : Fin k → Fin N) (hf : StrictMono f) (hC : ∀ a, a ∈ C ↔ ∃ s, f s = a) :
    minorIJ T C C = (T.submatrix f f).det := by
  have e : C = Finset.univ.image f := by
    ext a
    simp [hC]
  have hc : C.card = k := by
    rw [e, Finset.card_image_of_injective _ hf.injective]
    simp
  rw [MinorCalc.minorIJ_eq_det T C C k hc hc,
    ← Finset.orderEmbOfFin_unique hc (f := f) (fun s => (hC _).2 ⟨s, rfl⟩) hf]

variable {p q : ℕ}

theorem minor_w (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) (i : Fin (p + q)) (hi : (i : ℕ) + 1 ≤ p) :
    (minorIJ Γ (stepCols (p + q) p i) (stepCols (p + q) p i)).re = leadMinor (wBlock Γ) (i + 1) := by
  rw [minor_emb Γ _ (fun s => wEmb p q (Fin.castLE hi s)) (fun a b h => wEmb_strictMono p q h) fun a => ?_]
  · unfold leadMinor
    rw [dif_pos hi]
    rfl
  · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos hi]
    constructor
    · intro h
      exact ⟨⟨a - q, by omega⟩, Fin.ext (by show q + (a - q) = a; omega)⟩
    · rintro ⟨s, rfl⟩
      have := s.2
      show _ ≤ q + (s : ℕ) ∧ q + (s : ℕ) < _
      omega

theorem minor_om (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) (i : Fin (p + q)) (hi : ¬ (i : ℕ) + 1 ≤ p) :
    (minorIJ Γ (stepCols (p + q) p i) (stepCols (p + q) p i)).re = leadMinor (omBlock Γ) (i + 1 - p) := by
  have hq : (i : ℕ) + 1 - p ≤ q := by have := i.2; omega
  rw [minor_emb Γ _ (fun s => omEmb p q (Fin.castLE hq s)) (fun a b h => omEmb_strictMono p q h) fun a => ?_]
  · unfold leadMinor
    rw [dif_pos hq]
    rfl
  · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg hi]
    constructor
    · intro h
      exact ⟨⟨a, h⟩, rfl⟩
    · rintro ⟨s, rfl⟩
      exact s.2

def pot (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) (n : ℕ) : ℝ :=
  (1 / 2) * Real.log (leadMinor (wBlock Γ) (min n p)) + (1 / 2) * Real.log (leadMinor (omBlock Γ) (n - p))

theorem log_mu {Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ} (hΓ : Γ.PosDef) (m : Fin (p + q)) :
    0 < mu p q Γ m ∧ Real.log (mu p q Γ m) = pot Γ (m + 1) - pot Γ m := by
  have hW : (wBlock Γ).PosDef := hΓ.submatrix (wEmb_strictMono p q).injective
  have hO : (omBlock Γ).PosDef := hΓ.submatrix (omEmb_strictMono p q).injective
  have hm := m.2
  unfold mu pot
  split_ifs with h
  · obtain ⟨a, b⟩ := log_grN hW h
    refine ⟨a, ?_⟩
    rw [b, min_eq_left (show (m : ℕ) + 1 ≤ p from h), min_eq_left h.le, show (m : ℕ) + 1 - p = 0 by omega,
      show (m : ℕ) - p = 0 by omega]
    ring
  · rw [grN_rev _ hO (k := m - p) (by omega)]
    obtain ⟨a, b⟩ := log_grN hO (k := m - p) (by omega)
    refine ⟨a, ?_⟩
    rw [b, min_eq_right (show p ≤ (m : ℕ) + 1 by omega), min_eq_right (show p ≤ (m : ℕ) by omega),
      show (m : ℕ) + 1 - p = m - p + 1 by omega]
    ring

theorem sum_tele {N : ℕ} (f : ℕ → ℝ) (i : Fin N) :
    ∑ m ∈ Finset.Iic i, (f ((m : ℕ) + 1) - f m) = f (i + 1) - f 0 := by
  rw [← Finset.sum_range_sub f]
  refine Finset.sum_bij (fun m _ => (m : ℕ)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro m hm
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (Fin.le_def.1 (Finset.mem_Iic.1 hm)))
  · intro a _ b _ h
    exact Fin.ext h
  · intro n hn
    have h1 := Finset.mem_range.1 hn
    have h2 := i.2
    exact ⟨⟨n, by omega⟩, Finset.mem_Iic.2 (show n ≤ (i : ℕ) by omega), rfl⟩

open Classical in
theorem pot_eq {Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ} (hΓ : Γ.PosDef) (i : Fin (p + q)) :
    pot Γ (i + 1) = (1 / 2) * Real.log (detFac p i Γ).re + if IsProperStep (p + q) p i then
      (1 / 2) * Real.log (minorIJ Γ (stepCols (p + q) p i) (stepCols (p + q) p i)).re else 0 := by
  have hW : (wBlock Γ).PosDef := hΓ.submatrix (wEmb_strictMono p q).injective
  have hO : (omBlock Γ).PosDef := hΓ.submatrix (omEmb_strictMono p q).injective
  have hi := i.2
  unfold pot detFac IsProperStep
  rw [minorIJ_wIdx, minorIJ_omIdx]
  by_cases hN : (i : ℕ) + 1 = p + q
  · rw [if_pos (by omega), if_pos hN, if_neg (fun h => h.2 hN), min_eq_right (by omega),
      show (i : ℕ) + 1 - p = q by omega, leadMinor_size_self, leadMinor_size_self, re_mul_pos hW.det_pos,
      Real.log_mul (Complex.pos_iff.1 hW.det_pos).1.ne' (Complex.pos_iff.1 hO.det_pos).1.ne']
    ring
  · rw [if_neg hN, mul_one]
    rcases lt_trichotomy ((i : ℕ) + 1) p with h | h | h
    · rw [if_neg (by omega), if_pos ⟨h.ne, hN⟩, minor_w Γ i h.le, min_eq_left h.le,
        show (i : ℕ) + 1 - p = 0 by omega, leadMinor_size_zero]
      simp
    · rw [if_pos h.ge, if_neg (fun h' => h'.1 h), min_eq_right h.ge,
        show (i : ℕ) + 1 - p = 0 by omega, leadMinor_size_zero, leadMinor_size_self]
      simp
    · rw [if_pos h.le, if_pos ⟨h.ne', hN⟩, minor_om Γ i (by omega), min_eq_right h.le, leadMinor_size_self]

end HeightCancellation.C4

open scoped ComplexOrder in
open Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB HeightCancellation.C4 in
theorem HeightCancellation.c4 : SquareStatements.Sing.C4 := by
  intro p q G h bG hG bh hh
  have hP : (hᴴ * G * h).PosDef := hG.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det h).2 hh.isUnit))
  refine ⟨fun m => (log_mu hP m).1, fun i => ⟨CPts.detFac_ne_zero (Nat.le_add_right p q) i bh hh, ?_⟩⟩
  simp only [(log_mu hP _).2]
  rw [sum_tele (pot (hᴴ * G * h)) i, pot_eq hP,
    PositivityTheory.Xgp.c_bm_exists_hom.log_detFac (Nat.le_add_right p q) i hG bG bh hh]
  have e : pot (hᴴ * G * h) 0 = 0 := by simp [pot, leadMinor_size_zero]
  rw [e, blockPot]
  ring
