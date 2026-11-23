import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDensityAtIdentityUnitaryGroupProbability

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace GlobalTheory.GaugeVolFixer

open PI.RhsWLim PI.RhsWLim.W

variable {k r : ℕ}

def pW (k r : ℕ) (c : Fin k) : Fin (2 * r + k + 1) := ⟨r + c.val, by omega⟩

theorem pW_inj : Function.Injective (pW k r) := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; simp [pW] at this; exact this)

def Ew (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin k) ℂ := fun i c => if i = pW k r c then 1 else 0

theorem EwT_Ew : (Ew k r)ᵀ * Ew k r = 1 := by
  ext c d
  rw [Matrix.mul_apply, Finset.sum_eq_single (pW k r d)]
  · simp only [Matrix.transpose_apply, Ew, Matrix.one_apply]
    by_cases h : c = d
    · subst h; simp
    · rw [if_neg (fun h' => h (pW_inj h').symm), if_neg h]; simp
  · intro i _ hi; simp [Ew, hi]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem Ew_conjT : (Ew k r)ᴴ = (Ew k r)ᵀ := by
  ext i c; simp [Ew, Matrix.conjTranspose_apply]

def iota (A : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  1 - Ew k r * (Ew k r)ᵀ + Ew k r * A * (Ew k r)ᵀ

theorem iota_mul (A B : Matrix (Fin k) (Fin k) ℂ) : iota (r := r) (A * B) = iota (r := r) A * iota (r := r) B := by
  unfold iota
  have h := EwT_Ew (k := k) (r := r)
  set E := Ew k r
  have h1 : E * Eᵀ * (E * Eᵀ) = E * Eᵀ := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Eᵀ, h, Matrix.one_mul]
  have h2 : E * Eᵀ * (E * B * Eᵀ) = E * B * Eᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Eᵀ, ← Matrix.mul_assoc Eᵀ, h, Matrix.one_mul, ← Matrix.mul_assoc]
  have h3 : E * A * Eᵀ * (E * Eᵀ) = E * A * Eᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Eᵀ, h, Matrix.one_mul]
  have h4 : E * A * Eᵀ * (E * B * Eᵀ) = E * (A * B) * Eᵀ := by
    rw [Matrix.mul_assoc (E * A), ← Matrix.mul_assoc Eᵀ, ← Matrix.mul_assoc Eᵀ, h, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, h1, h2, h3, h4]
  abel

theorem iota_conjT (A : Matrix (Fin k) (Fin k) ℂ) : (iota (r := r) A)ᴴ = iota (r := r) Aᴴ := by
  unfold iota
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Ew_conjT]
  have : ((Ew k r)ᵀ)ᴴ = Ew k r := by rw [← Ew_conjT, Matrix.conjTranspose_conjTranspose]
  rw [this]
  simp only [Matrix.mul_assoc]

theorem tau_pW (c : Fin k) : HU.tau k r (pW k r c) = pW k r c := by
  apply Fin.ext; simp [HU.tau, pW]

theorem sgn_pW (c : Fin k) : HU.sgn k r (pW k r c) = 1 := by
  unfold HU.sgn; rw [if_neg (show (pW k r c).val ≠ r + k by show r + c.val ≠ r + k; omega)]

theorem hpk_mul_apply' {X : Type*} (A : Matrix (Fin (2 * r + k + 1)) X ℂ) (i : Fin (2 * r + k + 1)) (j : X) :
    (Hpk k r * A) i j = HU.sgn k r i * A (HU.tau k r i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (HU.tau k r i)]
  · rw [HU.hpk_row, if_pos rfl]
  · intro m _ hm
    rw [HU.hpk_row, if_neg hm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem hpk_Ew : Hpk k r * Ew k r = Ew k r := by
  ext i c
  rw [hpk_mul_apply']
  simp only [Ew]
  by_cases h : HU.tau k r i = pW k r c
  · have hi : i = pW k r c := by rw [← HU.tau_tau i, h, tau_pW]
    rw [if_pos h, if_pos hi, hi, sgn_pW, mul_one]
  · have hi : i ≠ pW k r c := fun hi => h (by rw [hi, tau_pW])
    rw [if_neg h, if_neg hi, mul_zero]

theorem EwT_hpk : (Ew k r)ᵀ * Hpk k r = (Ew k r)ᵀ := by
  ext c j
  rw [Matrix.mul_apply, Finset.sum_eq_single (pW k r c)]
  · rw [Matrix.transpose_apply, Matrix.transpose_apply, Ew, if_pos rfl, one_mul, HU.hpk_row, tau_pW, sgn_pW, Ew]
  · intro b _ hb; rw [Matrix.transpose_apply, Ew, if_neg hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem EwT_bvec (j : Fin (2 * r + k + 1)) (hj : ∀ c, j ≠ pW k r c) : (Ew k r)ᵀ *ᵥ bvec j = 0 := by
  funext c
  rw [Matrix.mulVec, dotProduct]
  simp [bvec, Pi.single_apply, Ew, Matrix.transpose_apply, hj c]

theorem iota_fix (A : Matrix (Fin k) (Fin k) ℂ) (j : Fin (2 * r + k + 1)) (hj : ∀ c, j ≠ pW k r c) :
    iota (r := r) A *ᵥ bvec j = bvec j := by
  unfold iota
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    EwT_bvec j hj]
  simp

theorem iota_UH {A : Matrix (Fin k) (Fin k) ℂ} (hA : Aᴴ * A = 1) : iota (r := r) A ∈ UH (Hpk k r) := by
  show (iota (r := r) A)ᴴ * Hpk k r * iota (r := r) A = Hpk k r
  rw [iota_conjT]
  unfold iota
  have h := EwT_Ew (k := k) (r := r)
  have hH := hpk_Ew (k := k) (r := r)
  have hH' := EwT_hpk (k := k) (r := r)
  set E := Ew k r
  set H := Hpk k r
  have q1 : E * Eᵀ * H = E * Eᵀ := by rw [Matrix.mul_assoc, hH']
  have q2 : H * (E * Eᵀ) = E * Eᵀ := by rw [← Matrix.mul_assoc, hH]
  have q3 : H * (E * A * Eᵀ) = E * A * Eᵀ := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hH]
  have q4 : E * Aᴴ * Eᵀ * H = E * Aᴴ * Eᵀ := by rw [Matrix.mul_assoc, hH']
  have q5 : E * Eᵀ * (E * Eᵀ) = E * Eᵀ := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Eᵀ, h, Matrix.one_mul]
  have q6 : E * Eᵀ * (E * A * Eᵀ) = E * A * Eᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Eᵀ, ← Matrix.mul_assoc Eᵀ, h, Matrix.one_mul, ← Matrix.mul_assoc]
  have q7 : E * Aᴴ * Eᵀ * (E * Eᵀ) = E * Aᴴ * Eᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Eᵀ, h, Matrix.one_mul]
  have q8 : E * Aᴴ * Eᵀ * (E * A * Eᵀ) = E * Eᵀ := by
    rw [Matrix.mul_assoc (E * Aᴴ), ← Matrix.mul_assoc Eᵀ, ← Matrix.mul_assoc Eᵀ, h, Matrix.one_mul]
    rw [← Matrix.mul_assoc (E * Aᴴ), Matrix.mul_assoc E, hA, Matrix.mul_one]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc] at *
  simp only [q1, q2, q3, q4, q5, q6, q7, q8]
  abel

abbrev SW (k r : ℕ) : Set (Mat k r) := UWset k r (wLast k r)

abbrev U1 (k : ℕ) : Set (Matrix (Fin k) (Fin k) ℂ) := UH (1 : Matrix (Fin k) (Fin k) ℂ)

theorem mem_unitaryGroupMatrixSet_iff {A : Matrix (Fin k) (Fin k) ℂ} : A ∈ U1 k ↔ Aᴴ * A = 1 := by
  show Aᴴ * 1 * A = 1 ↔ _
  rw [Matrix.mul_one]

theorem iota_mem {A : Matrix (Fin k) (Fin k) ℂ} (hA : A ∈ U1 k) : iota (r := r) A ∈ SW k r := by
  have hA' := mem_unitaryGroupMatrixSet_iff.1 hA
  refine ⟨iota_UH hA', fun a => ⟨iota_fix A _ fun c h => ?_, iota_fix A _ fun c h => ?_⟩, iota_fix A _ fun c h => ?_⟩
  · have := congrArg Fin.val h; simp [eI, pW] at this; omega
  · have := congrArg Fin.val h; simp [esI, pW] at this; have := a.isLt; have := c.isLt; omega
  · have := congrArg Fin.val h; simp [wI, pW] at this; have := c.isLt; omega

theorem nonW (i : Fin (2 * r + k + 1)) (hi : ∀ c, i ≠ pW k r c) :
    (∃ a : Fin r, i = eI k r a) ∨ (∃ a : Fin r, i = esI k r a) ∨ i = wI k r (Fin.last k) := by
  have := i.isLt
  by_cases h1 : i.val < r
  · exact Or.inl ⟨⟨i.val, h1⟩, Fin.ext rfl⟩
  · by_cases h2 : i.val < r + k
    · exact absurd (Fin.ext (by simp [pW]; omega) : i = pW k r ⟨i.val - r, by omega⟩) (hi _)
    · by_cases h3 : i.val = r + k
      · exact Or.inr (Or.inr (Fin.ext (by simp [wI]; omega)))
      · exact Or.inr (Or.inl ⟨⟨2 * r + k - i.val, by omega⟩, Fin.ext (by simp [esI]; omega)⟩)

theorem tau_nonW (i : Fin (2 * r + k + 1)) (hi : ∀ c, i ≠ pW k r c) : ∀ c, HU.tau k r i ≠ pW k r c := by
  intro c h
  apply hi c
  rw [← HU.tau_tau i, h, tau_pW]

theorem fix_nonW {g : Mat k r} (hg : g ∈ SW k r) (j : Fin (2 * r + k + 1)) (hj : ∀ c, j ≠ pW k r c) :
    g *ᵥ bvec j = bvec j := by
  rcases nonW j hj with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl
  · exact (hg.2.1 a).1
  · exact (hg.2.1 a).2
  · exact hg.2.2

theorem col_nonW {g : Mat k r} (hg : g ∈ SW k r) (i j : Fin (2 * r + k + 1)) (hj : ∀ c, j ≠ pW k r c) :
    g i j = if i = j then 1 else 0 := by
  have := congrFun (fix_nonW hg j hj) i
  rw [Matrix.mulVec, dotProduct] at this
  simpa [bvec, Pi.single_apply, eq_comm] using this

theorem row_nonW {g : Mat k r} (hg : g ∈ SW k r) (i j : Fin (2 * r + k + 1)) (hi : ∀ c, i ≠ pW k r c) :
    g i j = if i = j then 1 else 0 := by
  have hmW := tau_nonW i hi
  have hU : gᴴ * (Hpk k r * g) = Hpk k r := by rw [← Matrix.mul_assoc]; exact hg.1
  have e := congrFun (congrFun hU (HU.tau k r i)) j
  rw [Matrix.mul_apply, Finset.sum_eq_single (HU.tau k r i)] at e
  · rw [Matrix.conjTranspose_apply, col_nonW hg _ _ hmW, if_pos rfl, star_one, one_mul, HU.hpk_mul_apply,
      HU.tau_tau, HU.hpk_row, HU.tau_tau] at e
    have hs : HU.sgn k r (HU.tau k r i) ≠ 0 := by unfold HU.sgn; split_ifs <;> norm_num
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl] at e
      rw [if_pos rfl]
      exact mul_left_cancel₀ hs (e.trans (mul_one _).symm)
    · rw [if_neg (Ne.symm hij)] at e
      rw [if_neg hij]
      exact (mul_eq_zero.1 e).resolve_left hs
  · intro l _ hl
    rw [Matrix.conjTranspose_apply, col_nonW hg _ _ hmW, if_neg hl, star_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem isMatGroup_SW : PI.IsMatGroup (SW k r) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
    · exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
        continuous_const
    · have e : {g : Mat k r | ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧
          g *ᵥ bvec (esI k r a) = bvec (esI k r a)} = ⋂ a : Fin r, ({g : Mat k r | g *ᵥ bvec (eI k r a) =
          bvec (eI k r a)} ∩ {g | g *ᵥ bvec (esI k r a) = bvec (esI k r a)}) := by ext g; simp
      show IsClosed {g : Mat k r | ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧
          g *ᵥ bvec (esI k r a) = bvec (esI k r a)}
      rw [e]
      exact isClosed_iInter fun a => IsClosed.inter
        (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)
        (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)
    · exact isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const
  · exact ⟨HU.uh_one, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
  · intro a ha b hb
    refine ⟨HU.uh_mul ha.1 hb.1, fun c => ⟨?_, ?_⟩, ?_⟩
    · rw [← Matrix.mulVec_mulVec, (hb.2.1 c).1, (ha.2.1 c).1]
    · rw [← Matrix.mulVec_mulVec, (hb.2.1 c).2, (ha.2.1 c).2]
    · rw [← Matrix.mulVec_mulVec, hb.2.2, ha.2.2]
  · intro a ha
    have hu := HU.isUnit_of_uh ha.1
    have hinv : ∀ v, a *ᵥ v = v → a⁻¹ *ᵥ v = v := fun v hv => by
      conv_lhs => rw [← hv]
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
    exact ⟨⟨HU.uh_inv ha.1, fun c => ⟨hinv _ (ha.2.1 c).1, hinv _ (ha.2.1 c).2⟩, hinv _ ha.2.2⟩,
      Matrix.mul_nonsing_inv _ hu⟩

end GlobalTheory.GaugeVolFixer

namespace GlobalTheory.GaugeVolFixer

open PI.RhsWLim PI.RhsWLim.W

variable {k r : ℕ}

theorem Ew_pW (c b : Fin k) : Ew k r (pW k r c) b = if c = b then 1 else 0 := by
  unfold Ew
  by_cases h : c = b
  · rw [if_pos (by rw [h]), if_pos h]
  · rw [if_neg (fun e => h (pW_inj e)), if_neg h]

theorem wEmbeddingConj_apply_wPositions (M : Matrix (Fin k) (Fin k) ℂ) (c d : Fin k) :
    (Ew k r * M * (Ew k r)ᵀ) (pW k r c) (pW k r d) = M c d := by
  rw [Matrix.mul_apply, Finset.sum_eq_single d]
  · rw [Matrix.transpose_apply, Ew_pW, if_pos rfl, mul_one, Matrix.mul_apply, Finset.sum_eq_single c]
    · rw [Ew_pW, if_pos rfl, one_mul]
    · intro b _ hb; rw [Ew_pW, if_neg (Ne.symm hb), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb; rw [Matrix.transpose_apply, Ew_pW, if_neg (Ne.symm hb), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem EMET_out_row (M : Matrix (Fin k) (Fin k) ℂ) (i j : Fin (2 * r + k + 1)) (hi : ∀ c, i ≠ pW k r c) :
    (Ew k r * M * (Ew k r)ᵀ) i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [Matrix.mul_apply, Finset.sum_eq_zero (fun c _ => by simp [Ew, hi c]), zero_mul]

theorem EMET_out_col (M : Matrix (Fin k) (Fin k) ℂ) (i j : Fin (2 * r + k + 1)) (hj : ∀ c, j ≠ pW k r c) :
    (Ew k r * M * (Ew k r)ᵀ) i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun d _ => ?_
  simp [Ew, Matrix.transpose_apply, hj d]

theorem unitaryBlockEmbeddingAtWPositions_apply_wPositions (A : Matrix (Fin k) (Fin k) ℂ) (c d : Fin k) :
    iota (r := r) A (pW k r c) (pW k r d) = A c d := by
  unfold iota
  have h1 := wEmbeddingConj_apply_wPositions (r := r) (1 : Matrix (Fin k) (Fin k) ℂ) c d
  rw [Matrix.mul_one] at h1
  rw [Matrix.add_apply, Matrix.sub_apply, h1, wEmbeddingConj_apply_wPositions, Matrix.one_apply, Matrix.one_apply]
  by_cases h : c = d
  · subst h; simp
  · rw [if_neg (fun e => h (pW_inj e)), if_neg h]; ring

theorem iota_apply_out (A : Matrix (Fin k) (Fin k) ℂ) (i j : Fin (2 * r + k + 1))
    (h : (∀ c, i ≠ pW k r c) ∨ (∀ c, j ≠ pW k r c)) : iota (r := r) A i j = if i = j then 1 else 0 := by
  unfold iota
  have e1 : (Ew k r * (Ew k r)ᵀ) i j = 0 := by
    have := (show Ew k r * (Ew k r)ᵀ = Ew k r * (1 : Matrix (Fin k) (Fin k) ℂ) * (Ew k r)ᵀ by rw [Matrix.mul_one])
    rw [this]
    rcases h with h | h
    · exact EMET_out_row (1 : Matrix (Fin k) (Fin k) ℂ) i j h
    · exact EMET_out_col (1 : Matrix (Fin k) (Fin k) ℂ) i j h
  have e2 : (Ew k r * A * (Ew k r)ᵀ) i j = 0 := by
    rcases h with h | h
    · exact EMET_out_row A i j h
    · exact EMET_out_col A i j h
  rw [Matrix.add_apply, Matrix.sub_apply, e1, e2, Matrix.one_apply]; ring

def blk (g : Mat k r) : Matrix (Fin k) (Fin k) ℂ := (Ew k r)ᵀ * g * Ew k r

theorem blk_apply (g : Mat k r) (c d : Fin k) : blk g c d = g (pW k r c) (pW k r d) := by
  rw [blk, Matrix.mul_apply, Finset.sum_eq_single (pW k r d)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (pW k r c)]
    · simp [Ew]
    · intro b _ hb; simp [Ew, Matrix.transpose_apply, hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb; simp [Ew, hb]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem blk_iota (A : Matrix (Fin k) (Fin k) ℂ) : blk (iota (r := r) A) = A := by
  ext c d; rw [blk_apply, unitaryBlockEmbeddingAtWPositions_apply_wPositions]

theorem iota_inj {A B : Matrix (Fin k) (Fin k) ℂ} (h : iota (r := r) A = iota (r := r) B) : A = B := by
  rw [← blk_iota (r := r) A, ← blk_iota (r := r) B, h]

theorem eq_iota_blk {g : Mat k r}
    (h : ∀ i j, ((∀ c, i ≠ pW k r c) ∨ (∀ c, j ≠ pW k r c)) → g i j = if i = j then 1 else 0) :
    g = iota (r := r) (blk g) := by
  ext i j
  by_cases hi : ∃ c, i = pW k r c
  · obtain ⟨c, rfl⟩ := hi
    by_cases hj : ∃ d, j = pW k r d
    · obtain ⟨d, rfl⟩ := hj
      rw [unitaryBlockEmbeddingAtWPositions_apply_wPositions, blk_apply]
    · push_neg at hj
      rw [iota_apply_out _ _ _ (Or.inr hj), h _ _ (Or.inr hj)]
  · push_neg at hi
    rw [iota_apply_out _ _ _ (Or.inl hi), h _ _ (Or.inl hi)]

theorem out_SW {g : Mat k r} (hg : g ∈ SW k r) (i j : Fin (2 * r + k + 1))
    (h : (∀ c, i ≠ pW k r c) ∨ (∀ c, j ≠ pW k r c)) : g i j = if i = j then 1 else 0 := by
  rcases h with h | h
  · exact row_nonW hg i j h
  · exact col_nonW hg i j h

theorem blk_unitary {g : Mat k r} (hg : g ∈ SW k r) : blk g ∈ U1 k := by
  rw [mem_unitaryGroupMatrixSet_iff]
  set A := blk g
  have hgi : g = iota (r := r) A := eq_iota_blk (out_SW hg)
  have hUi : (iota (r := r) A)ᴴ * Hpk k r * iota (r := r) A = Hpk k r := hgi ▸ hg.1
  have hE := EwT_Ew (k := k) (r := r)
  have hIE : iota (r := r) A * Ew k r = Ew k r * A := by
    unfold iota
    rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc (Ew k r) (Ew k r)ᵀ, hE, Matrix.mul_one,
      Matrix.mul_assoc (Ew k r * A), hE, Matrix.mul_one, sub_self, zero_add]
  have hEI : (Ew k r)ᵀ * (iota (r := r) A)ᴴ = Aᴴ * (Ew k r)ᵀ := by
    have := congrArg Matrix.conjTranspose hIE
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Ew_conjT] at this
    exact this
  have key : (Ew k r)ᵀ * ((iota (r := r) A)ᴴ * Hpk k r * iota (r := r) A) * Ew k r = Aᴴ * A := by
    calc (Ew k r)ᵀ * ((iota (r := r) A)ᴴ * Hpk k r * iota (r := r) A) * Ew k r
        = ((Ew k r)ᵀ * (iota (r := r) A)ᴴ) * Hpk k r * (iota (r := r) A * Ew k r) := by
          simp only [Matrix.mul_assoc]
      _ = (Aᴴ * (Ew k r)ᵀ) * Hpk k r * (Ew k r * A) := by rw [hEI, hIE]
      _ = Aᴴ * ((Ew k r)ᵀ * Hpk k r * Ew k r) * A := by simp only [Matrix.mul_assoc]
      _ = Aᴴ * A := by rw [EwT_hpk, hE, Matrix.mul_one]
  rw [← key, hUi, EwT_hpk, hE]

def cE (k r : ℕ) : Matrix (Fin k) (Fin k) ℂ →ₗ[ℝ] Mat k r where
  toFun Y := Ew k r * Y * (Ew k r)ᵀ
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    rw [RingHom.id_apply, ← Complex.coe_smul, ← Complex.coe_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem cE_apply (Y : Matrix (Fin k) (Fin k) ℂ) : cE k r Y = Ew k r * Y * (Ew k r)ᵀ := rfl

theorem blk_cE (Y : Matrix (Fin k) (Fin k) ℂ) : blk (cE k r Y) = Y := by
  ext c d; rw [blk_apply, cE_apply, wEmbeddingConj_apply_wPositions]

theorem cE_pow (Y : Matrix (Fin k) (Fin k) ℂ) (m : ℕ) :
    (cE k r Y) ^ m = Ew k r * Y ^ m * (Ew k r)ᵀ + (if m = 0 then 1 - Ew k r * (Ew k r)ᵀ else 0) := by
  have h := EwT_Ew (k := k) (r := r)
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, if_neg (Nat.succ_ne_zero m), add_zero, cE_apply, Matrix.add_mul]
    have e1 : Ew k r * Y ^ m * (Ew k r)ᵀ * (Ew k r * Y * (Ew k r)ᵀ) = Ew k r * Y ^ (m + 1) * (Ew k r)ᵀ := by
      rw [Matrix.mul_assoc (Ew k r * Y ^ m), ← Matrix.mul_assoc (Ew k r)ᵀ, ← Matrix.mul_assoc (Ew k r)ᵀ, h,
        Matrix.one_mul, pow_succ]
      simp only [Matrix.mul_assoc]
    have hh : ∀ X : Matrix (Fin k) (Fin (2 * r + k + 1)) ℂ, (Ew k r)ᵀ * (Ew k r * X) = X := fun X => by
      rw [← Matrix.mul_assoc, h, Matrix.one_mul]
    have e2 : (if m = 0 then 1 - Ew k r * (Ew k r)ᵀ else 0) * (Ew k r * Y * (Ew k r)ᵀ) = 0 := by
      split_ifs
      · simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hh, sub_self]
      · rw [Matrix.zero_mul]
    rw [e1, e2, add_zero]

theorem exp_cE (Y : Matrix (Fin k) (Fin k) ℂ) : NormedSpace.exp (cE k r Y) = iota (r := r) (NormedSpace.exp Y) := by
  letI : SeminormedRing (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : SeminormedRing (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.linftyOpNormedAlgebra
  let L0 : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    { toFun := fun M => Ew k r * M * (Ew k r)ᵀ
      map_add' := fun M N => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c M => by rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul] }
  let L : Matrix (Fin k) (Fin k) ℂ →L[ℂ] Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    LinearMap.toContinuousLinearMap L0
  have hL : ∀ M, L M = Ew k r * M * (Ew k r)ᵀ := fun M => rfl
  set Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := 1 - Ew k r * (Ew k r)ᵀ with hQ
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ), NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  have hs := NormedSpace.expSeries_summable' (𝕂 := ℂ) Y
  simp_rw [cE_pow, smul_add]
  have hs1 : Summable fun m : ℕ => ((m.factorial : ℂ)⁻¹) • (Ew k r * Y ^ m * (Ew k r)ᵀ) := by
    have := (L.summable hs)
    simpa [hL, Matrix.mul_smul, Matrix.smul_mul] using this
  have hs2 : Summable fun m : ℕ => ((m.factorial : ℂ)⁻¹) • (if m = 0 then Q else 0) := by
    refine summable_of_ne_finset_zero (s := {0}) fun m hm => ?_
    rw [Finset.mem_singleton] at hm
    rw [if_neg hm, smul_zero]
  rw [hs1.tsum_add hs2]
  have t2 : ∑' m : ℕ, ((m.factorial : ℂ)⁻¹) • (if m = 0 then Q else 0) = Q := by
    rw [tsum_eq_single 0]
    · simp
    · intro m hm; rw [if_neg hm, smul_zero]
  have t1 : ∑' m : ℕ, ((m.factorial : ℂ)⁻¹) • (Ew k r * Y ^ m * (Ew k r)ᵀ) =
      Ew k r * (∑' m : ℕ, ((m.factorial : ℂ)⁻¹) • Y ^ m) * (Ew k r)ᵀ := by
    rw [← hL, L.map_tsum hs]
    refine tsum_congr fun m => ?_
    rw [map_smul, hL]
  rw [t1, t2, hQ]
  unfold iota
  abel

theorem entry_zero_of_const {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) (c : ℂ)
    (h : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) i j = c) : X i j = 0 := by
  letI : SeminormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedAlgebra
  have h1 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • X)) (NormedSpace.exp ((0 : ℝ) • X) * X) 0 :=
    hasDerivAt_exp_smul_const X 0
  let L : Matrix (Fin d) (Fin d) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h3 : (L ∘ fun u : ℝ => NormedSpace.exp (u • X)) = fun _ => c := by
    funext u
    have hu : (u • X) = ((u : ℂ) • X) := (Complex.coe_smul u X).symm
    simp only [Function.comp, hu]
    exact h u
  rw [h3] at h2
  have h4 := h2.unique (hasDerivAt_const (0 : ℝ) c)
  have h5 : (NormedSpace.exp ((0 : ℝ) • X) * X) i j = 0 := h4
  simpa using h5

theorem smul_cE (t : ℝ) (Y : Matrix (Fin k) (Fin k) ℂ) : (t : ℂ) • cE k r Y = cE k r ((t : ℂ) • Y) := by
  rw [cE_apply, cE_apply, Matrix.mul_smul, Matrix.smul_mul]

theorem lieOf_SW : lieOf (SW k r) = cE k r '' lieOf (U1 k) := by
  ext Z
  constructor
  · intro hZ
    have hout : ∀ i j, ((∀ c, i ≠ pW k r c) ∨ (∀ c, j ≠ pW k r c)) → Z i j = 0 := fun i j h =>
      entry_zero_of_const Z i j (if i = j then 1 else 0) fun t => out_SW (hZ t) i j h
    have hZY : cE k r (blk Z) = Z := by
      ext i j
      rw [cE_apply]
      by_cases hi : ∃ c, i = pW k r c
      · obtain ⟨c, rfl⟩ := hi
        by_cases hj : ∃ d, j = pW k r d
        · obtain ⟨d, rfl⟩ := hj
          rw [wEmbeddingConj_apply_wPositions, blk_apply]
        · push_neg at hj
          rw [EMET_out_col _ _ _ hj, hout _ _ (Or.inr hj)]
      · push_neg at hi
        rw [EMET_out_row _ _ _ hi, hout _ _ (Or.inl hi)]
    refine ⟨blk Z, fun t => ?_, hZY⟩
    have h1 := blk_unitary (hZ t)
    rwa [← hZY, smul_cE, exp_cE, blk_iota] at h1
  · rintro ⟨Y, hY, rfl⟩ t
    rw [smul_cE, exp_cE]
    exact iota_mem (hY t)

end GlobalTheory.GaugeVolFixer

namespace GlobalTheory.GaugeVolFixer

open PI.RhsWLim PI.RhsWLim.W

variable {k r : ℕ}

def RLm (m : ℕ) : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) where
  toFun X := (WithLp.equiv 2 _).symm (realifyFun X)
  map_add' X Y := by
    ext p
    rcases p with ⟨i, j, b⟩
    cases b <;> simp [realifyFun]
  map_smul' c X := by
    ext p
    rcases p with ⟨i, j, b⟩
    cases b <;> simp [realifyFun]

def ULm (m : ℕ) : EuclideanSpace ℝ (Fin m × Fin m × Bool) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ where
  toFun := unrealify
  map_add' x y := by ext i j; apply Complex.ext <;> simp [unrealify]
  map_smul' c x := by ext i j; apply Complex.ext <;> simp [unrealify]

theorem unrealify_RLm {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : unrealify (RLm m X) = X := by
  ext i j
  apply Complex.ext <;> simp [unrealify, RLm, realifyFun]

theorem RLm_unrealify {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : RLm m (unrealify x) = x := by
  ext p
  rcases p with ⟨i, j, b⟩
  cases b <;> simp [unrealify, RLm, realifyFun]

theorem norm_sq_RLm {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : ‖RLm m X‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply]
  simp [RLm, realifyFun, sq]
  ring

def Lc (k r : ℕ) : EuclideanSpace ℝ (Fin k × Fin k × Bool) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) :=
  RLm (2 * r + k + 1) ∘ₗ cE k r ∘ₗ ULm k

theorem Lc_apply (x : EuclideanSpace ℝ (Fin k × Fin k × Bool)) :
    Lc k r x = RLm (2 * r + k + 1) (cE k r (unrealify x)) := rfl

theorem sum_eq_sum_wPositions (f : Fin (2 * r + k + 1) → ℝ) (hf : ∀ i, (∀ c, i ≠ pW k r c) → f i = 0) :
    ∑ i, f i = ∑ c, f (pW k r c) := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (pW k r))) (fun i _ hi => hf i (fun c h => hi
    (Finset.mem_image.2 ⟨c, Finset.mem_univ _, h.symm⟩))), Finset.sum_image (fun a _ b _ h => pW_inj h)]

theorem norm_Lc (x : EuclideanSpace ℝ (Fin k × Fin k × Bool)) : ‖Lc k r x‖ = ‖x‖ := by
  set Y := unrealify x
  have h1 := norm_sq_RLm (cE k r Y)
  have h2 := norm_sq_RLm Y
  rw [RLm_unrealify] at h2
  have e : ∑ i, ∑ j, ‖cE k r Y i j‖ ^ 2 = ∑ c, ∑ d, ‖Y c d‖ ^ 2 := by
    rw [sum_eq_sum_wPositions (fun i => ∑ j, ‖cE k r Y i j‖ ^ 2) (fun i hi => Finset.sum_eq_zero fun j _ => by
      rw [cE_apply, EMET_out_row Y i j hi, norm_zero]; ring)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sum_eq_sum_wPositions (fun j => ‖cE k r Y (pW k r c) j‖ ^ 2) (fun j hj => by rw [cE_apply, EMET_out_col Y _ j hj, norm_zero]; ring)]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [cE_apply, wEmbeddingConj_apply_wPositions]
  rw [e, ← h2] at h1
  rw [Lc_apply]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1

theorem Lc_inj : Function.Injective (Lc k r) := by
  intro x y h
  rw [Lc_apply, Lc_apply] at h
  have h1 := congrArg unrealify h
  rw [unrealify_RLm, unrealify_RLm] at h1
  have h2 := congrArg blk h1
  rw [blk_cE, blk_cE] at h2
  rw [← RLm_unrealify x, ← RLm_unrealify y, h2]

theorem lieE_SW : lieE (SW k r) = (lieE (U1 k)).map (Lc k r) := by
  unfold lieE
  rw [lieOf_SW, Submodule.map_span, Set.image_image, Set.image_image]
  congr 1

def isoE (k r : ℕ) : lieE (U1 k) ≃ₗ[ℝ] lieE (SW k r) :=
  (Submodule.equivMapOfInjective (Lc k r) Lc_inj (lieE (U1 k))).trans (LinearEquiv.ofEq _ _ lieE_SW.symm)

theorem isoE_coe (x : lieE (U1 k)) :
    ((isoE k r x : lieE (SW k r)) : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) =
      Lc k r (x : EuclideanSpace ℝ (Fin k × Fin k × Bool)) := rfl

theorem norm_isoE (x : lieE (U1 k)) : ‖isoE k r x‖ = ‖x‖ := by
  change ‖((isoE k r x : lieE (SW k r)) : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖ =
    ‖(x : EuclideanSpace ℝ (Fin k × Fin k × Bool))‖
  rw [isoE_coe, norm_Lc]

def isoL (k r : ℕ) : lieE (U1 k) ≃ₗᵢ[ℝ] lieE (SW k r) :=
  { isoE k r with norm_map' := norm_isoE }

theorem isoL_coe (x : lieE (U1 k)) :
    ((isoL k r x : lieE (SW k r)) : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) =
      Lc k r (x : EuclideanSpace ℝ (Fin k × Fin k × Bool)) := rfl

theorem vol_ball_eq (ρ : ℝ) : volume (Metric.ball (0 : lieE (SW k r)) ρ) =
    volume (Metric.ball (0 : lieE (U1 k)) ρ) := by
  have hT : MeasurePreserving (isoL k r) := (isoL k r).measurePreserving
  have e : (isoL k r) ⁻¹' Metric.ball 0 ρ = Metric.ball 0 ρ := by
    ext y; simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]
  rw [← e, hT.measure_preimage measurableSet_ball.nullMeasurableSet]

def iM (k r : ℕ) (x : PI.MtM k) : Mt k r := iota (r := r) (Matrix.of x)

def bM (k r : ℕ) (y : Mt k r) : PI.MtM k := blk (Matrix.of y)

theorem continuous_iM : Continuous (iM k r) := by
  show Continuous fun x : PI.MtM k =>
    ((1 - Ew k r * (Ew k r)ᵀ + Ew k r * (Matrix.of x) * (Ew k r)ᵀ : Mat k r))
  exact continuous_const.add ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)

theorem continuous_bM : Continuous (bM k r) := by
  show Continuous fun y : Mt k r => (((Ew k r)ᵀ * Matrix.of y * Ew k r : Matrix (Fin k) (Fin k) ℂ))
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem iM_memb : MeasurableEmbedding (iM k r) :=
  (Function.LeftInverse.isClosedEmbedding (f := bM k r) (fun x => blk_iota (Matrix.of x)) continuous_bM
    continuous_iM).measurableEmbedding

def eS (k : ℕ) (ρ : ℝ) : Set (PI.MtM k) :=
  (fun X : lieE (U1 k) => Matrix.of.symm (NormedSpace.exp (unrealify (X : EuclideanSpace ℝ (Fin k × Fin k × Bool))))) ''
    Metric.ball 0 ρ

theorem exp_isoL (x : lieE (U1 k)) :
    NormedSpace.exp (unrealify ((isoL k r x : lieE (SW k r)) :
      EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))) =
      iota (r := r) (NormedSpace.exp (unrealify (x : EuclideanSpace ℝ (Fin k × Fin k × Bool)))) := by
  rw [isoL_coe, Lc_apply, unrealify_RLm, exp_cE]

theorem preimage_expBall (ρ : ℝ) : iM k r ⁻¹' expBall (k := k) (r := r) (SW k r) ρ = eS k ρ := by
  ext x
  simp only [Set.mem_preimage, expBall, eS, Set.mem_image]
  constructor
  · rintro ⟨y, hy, hyx⟩
    obtain ⟨z, rfl⟩ := (isoL k r).surjective y
    refine ⟨z, ?_, ?_⟩
    · rw [mem_ball_zero_iff] at hy ⊢; rwa [LinearIsometryEquiv.norm_map] at hy
    · have : iota (r := r) (NormedSpace.exp (unrealify (z : EuclideanSpace ℝ (Fin k × Fin k × Bool)))) =
          iota (r := r) (Matrix.of x) := by
        rw [← exp_isoL]; exact hyx
      exact iota_inj this
  · rintro ⟨z, hz, hzx⟩
    refine ⟨isoL k r z, ?_, ?_⟩
    · rw [mem_ball_zero_iff] at hz ⊢; rwa [LinearIsometryEquiv.norm_map]
    · show NormedSpace.exp (unrealify ((isoL k r z : lieE (SW k r)) :
        EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))) = iota (r := r) (Matrix.of x)
      rw [exp_isoL, ← hzx]; rfl

theorem gaugeVolUk : W.GaugeVolUk := by
  intro k r ν hν
  obtain ⟨μ₀, hμ₀, h₀⟩ := GlobalTheory.UnitaryVolume.exists_prob_haar (GlobalTheory.UnitaryVolume.isMatGroup_UH_one k)
    (GlobalTheory.UnitaryVolume.isCompact_UH_one k)
  have hD : Tendsto (fun ρ : ℝ => μ₀ (eS k ρ) / volume (Metric.ball (0 : lieE (U1 k)) ρ)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (volU k)⁻¹)) := GlobalTheory.UnitaryVolume.hasDens_unitary k μ₀ hμ₀ h₀
  have hvpos : 0 < volU k := Finset.prod_pos fun i _ => by have := Real.pi_pos; positivity
  set ν0 : Measure (Mt k r) := ENNReal.ofReal (volU k) • μ₀.map (iM k r) with hν0def
  have hν0 : ∀ s, ν0 s = ENNReal.ofReal (volU k) * μ₀ (iM k r ⁻¹' s) := fun s => by
    rw [hν0def, Measure.smul_apply, smul_eq_mul, iM_memb.map_apply]
  have hu0 : ν0 Set.univ = ENNReal.ofReal (volU k) := by rw [hν0, Set.preimage_univ, h₀, mul_one]
  have hfin : IsFiniteMeasure ν0 := ⟨by rw [hu0]; exact ENNReal.ofReal_lt_top⟩
  have hH : PI.IsHaarOnM (SW k r) ν0 := by
    refine ⟨inferInstance, fun h => ?_, ?_, fun s hs => ?_⟩
    · have := hu0
      rw [h, Measure.coe_zero, Pi.zero_apply] at this
      exact (ENNReal.ofReal_pos.2 hvpos).ne' this.symm
    · rw [hν0]
      have : μ₀ (iM k r ⁻¹' {x | Matrix.of x ∉ SW k r}) = 0 :=
        measure_mono_null (fun x hx => fun hx' => hx (iota_mem hx')) hμ₀.2.2.1
      rw [this, mul_zero]
    · have hb := blk_unitary hs
      have hcomp : PI.lmulQ s ∘ iM k r = iM k r ∘ PI.lmulQ (blk s) := by
        funext x
        show s * iota (r := r) (Matrix.of x) = iota (r := r) (blk s * Matrix.of x)
        rw [iota_mul, ← eq_iota_blk (out_SW hs)]
      rw [hν0def, Measure.map_smul, Measure.map_map (GlobalTheory.MatHaar.lmulQ_cont s).measurable iM_memb.measurable, hcomp,
        ← Measure.map_map iM_memb.measurable (GlobalTheory.MatHaar.lmulQ_cont (blk s)).measurable, hμ₀.2.2.2 _ hb]
  have hr0 : Tendsto (fun ρ : ℝ => (ν0 (expBall (k := k) (r := r) (SW k r) ρ)).toReal / sVol k r (SW k r) ρ)
      (𝓝[>] 0) (𝓝 1) := by
    have h1 := ((ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hD).const_mul (volU k)
    rw [ENNReal.toReal_ofReal (inv_nonneg.2 hvpos.le), mul_inv_cancel₀ hvpos.ne'] at h1
    refine h1.congr fun ρ => ?_
    simp only [Function.comp, sVol]
    rw [hν0, preimage_expBall, vol_ball_eq, ENNReal.toReal_mul, ENNReal.toReal_ofReal hvpos.le, ENNReal.toReal_div,
      mul_div_assoc]
  obtain ⟨huniq, -, -⟩ := GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ (SW k r) ν0 isMatGroup_SW hH
  obtain ⟨c, hc0, hct, hνc⟩ := huniq ν hν.1
  have hlimc : Tendsto (fun ρ : ℝ => (ν (expBall (k := k) (r := r) (SW k r) ρ)).toReal / sVol k r (SW k r) ρ)
      (𝓝[>] 0) (𝓝 (c.toReal * 1)) := by
    refine (hr0.const_mul c.toReal).congr fun ρ => ?_
    simp only [hνc, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, mul_div_assoc]
  have hc1 : c.toReal * 1 = 1 := tendsto_nhds_unique hlimc hν.2
  have hc : c = 1 := by
    rw [mul_one] at hc1
    rw [← ENNReal.ofReal_toReal hct.ne, hc1, ENNReal.ofReal_one]
  rw [hνc, hc, one_smul, hu0]

end GlobalTheory.GaugeVolFixer
