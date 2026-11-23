import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelOneWordEstimate
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GramProductIdentities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RealWeightedForms
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SupremumAIsMajorant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InsertUnitMatrixZeroApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleAtOfAdmissibleList
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCutInside

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt NumberField Finset

noncomputable section

section node

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem ntop_eq_N' (S : C.HidaSetting E Wp Wq) : (S.Ntop : ℝ) = S.G.N := by
  unfold C.HidaSetting.Ntop Sz.Glob.N C.Kst
  push_cast
  ring

theorem cutI_eq (S : C.HidaSetting E Wp Wq) (v : Fin S.f) :
    (S.G.place (S.pl v)).cutI S.l = Set.Icc (S.cutLo v) (S.cutHi v) := by
  ext Y
  simp only [Sz.Cfg.cutI, Set.mem_ofPred_eq, Set.mem_Icc, C.HidaSetting.cutLo, C.HidaSetting.cutHi]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem qC_re (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (y : ℝ) :
    (M.qC (D.parOf S v) (y : ℂ)).re = (S.G.place (S.pl v)).q S.de S.de' S.T S.T' y := by
  rw [PBF.qC_ofReal, Complex.ofReal_re]
  rfl

variable {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem q_pos_cut (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (y : ℝ)
    (hy : y ∈ Set.Icc (S.cutLo v) (S.cutHi v)) : 0 < (M.qC (D.parOf S v) (y : ℂ)).re := by
  have hy' := PBCut.cutInside_of_built hB v y hy
  obtain ⟨-, -, -, -, -, -, -, hl1, hlk, -⟩ := hB
  rw [PBF.qC_ofReal, Complex.ofReal_re]
  exact PBF.qreal_pos (D.parOf S v) (p v).hP.1 (S.l + 1) (by omega) (by show S.l + 1 ≤ S.G.k; omega) y hy'

theorem core_bdd (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) :
    BddAbove ((fun Y => (S.G.place (S.pl v)).core S.de S.de' S.T S.T' Y) '' Set.Icc (S.cutLo v) (S.cutHi v)) := by
  apply IsCompact.bddAbove_image isCompact_Icc
  intro Y hY
  have hq : 0 < (S.G.place (S.pl v)).q S.de S.de' S.T S.T' Y := by
    rw [← qC_re]
    exact q_pos_cut hB v Y hY
  have hPc : Continuous fun Y => (S.G.place (S.pl v)).P Y := by
    unfold Sz.Cfg.P
    fun_prop
  have hqc : Continuous fun Y => (S.G.place (S.pl v)).q S.de S.de' S.T S.T' Y := by
    unfold Sz.Cfg.q
    fun_prop
  have hnum : Continuous fun Y => (S.G.place (S.pl v)).P Y * (S.G.place (S.pl v)).P (Y + 1) :=
    hPc.mul (hPc.comp (continuous_id.add continuous_const))
  have hf : ContinuousAt (fun Y => (S.G.place (S.pl v)).P Y * (S.G.place (S.pl v)).P (Y + 1) /
      (S.G.place (S.pl v)).q S.de S.de' S.T S.T' Y) Y :=
    hnum.continuousAt.div hqc.continuousAt hq.ne'
  exact (Real.continuous_sqrt.continuousAt.comp (continuous_abs.continuousAt.comp hf)).continuousWithinAt

theorem supA_nonneg (S : C.HidaSetting E Wp Wq) (hg : 0 < S.G.g) (hk : 0 < S.G.ka) (v : Fin S.f) (one : Bool) :
    0 ≤ J.supA S.G S.de S.de' S.T S.T' S.l one (S.pl v) := by
  have key : ∀ T0 : Set ℝ, 0 ≤ sSup ((fun Y => S.G.g ^ S.G.m *
      (S.G.place (S.pl v)).be S.G.ka S.de S.de' S.T S.T' Y) '' T0) := by
    intro T0
    apply Real.sSup_nonneg
    rintro _ ⟨Y, -, rfl⟩
    apply mul_nonneg (pow_nonneg hg.le _)
    unfold Sz.Cfg.be
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hk.le _)) (Real.sqrt_nonneg _)
  unfold J.supA
  apply div_nonneg
  · cases one
    · simp only [Bool.false_eq_true, ↓reduceIte, Sz.Glob.supI]
      exact key _
    · simp only [↓reduceIte, Sz.Glob.cutSupLong]
      exact key _
  · exact mul_nonneg (pow_nonneg hg.le _) (inv_nonneg.mpr (pow_nonneg hk.le _))

theorem core_le_supA (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (one : Bool) (y : ℝ)
    (hy : if one then y ∈ (S.G.place (S.pl v)).cutIntervalLong S.l S.G.N else y ∈ (S.G.place (S.pl v)).cutI S.l) :
    (S.G.place (S.pl v)).core S.de S.de' S.T S.T' y ≤ J.supA S.G S.de S.de' S.T S.T' S.l one (S.pl v) := by
  obtain ⟨hg1, hg2, -, -, -, -, -, -, -, -, hG, -⟩ := id hB
  have hg : 0 < S.G.g := by
    unfold Sz.Glob.g
    exact mul_pos (Nat.cast_pos.mpr hg1) (Nat.cast_pos.mpr hg2)
  have hv : 0 < S.G.v := by
    rw [S.hv]
    have := Jx5.rd_pos' (E := E)
    linarith
  have hk : 0 < S.G.ka := by
    unfold Sz.Glob.ka
    exact div_pos Real.pi_pos hv
  have hsub := Jx5.sup_core S.G S.de S.de' S.T S.T' (S.pl v) hg hk
  have hbdd : BddAbove ((fun Y => (S.G.place (S.pl v)).core S.de S.de' S.T S.T' Y) ''
      (S.G.place (S.pl v)).cutI S.l) := by
    rw [cutI_eq]
    exact core_bdd hB v
  unfold J.supA
  cases one
  · simp only [Bool.false_eq_true, ↓reduceIte] at hy ⊢
    unfold Sz.Glob.supI
    rw [hsub]
    exact le_csSup hbdd ⟨y, hy, rfl⟩
  · simp only [↓reduceIte] at hy ⊢
    unfold Sz.Glob.cutSupLong
    rw [hsub]
    refine le_csSup (hbdd.mono (Set.image_mono ?_)) ⟨y, hy, rfl⟩
    intro Y hY
    simp only [Sz.Cfg.cutIntervalLong, Sz.Cfg.cutI, Set.mem_ofPred_eq] at hY ⊢
    refine ⟨hY.1, le_trans hY.2 ?_⟩
    have h1 := (hG v).1
    simp only [C.HidaSetting.cutHi, C.HidaSetting.cutLo] at h1
    rw [← ntop_eq_N' S]
    have h0 : (0 : ℝ) ≤ S.Ntop := Nat.cast_nonneg _
    have h3 := pow_nonneg h0 3
    linarith

end node

section nodeb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem node_far (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (a : List C.Letter) (ha : D.AdmAt S v a)
    (y : ℝ) (one : Bool) (hy : (one = false ∧ ∃ a', a.length < a' ∧ a' ≤ S.Ntop ∧ y ∈ S.grid v a') ∨
      (one = true ∧ y ∈ S.grid1 v ∧ ∀ x ∈ a, PBD.Sep (true, y) x)) (z : C.Letter) (hz : z ∈ a) :
    (if one then (S.Ntop : ℝ) ^ 2 / 8 else (S.Ntop : ℝ) ^ 2 + 1) ≤ |y - PBD.nodeOf z| ∧
    (if one then (S.Ntop : ℝ) ^ 2 / 8 else (S.Ntop : ℝ) ^ 2 + 1) ≤ |y - (PBD.nodeOf z + 1)| := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hG, -⟩ := id hB
  obtain ⟨w, hw⟩ := ha
  have hA : PBD.AdmList S v a := hw ▸ PBD.admissible_list_of_word S w v
  have hz' := PBD.nodeOf_mem_grid_or_grid1 S v a hA z hz
  suffices key : ∀ e ∈ ({0, 1} : Finset ℝ),
      (if one then (S.Ntop : ℝ) ^ 2 / 8 else (S.Ntop : ℝ) ^ 2 + 1) ≤ |y - (PBD.nodeOf z + e)| by
    refine ⟨?_, key 1 (by simp)⟩
    simpa using key 0 (by simp)
  intro e he
  rcases hy with ⟨rfl, a', ha', -, hya'⟩ | ⟨rfl, hy1, hsep⟩
  · rw [if_neg (by decide)]
    rcases hz' with ⟨n, hn, hzn⟩ | hz1
    · have h := PBD.sep_grid S hG v hya' hzn (by omega) (e := 0) (by simp) he
      simpa using h
    · have h := (hG v).2.2.2.2.1 (PBD.nodeOf z) hz1 a' y hya' e he 0 (by simp)
      rw [abs_sub_comm] at h
      simpa using h
  · rw [if_pos rfl]
    rcases hz' with ⟨n, -, hzn⟩ | hz1
    · have h := (hG v).2.2.2.2.1 y hy1 n (PBD.nodeOf z) hzn 0 (by simp) e he
      have h8 : (S.Ntop : ℝ) ^ 2 / 8 ≤ (S.Ntop : ℝ) ^ 2 + 1 := by
        linarith [sq_nonneg (S.Ntop : ℝ)]
      simp only [add_zero] at h
      linarith
    · have hne : y ≠ PBD.nodeOf z := by
        intro hyz
        have hs : ∀ δ : ℤ, -2 ≤ δ → δ ≤ 2 → 2 < |y - z.2 + δ| := hsep z hz
        obtain ⟨b, t⟩ := z
        cases b
        · have h := hs 1 (by norm_num) (by norm_num)
          simp only [PBD.nodeOf, Bool.false_eq_true, ↓reduceIte] at hyz
          rw [hyz] at h
          norm_num at h
        · have h := hs 0 (by norm_num) (by norm_num)
          simp only [PBD.nodeOf, ↓reduceIte] at hyz
          rw [hyz] at h
          norm_num at h
      have h := (hG v).2.2.2.1 y hy1 (PBD.nodeOf z) hz1 hne 0 (by simp) e he
      simpa using h

theorem node_bound (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (a : List C.Letter) (ha : D.AdmAt S v a)
    (haN : a.length ≤ S.Ntop) (y : ℝ) (one : Bool)
    (hy : (one = false ∧ ∃ a', a.length < a' ∧ a' ≤ S.Ntop ∧ y ∈ S.grid v a') ∨
      (one = true ∧ y ∈ S.grid1 v ∧ ∀ x ∈ a, PBD.Sep (true, y) x)) :
    0 < (Wd.qw (M.qC (D.parOf S v)) (D.positionted a) (y : ℂ)).re ∧
      |S.P v y * S.P v (y + 1)| / (Wd.qw (M.qC (D.parOf S v)) (D.positionted a) (y : ℂ)).re ≤
        (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l one (S.pl v)) ^ 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hG, -⟩ := id hB
  have hcut : y ∈ (S.G.place (S.pl v)).cutI S.l := by
    refine ((hG v).2.2.2.2.2 y ?_).1
    rcases hy with ⟨-, a', -, -, h⟩ | ⟨-, h, -⟩
    · exact Or.inl ⟨a', h⟩
    · exact Or.inr h
  have hyc : y ∈ Set.Icc (S.cutLo v) (S.cutHi v) := by
    rw [← cutI_eq]
    exact hcut
  have hqpos := q_pos_cut hB v y hyc
  have hreal : ∀ l ∈ D.positionted a, l.pt.im = 0 := by
    intro l hl
    simp only [D.positionted, List.mem_ofFn] at hl
    obtain ⟨i, rfl⟩ := hl
    simp
  have hqim : (M.qC (D.parOf S v) (y : ℂ)).im = 0 := by
    rw [PBF.qC_ofReal, Complex.ofReal_im]
  have hconv := RealWeightedForms.qwOfReal (Fin a.length) (M.qC (D.parOf S v)) (D.positionted a) y hqim hreal
  have h8 : 8 ≤ S.Ntop := by
    unfold C.HidaSetting.Ntop C.Kst
    omega
  have hlen : ((D.positionted a).map fun l => (⟨l.plus, l.intersection_update_fsHerm_neg_one, l.pt.re⟩ : Wd.Letter ℝ (Fin a.length))).length
      ≤ S.Ntop := by
    simpa [D.positionted] using haN
  have hdl : (S.Ntop : ℝ) ^ 2 / 8 ≤ (if one then (S.Ntop : ℝ) ^ 2 / 8 else (S.Ntop : ℝ) ^ 2 + 1) := by
    split_ifs <;> linarith [sq_nonneg (S.Ntop : ℝ)]
  have hlet : ∀ l ∈ (D.positionted a).map fun l => (⟨l.plus, l.intersection_update_fsHerm_neg_one, l.pt.re⟩ : Wd.Letter ℝ (Fin a.length)),
      if l.plus then (if one then (S.Ntop : ℝ) ^ 2 / 8 else (S.Ntop : ℝ) ^ 2 + 1) ≤ |y - l.pt| else
        (if one then (S.Ntop : ℝ) ^ 2 / 8 else (S.Ntop : ℝ) ^ 2 + 1) ≤ |y - l.pt| ∧
          (if one then (S.Ntop : ℝ) ^ 2 / 8 else (S.Ntop : ℝ) ^ 2 + 1) ≤ |y - (l.pt - 1)| := by
    intro l hl
    simp only [List.mem_map, D.positionted, List.mem_ofFn] at hl
    obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hl
    have hz : a.get i ∈ a := List.get_mem a i
    have hf := node_far hB v a ha y one hy (a.get i) hz
    simp only [Complex.ofReal_re]
    generalize a.get i = z at hf
    obtain ⟨b, t⟩ := z
    cases b
    · simp only [PBD.nodeOf, Bool.false_eq_true, ↓reduceIte, sub_add_cancel] at hf ⊢
      exact ⟨hf.2, hf.1⟩
    · simp only [PBD.nodeOf, ↓reduceIte] at hf ⊢
      exact hf.1
  have hq8 := PBD.level_one_word_estimate (Fin a.length) (fun t : ℝ => (M.qC (D.parOf S v) (t : ℂ)).re)
    ((D.positionted a).map fun l => (⟨l.plus, l.intersection_update_fsHerm_neg_one, l.pt.re⟩ : Wd.Letter ℝ (Fin a.length))) S.Ntop
    (if one then (S.Ntop : ℝ) ^ 2 / 8 else (S.Ntop : ℝ) ^ 2 + 1) y h8 hlen hdl hlet hqpos.ne'
  obtain ⟨hlo, -⟩ := hq8
  rw [hconv, Complex.ofReal_re]
  generalize Wd.qw (fun t : ℝ => (M.qC (D.parOf S v) (t : ℂ)).re)
    ((D.positionted a).map fun l => (⟨l.plus, l.intersection_update_fsHerm_neg_one, l.pt.re⟩ : Wd.Letter ℝ (Fin a.length))) y = Q at hlo ⊢
  have hlo' : Real.exp (-2) * (M.qC (D.parOf S v) (y : ℂ)).re ≤ Q := by
    have := (le_div_iff₀ hqpos).mp hlo
    linarith
  have hpos : 0 < Real.exp (-2) * (M.qC (D.parOf S v) (y : ℂ)).re := mul_pos (Real.exp_pos _) hqpos
  refine ⟨lt_of_lt_of_le hpos hlo', ?_⟩
  have hmem1 : if one then y ∈ (S.G.place (S.pl v)).cutIntervalLong S.l S.G.N else y ∈ (S.G.place (S.pl v)).cutI S.l := by
    rcases hy with ⟨rfl, -⟩ | ⟨rfl, h1, -⟩
    · rw [if_neg (by decide)]
      exact hcut
    · rw [if_pos rfl, ← ntop_eq_N' S]
      exact ((hG v).2.2.1 y h1).1
  have hcore := core_le_supA hB v one y hmem1
  have hc0 : 0 ≤ (S.G.place (S.pl v)).core S.de S.de' S.T S.T' y := Real.sqrt_nonneg _
  have hqR := qC_re S v y
  have hcsq : ((S.G.place (S.pl v)).core S.de S.de' S.T S.T' y) ^ 2 =
      |S.P v y * S.P v (y + 1)| / (M.qC (D.parOf S v) (y : ℂ)).re := by
    unfold Sz.Cfg.core
    rw [Real.sq_sqrt (abs_nonneg _), abs_div, hqR, abs_of_pos (a := (S.G.place (S.pl v)).q S.de S.de' S.T S.T' y) (by rw [← hqR]; exact hqpos)]
    rfl
  have hne : (M.qC (D.parOf S v) (y : ℂ)).re ≠ 0 := hqpos.ne'
  calc |S.P v y * S.P v (y + 1)| / Q
      ≤ |S.P v y * S.P v (y + 1)| / (Real.exp (-2) * (M.qC (D.parOf S v) (y : ℂ)).re) :=
        div_le_div_of_nonneg_left (abs_nonneg _) hpos hlo'
    _ = Real.exp 2 * (|S.P v y * S.P v (y + 1)| / (M.qC (D.parOf S v) (y : ℂ)).re) := by
        rw [Real.exp_neg]
        field_simp
    _ = Real.exp 2 * ((S.G.place (S.pl v)).core S.de S.de' S.T S.T' y) ^ 2 := by rw [hcsq]
    _ ≤ Real.exp 2 * (J.supA S.G S.de S.de' S.T S.T' S.l one (S.pl v)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc0 hcore 2) (Real.exp_pos 2).le
    _ = (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l one (S.pl v)) ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul]
        norm_num

end nodeb

end

end Formalism.FourierDecayAlt.P.PBL
