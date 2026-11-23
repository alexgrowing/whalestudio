import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXECPfA

noncomputable section

open MeasureTheory Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.EC

open Formalism.QuantumDeterminants WlocSk.NB
open Formalism.MainNotions.BridgeCSB (Fil lieN dg)

variable {k r : ℕ}

theorem mp_toC : MeasurePreserving (toC (k := k) (r := r)) volume volume := by
  have h1 := volume_measurePreserving_sumPiEquivProdPi (fun _ : J k r => ℝ)
  have h2 := volume_measurePreserving_sumPiEquivProdPi (fun _ : CI k r ⊕ CI k r => ℝ)
  have h3 := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (CI k r)).symm
  have h4 : MeasurePreserving (fun (w : CI k r → ℝ × ℝ) (i : CI k r) =>
      Complex.measurableEquivRealProd.symm (w i)) volume volume :=
    volume_preserving_pi (fun _ => Complex.volume_preserving_equiv_real_prod.symm)
  have h5 := ((h4.comp h3).comp h2).prod (MeasurePreserving.id (volume : Measure (Fin r → ℝ)))
  have h6 := h5.comp h1
  convert h6 using 1
  all_goals first | rfl | (funext y; rfl)

def fromC (t : (CI k r → ℂ) × (Fin r → ℝ)) : J k r → ℝ
  | Sum.inl (Sum.inl c) => (t.1 c).re
  | Sum.inl (Sum.inr c) => (t.1 c).im
  | Sum.inr a => t.2 a

theorem toC_fromC (t : (CI k r → ℂ) × (Fin r → ℝ)) : toC (fromC t) = t := by
  rfl

theorem continuous_fromC : Continuous (fromC (k := k) (r := r)) := by
  refine continuous_pi fun j => ?_
  rcases j with (c | c) | a
  · exact Complex.continuous_re.comp ((continuous_apply c).comp continuous_fst)
  · exact Complex.continuous_im.comp ((continuous_apply c).comp continuous_fst)
  · exact (continuous_apply a).comp continuous_snd

section Cont

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem continuous_expLJ : Continuous fun y : J k r → ℝ => (NormedSpace.exp (LJ y) : Mx k r) :=
  NormedSpace.exp_continuous.comp continuous_LJ

end Cont

def sJ (y : J k r → ℝ) : J k r → ℝ := fromC (psiC (NormedSpace.exp (LJ y)), psiR (NormedSpace.exp (LJ y)))

theorem continuous_sJ : Continuous (sJ (k := k) (r := r)) :=
  continuous_fromC.comp ((continuous_psiC.comp continuous_expLJ).prodMk (continuous_psiR.comp continuous_expLJ))

theorem entry_of_fil {D E : Mx k r} {p : ℕ} (h : Fil (p + 1) (D - E)) {i j : Fin (2 * r + k + 1)}
    (hij : dg k r j ≤ dg k r i + p) : D i j = E i j := by
  have h1 := h i j (by omega)
  rw [Matrix.sub_apply, sub_eq_zero] at h1
  exact h1

theorem mof_sub {g g' : Mx k r} (hg : g ∈ Nset k r) (hg' : g' ∈ Nset k r) (a b : Fin r)
    (hG : Fil (2 * r - a.val - b.val) (g - g')) :
    mof g a b - mof g' a b = g (eI k r a) (esI k r b) - g' (eI k r a) (esI k r b) := by
  have h1 := ((Formalism.MainNotions.BridgeCSB.mem_N_iff g).1 hg).2
  have h1' := ((Formalism.MainNotions.BridgeCSB.mem_N_iff g').1 hg').2
  have key : ∀ c : Fin r, star (g (esI k r c) (esI k r a)) * g (eI k r c) (esI k r b) -
      star (g' (esI k r c) (esI k r a)) * g' (eI k r c) (esI k r b) =
      if c = a then g (eI k r a) (esI k r b) - g' (eI k r a) (esI k r b) else 0 := by
    intro c
    have ha := a.isLt; have hb := b.isLt; have hc := c.isLt
    rcases lt_trichotomy c a with h | rfl | h
    · have hca : c.val < a.val := h
      have e1 := h1 (esI k r c) (esI k r a) (by rw [dg_esI, dg_esI]; omega)
      have e2 := h1' (esI k r c) (esI k r a) (by rw [dg_esI, dg_esI]; omega)
      rw [Matrix.sub_apply, Matrix.one_apply, if_neg (fun e => (ne_of_lt h) (esI_inj.1 e)), sub_zero] at e1 e2
      rw [e1, e2, if_neg (ne_of_lt h)]; simp
    · have e1 := h1 (esI k r c) (esI k r c) (by rw [dg_esI]; omega)
      have e2 := h1' (esI k r c) (esI k r c) (by rw [dg_esI]; omega)
      rw [Matrix.sub_apply, Matrix.one_apply, if_pos rfl, sub_eq_zero] at e1 e2
      rw [e1, e2, if_pos rfl]; simp
    · have hac : a.val < c.val := h
      have e1 := hG (esI k r c) (esI k r a) (by rw [dg_esI, dg_esI]; omega)
      have e2 := hG (eI k r c) (esI k r b) (by rw [dg_esI, dg_eI]; omega)
      rw [Matrix.sub_apply, sub_eq_zero] at e1 e2
      rw [e1, e2, if_neg (ne_of_gt h), sub_self]
  simp only [mof, Matrix.mul_apply, conjTranspose_apply, bF, bC]
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun c _ => key c)]
  simp

theorem psiC_sub (t t' : (CI k r → ℂ) × (Fin r → ℝ)) (c : CI k r)
    (hG : Fil (hC c) (NormedSpace.exp (Lm t) - NormedSpace.exp (Lm t')))
    (hE : Fil (hC c + 1) ((NormedSpace.exp (Lm t) - NormedSpace.exp (Lm t')) - (Lm t - Lm t'))) :
    psiC (NormedSpace.exp (Lm t)) c - psiC (NormedSpace.exp (Lm t')) c = t.1 c - t'.1 c := by
  have hg := Formalism.MainNotions.BridgeCSB.exp_mem_N (Lm_mem t)
  have hg' := Formalism.MainNotions.BridgeCSB.exp_mem_N (Lm_mem t')
  have ent : ∀ i j, dg k r j ≤ dg k r i + hC c →
      (NormedSpace.exp (Lm t) - NormedSpace.exp (Lm t')) i j = (Lm t - Lm t') i j :=
    fun i j h => entry_of_fil hE h
  rcases c with ⟨⟨a, b⟩, h⟩ | ⟨a, j⟩ | ⟨⟨a, b⟩, h⟩
  · have hab : a.val < b.val := h
    have := ent (eI k r a) (eI k r b) (by rw [dg_eI, dg_eI]; simp only [hC]; omega)
    simp only [Matrix.sub_apply, Lm_ee, chart_matrix_upper _ h] at this
    exact this
  · have := ent (eI k r a) (wI k r j) (by rw [dg_eI, dg_wI]; simp only [hC]; omega)
    simp only [Matrix.sub_apply, Lm_ew] at this
    exact this
  · have hab' : a.val < b.val := h
    have hb := b.isLt
    have eh : hC (Sum.inr (Sum.inr ⟨(a, b), h⟩) : CI k r) = 2 * r - a.val - b.val := rfl
    have hab := mof_sub hg hg' a b (by rw [← eh]; exact hG)
    have hba := mof_sub hg hg' b a (by
      have : 2 * r - b.val - a.val = 2 * r - a.val - b.val := by omega
      rw [this, ← eh]; exact hG)
    have e1 := ent (eI k r a) (esI k r b) (by rw [dg_eI, dg_esI, eh]; omega)
    have e2 := ent (eI k r b) (esI k r a) (by rw [dg_eI, dg_esI, eh]; omega)
    simp only [Matrix.sub_apply, Lm_es] at e1 e2
    have hba' := congrArg star hba
    have e2' := congrArg star e2
    simp only [star_sub] at hba' e2'
    have sk := cK_skew t.1 t.2 a b
    have sk' := cK_skew t'.1 t'.2 a b
    have hx : ∀ x : CI k r → ℂ, ∀ s, cK x s a b = x (Sum.inr (Sum.inr ⟨(a, b), h⟩)) := by
      intro x s; unfold cK; rw [dif_pos h]
    show kof _ a b - kof _ a b = _
    rw [← hx t.1 t.2, ← hx t'.1 t'.2]
    simp only [kof]
    linear_combination (1 / 2 : ℂ) * hab + (1 / 2 : ℂ) * e1 - (1 / 2 : ℂ) * hba' - (1 / 2 : ℂ) * e2' -
      (1 / 2 : ℂ) * sk + (1 / 2 : ℂ) * sk'

theorem psiR_sub (t t' : (CI k r → ℂ) × (Fin r → ℝ)) (a : Fin r)
    (hG : Fil (2 * r - 2 * a.val) (NormedSpace.exp (Lm t) - NormedSpace.exp (Lm t')))
    (hE : Fil (2 * r - 2 * a.val + 1) ((NormedSpace.exp (Lm t) - NormedSpace.exp (Lm t')) - (Lm t - Lm t'))) :
    psiR (NormedSpace.exp (Lm t)) a - psiR (NormedSpace.exp (Lm t')) a = t.2 a - t'.2 a := by
  have hg := Formalism.MainNotions.BridgeCSB.exp_mem_N (Lm_mem t)
  have hg' := Formalism.MainNotions.BridgeCSB.exp_mem_N (Lm_mem t')
  have ha := a.isLt
  have hm := mof_sub hg hg' a a (by
    have : 2 * r - a.val - a.val = 2 * r - 2 * a.val := by omega
    rw [this]; exact hG)
  have e1 := entry_of_fil hE (i := eI k r a) (j := esI k r a) (by rw [dg_eI, dg_esI]; omega)
  simp only [Matrix.sub_apply, Lm_es] at e1
  have hk : ∀ (x : CI k r → ℂ) (s : Fin r → ℝ), cK x s a a = (s a : ℂ) * Complex.I := by
    intro x s; unfold cK; rw [dif_neg (lt_irrefl a), dif_neg (lt_irrefl a)]
  rw [hk, hk] at e1
  have := congrArg Complex.im (hm.trans e1)
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, add_zero] at this
  simp only [psiR]
  linarith

theorem sJ_shear (i : J k r) (y y' : J k r → ℝ) (h : ∀ j, ht j < ht i → y j = y' j) :
    sJ y i - y i = sJ y' i - y' i := by
  have hF := Lm_fil_sub h
  have hE := Formalism.MainNotions.BridgeCSB.Fil.exp_sub_exp (chart_filtration_one (toC y)) (chart_filtration_one (toC y')) hF
  have hG : Fil (ht i) (NormedSpace.exp (Lm (toC y)) - NormedSpace.exp (Lm (toC y'))) := by
    have := (hE.mono (Nat.le_succ _)).add hF
    rwa [sub_add_cancel] at this
  rcases i with (c | c) | a
  · have := congrArg Complex.re (psiC_sub (toC y) (toC y') c hG hE)
    simp only [Complex.sub_re] at this
    show (psiC (NormedSpace.exp (Lm (toC y))) c).re - ((toC y).1 c).re =
      (psiC (NormedSpace.exp (Lm (toC y'))) c).re - ((toC y').1 c).re
    linarith
  · have := congrArg Complex.im (psiC_sub (toC y) (toC y') c hG hE)
    simp only [Complex.sub_im] at this
    show (psiC (NormedSpace.exp (Lm (toC y))) c).im - ((toC y).1 c).im =
      (psiC (NormedSpace.exp (Lm (toC y'))) c).im - ((toC y').1 c).im
    linarith
  · have := psiR_sub (toC y) (toC y') a hG hE
    show psiR (NormedSpace.exp (Lm (toC y))) a - (toC y).2 a =
      psiR (NormedSpace.exp (Lm (toC y'))) a - (toC y').2 a
    linarith

theorem shear_change_holds : ShearStep := by
  intro k r
  refine ⟨fun y => (psiC (NormedSpace.exp (LJ y)), psiR (NormedSpace.exp (LJ y))), ?_, ?_⟩
  · have hS := Formalism.MainNotions.BridgeCSB.shearMP (J k r) ht sJ continuous_sJ.measurable
      (fun i y y' h => sJ_shear i y y' h)
    have := mp_toC.comp hS
    convert this using 1
    funext y
    simp only [Function.comp, sJ, toC_fromC]
  · intro y
    exact nilpotent_chart_left_inverse (Formalism.MainNotions.BridgeCSB.exp_mem_N (Lm_mem (toC y)))

end Formalism.L2.SG.Pf.NcReal.JX.EC
