import Mathlib
import Formalism.PeriodIntegrals.PairValDefs
import Formalism.PeriodIntegrals.NormRepChange
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.NlamFrameMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXOfMemXS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXOfMemSpanO

noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.PairValDefs IsDedekindDomain

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem sgUp_eq_sum {K : Type} [Field K] [NumberField K] (U : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    sgUp U = ∑ a : Fin r, U a.castSucc a.succ := by
  unfold sgUp
  rw [Fin.sum_univ_castSucc, dif_neg (by simp), add_zero]
  apply Finset.sum_congr rfl
  intro a _
  rw [dif_pos (by simp)]
  rfl

theorem frame_d_mem {Λ : Submodule (𝓞 E) S.V} (G : LFlag S r T) {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ G)
    (b : Fin (r + 1)) : n (frame G b) - frame G b ∈ G.fl.X := by
  obtain ⟨he, hz⟩ := nlam_frame_mem G hn
  induction b using Fin.lastCases with
  | last => rw [frame_last]; exact hz
  | cast i => rw [frame_castSucc]; exact Xa_le_X _ _ (he i)

theorem coefX_finset_sum (F : FlagG S r T) {ι : Type*} (s : Finset ι) (v : ι → S.V) (hv : ∀ i, v i ∈ F.X)
    (a : Fin r) : F.coefX (∑ i ∈ s, v i) a = ∑ i ∈ s, F.coefX (v i) a := by
  induction s using Finset.induction_on with
  | empty => simp [coefX_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, coefX_add _ (hv i) (Submodule.sum_mem _ fun j _ => hv j), ih]

theorem frameAct_one (f : Fin (r + 1) → S.V) (b : Fin (r + 1)) :
    frameAct f (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) b = f b := by
  unfold frameAct
  simp [Matrix.one_apply]

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fmat_sup (D : D7) {T : D.host.E} (G : LFlag (VS D) D.R.rS T) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (a : Fin D.R.rS) :
    fmat D G n a.castSucc a.succ = G.fl.coefX (n (frame G a.succ) - frame G a.succ) a := by
  unfold fmat
  rw [if_neg (fun h => by have := congrArg Fin.val h; simp at this), zero_add, dif_pos (by simp)]
  rfl

theorem loc_entry (D : D7) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (G : LFlag (VS D) D.R.rS T)
    (G₁ G₂ : LFlag (VS D) D.R.rS T') (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NLam Λ G)
    (hm : m ∈ NLam Λ G₁) (hfr : ∀ a, frame G₂ a = n (m (frame G₁ a))) (hC : IsFixedConv Λ (gS D) G)
    (hC₁ : IsFixedConv Λ (gS D) G₁) (hA1 : AdmWit Λ (gS D) G G₁ 1) (hA2 : AdmWit Λ (gS D) G G₂ 1)
    (hz₁ : G₁.fl.z ∈ Λ) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)
    (hg : ((gS D : ℕ) : D.host.E) ≠ 0) (a : Fin D.R.rS) :
    IntP P ((fmat D G n a.castSucc a.succ + fmat D G₁ m a.castSucc a.succ) / (gS D : D.host.E)) := by
  set b := a.succ with hb
  have hw : ∀ c, frame G₁ c - frame G c ∈ LP P (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
    intro c
    have := hA1.2.2 c P hP
    rw [frameAct_one] at this
    exact this
  have hw2 : ∀ c, frame G₂ c - frame G c ∈ LP P (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
    intro c
    have := hA2.2.2 c P hP
    rw [frameAct_one] at this
    exact this
  have hwe : ∀ c : Fin D.R.rS, G₁.fl.e c - G.fl.e c ∈ LP P (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
    intro c
    have := hw c.castSucc
    rw [frame_castSucc, frame_castSucc] at this
    exact this
  have hf1LP : ∀ c, frame G₁ c ∈ LP P Λ := by
    intro c
    induction c using Fin.lastCases with
    | last => rw [frame_last]; exact mem_localization_of_mem₃ P hz₁
    | cast i => rw [frame_castSucc]; exact e_mem_LP P hC₁ hP i
  have hd'X := frame_d_mem G₁ hm b
  have hmLP : m (frame G₁ b) - frame G₁ b ∈ LP P Λ :=
    sub_mem_localization P (LP_map P (m : (VS D).V →ₗ[D.host.E] (VS D).V) (fun v hv => nlam_mem hm hv) (hf1LP b)) (hf1LP b)
  have hM'int : ∀ c, IntP P (G₁.fl.coefX (m (frame G₁ b) - frame G₁ b) c) :=
    fun c => coef_intP P hC₁ hP hmLP hd'X c
  have hd'sum : m (frame G₁ b) = frame G₁ b + ∑ c, G₁.fl.coefX (m (frame G₁ b) - frame G₁ b) c • G₁.fl.e c := by
    rw [coefX_sum _ hd'X]; abel
  have hM'zero : ∀ c : Fin D.R.rS, a.val < c.val → G₁.fl.coefX (m (frame G₁ b) - frame G₁ b) c = 0 := by
    intro c hac
    have hr : a.val + 1 < D.R.rS := by have := c.isLt; omega
    have hbi : b = (⟨a.val + 1, hr⟩ : Fin D.R.rS).castSucc := Fin.ext rfl
    rw [hbi, frame_castSucc]
    exact coefX_eq_zero _ ((nlam_frame_mem G₁ hm).1 _) c (by simp; omega)
  set M' := fun c => G₁.fl.coefX (m (frame G₁ b) - frame G₁ b) c with hM'
  set Y := (n (frame G b) - frame G b) + ∑ c, M' c • G.fl.e c + ∑ c, M' c • (n (G.fl.e c) - G.fl.e c) with hY
  have hYeq : Y = (frame G₂ b - frame G b) - (frame G₁ b - frame G b) + (frame G₁ b - frame G b) -
      n (frame G₁ b - frame G b) - n (∑ c, M' c • (G₁.fl.e c - G.fl.e c)) := by
    rw [hY, hfr b, hd'sum]
    simp only [map_add, map_sub, map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
    abel
  have hYLg : Y ∈ LP P (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
    rw [hYeq]
    refine sub_mem (sub_mem (add_mem (sub_mem (hw2 b) (hw b)) (hw b)) ?_) ?_
    · exact LP_map P (n : (VS D).V →ₗ[D.host.E] (VS D).V) (nlam_gLam hn _) (hw b)
    · exact LP_map P (n : (VS D).V →ₗ[D.host.E] (VS D).V) (nlam_gLam hn _)
        (LP_sum P _ _ fun c _ => smul_mem_localization P (hM'int c) (hwe c))
  have hdX : ∀ c : Fin D.R.rS, n (G.fl.e c) - G.fl.e c ∈ G.fl.X := fun c => Xa_le_X _ _ ((nlam_frame_mem G hn).1 c)
  have hYX : Y ∈ G.fl.X := by
    refine add_mem (add_mem (frame_d_mem G hn b) (Submodule.sum_mem _ fun c _ => ?_))
      (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hdX c))
    exact Submodule.smul_mem _ _ (e_mem_X _ c)
  have hcoef := coef_intP_g P hC hP hg hYLg hYX a
  have hYa : G.fl.coefX Y a = fmat D G n a.castSucc a.succ + fmat D G₁ m a.castSucc a.succ := by
    rw [fmat_sup, fmat_sup, hY]
    rw [coefX_add _ (add_mem (frame_d_mem G hn b) (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (e_mem_X _ c)))
      (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hdX c)),
      coefX_add _ (frame_d_mem G hn b) (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (e_mem_X _ c)),
      coefX_finset_sum _ _ _ (fun c => Submodule.smul_mem _ _ (e_mem_X _ c)),
      coefX_finset_sum _ _ _ (fun c => Submodule.smul_mem _ _ (hdX c))]
    have h3 : ∑ c, G.fl.coefX (M' c • (n (G.fl.e c) - G.fl.e c)) a = 0 := by
      apply Finset.sum_eq_zero
      intro c _
      rw [coefX_smul _ (hdX c)]
      by_cases hac : a.val < c.val
      · rw [show M' c = 0 from hM'zero c hac, zero_mul]
      · rw [coefX_eq_zero _ ((nlam_frame_mem G hn).1 c) a (by omega), mul_zero]
    rw [h3, add_zero]
    simp only [coefX_smul_e, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  rw [← hYa]
  exact hcoef

theorem stepLoc (D : D7) : StepLoc D := by
  intro Λ T T' G G₁ G₂ n m hn hm hfr hC hC₁ hA1 hA2 _ hz₁ P hP
  have hg : ((gS D : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (by
    unfold gS; exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  rw [sgUp_eq_sum (fmat D G n), sgUp_eq_sum (fmat D G₁ m), ← Finset.sum_add_distrib, Finset.sum_div]
  exact valuation_le_one_of_isIntegralAt P (intP_sum P _ _ fun a _ =>
    loc_entry D Λ G G₁ G₂ n m hn hm hfr hC hC₁ hA1 hA2 hz₁ P hP hg a)

end PI.NRCW
