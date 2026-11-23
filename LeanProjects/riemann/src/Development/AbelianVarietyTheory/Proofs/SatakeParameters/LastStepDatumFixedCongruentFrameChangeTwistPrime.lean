import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTwistPrimeInvariantCongruentFrames
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopStep GlobalTheory.TopLaw GlobalTheory.TopFrameQ

namespace GlobalTheory.TopFrameQM

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu))

theorem topDat_frames_qM {m2 : ℕ} (hm : R.m = m2 + 2) (hc : cst.Ok) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (hD : 2 * cst.M ≤ cst.D P)
    (κ : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1)))
    (κ' : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1)))
    (hκ : κ ∈ GLint X.E _ P.1)
    (hκc : ∀ w ∈ stdAt X.E _ P.1, ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E _ P.1)
    (hκ' : κ' ∈ GLint X.E _ P.1)
    (hκ'c : ∀ w ∈ stdAt X.E _ P.1, ((qOf P.1 : X.E) ^ (2 * cst.M))⁻¹ • (κ' w - w) ∈ stdAt X.E _ P.1)
    (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y'' : Sp X.E (R.N (m2 + 1)))
    (hy'' : ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y'' l)) :
    topDat Ch sel mu cst (m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
      topDat Ch sel mu cst (m2 + 1) P y y'' := by
  have hM1 : 1 ≤ cst.M := hc.M_pos
  have hMD : cst.M + 1 ≤ cst.D P := by omega
  have hMD' : cst.M + 1 ≤ 2 * cst.M := by omega
  have hq : (qOf P.1 : X.E) ≠ 0 := qOf_ne_zero
  have hκ's : κ'.symm ∈ GLint X.E _ P.1 := (GLint X.E _ P.1).inv_mem hκ'
  have hκs : κ.symm ∈ GLint X.E _ P.1 := (GLint X.E _ P.1).inv_mem hκ
  have hκ'sc := cong_symm hκ' hκ'c
  by_cases hg : ∀ j, abelian₂ P.1 (R.N (m2 + 1 + 1)) cst.M (y (Pi.single j 1))
  · unfold topDat
    congr 1
    · unfold PhiTopG
      rw [if_neg hP]
      have hc0 : cOf R (m2 + 1) = 0 := cOf_topB hm
      have hw : ∀ w ∈ stdAt X.E (R.N (m2 + 1)) P.1, ∀ l : Fin (R.N (m2 + 1 + 1)), l.1 + 1 < R.N (m2 + 1 + 1) →
          IntAt P.1 ((κ'.symm (y (κ w)) - y w) l / (qOf P.1 : X.E)) := by
        intro w hw l hl
        have hu := abelian₂.of_basis y hg (glint_mem (⟨κ, hκ⟩ : GLint X.E _ P.1) hw)
        have d1 := mem_stdAt.1 (abelian₂.move hκ's hκ'sc hMD' hu).2 l
        have e1 := intAt_inv_pow_le (a := 1) (by omega) d1
        have hu' : ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E _ P.1 := hκc w hw
        have hyu := (abelian₂.of_basis y hg hu').2 l hl
        rw [map_smul, map_sub, Pi.smul_apply, smul_eq_mul] at hyu
        have e2 := intAt_inv_pow_le (a := 1) (by omega) hyu
        rw [pow_one] at e1 e2
        have e3 := e1.add e2
        rw [← add_div] at e3
        convert e3 using 2
        simp only [Pi.sub_apply]
        ring
      have key := fun z hz => GlobalTheory.TopInv.PhiQ_add (K := X.K) (GlobalTheory.TopInv.qOf_mem P.1) hq
        (resChar (mu : Chr X.F X.E X.K) P.1) R.k R.r (cOf R (m2 + 1)) (R.N (m2 + 1)) (R.N (m2 + 1 + 1) - 1) hc0
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) z hz
      refine (congrArg _ (add_sub_cancel _ _)).symm.trans (key _ ?_)
      intro s l
      have hws : (LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) (Pi.single s (1 : X.E)) : Sp X.E _) ∈
          stdAt X.E (R.N (m2 + 1)) P.1 :=
        mem_stdAt.2 fun a => GlobalTheory.TopInv.single_int s (Fin.castAdd _ a)
      have := hw _ hws ⟨l.1, by omega⟩ (by show l.1 + 1 < _; omega)
      exact this
    · have h1 := ftY_comp_glint sel mu cst hc P (fun _ => hD) ⟨κ, hκ⟩
          (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.symm.toLinearMap ∘ₗ y) y'' (κ.symm y'')
          (fun h => absurd h hP) (fun _ => hy'') (fun h => absurd h hP)
          (fun _ => by
            show ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (κ (κ.symm y'') - y'') ∈ _
            rw [LinearEquiv.apply_symm_apply, sub_self, smul_zero]
            exact zero_mem _)
      refine h1.trans ?_
      have hy''s : ((qOf P.1 : X.E) ^ cst.M) • y'' ∈ stdAt X.E _ P.1 :=
        mem_stdAt.2 fun l => by simpa only [Pi.smul_apply, smul_eq_mul] using hy'' l
      have hδ : ∀ i, IntAt P.1 (((qOf P.1 : X.E) ^ cst.M)⁻¹ *
          ((atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.symm.toLinearMap ∘ₗ y) -
            atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) (Pi.single i 1)) := by
        intro i
        have d1 := mem_stdAt.1 (abelian₂.move hκ's hκ'sc (v := y (Pi.single i 1)) hMD' (hg i)).2
        have e1 : ∀ l, IntAt P.1 ((κ'.symm (y (Pi.single i 1)) - y (Pi.single i 1)) l / (qOf P.1 : X.E) ^ cst.M) :=
          fun l => intAt_inv_pow_le (by omega) (d1 l)
        have e2 := GlobalTheory.TopInv.atNL_int (R.N (m2 + 1 + 1) - 1) _ _ e1
        rw [inv_mul_eq_div]
        convert e2 using 2
        simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
        rfl
      have h2 := GlobalTheory.ftY_pert_qM sel mu cst hc P hP hD (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y)
        _ y'' hδ hy''s
      rw [add_sub_cancel] at h2
      exact h2
  · have h0 : topDat Ch sel mu cst (m2 + 1) P y y'' = 0 := by
      by_contra hne
      exact hg (lam_of_topDat_ne Ch sel mu cst _ P hP y y'' hne)
    rw [h0]
    by_contra hne
    apply hg
    have h1 := lam_of_topDat_ne Ch sel mu cst _ P hP _ _ hne
    have h2 := lam_comp hκs hκ' hκ'c hMD' _ h1
    intro j
    have := h2 j
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using this

end Main

example : (∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) {m2 : ℕ}, R.m = m2 + 2 → cst.Ok → ∀ (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
  2 * cst.M ≤ cst.D P →
  ∀ (κ : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1)))
    (κ' : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))),
  κ ∈ GLint X.E (R.N (m2 + 1)) P.1 →
  (∀ w ∈ stdAt X.E (R.N (m2 + 1)) P.1, ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E (R.N (m2 + 1)) P.1) →
  κ' ∈ GLint X.E (R.N (m2 + 1 + 1)) P.1 →
  (∀ w ∈ stdAt X.E (R.N (m2 + 1 + 1)) P.1, ((qOf P.1 : X.E) ^ (2 * cst.M))⁻¹ • (κ' w - w) ∈ stdAt X.E (R.N (m2 + 1 + 1)) P.1) →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y'' : Sp X.E (R.N (m2 + 1))),
  (∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y'' l)) →
  topDat Ch sel mu cst (m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
    topDat Ch sel mu cst (m2 + 1) P y y'') := by
  intro X Pr R Ch sel S mu cst m2 hm hc P hP hD κ κ' hκ hκc hκ' hκ'c y y'' hy''
  exact topDat_frames_qM Ch sel mu cst hm hc P hP hD κ κ' hκ hκc hκ' hκ'c y y'' hy''

end GlobalTheory.TopFrameQM
