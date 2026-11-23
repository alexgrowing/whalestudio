import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFIdPol
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFpmDecay
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimBdPf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnergyReal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplySub

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate

noncomputable section

section lin

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem cv_smul' {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (Y α : ℂ) (f : B.Mat k r → E) :
    Q.CV k r Y (α • f) = α • Q.CV k r Y f :=
  Formalism.FourierDecayAlt.P5.qminorOp_smulC (Formalism.FourierDecayAlt.P5.eH_smulC (k := k) (r := r)) _ _ _ α f

theorem cv_add_GV (D : B.RealPlaceData k r Wp Wq) (Y : ℂ) {H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h₁ : B.CkOn ⊤ (B.GV k r) H₁) (h₂ : B.CkOn ⊤ (B.GV k r) H₂) :
    ∀ g ∈ B.GV k r, Q.CV k r Y (fun x => H₁ x + H₂ x) g = Q.CV k r Y H₁ g + Q.CV k r Y H₂ g := by
  intro g hg
  obtain ⟨-, -, -, -, hApp⟩ := CutMP.ER.capacity_theta_facts k r Wp Wq D 1 Y 1 0
  have hn : ∀ {H : B.Mat k r → (Wq →L[ℂ] Wp)}, B.CkOn ⊤ (B.GV k r) H →
      B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (B.GV k r) H := fun h => Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top h
  have h₂' : B.CkOn ⊤ (B.GV k r) ((-1 : ℂ) • H₂) := JCx2.ckOn_smul' (-1 : ℂ) h₂
  have e : (fun x => H₁ x + H₂ x) = fun x => H₁ x - ((-1 : ℂ) • H₂) x := by
    funext x; simp
  have hs : B.CkOn ⊤ (B.GV k r) (fun x => H₁ x - ((-1 : ℂ) • H₂) x) := by
    rw [← e]; exact JCx2.ckOn_add' h₁ h₂
  have a1 := hApp _ (hn hs) g hg
  have a2 := hApp _ (hn h₁) g hg
  have a3 := hApp _ (hn h₂') g hg
  have hsub := PBE.opApply_sub (CutMP.ER.capTh k r Wp Wq 1 Y) h₁ h₂' g hg
  rw [one_smul] at a1 a2 a3
  rw [e, ← a1, hsub, a2, a3, cv_smul']
  simp [sub_eq_add_neg]

theorem cv_lin_GV (D : B.RealPlaceData k r Wp Wq) (Y a b : ℂ) {H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h₁ : B.CkOn ⊤ (B.GV k r) H₁) (h₂ : B.CkOn ⊤ (B.GV k r) H₂) :
    ∀ g ∈ B.GV k r, Q.CV k r Y (fun x => a • H₁ x + b • H₂ x) g = a • Q.CV k r Y H₁ g + b • Q.CV k r Y H₂ g := by
  intro g hg
  have h := cv_add_GV D Y (JCx2.ckOn_smul' a h₁) (JCx2.ckOn_smul' b h₂) g hg
  have e : (fun x => a • H₁ x + b • H₂ x) = fun x => (a • H₁) x + (b • H₂) x := rfl
  rw [e, h, cv_smul', cv_smul']
  rfl

theorem fold_lin (D : B.RealPlaceData k r Wp Wq) (s a b : ℂ) : ∀ (w : List (Bool × ℝ))
    (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) H₁ → B.CkOn ⊤ (B.GV k r) H₂ →
    ∀ g ∈ B.GV k r, w.foldr (CutMP.ER.opL k r s) (fun x => a • H₁ x + b • H₂ x) g =
      a • w.foldr (CutMP.ER.opL k r s) H₁ g + b • w.foldr (CutMP.ER.opL k r s) H₂ g
  | [], _, _, _, _ => fun _ _ => rfl
  | x :: w, H₁, H₂, h₁, h₂ => by
    intro g hg
    have ih := fold_lin D s a b w H₁ H₂ h₁ h₂
    have s1 := CutMP.ER.fold_smooth CutMP.ER.coefficient_vector_smoothness s w H₁ h₁
    have s2 := CutMP.ER.fold_smooth CutMP.ER.coefficient_vector_smoothness s w H₂ h₂
    have h12 : B.CkOn ⊤ (B.GV k r) (fun x => a • H₁ x + b • H₂ x) :=
      JCx2.ckOn_add' (JCx2.ckOn_smul' a h₁) (JCx2.ckOn_smul' b h₂)
    have s12 := CutMP.ER.fold_smooth CutMP.ER.coefficient_vector_smoothness s w _ h12
    have sK : B.CkOn ⊤ (B.GV k r) (fun y => a • w.foldr (CutMP.ER.opL k r s) H₁ y +
        b • w.foldr (CutMP.ER.opL k r s) H₂ y) :=
      JCx2.ckOn_add' (JCx2.ckOn_smul' a s1) (JCx2.ckOn_smul' b s2)
    simp only [List.foldr_cons, CutMP.ER.opL]
    rw [CutMP.ER.coefficient_vector_congr k r Wp Wq s (x.2 : ℂ) _ _ s12 sK ih g hg]
    simp only [Pi.smul_apply]
    rw [cv_lin_GV D _ a b s1 s2 g hg, smul_add, smul_comm s a, smul_comm s b]

theorem beta_form_linear_left (D : B.RealPlaceData k r Wp Wq) {A : ℝ} (hA : B.AB k r ≤ A) (a b : ℂ)
    {X Y Z : B.Mat k r → (Wq →L[ℂ] Wp)} (hX : B.InCC A 5 X) (hY : B.InCC A 5 Y) (hZ : B.InCC A 5 Z) :
    B.beta D (fun g => a • X g + b • Y g) Z = a * B.beta D X Z + b * B.beta D Y Z := by
  have h := beta_sum_left D hA ![a, b] ![X, Y] (fun i => by fin_cases i <;> assumption) hZ Finset.univ
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact h

theorem beta_form_conj_linear_right (D : B.RealPlaceData k r Wp Wq) {A : ℝ} (hA : B.AB k r ≤ A) (a b : ℂ)
    {X Y Z : B.Mat k r → (Wq →L[ℂ] Wp)} (hX : B.InCC A 5 X) (hY : B.InCC A 5 Y) (hZ : B.InCC A 5 Z) :
    B.beta D Z (fun g => a • X g + b • Y g) = conj a * B.beta D Z X + conj b * B.beta D Z Y := by
  rw [CutMP.ER.beta_conj D Z, beta_form_linear_left D hA a b hX hY hZ, map_add, map_mul, map_mul,
    ← CutMP.ER.beta_conj D Z X, ← CutMP.ER.beta_conj D Z Y]

end lin

section main

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem pairing_middle_all_levels_holds : NFPairMidAll := by
  intro Cb
  refine ⟨100, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH χ' hχ' w hw hN ε hε
  obtain ⟨hχ, -, hf, hfA, hA5, -⟩ := hH
  have hχc := hχ
  have hχ'c := hχ'
  set Bs := p.T.base with hBs
  set s : ℂ := M.sgn P p.l0 with hsdef
  have hs : conj s = s := by rw [hsdef]; unfold M.sgn; simp
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) := fun g₀ _ =>
    ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  set F' := TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ with hF'
  have hF's : B.CkOn ⊤ (B.GV P.k P.r) F' := ckOn_fpm p p₀ hf hid
  have hF'A := inCC_fpm_id p p₀ hfA
  set nn : ℕ := w.length * (2 * P.r + P.k + 1) + (2 * P.r + P.k + 1 + 5) with hnn
  have hbound := CutMP.ER.bound_aux P.r P.k w.length N (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)) hN hA5
  obtain ⟨-, ⟨δ₁, hδ₁, hz₁⟩, -⟩ := hχ'
  obtain ⟨-, ⟨δ₂, hδ₂, hz₂⟩, -⟩ := hχ
  set c₀ : ℝ := min δ₁ δ₂ * ε with hc₀
  have hc₀p : 0 < c₀ := mul_pos (lt_min hδ₁ hδ₂) hε
  have hgood : ∀ ψ : ℝ → ℝ, C6.IsCut0 ψ → (∀ x, x < min δ₁ δ₂ → ψ x = 0) →
      CutMP.ER.Good Bs (B.AB P.k P.r) nn c₀ (D.cutF Bs ψ F' ε) := by
    intro ψ hψ hz
    refine ⟨Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF Bs hψ hF's ε,
      Formalism.FourierDecayAlt.P.PBE.cutF_inCC Bs hψ hF'A hε _ _ hbound, fun g _ hg => ?_⟩
    by_contra hlt
    push Not at hlt
    apply hg
    have h0 : ψ (Gf P.k P.r Bs.z Bs.z' g / ε) = 0 := hz _ (by rw [div_lt_iff₀ hε]; exact hlt)
    simp only [D.cutF, h0, Complex.ofReal_zero, zero_smul]
  have gu := hgood χ' hχ'c (fun x hx => hz₁ x (lt_of_lt_of_le hx (min_le_left _ _)))
  have gv := hgood χ hχc (fun x hx => hz₂ x (lt_of_lt_of_le hx (min_le_right _ _)))
  have gm := hgood (midCut χ' χ) (isCut0_midCut hχ'c hχc) (fun x hx => by
    simp only [midCut, hz₁ x (lt_of_lt_of_le hx (min_le_left _ _)), hz₂ x (lt_of_lt_of_le hx (min_le_right _ _))]
    norm_num)
  set u := D.cutF Bs χ' F' ε with hu
  set v := D.cutF Bs χ F' ε with hv
  set m := D.cutF Bs (midCut χ' χ) F' ε with hm
  have hm_eq : m = fun g => (1 / 2 : ℂ) • u g + (1 / 2 : ℂ) • v g := by
    funext g
    simp only [hm, hu, hv, D.cutF, midCut]
    rw [smul_smul, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring
  have pe : ∀ X Z : B.Mat P.k P.r → (Wq →L[ℂ] Wp),
      pair0 p X Z w = B.beta Bs (w.foldr (CutMP.ER.opL P.k P.r s) X) Z := fun _ _ => rfl
  set fu := w.foldr (CutMP.ER.opL P.k P.r s) u with hfu
  set fv := w.foldr (CutMP.ER.opL P.k P.r s) v with hfv
  have n5 : 5 ≤ nn := le_trans (by omega : 5 ≤ 2 * P.r + P.k + 1 + 5) (Nat.le_add_left _ _)
  have gfold : ∀ H, CutMP.ER.Good Bs (B.AB P.k P.r) nn c₀ H →
      B.InCC (B.AB P.k P.r) 5 (w.foldr (CutMP.ER.opL P.k P.r s) H) := by
    intro H hG
    have h := CutMP.ER.fold_good CutMP.ER.coefficient_vector_smoothness CutMP.ER.coefficient_vector_in_class CutMP.ER.coefficient_vector_support s w
      (2 * P.r + P.k + 1 + 5) H (CutMP.ER.good_mono (le_of_eq (Nat.add_comm _ _)) hG)
    exact CutMP.ER.inCC_mono (by omega) h.2.1
  have iu := CutMP.ER.inCC_mono n5 gu.2.1
  have iv := CutMP.ER.inCC_mono n5 gv.2.1
  have im := CutMP.ER.inCC_mono n5 gm.2.1
  have ifu := gfold u gu
  have ifv := gfold v gv
  have hAB : B.AB P.k P.r ≤ B.AB P.k P.r := le_rfl

  have hfm : ∀ g ∈ B.GV P.k P.r, w.foldr (CutMP.ER.opL P.k P.r s) m g =
      (1 / 2 : ℂ) • fu g + (1 / 2 : ℂ) • fv g := by
    rw [hm_eq]
    exact fold_lin Bs s _ _ w u v gu.1 gv.1
  have Pmm : pair0 p m m w = (1 / 2 : ℂ) * ((1 / 2 : ℂ) * B.beta Bs fu u + (1 / 2 : ℂ) * B.beta Bs fu v) +
      (1 / 2 : ℂ) * ((1 / 2 : ℂ) * B.beta Bs fv u + (1 / 2 : ℂ) * B.beta Bs fv v) := by
    have hc : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.conj_ofReal]
    rw [pe, CutMP.ER.beta_form_congr_holds P.k P.r Wp Wq Bs _ (fun g => (1 / 2 : ℂ) • fu g + (1 / 2 : ℂ) • fv g) m m hfm
      (fun _ _ => rfl), beta_form_linear_left Bs hAB _ _ ifu ifv im, hm_eq, beta_form_conj_linear_right Bs hAB _ _ iu iv ifu,
      beta_form_conj_linear_right Bs hAB _ _ iu iv ifv, hc]

  have capA : CutMP.ER.CapAdj :=
    CutMP.ER.capAdj_of_int (CutMP.ER.capAdjInt_of_scalar CutMP.ER.capacity_adjoint_scalar)
  have hvu : B.beta Bs fv u = (starRingEnd ℂ) (B.beta Bs fu v) := by
    have h1 := CutMP.ER.fold_adj capA CutMP.ER.capacity_theta_facts CutMP.ER.beta_form_congr_holds CutMP.ER.coefficient_vector_smoothness
      CutMP.ER.coefficient_vector_in_class CutMP.ER.coefficient_vector_support Bs hAB hc₀p hs w v u gv gu
    have h2 := CutMP.ER.beta_form_congr_holds P.k P.r Wp Wq Bs v v (w.reverse.foldr (CutMP.ER.opL P.k P.r s) u) fu
      (fun _ _ => rfl) (CutMP.ER.fold_rev CutMP.ER.coefficient_vector_smoothness CutMP.ER.coefficient_vector_congr CutMP.ER.coefficient_vector_commutation s w u gu.1)
    rw [h1, h2, CutMP.ER.beta_conj Bs v fu]
  rw [Pmm, pe u u, pe v v, pe u v, hvu]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.conj_re]
  ring

end main

end

end Formalism.FourierDecayAlt.P.CutBP
