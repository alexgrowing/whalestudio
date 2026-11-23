import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDBeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDResRad
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactSupportInClassGeneral

open MeasureTheory Filter Topology
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

def eR (k r : ℕ) (x : (Fin r → ℂ) × Mx k r) : B.Mat k r := wCell k r (Fin.last r) x.1 * x.2

def RDSPIpSwap : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt k r))
    (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ), radIp μ Φ Ψ = LocFacts₂ μ 0 Ψ Φ c

def RDSPEOm : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq),
    (∀ x ∈ DomR k r D.z D.z', eR k r x ∈ JF.Om k r D.z D.z') ∧ ContinuousOn (eR k r) (DomR k r D.z D.z') ∧
      JF.Om k r D.z D.z' ⊆ B.GPos D

def RDSPZeroR : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (X Y : B.Mat k r → (Wq →L[ℂ] Wp)), X ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (JF.Om k r D.z D.z') →
      Y ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (JF.Om k r D.z D.z') →
      (∀ x ∈ DomR k r D.z D.z', X (eR k r x) = Y (eR k r x)) → ∀ g ∈ JF.Om k r D.z D.z', X g = Y g

def RDSPExh : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq),
    ∀ X ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (JF.Om k r D.z D.z'), ∀ C : Set (B.Mat k r), IsCompact C →
      C ⊆ JF.Om k r D.z D.z' →
      ∃ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (U : Set (B.Mat k r)), B.CkOn ⊤ (B.GV k r) F ∧ HasCompactSupport F ∧
        tsupport F ⊆ JF.Om k r D.z D.z' ∧ IsOpen U ∧ C ⊆ U ∧
        (∀ p, D.inSS p → ∀ g ∈ JF.Om k r D.z D.z', B.sgs p g ∈ U → g ∈ U) ∧
        ∀ g ∈ JF.Om k r D.z D.z', (g ∈ U → B.JF D F g = X g) ∧ (X g = 0 → B.JF D F g = 0)

def RDSPJFMem : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) F → HasCompactSupport F → tsupport F ⊆ JF.Om k r D.z D.z' →
      B.JF D F ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (JF.Om k r D.z D.z') ∧
      ∀ g ∈ JF.Om k r D.z D.z', B.JF D F g ≠ 0 → ∃ p, D.inSS p ∧ B.sgs p g ∈ tsupport F

def RDSPOp : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq), B.SmoothCoef (B.GPos D) Θ → B.Commutes D (B.GPos D) Θ →
    ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F → HasCompactSupport F → tsupport F ⊆ JF.Om k r D.z D.z' →
      (B.CkOn ⊤ (B.GV k r) (B.opApply Θ F) ∧ HasCompactSupport (B.opApply Θ F) ∧
        tsupport (B.opApply Θ F) ⊆ tsupport F) ∧
      (B.CkOn ⊤ (B.GV k r) (B.opAdj Θ F) ∧ HasCompactSupport (B.opAdj Θ F) ∧
        tsupport (B.opAdj Θ F) ⊆ tsupport F) ∧
      ∀ g ∈ JF.Om k r D.z D.z', B.opApply Θ (B.JF D F) g = B.JF D (B.opApply Θ F) g ∧
        B.opAdj Θ (B.JF D F) g = B.JF D (B.opAdj Θ F) g

def RDSPLoc : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Θ : B.DiffOp k r Wp Wq)
    (U : Set (B.Mat k r)) (X Y : B.Mat k r → (Wq →L[ℂ] Wp)), IsOpen U → (∀ g ∈ U, g ∈ B.GV k r → X g = Y g) →
      ∀ g ∈ U, g ∈ B.GV k r → B.opApply Θ X g = B.opApply Θ Y g ∧ B.opAdj Θ X g = B.opAdj Θ Y g

section Help

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem rdsp_hsVec_zero : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
  unfold B.hsVec; simp; rfl

theorem rdsp_ip_congr {a b a' b' : Wq →L[ℂ] Wp} (hb : b = b') (ha : b ≠ 0 → a = a') :
    inner ℂ (B.hsVec a) (B.hsVec b) = inner ℂ (B.hsVec a') (B.hsVec b') := by
  by_cases h : b = 0
  · rw [← hb, h, rdsp_hsVec_zero, inner_zero_right, inner_zero_right]
  · rw [← hb, ha h]

theorem rdsp_resG_congr (J J' : B.Mat k r → (Wq →L[ℂ] Wp)) (x : (Fin r → ℂ) × Mx k r)
    (h : J (eR k r x) = J' (eR k r x)) :
    resG k r (Fin.last r) J x.1 x.2 = resG k r (Fin.last r) J' x.1 x.2 := by
  show _ • J (eR k r x) = _ • J' (eR k r x)
  rw [h]

theorem rdsp_resG_ne (J : B.Mat k r → (Wq →L[ℂ] Wp)) (x : (Fin r → ℂ) × Mx k r)
    (h : resG k r (Fin.last r) J x.1 x.2 ≠ 0) : J (eR k r x) ≠ 0 := by
  intro h0
  apply h
  show _ • J (eR k r x) = 0
  rw [h0, smul_zero]

theorem rdsp_resG_zero (J : B.Mat k r → (Wq →L[ℂ] Wp)) (x : (Fin r → ℂ) × Mx k r) (hx : x.1 ∈ OmX r)
    (h : resG k r (Fin.last r) J x.1 x.2 = 0) : J (eR k r x) = 0 := by
  have h' : ((∏ a : Fin r, (if a.val < (Fin.last r).val then ‖x.1 a‖ ^ (Mdim k r a - 1) else 1) : ℝ) : ℂ) •
      J (eR k r x) = 0 := h
  rcases smul_eq_zero.1 h' with h1 | h1
  · exfalso
    rw [Complex.ofReal_eq_zero, Finset.prod_eq_zero_iff] at h1
    obtain ⟨a, -, ha⟩ := h1
    rw [if_pos (show (a : ℕ) < ((Fin.last r : Fin (r + 1)) : ℕ) by simp)] at ha
    refine hx a (norm_eq_zero.1 ?_)
    rcases Nat.eq_zero_or_pos (Mdim k r a - 1) with hn | hn
    · rw [hn, pow_zero] at ha; exact absurd ha one_ne_zero
    · exact (pow_eq_zero_iff hn.ne').1 ha
  · exact h1

end Help

theorem rDSPair_of_cut (hSw : RDSPIpSwap) (hE : RDSPEOm) (hZ : RDSPZeroR) (hX : RDSPExh) (hM : RDSPJFMem)
    (hO : RDSPOp) (hL : RDSPLoc) : RDSPair := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Θ hΘ J K hJ hK Φ₁ Φ₂ Φ₃ Φ₄ h1 h2 h3 h4
    hT
  subst hz hz' hπ hπ'
  obtain ⟨Kc, hKc, hKcD, hKc0⟩ := hT
  obtain ⟨hEO, hEc, hOP⟩ := hE P.k P.r Wp Wq D
  have hC0c : IsCompact (eR P.k P.r '' Kc) := hKc.image_of_continuousOn (hEc.mono hKcD)
  have hC0O : eR P.k P.r '' Kc ⊆ JF.Om P.k P.r D.z D.z' := by
    rintro _ ⟨x, hx, rfl⟩; exact hEO x (hKcD hx)
  obtain ⟨F₁, U₁, hF₁s, hF₁c, hF₁O, -, hC0U₁, -, hF₁K⟩ := hX P.k P.r Wp Wq D K hK _ hC0c hC0O
  obtain ⟨F₂, U₂, hF₂s, hF₂c, hF₂O, hU₂o, hCU₂, hU₂sat, hF₂J⟩ :=
    hX P.k P.r Wp Wq D J hJ _ (hC0c.union hF₁c) (Set.union_subset hC0O hF₁O)
  obtain ⟨⟨hA1s, hA1c, hA1t⟩, -, hJ1⟩ := hO P.k P.r Wp Wq D Θ hΘ.1 hΘ.2.1 F₁ hF₁s hF₁c hF₁O
  obtain ⟨-, ⟨hB2s, hB2c, hB2t⟩, hJ2⟩ := hO P.k P.r Wp Wq D Θ hΘ.1 hΘ.2.1 F₂ hF₂s hF₂c hF₂O
  have hF₁O' : tsupport (B.opApply Θ F₁) ⊆ JF.Om P.k P.r D.z D.z' := hA1t.trans hF₁O
  have hF₂O' : tsupport (B.opAdj Θ F₂) ⊆ JF.Om P.k P.r D.z D.z' := hB2t.trans hF₂O
  have hM1 := hM P.k P.r Wp Wq D F₁ hF₁s hF₁c hF₁O
  have hM2 := hM P.k P.r Wp Wq D F₂ hF₂s hF₂c hF₂O
  have hM3 := hM P.k P.r Wp Wq D _ hA1s hA1c hF₁O'
  have hM4 := hM P.k P.r Wp Wq D _ hB2s hB2c hF₂O'

  have hKeq : ∀ g ∈ JF.Om P.k P.r D.z D.z', K g = B.JF D F₁ g := by
    refine hZ P.k P.r Wp Wq D K (B.JF D F₁) hK hM1.1 fun x hx => ?_
    by_cases hxK : x ∈ Kc
    · exact ((hF₁K (eR P.k P.r x) (hEO x hx)).1 (hC0U₁ ⟨x, hxK, rfl⟩)).symm
    · have h0 : K (eR P.k P.r x) = 0 := by
        refine rdsp_resG_zero K x hx.1 ?_
        rw [← h2 x hx]; exact hKc0 x hxK
      rw [h0, (hF₁K (eR P.k P.r x) (hEO x hx)).2 h0]
  have hOpen : IsOpen (Q.OmPlus P.k P.r D.z D.z') := Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open D.z D.z'

  have hΘK : ∀ g ∈ JF.Om P.k P.r D.z D.z', B.opApply Θ K g = B.JF D (B.opApply Θ F₁) g := by
    intro g hg
    rw [(hL P.k P.r Wp Wq Θ _ K (B.JF D F₁) hOpen (fun g' hg' hgv => hKeq g' ⟨hgv, hg'⟩) g hg.2 hg.1).1]
    exact (hJ1 g hg).1

  have hΘJ : ∀ g ∈ JF.Om P.k P.r D.z D.z', g ∈ U₂ → B.opAdj Θ J g = B.JF D (B.opAdj Θ F₂) g := by
    intro g hg hgU
    rw [(hL P.k P.r Wp Wq Θ _ J (B.JF D F₂) (hU₂o.inter hOpen)
      (fun g' hg' hgv => ((hF₂J g' ⟨hgv, hg'.2⟩).1 hg'.1).symm) g ⟨hgU, hg.2⟩ hg.1).2]
    exact (hJ2 g hg).2

  obtain ⟨A₁, hA₁⟩ := radial_residue_formula Wp Wq P D.z D.z' D.π D.π' X μ L st l0 hD _ hM4.1
  obtain ⟨A₂, hA₂⟩ := radial_residue_formula Wp Wq P D.z D.z' D.π D.π' X μ L st l0 hD _ hM1.1
  obtain ⟨A₃, hA₃⟩ := radial_residue_formula Wp Wq P D.z D.z' D.π D.π' X μ L st l0 hD _ hM2.1
  obtain ⟨A₄, hA₄⟩ := radial_residue_formula Wp Wq P D.z D.z' D.π D.π' X μ L st l0 hD _ hM3.1

  have eL : radIp μ Φ₁ Φ₂ = radIp μ A₁ A₂ := by
    unfold radIp
    refine integral_congr_ae (Eventually.of_forall fun c => ?_)
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    dsimp only
    by_cases hx : (c, Matrix.of g) ∈ DomR P.k P.r D.z D.z'
    · have e2 : (Φ₂ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of g) = (A₂ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of g) := by
        rw [h2 _ hx, hA₂ _ hx]
        exact rdsp_resG_congr _ _ _ (hKeq _ (hEO _ hx))
      refine rdsp_ip_congr e2 fun hne => ?_
      have hxK : (c, Matrix.of g) ∈ Kc := by
        by_contra hxK; exact hne (hKc0 _ hxK)
      rw [h1 _ hx, hA₁ _ hx]
      exact rdsp_resG_congr _ _ _ (hΘJ _ (hEO _ hx) (hCU₂ (Or.inl ⟨_, hxK, rfl⟩)))
    · have z2 : (Φ₂ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of g) = 0 := Φ₂.2.1 (c, Matrix.of g) hx
      have z2' : (A₂ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of g) = 0 := A₂.2.1 (c, Matrix.of g) hx
      exact rdsp_ip_congr (z2.trans z2'.symm) fun hne => absurd z2 hne

  have eR' : radIp μ Φ₃ Φ₄ = radIp μ A₃ A₄ := by
    unfold radIp
    refine integral_congr_ae (Eventually.of_forall fun c => ?_)
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    dsimp only
    by_cases hx : (c, Matrix.of g) ∈ DomR P.k P.r D.z D.z'
    · have e4 : (Φ₄ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of g) = (A₄ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of g) := by
        rw [h4 _ hx, hA₄ _ hx]
        exact rdsp_resG_congr _ _ _ (hΘK _ (hEO _ hx))
      refine rdsp_ip_congr e4 fun hne => ?_
      rw [e4, hA₄ _ hx] at hne
      have hne' := rdsp_resG_ne _ _ hne
      obtain ⟨p, hp, hps⟩ := hM3.2 _ (hEO _ hx) hne'
      have hU : eR P.k P.r (c, Matrix.of g) ∈ U₂ := hU₂sat p hp _ (hEO _ hx) (hCU₂ (Or.inr (hA1t hps)))
      rw [h3 _ hx, hA₃ _ hx]
      exact rdsp_resG_congr _ _ _ ((hF₂J _ (hEO _ hx)).1 hU).symm
    · have z4 : (Φ₄ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of g) = 0 := Φ₄.2.1 (c, Matrix.of g) hx
      have z4' : (A₄ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of g) = 0 := A₄.2.1 (c, Matrix.of g) hx
      exact rdsp_ip_congr (z4.trans z4'.symm) fun hne => absurd z4 hne

  obtain ⟨C1, -, hB⟩ := radial_beta_identity P.k P.r Wp Wq D μ hD.2.1
  have hcc : ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV P.k P.r) F → HasCompactSupport F →
      ∀ (A : ℝ) (m : ℕ), B.InCC A m F := fun F hF hFc A m =>
    Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hF hFc (fun g _ hg => image_eq_zero_of_notMem_tsupport hg) A m
  have hβ := Formalism.FourierDecayAlt.P.CompactSupportClassLemmas.compact_support_in_class_general D Θ hΘ.1 hΘ.2.1 F₁ F₂ hF₁s hF₁c (fun g hg _ => hOP (hF₁O hg)) hF₂s hF₂c
    (fun g hg _ => hOP (hF₂O hg))
  rw [eL, eR', hSw P.k P.r D.z D.z' Wp Wq D.π D.π' μ A₁ A₂ 0, hSw P.k P.r D.z D.z' Wp Wq D.π D.π' μ A₃ A₄ 0,
    hB F₁ (B.opAdj Θ F₂) A₂ A₁ (hcc _ hF₁s hF₁c) (hcc _ hB2s hB2c) hA₂ hA₁ 0,
    hB (B.opApply Θ F₁) F₂ A₄ A₃ (hcc _ hA1s hA1c) (hcc _ hF₂s hF₂c) hA₄ hA₃ 0, hβ.2.2.2.2]

end Formalism.FourierDecayAlt.P.CutSE
