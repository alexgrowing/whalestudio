import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RhoTopStepOfPair

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial

section At

variable (p n' : ℕ) {W Qq O Kf : Type} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [Field Kf]
  [Algebra O Kf] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) {m : ℕ} (r : ℕ)

def TSProp (X : Fin n' → Fin (m + 1) → ℤ) (Ψ : Module.Dual Kf (Vsp Kf X) ≃ₗ[Kf] Vsp Kf X) : Prop :=
  (∀ L : Submodule W (Fin (m + 1) → Qq), IsLattice W L →
    (dualLat O Kf (HL (O := O) ι σ X L)).map (Ψ.toLinearMap.restrictScalars O) ≤ HL ι σ X (latDual L) ∧
    scale ((p : Kf) ^ (kap1 p X : ℤ)) (HL (O := O) ι σ X (latDual L)) ≤
      (dualLat O Kf (HL (O := O) ι σ X L)).map (Ψ.toLinearMap.restrictScalars O)) ∧
  ∀ e : Edge W Qq (m + 1), IsEdge p n' r e →
    (Re' p ι σ w r X e).map (Ψ.toLinearMap.restrictScalars O) ≤ Re p ι σ w r X e.dual ∧
    scale ((p : Kf) ^ (kap1 p X : ℤ)) (Re p ι σ w r X e.dual) ≤
      (Re' p ι σ w r X e).map (Ψ.toLinearMap.restrictScalars O)

variable (TT : Finset (Fin n')) (d : Fin n' → ℕ) (rest lam : Fin n' → Fin (m + 1) → ℤ)

def TSOpAt (c0 : ℕ) (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d))) : Prop :=
  ∃ (Ψ0 : Module.Dual Kf (Vsp Kf lam) ≃ₗ[Kf] Vsp Kf lam)
    (Ψf : Module.Dual Kf (Vsp Kf (flW (m := m) d)) ≃ₗ[Kf] Vsp Kf (flW (m := m) d)),
    TSProp p n' (W := W) (O := O) ι σ w r lam Ψ0 ∧ TSProp p n' (W := W) (O := O) ι σ w r (flW d) Ψf ∧
    (∀ (β : Vsp Kf rest) (F : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)) (s : Vsp Kf rest) (u : Vsp Kf lam),
      ((u : Vsp Kf lam) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = ((Θ F : Vsp Kf (flW (m := m) d)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * ((s : Vsp Kf rest) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) →
      ∃ F' : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O),
        (F' : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈
          OpCl TT c0 (Submodule.span (KK O) {(F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O))}) ∧
        ∀ (T : Module.Dual Kf (Vsp Kf (flW (m := m) d))) (z : Vsp Kf lam),
          (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = ((Ψf T : Vsp Kf (flW (m := m) d)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * (β : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) →
          (p : Kf) ^ Ar r rest * ((p : Kf) ^ kap1 p lam * Ψ0.symm z u) = T (Θ F'))

def OntoAt (e : Edge W Qq (m + 1)) : Prop :=
  Re p ι σ w r lam e ≤ Submodule.span O {z : Vsp Kf lam | ∃ y ∈ Re p ι σ w r (flW d) e,
    ∃ β ∈ Re p ι σ w r rest e, (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = (y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * (β : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)}

variable {p n' ι σ w r}

theorem ts_sub {X : Fin n' → Fin (m + 1) → ℤ} {Ψ : Module.Dual Kf (Vsp Kf X) ≃ₗ[Kf] Vsp Kf X}
    {A : Submodule O (Module.Dual Kf (Vsp Kf X))} {B : Submodule O (Vsp Kf X)}
    (h : A.map (Ψ.toLinearMap.restrictScalars O) ≤ B) : ∀ T ∈ A, Ψ T ∈ B := fun T hT => h ⟨T, hT, rfl⟩

theorem ts_sup {X : Fin n' → Fin (m + 1) → ℤ} {Ψ : Module.Dual Kf (Vsp Kf X) ≃ₗ[Kf] Vsp Kf X}
    {A : Submodule O (Module.Dual Kf (Vsp Kf X))} {B : Submodule O (Vsp Kf X)} {κ : ℕ}
    (h : scale ((p : Kf) ^ (κ : ℤ)) B ≤ A.map (Ψ.toLinearMap.restrictScalars O)) :
    ∀ y ∈ B, Ψ.symm ((p : Kf) ^ κ • y) ∈ A := by
  intro y hy
  obtain ⟨T, hT, hTe⟩ := h (mem_scale.2 ⟨y, hy, rfl⟩)
  have : Ψ T = (p : Kf) ^ κ • y := by rw [← zpow_natCast]; exact hTe
  rw [← this, Ψ.symm_apply_apply]
  exact hT

theorem pairAt_of_tsop (c0 : ℕ) (bK : ℝ) (e : Edge W Qq (m + 1)) (he : IsEdge p n' r e)
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d)))
    (hsize : ((kap1 p lam + kap1 p (flW (m := m) d) : ℕ) : ℝ) ≤ bK)
    (hon : OntoAt p n' ι σ w r d rest lam e.dual)
    (h : TSOpAt p n' (W := W) ι σ w r TT d rest lam c0 Θ) : PairAt p n' ι σ w r TT d rest lam c0 bK e Θ := by
  obtain ⟨Ψ0, Ψf, h0, hf, hop⟩ := h
  refine ⟨kap1 p lam, kap1 p (flW (m := m) d), Ψ0, Ψf, hsize, ts_sub (hf.1 e.tgt he.2.1).1,
    fun e' he' _ => ts_sub (hf.2 e' he').1, ts_sup (hf.2 e he).2, ts_sup (h0.1 e.tgt he.2.1).2,
    fun e' he' _ => ts_sup (h0.2 e' he').2, ts_sub (h0.2 e he).1, hon, hop⟩

end At

def TSOpStep (C : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    ∀ hSet : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w,
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
      IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
      ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
        IsTrueTheta hSet.1 (dT TT lam0) (flW (dT TT lam0)) (vecE n') hm Θ →
        TSOpAt p n' (W := W) ι σ w r TT (dT TT lam0) (topW TT (restW TT lam0)) (topW TT lam0) c0 Θ

def SizeStep (C CK : ℝ) : Prop :=
  ∀ (p n' m r : ℕ) (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ((kap1 p (topW TT lam0) + kap1 p (flW (m := m) (dT TT lam0)) : ℕ) : ℝ) ≤
      CK * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a

def OntoAll : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O), HidaSetting p n' W Qq O Kf ι σ j w →
    ∀ (m r : ℕ) (d : Fin n' → ℕ) (rest lam : Fin n' → Fin (m + 1) → ℤ), lam = flW d + rest → IsDominant rest →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → OntoAt p n' ι σ w r d rest lam e

def RestTSOp (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → TSOpStep C

def RestSize : Prop := ∃ CK C₁ : ℝ, 0 < CK ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → SizeStep C CK

theorem restPairTop_of (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (hop : RestTSOp D CLa Ck Crk Cdeg) (hsz : RestSize)
    (hon : OntoAll) : RestPairTop D CLa Ck Crk Cdeg := by
  intro hA
  obtain ⟨C₂, hC2, h2⟩ := hop hA
  obtain ⟨CK, C₃, hCK, hC3, h3⟩ := hsz
  refine ⟨CK, max C₂ C₃, hCK, lt_of_lt_of_le hC2 (le_max_left _ _), ?_⟩
  intro C hC p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ
    e he htgt hm g hhm hg hbasis Θ hΘ
  have hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hr2 : 2 ≤ r := H.2.1
  have hdom : IsDominant lam0 := H.2.2.2.2.1.2.1
  exact pairAt_of_tsop TT (dT TT lam0) _ _ c0 _ e he Θ
    (h3 C (le_trans (le_max_right _ _) hC) p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar H)
    (hon p n' W Qq O Kf ι σ j w hSet.1 m r (dT TT lam0) _ _ (topW_lam TT lam0)
      (topW_dom TT (restW_dom (by omega) TT lam0 hdom)) e.dual (Formalism.L2.G.Model.dual_edge hSet.1 m r e he).1)
    (h2 C (le_trans (le_max_left _ _) hC) p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H
      φ hφ e he htgt hm g hhm hg hbasis Θ hΘ)

theorem restCloudB_of_three (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (hop : RestTSOp D CLa Ck Crk Cdeg) (hsz : RestSize)
    (hon : OntoAll) : RestCloudB D CLa Ck Crk Cdeg :=
  restCloudB_of_pair D CLa Ck Crk Cdeg (restPairTop_of D CLa Ck Crk Cdeg hop hsz hon)

end Formalism.MainNotions.TestSideCounting
