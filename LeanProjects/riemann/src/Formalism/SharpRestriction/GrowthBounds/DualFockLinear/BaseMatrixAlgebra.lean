import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RestCloudBOfThree
import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideFinal

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.L2.G.Model.TS (fockR)

def RestTSX : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w →
    ∀ (m r : ℕ) (X : Fin n' → Fin (m + 1) → ℤ), IsDominant X →
    ∃ (Ψ : Module.Dual Kf ↥(Vsp Kf X) ≃ₗ[Kf] ↥(Vsp Kf X)) (c : Kf), c ≠ 0 ∧
      TSProp p n' (W := W) (O := O) ι σ w r X Ψ ∧
      ∀ y u : Vsp Kf X, Ψ.symm y u =
        c * fockR (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)
          (y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)

def OpFAt {n' : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] {m : ℕ} (TT : Finset (Fin n'))
    (d : Fin n' → ℕ) (rest : Fin n' → Fin (m + 1) → ℤ) (c0 : ℕ)
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d))) : Prop :=
  ∀ (κ : Kf) (β s : Vsp Kf rest) (F : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)),
    ∃ F' : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O),
      (F' : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈
        OpCl TT c0 (Submodule.span (KK O) {(F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O))}) ∧
      ∀ Y : Vsp Kf (flW (m := m) d),
        fockR ((Θ F' : Vsp Kf (flW (m := m) d)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)
            (Y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
          κ * fockR (((Θ F : Vsp Kf (flW (m := m) d)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
              (s : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf))
            ((Y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
              (β : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf))

def OpFStep (C : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    ∀ hSet : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w,
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq), IsUnit hm.det →
      ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
        IsTrueTheta hSet.1 (dT TT lam0) (flW (dT TT lam0)) (vecE n') hm Θ →
        OpFAt TT (dT TT lam0) (topW TT (restW TT lam0)) c0 Θ

def RestOpF : Prop := ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → OpFStep C

theorem tsOpAt_of {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (hS : HidaSetting p n' W Qq O Kf ι σ j w) (hX : RestTSX)
    {m : ℕ} (r : ℕ) (TT : Finset (Fin n')) (d : Fin n' → ℕ) (rest lam : Fin n' → Fin (m + 1) → ℤ)
    (hlam : IsDominant lam) (c0 : ℕ)
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d)))
    (hOp : OpFAt TT d rest c0 Θ) : TSOpAt p n' (W := W) ι σ w r TT d rest lam c0 Θ := by
  obtain ⟨Ψ0, a0, ha0, t0, f0⟩ := hX p n' W Qq O Kf ι σ j w hS m r lam hlam
  obtain ⟨Ψf, af, haf, tf, ff⟩ := hX p n' W Qq O Kf ι σ j w hS m r (flW d) (flW_dom d)
  refine ⟨Ψ0, Ψf, t0, tf, ?_⟩
  intro β F s u hu
  obtain ⟨F', h1, h2⟩ := hOp ((p : Kf) ^ Ar r rest * ((p : Kf) ^ kap1 p lam * a0) / af) β s F
  refine ⟨F', h1, ?_⟩
  intro T z hz
  have e1 : T (Θ F') = af * fockR ((Θ F' : Vsp Kf (flW (m := m) d)) :
      MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) (Ψf T : Vsp Kf (flW (m := m) d)) := by
    rw [← ff (Ψf T) (Θ F'), LinearEquiv.symm_apply_apply]
  rw [e1, h2 (Ψf T), f0 z u, hu, hz]
  field_simp

theorem restTSOp_of (hX : RestTSX) (hOp : RestOpF) (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) :
    RestTSOp D CLa Ck Crk Cdeg := by
  intro _
  obtain ⟨C₁, hC1, h⟩ := hOp
  refine ⟨C₁, hC1, fun C hC => ?_⟩
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de hh x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ
    e he htgt hm g hhm hg hbasis Θ hΘ
  have hdom : IsDominant lam0 := H.2.2.2.2.1.2.1
  exact tsOpAt_of hSet.1 hX r TT (dT TT lam0) _ _ (topW_dom TT hdom) c0 Θ
    (h C hC p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de hh x lam0 aT bT a Y cpp c0 Dp cStar hSet H hm hhm Θ hΘ)

end Formalism.MainNotions.TestSideCounting
