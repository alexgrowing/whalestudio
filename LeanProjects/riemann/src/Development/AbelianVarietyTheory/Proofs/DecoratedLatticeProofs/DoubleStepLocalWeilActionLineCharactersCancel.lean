import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QPl.LineCancel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isComp_mul (p : Place D k) {χ χ' : (AE D)ˣ →* Circle} {μ μ' : kˣ →* ℂˣ} (h : p.IsComp χ μ)
    (h' : p.IsComp χ' μ') : p.IsComp (χ * χ') (μ * μ') := by
  intro x a ha
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, h x a ha, h' x a ha, Circle.coe_mul]

theorem isComp_inv (p : Place D k) {χ : (AE D)ˣ →* Circle} {μ : kˣ →* ℂˣ} (h : p.IsComp χ μ) :
    p.IsComp χ⁻¹ μ⁻¹ := by
  intro x a ha
  rw [MonoidHom.inv_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, h x a ha, Circle.coe_inv]

theorem om_mul {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ ν : kˣ →* ℂˣ) (g : GL a k)
    (h : GL b k) (Φ : Matrix b a k → ℂ) :
    om (μ * ν) g h Φ = (((ν (Matrix.GeneralLinearGroup.det g) * (ν (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ)) : ℂ) •
      om μ g h Φ := by
  funext t
  simp only [om, Pi.smul_apply, smul_eq_mul, MonoidHom.mul_apply, mul_inv, Units.val_mul]
  ring

theorem val_smul_inv {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} (S : Dbl2 ψ σ) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ)
    (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (A : WO S.B.V S.J.W → ℂ) (B : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ)
    (f : GA D S.B'.V → ℂ) (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) (z : ℂˣ) :
    S.val c₁ c₂ ((z : ℂ) • A) (((z⁻¹ : ℂˣ) : ℂ) • B) φ f g h₁ h₂ = S.val c₁ c₂ A B φ f g h₁ h₂ := by
  have e : S.con ((z : ℂ) • A) (((z⁻¹ : ℂˣ) : ℂ) • B) g h₁ h₂ = S.con A B g h₁ h₂ := by
    unfold Dbl2.con
    rw [map_smul, map_smul, GlobalTheory.HandHom.flatBF_smul, GlobalTheory.HandHom.flatFB_smul]
    funext u v
    unfold GlobalTheory.Unf.contr
    congr 1
    funext w
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_mul_mul_comm, Units.inv_mul, one_mul]
  unfold Dbl2.val
  rw [e]

end GlobalTheory.QPl.LineCancel

namespace GlobalTheory.QPl.LineCancel

theorem scal_one {G : Type} [Group G] (μ ζ : G →* ℂˣ) (a x : G) : ζ x = ((μ⁻¹ * ζ) * μ) a * (ζ⁻¹ a * (ζ⁻¹ x)⁻¹) := by
  rw [inv_mul_cancel_comm]
  simp only [MonoidHom.inv_apply, inv_inv, mul_inv_cancel_left]

theorem scal_two {G : Type} [Group G] (μ ζ : G →* ℂˣ) (x : G) : (ζ x)⁻¹ = (μ⁻¹ * (μ * ζ⁻¹)) x := by
  rw [inv_mul_cancel_left, MonoidHom.inv_apply]

end GlobalTheory.QPl.LineCancel

namespace GlobalTheory.QPl.LineCancel

theorem val_om_loc : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S)
    (T₁ : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.B.V S.J.W → ℂ))
    (T₂ : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.J.W S.B'.V → ℂ)),
    (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ →
  ∀ (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (φ : GA D S.B.A → ℂ) (F : GA D S.B'.V → ℂ)
    (a : GL (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) (x : GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) (y : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k)
    (Φ₁ Φ₁' : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k))
    (Φ₂ Φ₂' : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k)),
    Φ₁'.1 = om Q.μ₁ a x Φ₁.1 → Φ₂'.1 = om Q.μ₂ x y Φ₂.1 →
    S.val c₁ c₂ (S.s₁.om (Q.gl₀ a, Q.gl₁ x) (T₁ Φ₁)) (S.s₂.om (Q.gl₁ x, Q.gl₂ y) (T₂ Φ₂)) φ F 1 1 1 =
      S.val c₁ c₂ (T₁ Φ₁') (T₂ Φ₂') φ F 1 1 1 := by
  intro D ψ hψ σ S Q T₁ T₂ h₁ h₂ c₁ c₂ φ F a x y Φ₁ Φ₁' Φ₂ Φ₂' e₁ e₂
  obtain ⟨ζ, hζ⟩ := GlobalTheory.LocMod.Witness.exists_isComp (ofSplit Q.q) S.χz
  have k₁' : (ofSplit Q.q).IsComp S.χ₁ Q.μ₁⁻¹ := by simpa using isComp_inv _ Q.comp₁
  have k₂' : (ofSplit Q.q).IsComp S.χ₂ Q.μ₂⁻¹ := by simpa using isComp_inv _ Q.comp₂
  have hV₁ : (ofSplit Q.q).IsComp S.s₁.χV (Q.μ₁⁻¹ * ζ) := by rw [S.V₁]; exact isComp_mul _ k₁' hζ
  have hW₁ : (ofSplit Q.q).IsComp S.s₁.χW Q.μ₁⁻¹ := by rw [S.W₁]; exact k₁'
  have hV₂ : (ofSplit Q.q).IsComp S.s₂.χV Q.μ₂⁻¹ := by rw [S.V₂]; exact k₂'
  have hW₂ : (ofSplit Q.q).IsComp S.s₂.χW (Q.μ₂⁻¹ * ζ) := by rw [S.W₂]; exact isComp_mul _ k₂' hζ
  have r₁ := GlobalTheory.T.weilDatum_localModel_formula D Q.k (ofSplit Q.q) ψ S.B.V S.J.W S.s₁.χV S.s₁.χW S.s₁.om S.s₁.weil (Q.μ₁⁻¹ * ζ) Q.μ₁⁻¹ hV₁ hW₁
    (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.F.G₀ Q.F.G₁ T₁ h₁ (Q.gl₀ a) a (Q.gl₁ x) x (Q.loc₀ a)
    (Q.loc₁ x) Φ₁ (((ζ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) • Φ₁') (by
      rw [Submodule.coe_smul, e₁, mul_inv, inv_inv, om_mul, smul_smul, ← Units.val_mul]
      congr 2
      exact scal_one Q.μ₁ ζ _ _)
  have r₂ := GlobalTheory.T.weilDatum_localModel_formula D Q.k (ofSplit Q.q) ψ S.J.W S.B'.V S.s₂.χV S.s₂.χW S.s₂.om S.s₂.weil Q.μ₂⁻¹ (Q.μ₂⁻¹ * ζ) hV₂ hW₂
    (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.F.G₁ Q.F.G₂ T₂ h₂ (Q.gl₁ x) x (Q.gl₂ y) y (Q.loc₁ x)
    (Q.loc₂ y) Φ₂ ((((ζ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) • Φ₂') (by
      rw [Submodule.coe_smul, e₂, inv_inv, mul_inv, inv_inv]
      congr 2
      exact scal_two Q.μ₂ ζ _)
  rw [r₁, r₂, map_smul, map_smul]
  exact val_smul_inv S c₁ c₂ _ _ φ F 1 1 1 _

end GlobalTheory.QPl.LineCancel
