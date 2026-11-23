import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFieldFv

noncomputable section

namespace GlobalTheory.IndLineGL

open GlobalTheory.SmGL GlobalTheory.PRep
open scoped TensorProduct

section General

variable {G V Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]

def HomLeOne (ρ : Representation ℂ G V) (τ : Representation ℂ G Y) : Prop :=
  ∀ μ μ' : ρ.IntertwiningMap τ, μ.toLinearMap = 0 ∨ ∃ c : ℂ, μ'.toLinearMap = c • μ.toLinearMap

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def leviTgt {m : ℕ} {P₁ : Type} [AddCommGroup P₁] [Module ℂ P₁] (σ₁ : Representation ℂ (GL (Fin m) k) P₁)
    (ξ₁ ξ₂ : kˣ →* ℂˣ) : Representation ℂ (Levi k fun i : Fin 3 => Fin (blk3 m i)) P₁ :=
  twist (σ₁.comp (Pi.evalMonoidHom (fun i : Fin 3 => GL (Fin (blk3 m i)) k) 1))
    (ξ₁.comp (Matrix.GeneralLinearGroup.det.comp (Pi.evalMonoidHom (fun i : Fin 3 => GL (Fin (blk3 m i)) k) 0)) *
      ξ₂.comp (Matrix.GeneralLinearGroup.det.comp (Pi.evalMonoidHom (fun i : Fin 3 => GL (Fin (blk3 m i)) k) 2)))

theorem leviTgt_apply {m : ℕ} {P₁ : Type} [AddCommGroup P₁] [Module ℂ P₁] (σ₁ : Representation ℂ (GL (Fin m) k) P₁)
    (ξ₁ ξ₂ : kˣ →* ℂˣ) (l : Levi k fun i : Fin 3 => Fin (blk3 m i)) (y : P₁) :
    leviTgt σ₁ ξ₁ ξ₂ l y = ((ξ₁ (Matrix.GeneralLinearGroup.det (l 0)) * ξ₂ (Matrix.GeneralLinearGroup.det (l 2)) : ℂˣ) : ℂ) •
      σ₁ (l 1) y := rfl

variable (k) in

def torusPt (m : ℕ) (t₁ t₂ : kˣ) : Levi k fun i : Fin 3 => Fin (blk3 m i) :=
  Pi.mulSingle (M := fun i : Fin 3 => GL (Fin (blk3 m i)) k) 0 (Matrix.GeneralLinearGroup.scalar (Fin (blk3 m 0)) t₁) *
    Pi.mulSingle (M := fun i : Fin 3 => GL (Fin (blk3 m i)) k) 2 (Matrix.GeneralLinearGroup.scalar (Fin (blk3 m 2)) t₂)

variable (k) in

def detPair (a a' : ℕ) (α₀ β₀ : kˣ →* ℂˣ) : Representation ℂ (Levi k (Two (Fin a) (Fin a'))) (ℂ ⊗[ℂ] ℂ) :=
  (extTensor (detRep (Fin a) α₀) (detRep (Fin a') β₀)).comp (leviTwo k (Fin a) (Fin a')).symm.toMonoidHom

theorem prod₂_detRep_eq (a a' : ℕ) (α₀ β₀ : kˣ →* ℂˣ) :
    prod₂ (detRep (Fin a) α₀) (detRep (Fin a') β₀) = parInd (two (stdSum rfl)) (detPair k a a' α₀ β₀) := rfl

variable (k) in

def cellChar (a a' : ℕ) (α₀ β₀ : kˣ →* ℂˣ) (b : Bool → Fin 3 → ℕ) (t₁ t₂ : kˣ) : ℂˣ :=
  ∏ r : Bool, ((cond r β₀ α₀ * absPow k ((1 - ((cond r a' a : ℕ) : ℂ)) / 2)) t₁) ^ b r 0 *
    ((cond r β₀ α₀ * absPow k ((((cond r a' a : ℕ) : ℂ) - 1) / 2)) t₂) ^ b r 2

variable (k) in

def cellMid (α₀ β₀ : kˣ →* ℂˣ) (b : Bool → Fin 3 → ℕ) :=
  prod₂ (detRep (Fin (b false 1)) (α₀ * absPow k ((((b false 0 : ℕ) : ℂ) - (b false 2 : ℕ)) / 2)))
    (detRep (Fin (b true 1)) (β₀ * absPow k ((((b true 0 : ℕ) : ℂ) - (b true 2 : ℕ)) / 2)))

end GlobalTheory.IndLineGL

namespace GlobalTheory.IndLineGL

open GlobalTheory.SmGL GlobalTheory.PRep
open scoped TensorProduct

section General

variable {G V V' Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup Y] [Module ℂ Y]

theorem HomLeOne.of_equiv {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'} {τ : Representation ℂ G Y}
    (φ : ρ.Equiv ρ') (h : HomLeOne ρ' τ) : HomLeOne ρ τ := by
  intro μ μ'
  have key : ∀ v : V, φ.symm (φ v) = v := fun v => φ.toLinearEquiv.symm_apply_apply v
  rcases h (μ.comp φ.symm.toIntertwiningMap) (μ'.comp φ.symm.toIntertwiningMap) with h0 | ⟨c, hc⟩
  · left
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun h0 (φ v)
    simpa [key] using this
  · right
    refine ⟨c, LinearMap.ext fun v => ?_⟩
    have := LinearMap.congr_fun hc (φ v)
    simpa [key] using this

theorem smul_of_equiv {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'} (φ : ρ.Equiv ρ') {z : G} {c : ℂ}
    (h : ∀ y, ρ' z y = c • y) (x : V) : ρ z x = c • x := by
  apply φ.toLinearEquiv.injective
  have h1 := Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap z x
  rw [Representation.Equiv.toLinearEquiv_apply, h1, h, map_smul, Representation.Equiv.toLinearEquiv_apply]

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem torusPt_zero (m : ℕ) (t₁ t₂ : kˣ) :
    torusPt k m t₁ t₂ 0 = Matrix.GeneralLinearGroup.scalar (Fin (blk3 m 0)) t₁ := by
  simp only [torusPt, Pi.mul_apply]
  rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (by decide : (0 : Fin 3) ≠ 2), mul_one]

theorem torusPt_one (m : ℕ) (t₁ t₂ : kˣ) : torusPt k m t₁ t₂ 1 = 1 := by
  simp only [torusPt, Pi.mul_apply]
  rw [Pi.mulSingle_eq_of_ne (by decide : (1 : Fin 3) ≠ 0), Pi.mulSingle_eq_of_ne (by decide : (1 : Fin 3) ≠ 2), mul_one]

theorem torusPt_two (m : ℕ) (t₁ t₂ : kˣ) :
    torusPt k m t₁ t₂ 2 = Matrix.GeneralLinearGroup.scalar (Fin (blk3 m 2)) t₂ := by
  simp only [torusPt, Pi.mul_apply]
  rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (by decide : (2 : Fin 3) ≠ 0), one_mul]

theorem leviTgt_torusPt {m : ℕ} {P₁ : Type} [AddCommGroup P₁] [Module ℂ P₁] (σ₁ : Representation ℂ (GL (Fin m) k) P₁)
    (ξ₁ ξ₂ : kˣ →* ℂˣ) (t₁ t₂ : kˣ) (y : P₁) :
    leviTgt σ₁ ξ₁ ξ₂ (torusPt k m t₁ t₂) y = ((ξ₁ t₁ * ξ₂ t₂ : ℂˣ) : ℂ) • y := by
  rw [leviTgt_apply, torusPt_zero, torusPt_one, torusPt_two, Matrix.GeneralLinearGroup.det_scalar,
    Matrix.GeneralLinearGroup.det_scalar]
  have h1 : σ₁ (1 : GL (Fin m) k) y = y := by rw [map_one]; rfl
  have hc0 : Fintype.card (Fin (blk3 m 0)) = 1 := by convert Fintype.card_fin (blk3 m 0) using 1 <;> rfl
  have hc2 : Fintype.card (Fin (blk3 m 2)) = 1 := by convert Fintype.card_fin (blk3 m 2) using 1 <;> rfl
  rw [hc0, hc2, pow_one, pow_one]
  exact congrArg _ h1

theorem isSmooth_detPair (a a' : ℕ) {α₀ β₀ : kˣ →* ℂˣ} (hα : IsSmoothChar α₀) (hβ : IsSmoothChar β₀) :
    IsSmooth (detPair k a a' α₀ β₀) :=
  isSmooth_comp (isSmooth_extTensor ((isSmooth_ofChar_iff (detChar (Fin a) α₀)).2 hα.detChar)
    ((isSmooth_ofChar_iff (detChar (Fin a') β₀)).2 hβ.detChar)) _
    (show Continuous fun g : Levi k (Two (Fin a) (Fin a')) => (g false, g true) from
      (continuous_apply false).prodMk (continuous_apply true))

end GlobalTheory.IndLineGL
