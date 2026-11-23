import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfCartan

noncomputable section

namespace GlobalTheory.ThK.LiftPair

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def rtr {m : ℕ} {J : Matrix (Fin m) (Fin m) E} (x : UA σ J) (u : UA σ J → ℂ) : UA σ J → ℂ := fun y => u (y * x)

def trSpan {G : Type} [Group G] {m : ℕ} {J : Matrix (Fin m) (Fin m) E} (L : G →* UA σ J) (f : UA σ J → ℂ) :
    Submodule ℂ (UA σ J → ℂ) :=
  Submodule.span ℂ (Set.range fun g => rtr (L g) f)

def liftSk (h : IsCMExt F E σ) {v : Pl F} (τ : E →ₐ[F] Fv F v) {m : ℕ} (J : Matrix (Fin m) (Fin m) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (hd : J.det ≠ 0) : GL (Fin m) (Fv F v) →* UA σ J :=
  GlobalTheory.SplitUnitLift.liftU h τ J (-1) (fun i j => by rw [hJ, map_neg, map_one, neg_one_mul])
    (by rw [show (J.map τ).det = τ J.det from (AlgHom.map_det τ J).symm]; exact isUnit_iff_ne_zero.2 ((map_ne_zero τ).2 hd))

def thPair {n m : ℕ} {JX : Matrix (Fin n) (Fin n) E} {JY : Matrix (Fin m) (Fin m) E}
    (om : UA σ JX × UA σ JY →* Module.End ℂ ((Fin n × Fin m → AF F) → ℂ)) (g : UA σ JX) (μ : Measure (UA σ JY))
    (𝓕 : Set (UA σ JY)) (u : UA σ JY → ℂ) (Φ : (Fin n × Fin m → AF F) → ℂ) : ℂ :=
  ∫ h in 𝓕, u h * (starRingEnd ℂ) (thetaSum F (om (g, h) Φ)) ∂μ

attribute [local instance] GlobalTheory.LocalData.complRel

local instance locFieldLP (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) := GlobalTheory.LocalData.isLocalField v

def modelA {v : Pl F} (α : (Fv F v)ˣ →* ℂˣ) (n : ℕ) {m : ℕ} (h : GL (Fin m) (Fv F v))
    (Ψ : Matrix (Fin n) (Fin m) (Fv F v) → ℂ) : Matrix (Fin n) (Fin m) (Fv F v) → ℂ := fun X =>
  (α (Matrix.GeneralLinearGroup.det h) : ℂ) *
    ((GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det h) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) *
    Ψ (X * ((h⁻¹ : GL (Fin m) (Fv F v)) : Matrix (Fin m) (Fin m) (Fv F v))ᵀ)

end GlobalTheory.ThK.LiftPair

end
