import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

noncomputable section

namespace GlobalTheory.LocTypeGood

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.SplitUnitLift

attribute [local instance] GlobalTheory.LocalData.complRel

local instance locFieldAt {F : Type} [Field F] [NumberField F] (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) :=
  GlobalTheory.LocalData.isLocalField v

def imgSpan {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ G V) (ρ : Representation ℂ G W) : Submodule ℂ W :=
  ⨆ (T : V →ₗ[ℂ] W) (_ : ∀ g, T ∘ₗ π g = ρ g ∘ₗ T), LinearMap.range T

def glReindex {k : Type} [Field k] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n) :
    GL m k →* GL n k :=
  Units.map (Matrix.reindexAlgEquiv k k e).toMonoidHom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def rtrAt (hcm : IsCMExt F E σ) {v : Pl F} (τ : E →ₐ[F] Fv F v) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) {x x' : ℕ}
    (e : Fin (x + x') ≃ Fin n) : Representation ℂ (GL (Fin (x + x')) (Fv F v)) (UA σ J → ℂ) :=
  (GlobalTheory.PRep.rightReg ℂ (UA σ J) ℂ).comp ((liftU hcm τ J ε herm hJ).comp (glReindex e))

def HasLocType (hcm : IsCMExt F E σ) {v : Pl F} (τ : E →ₐ[F] Fv F v) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) {x x' : ℕ}
    (e : Fin (x + x') ≃ Fin n) (χ₁ χ₂ : (Fv F v)ˣ →* ℂˣ) (f : UA σ J → ℂ) : Prop :=
  ∀ y : UA σ J, (fun z => f (z * y)) ∈ imgSpan (GlobalTheory.ThK.MidJac.detInd x x' χ₁ χ₂) (rtrAt hcm τ J ε herm hJ e)

def NotRealPow {v : Pl F} (τ : E →ₐ[F] Fv F v) (α β : Chr F E) : Prop :=
  ∀ t : ℝ, chrW α τ * (chrW β τ)⁻¹ ≠ GlobalTheory.SmGL.absPow (Fv F v) (t : ℂ)

end GlobalTheory.LocTypeGood
