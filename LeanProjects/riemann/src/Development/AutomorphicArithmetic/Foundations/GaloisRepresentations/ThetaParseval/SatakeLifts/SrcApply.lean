import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL

namespace UpperTheory.Gal.TP.Loc

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n d : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def IsLift (ν b : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin n) k) V) (π : Representation ℂ (GL (Fin d) k) W) : Prop :=
  ∃ β : SB (Matrix (Fin n) (Fin d) k) →ₗ[ℂ] V →ₗ[ℂ] W, β ≠ 0 ∧
    ∀ (g : GL (Fin n) k) (h : GL (Fin d) k) (Φ Φ' : SB (Matrix (Fin n) (Fin d) k)),
      (Φ' : Matrix (Fin n) (Fin d) k → ℂ) = GlobalTheory.SplitFlip.omA ν b g h Φ → ∀ v : V, β Φ' (σ g v) = π h (β Φ v)

def src (c : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin n) k) V) : Representation ℂ (GL (Fin n) k) V :=
  twist (σ.comp GlobalTheory.SplitFlip.invT) (detChar (Fin n) c)

theorem src_apply (c : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin n) k) V) (g : GL (Fin n) k) (v : V) :
    src c σ g v = ((c (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • σ (GlobalTheory.SplitFlip.invT g) v := rfl

end Local

def LiftIso : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n t : ℕ) (ν b : kˣ →* ℂˣ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin n) k) V) (π : Representation ℂ (GL (Fin (n + t)) k) W), n < t →
    IsSmoothChar ν → IsUnitaryChar ν → IsSmoothChar b → IsUnitaryChar b →
    IsSmooth σ → σ.IsIrreducible → IsUnitarisable σ → IsSmooth π → π.IsIrreducible → IsLift ν b σ π →
    Nonempty ((contra π).Equiv (prod₂ (contra (src (ν * b) σ)) (detRep (Fin t) b⁻¹)))

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def LiftSat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (n d : ℕ) (ν b : (w.adicCompletion K)ˣ →* ℂˣ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin n) (w.adicCompletion K)) V) (π : Representation ℂ (GL (Fin d) (w.adicCompletion K)) W),
    2 * n < d → IsUnram ν → IsUnitaryChar ν → IsUnram b → IsUnitaryChar b →
    IsSmooth σ → σ.IsIrreducible → IsUnitarisable σ → IsSmooth π → π.IsIrreducible → IsLift ν b σ π →
    ∀ ϖ : (w.adicCompletion K)ˣ, Formalism.UG.IsUnifV K w ϖ → ∀ B : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w σ B →
      GlobalTheory.LFun.HasSatGL w π (B.map (fun x => x⁻¹ * (ν ϖ * b ϖ)) + GlobalTheory.LFun.seg w (b ϖ) (d - n))

end UpperTheory.Gal.TP.Loc

end
