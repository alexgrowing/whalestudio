import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SrcApply

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL

namespace UpperTheory.Gal.TP.Loc

def LeftSmooth : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (Φ : SB (Matrix (Fin n) (Fin d) k)),
    {g : GL (Fin n) k | ∀ X : Matrix (Fin n) (Fin d) k, (Φ : Matrix (Fin n) (Fin d) k → ℂ) (g.val * X) =
      (Φ : Matrix (Fin n) (Fin d) k → ℂ) X} ∈ nhds (1 : GL (Fin n) k)

def KeepsSB : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ),
    (∀ (ν b : kˣ →* ℂˣ) (g : GL (Fin n) k) (h : GL (Fin d) k), ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) k),
      GlobalTheory.SplitFlip.omA ν b g h Φ ∈ SB (Matrix (Fin n) (Fin d) k)) ∧
    ∀ Ψ ∈ SB (Matrix (Fin d) (Fin n) k), (fun X : Matrix (Fin n) (Fin d) k => Ψ X.transpose) ∈ SB (Matrix (Fin n) (Fin d) k)

def ModelDict : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ν b : kˣ →* ℂˣ) (g : GL (Fin n) k) (h : GL (Fin d) k) (Ψ : Matrix (Fin d) (Fin n) k → ℂ)
    (X : Matrix (Fin n) (Fin d) k),
    GlobalTheory.SplitFlip.omA ν b (GlobalTheory.SplitFlip.invT g) h (fun Y => Ψ Y.transpose) X =
      (((ν * b) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * om b⁻¹ g h Ψ X.transpose

def Separates : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V), IsSmooth ρ →
    ∀ v : V, v ≠ 0 → ∃ l : smoothPart ρ.dual, (l : Module.Dual ℂ V) v ≠ 0

def PairOfLift : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ν b : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin n) k) V) (π : Representation ℂ (GL (Fin d) k) W),
    IsSmoothChar ν → IsSmoothChar b → IsSmooth π → IsLift ν b σ π → ThetaPair b⁻¹ (contra (src (ν * b) σ)) (contra π)

def SrcGood : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (c : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin n) k) V),
    IsSmoothChar c → IsUnitaryChar c → IsSmooth σ → σ.IsIrreducible → IsUnitarisable σ →
    IsSmooth (src c σ) ∧ (src c σ).IsIrreducible ∧ IsUnitarisable (src c σ)

def ContraIrr : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V), IsSmooth ρ → ρ.IsIrreducible →
    (contra ρ).IsIrreducible ∧ Nonempty (ρ.Equiv (contra (contra ρ)))

def ContraUnit : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V), IsSmooth ρ → ρ.IsIrreducible →
    IsUnitarisable ρ → IsUnitarisable (contra ρ) ∧ ∃ C : V ≃ₗ⋆[ℂ] smoothPart ρ.dual, ∀ g x, C (ρ g x) = contra ρ g (C x)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def SatContra : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion K)) V),
    IsSmooth ρ → ρ.IsIrreducible → IsUnitarisable ρ → ∀ B : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w ρ B →
      GlobalTheory.LFun.HasSatGL w (contra ρ) (B.map (·⁻¹))

def SatTwist : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) (c : (w.adicCompletion K)ˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion K)) V),
    IsUnram c → ∀ ϖ : (w.adicCompletion K)ˣ, Formalism.UG.IsUnifV K w ϖ → ∀ B : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w ρ B →
      GlobalTheory.LFun.HasSatGL w (twist ρ (detChar (Fin n) c)) (B.map (· * c ϖ))

def SatInvT : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion K)) V),
    ∀ B : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w ρ B → GlobalTheory.LFun.HasSatGL w (ρ.comp GlobalTheory.SplitFlip.invT) (B.map (·⁻¹))

def SatDet : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (t : ℕ) (c : (w.adicCompletion K)ˣ →* ℂˣ), IsUnram c → ∀ ϖ : (w.adicCompletion K)ˣ, Formalism.UG.IsUnifV K w ϖ →
    GlobalTheory.LFun.HasSatGL w (detRep (Fin t) c) (GlobalTheory.LFun.seg w (c ϖ) t)

def SatProd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin r) (w.adicCompletion K)) V) (τ : Representation ℂ (GL (Fin t) (w.adicCompletion K)) W),
    IsSmooth σ → σ.IsIrreducible → IsSmooth τ → τ.IsIrreducible → ∀ B C : Multiset ℂˣ,
      GlobalTheory.LFun.HasSatGL w σ B → GlobalTheory.LFun.HasSatGL w τ C → GlobalTheory.LFun.HasSatGL w (prod₂ σ τ) (B + C)

def SegInv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : ℂˣ) (t : ℕ), (GlobalTheory.LFun.seg w x t).map (·⁻¹) = GlobalTheory.LFun.seg w x⁻¹ t

end UpperTheory.Gal.TP.Loc

end
