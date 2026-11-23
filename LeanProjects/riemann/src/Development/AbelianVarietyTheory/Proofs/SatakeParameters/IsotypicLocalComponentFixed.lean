import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PadicIntGLSmulMemPrincipalCongruenceFixed
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicPartSpannedBySplitPlaceLocalComponent
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntertwiningFunctional
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT Formalism.L2.Host NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SepLoc

theorem exists_sep {K F V : Type*} [AddCommGroup F] [Module ℂ F] [AddCommGroup V] [Module ℂ V]
    (r : K → F →ₗ[ℂ] F) (ρ : K → V →ₗ[ℂ] V)
    (hirr : ∀ W : Submodule ℂ V, (∀ k, ∀ v ∈ W, ρ k v ∈ W) → W = ⊥ ∨ W = ⊤)
    (P : (V →ₗ[ℂ] F) → Prop) (hP : ∀ T, P T → ∀ k v, T (ρ k v) = r k (T v))
    (f : F) (hf : f ∈ ⨆ (T : V →ₗ[ℂ] F) (_ : P T), LinearMap.range T) (hf0 : f ≠ 0) :
    ∃ φ : F →ₗ[ℂ] V, φ f ≠ 0 ∧ ∀ k, ∀ f' ∈ ⨆ (T : V →ₗ[ℂ] F) (_ : P T), LinearMap.range T,
      φ (r k f') = ρ k (φ f') := by
  first
  | exact @_root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional
  | exact _root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional
  | (apply _root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional ..)

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), GlobalTheory.HeightCounting.IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → ∃ φ : (GAf L n → a.W) →ₗ[ℂ] σ.V, φ f ≠ 0 ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ f' ∈ NG.isoTyp a.ρ S, φ (NG.rt L n x f') = σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) (φ f') := by
  intro L _ _ _ n a S hS s σ hloc c hc hcL f hf hf0
  have hle := GlobalTheory.SpanLoc.main L n a S hS s σ hloc c hc hcL
  have hirr : ∀ W : Submodule ℂ σ.V, (∀ k : {x : GAf L n // TrivOutside {s.v} x}, ∀ v ∈ W,
      σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n k.1)) v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    let R : Subrepresentation σ.ρ := ⟨W, fun g v hv => by
      obtain ⟨x, hx, hxe⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s
        (Matrix.GeneralLinearGroup.map c.symm.toRingHom g)
      have hg : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = g := by
        rw [hxe]; ext i j; simp
      have := hW ⟨x, hx⟩ v hv
      rwa [hg] at this⟩
    haveI := σ.irr
    rcases eq_bot_or_eq_top R with h | h
    · left; exact congrArg Subrepresentation.toSubmodule h
    · right; exact congrArg Subrepresentation.toSubmodule h
  obtain ⟨φ, hφf, hφ⟩ := exists_sep (K := {x : GAf L n // TrivOutside {s.v} x}) (fun k => NG.rt L n k.1)
    (fun k => σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n k.1))) hirr
    (fun (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) => (∀ v, T v ∈ NG.AFall L n a.ρ) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v,
      T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v))
    (fun T hT k v => hT.2 k.1 k.2 v) f (hle hf) hf0
  exact ⟨φ, hφf, fun x hx f' hf' => hφ ⟨x, hx⟩ f' (hle hf')⟩

end GlobalTheory.SepLoc
