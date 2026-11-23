import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TensorFirstFactorIntegersOntoLocalIntegersStatement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem locSp_eq_image : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} (A : LocAt F E n G), SplAlg A → LocInt A → ∀ v (Λ : Submodule (𝓞 E) (Fin n → E)) (z' : Fin n → G.P.Qq v), z' ∈ locSp (G.P.W v) (A.iw v) Λ ↔ ∃ z ∈ latS (F := F) ((A.pl v).1.adicCompletion F) (intV E (A.pl v).1) Λ, ∀ k, (A.eQ v).symm (A.ph v (z k)) = z' k := by
  intro F E _ _ _ _ _ n p G A hS hI v Λ z'
  have hph := GlobalTheory.T.tensor_first_factor_integers_onto_local_integers A hS v
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      refine ⟨fun k => inclE (F := F) _ (x k), Submodule.subset_span ⟨x, hx, rfl⟩, fun k => ?_⟩
      rfl
    | zero => exact ⟨0, Submodule.zero_mem _, fun k => by simp⟩
    | add y₁ y₂ _ _ h₁ h₂ =>
      obtain ⟨z₁, hz₁, e₁⟩ := h₁
      obtain ⟨z₂, hz₂, e₂⟩ := h₂
      refine ⟨z₁ + z₂, Submodule.add_mem _ hz₁ hz₂, fun k => ?_⟩
      simp [e₁ k, e₂ k]
    | smul w y _ h =>
      obtain ⟨z, hz, e⟩ := h
      have hw : A.eQ v (algebraMap (G.P.W v) (G.P.Qq v) w) ∈ (A.pl v).1.adicCompletionIntegers F :=
        (hI v _).1 ⟨w, rfl⟩
      obtain ⟨s, hs, hse⟩ := hph.2 _ hw
      refine ⟨(⟨s, hs⟩ : intV E (A.pl v).1) • z, Submodule.smul_mem _ _ hz, fun k => ?_⟩
      show (A.eQ v).symm (A.ph v (s * z k)) = (w • y) k
      rw [map_mul, hse, map_mul, e k, RingEquiv.symm_apply_apply, Pi.smul_apply, Algebra.smul_def]
  · rintro ⟨z, hz, hzz⟩
    have key : ∀ z ∈ latS (F := F) ((A.pl v).1.adicCompletion F) (intV E (A.pl v).1) Λ,
        (fun k => (A.eQ v).symm (A.ph v (z k))) ∈ locSp (G.P.W v) (A.iw v) Λ := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero =>
        have h0 := Submodule.zero_mem (locSp (G.P.W v) (A.iw v) Λ)
        convert h0 using 1
        funext k
        simp
      | add y₁ y₂ _ _ h₁ h₂ =>
        have := Submodule.add_mem _ h₁ h₂
        simpa [Pi.add_def] using this
      | smul s y _ h =>
        obtain ⟨w, hw⟩ := (hI v ((A.eQ v).symm (A.ph v s))).2 (by simpa using hph.1 s.1 s.2)
        have := Submodule.smul_mem _ w h
        convert this using 1
        funext k
        show (A.eQ v).symm (A.ph v (s.1 * y k)) = _
        rw [Pi.smul_apply, Algebra.smul_def, hw, map_mul, map_mul]
    have := key z hz
    convert this using 1
    funext k
    exact (hzz k).symm

end GlobalTheory.TwV
