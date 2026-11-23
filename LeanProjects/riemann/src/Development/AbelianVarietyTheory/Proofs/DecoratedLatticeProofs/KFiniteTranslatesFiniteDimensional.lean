import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.FinDim

variable {D : D7}

theorem frameInv_eq_one {θ : InfFam D} {A : HSp D} {cA : CptF A} {a : GL (Fin A.rank) (AE D)} (hD : Defin θ A cA a)
    (τ : D.what₂.Tau) : frameInv θ A a τ = 1 := by
  have h := hD.maj_eq τ
  rw [Matrix.mul_one] at h
  rw [frameInv, Matrix.mul_assoc]
  exact mul_eq_one_comm.1 h

theorem isOpen_Kmax {θ : InfFam D} {A : HSp D} {cA : CptF A} {a : GL (Fin A.rank) (AE D)} (hD : Defin θ A cA a) :
    IsOpen (Kmax A a : Set (GA D A)) := by
  have e : (Kmax A a : Set (GA D A)) = levelOpen D.sp.cm.sig A.gram (frameLat A) := by
    ext g
    rw [SetLike.mem_coe, hD.maj.mem_Kmax_iff hD.inf, SetLike.mem_coe]
    simp [frameInv_eq_one hD]
  rw [e]
  exact isOpen_levelOpen _ _ _

end GlobalTheory.Core.Rk.FinDim

namespace GlobalTheory.Core.Rk.FinDim

theorem finiteDimensional_span_io : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → ∀ (W : HSp D) (χ : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) W), IsWeilDatumO ψ (dblSp A) W 1 χ omh → ∀ φ, IsKFinVec omh (Khat A a) φ → ∀ K : Set (GA D A), IsCompact K → FiniteDimensional ℂ (Submodule.span ℂ {f : WO (dblSp A) W → ℂ | ∃ g₁ ∈ K, ∃ g₂ ∈ K, f = omh (io A (g₁, g₂), 1) φ}) := by
  intro D ψ θ A cA a hD W χ omh _ φ hφ K hK
  set V₀ := Submodule.span ℂ {f : WO (dblSp A) W → ℂ | ∃ k ∈ Khat A a, f = omh (k, 1) φ} with hV₀
  haveI : FiniteDimensional ℂ V₀ := hφ
  have hU : ∀ x : GA D A, IsOpen {y : GA D A | x⁻¹ * y ∈ Kmax A a} := fun x =>
    (isOpen_Kmax hD).preimage (continuous_const.mul continuous_id)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : GA D A => {y : GA D A | x⁻¹ * y ∈ Kmax A a}) hU
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simp⟩)
  have hcov : ∀ g ∈ K, ∃ x ∈ t, ∃ k ∈ Kmax A a, g = x * k := by
    intro g hg
    obtain ⟨x, hx, hgx⟩ := Set.mem_iUnion₂.1 (ht hg)
    exact ⟨x, hx, x⁻¹ * g, hgx, by group⟩
  let S : Submodule ℂ (WO (dblSp A) W → ℂ) :=
    ⨆ p : {x // x ∈ t} × {x // x ∈ t}, V₀.map (omh (io A ((p.1 : GA D A), (p.2 : GA D A)), 1))
  haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_iSup _
  refine Submodule.finiteDimensional_of_le (Submodule.span_le.2 ?_ : _ ≤ S)
  rintro f ⟨g₁, hg₁, g₂, hg₂, rfl⟩
  obtain ⟨x₁, hx₁, k₁, hk₁, rfl⟩ := hcov g₁ hg₁
  obtain ⟨x₂, hx₂, k₂, hk₂, rfl⟩ := hcov g₂ hg₂
  have e : omh (io A (x₁ * k₁, x₂ * k₂), 1) φ = omh (io A (x₁, x₂), 1) (omh (io A (k₁, k₂), 1) φ) := by
    have : ((io A (x₁ * k₁, x₂ * k₂), (1 : GA D W)) : GA D (dblSp A) × GA D W) =
        (io A (x₁, x₂), 1) * (io A (k₁, k₂), 1) := by
      rw [Prod.mk_mul_mk, ← map_mul, Prod.mk_mul_mk, mul_one]
    rw [this, map_mul, Module.End.mul_apply]
  rw [SetLike.mem_coe, e]
  refine (Submodule.mem_iSup_of_mem (⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩ : {x // x ∈ t} × {x // x ∈ t}) ?_)
  exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨_, (io_mem_Khat A a).2 ⟨hk₁, hk₂⟩, rfl⟩)

end GlobalTheory.Core.Rk.FinDim

end
