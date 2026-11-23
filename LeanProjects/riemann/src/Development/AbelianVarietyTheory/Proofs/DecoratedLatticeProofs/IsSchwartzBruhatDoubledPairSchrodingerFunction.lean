import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SchwartzBruhatMixedFamilies
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateDecayRealEntries
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelSourceSupportFiniteComponentInBox
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergSupSobolevSeminormThetaLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledPairSchrodingerFunctionContinuousIntegrabStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DerivativeClosedFunctionClassSmoothAndSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchroedingerFunctionHasDerivAtRealLineDoubledPaiStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixRealSizeBoundsAlongRealParametrisatiStatement
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.SchwartzSch

variable {D : D7}

def volOf {A B : HSp D} (ν : Measure (WO A B)) (𝓨 : Set (WO A B)) (h : IsCovolOne (ratL B A) ν 𝓨) :
    GlobalTheory.Unf.VolM D B.rank A.rank := ⟨ν, 𝓨, h⟩

theorem continuous_finPart' : Continuous (finPart D) := by
  letI ti : TopologicalSpace (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E)
  obtain ⟨e, he, hec, -⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have : (finPart D : AE D → _) = fun z => (e z).2 := funext fun z => (he z).2.symm
  rw [this]
  exact continuous_snd.comp hec

variable {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {A B : HSp D} {ν : Measure (WO A B)}
  {𝓨 : Set (WO A B)} (hν : IsCovolOne (ratL B A) ν 𝓨) {f : WO (dblSp A) B → ℂ} (hf : IsThetaFunO ψ (dblSp A) B f)

include hψ hν hf

theorem sch_level : ∃ U : AddSubgroup (Mx D B.rank A.rank), IsOpen (U : Set (Mx D B.rank A.rank)) ∧
    ∀ u ∈ U, u.map (infPart D) = 0 → ∀ x, sch ψ A B ν 𝓨 f (x + u) = sch ψ A B ν 𝓨 f x := by
  obtain ⟨U, hUo, hU⟩ := hf.level
  refine ⟨U.comap ((dblDec A).extX B), ?_, ?_⟩
  · have hX : Continuous ((dblDec A).extX B) := continuous_id.matrix_mul continuous_const
    exact hUo.preimage hX
  · intro u hu h0 x
    have h0' : ((dblDec A).extX B u).map (infPart D) = 0 := by
      rw [HypDec.extX_apply, Matrix.map_mul, h0, Matrix.zero_mul]
    have h := (GlobalTheory.HeisMixSource.heis_mixS D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) (volOf ν 𝓨 hν) f hf).1 x u
    rw [hU _ hu h0'] at h
    exact (congrFun h 0).symm

theorem sch_supp : ∃ K : Set (Matrix (Fin B.rank) (Fin A.rank) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K ∧
    ∀ x, sch ψ A B ν 𝓨 f x ≠ 0 → x.map (finPart D) ∈ K := by
  obtain ⟨U, hUo, hU⟩ := hf.level
  obtain ⟨K, hK, hsupp⟩ :=
    GlobalTheory.Unf.mixS_support_inBox D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) (volOf ν 𝓨 hν) U hUo
  refine ⟨(fun k : Mx D B.rank A.rank => k.map (finPart D)) '' K,
    hK.image (continuous_id.matrix_map continuous_finPart'), ?_⟩
  intro x hx
  have hmem : f ∈ GlobalTheory.Size.thetaLevel ψ (dblSp A) B U := ⟨hf, hU⟩
  obtain ⟨k, hk, hxk⟩ := hsupp f hmem x 0 hx
  refine ⟨k, hk, ?_⟩
  have hs : (x - k).map (finPart D) = x.map (finPart D) - k.map (finPart D) :=
    Matrix.map_sub _ (fun a b => (finPart D).map_sub a b) x k
  rw [hs, sub_eq_zero] at hxk
  exact hxk.symm

theorem sch_schwartz (k : ℕ) (L : (Fin k → ℝ) →+ Mx D B.rank A.rank) (hL : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsRealParam L)
    (hinj : Function.Injective L) (x : Mx D B.rank A.rank) :
    ∃ g : SchwartzMap (Fin k → ℝ) ℂ, ∀ t, g t = sch ψ A B ν 𝓨 f (x + L t) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  let V : Set ((Fin k → ℝ) → ℂ) :=
    {φ | ∃ f', IsThetaFunO ψ (dblSp A) B f' ∧ φ = fun t => sch ψ A B ν 𝓨 f' (x + L t)}
  have hcont : ∀ φ ∈ V, Continuous φ := by
    rintro φ ⟨f', hf', rfl⟩
    exact (GlobalTheory.T.doubledPairSchrodingerFunction_continuous_integrable D ψ hψ A B ν 𝓨 hν f' hf').1.comp (continuous_const.add hL.1)
  have hder : ∀ φ ∈ V, ∀ i : Fin k, ∃ φ' ∈ V, ∀ t : Fin k → ℝ,
      HasDerivAt (fun s : ℝ => φ (t + s • (Pi.single i (1 : ℝ) : Fin k → ℝ))) (φ' t) 0 := by
    rintro φ ⟨f', hf', rfl⟩ i
    let M : ℝ →+ Mx D B.rank A.rank :=
      { toFun := fun s => L (s • (Pi.single i (1 : ℝ) : Fin k → ℝ))
        map_zero' := by rw [zero_smul, map_zero]
        map_add' := fun a b => by rw [add_smul, map_add] }
    have hMc : Continuous M := hL.1.comp (continuous_id.smul continuous_const)
    have hMf : ∀ s, (M s).map (finPart D) = 0 := fun s => hL.2 _
    obtain ⟨f'', hf'', hd⟩ := GlobalTheory.T.schroedingerFunction_hasDerivAt_real_line_doubledPair D ψ hψ A B ν 𝓨 hν f' hf' M hMc hMf
    refine ⟨fun t => sch ψ A B ν 𝓨 f'' (x + L t), ⟨f'', hf'', rfl⟩, fun t => ?_⟩
    have h := hd (x + L t)
    have he : (fun s : ℝ => sch ψ A B ν 𝓨 f' (x + L (t + s • (Pi.single i (1 : ℝ) : Fin k → ℝ)))) =
        fun s : ℝ => sch ψ A B ν 𝓨 f' (x + L t + M s) := by
      funext s
      simp only [map_add, add_assoc]
      rfl
    simp only at h ⊢
    rw [he]
    exact h
  have hdecay : ∀ φ ∈ V, ∀ N : ℕ, ∃ C : ℝ, ∀ t, ‖t‖ ^ N * ‖φ t‖ ≤ C := by
    rintro φ ⟨f', hf', rfl⟩ N
    obtain ⟨C₁, hC₁⟩ := (GlobalTheory.T.adelicMatrixRealSize_bounds_along_real_parametrisation D θ hθ B.rank A.rank k L hL).2 hinj
    obtain ⟨C₂, hC₂⟩ :=
      GlobalTheory.Unf.mixS_decay D ψ hψ θ hθ (dblSp A) (zeroSp D) B A.rank (dblDec A) (volOf ν 𝓨 hν) N
    have hfin := (GlobalTheory.Unf.SupFin.supSob_laws D ψ hψ θ hθ (dblSp A) B).1 N f' hf'
    have hne : (C₂ : ℝ≥0∞) * GlobalTheory.Unf.supSob ψ θ N f' ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hfin
    set c : ℝ := |C₁| * (1 + GlobalTheory.Unf.realSize θ x) with hc
    have hc0 : 0 ≤ c := mul_nonneg (abs_nonneg _) (by linarith [GlobalTheory.Unf.realSize_nonneg θ x])
    clear_value c
    refine ⟨c ^ N * ((C₂ : ℝ≥0∞) * GlobalTheory.Unf.supSob ψ θ N f').toReal, fun t => ?_⟩
    have hy0 := GlobalTheory.Unf.realSize_nonneg θ (x + L t)
    have hx0 := GlobalTheory.Unf.realSize_nonneg θ x
    have h1 : ‖t‖ ≤ c * (1 + GlobalTheory.Unf.realSize θ (x + L t)) := by
      calc ‖t‖ ≤ C₁ * (GlobalTheory.Unf.realSize θ (x + L t) + GlobalTheory.Unf.realSize θ x) := hC₁ x t
        _ ≤ |C₁| * (GlobalTheory.Unf.realSize θ (x + L t) + GlobalTheory.Unf.realSize θ x) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
        _ ≤ |C₁| * ((1 + GlobalTheory.Unf.realSize θ x) * (1 + GlobalTheory.Unf.realSize θ (x + L t))) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _)
        _ = c * (1 + GlobalTheory.Unf.realSize θ (x + L t)) := by rw [hc]; ring
    have h2 : ‖sch ψ A B ν 𝓨 f' (x + L t)‖ * (1 + GlobalTheory.Unf.realSize θ (x + L t)) ^ N ≤
        ((C₂ : ℝ≥0∞) * GlobalTheory.Unf.supSob ψ θ N f').toReal := by
      have h := hC₂ f' hf' (x + L t) 0
      change ‖sch ψ A B ν 𝓨 f' (x + L t)‖ₑ * _ ≤ _ at h
      rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)] at h
      exact (ENNReal.ofReal_le_iff_le_toReal hne).1 h
    calc ‖t‖ ^ N * ‖sch ψ A B ν 𝓨 f' (x + L t)‖
        ≤ (c * (1 + GlobalTheory.Unf.realSize θ (x + L t))) ^ N * ‖sch ψ A B ν 𝓨 f' (x + L t)‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) h1 N) (norm_nonneg _)
      _ = c ^ N * (‖sch ψ A B ν 𝓨 f' (x + L t)‖ * (1 + GlobalTheory.Unf.realSize θ (x + L t)) ^ N) := by
          generalize ‖sch ψ A B ν 𝓨 f' (x + L t)‖ = a
          generalize GlobalTheory.Unf.realSize θ (x + L t) = s
          rw [mul_pow]; ring
      _ ≤ c ^ N * ((C₂ : ℝ≥0∞) * GlobalTheory.Unf.supSob ψ θ N f').toReal :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hc0 N)
  have hS := (GlobalTheory.T.derivativeClosedFunctionClass_smooth_and_schwartz k V hcont hder).2 hdecay _ ⟨f, hf, rfl⟩
  exact hS

omit hψ hν hf in

theorem isSchwartzBruhat_sch : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 →
    ∀ f, IsThetaFunO ψ (dblSp A) B f → GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat (sch ψ A B ν 𝓨 f) := by
  intro D ψ hψ A B ν 𝓨 hν f hf
  exact ⟨sch_level hψ hν hf, sch_supp hψ hν hf, fun k L hL hinj x => sch_schwartz hψ hν hf k L hL hinj x⟩

end GlobalTheory.SchwartzSch
