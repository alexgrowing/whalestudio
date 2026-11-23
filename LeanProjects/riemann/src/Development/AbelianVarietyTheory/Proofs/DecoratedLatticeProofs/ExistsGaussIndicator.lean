import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.FirstClauseRankZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardUnitaryChartDoubledSpace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParameters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsHeckeCharRestrictionEtaInv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSiegelParabolicConjDoubledCompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryHeightIsSiegelHeightFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumTransportSchwartzBruhatStandardStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerStandardLeviActionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerSiegelUnipotentActionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylFormulaStandardUnitaryGroupWeilDatumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaFunNeZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.Inhab

theorem exists_gauss_indicator (D : D7) (θ : InfFam D) (A B : HSp D) (l : D.what₂.Tau → ℝ) (hl : ∀ τ, l τ ≠ 0)
    (s : D.what₂.Tau → Matrix (Fin B.rank) (Fin B.rank) ℂ) (hs : ∀ τ, IsCartanInv (gramAt D B τ) (s τ)) :
    ∃ Φ : schwartzA θ B.rank A.rank, Φ.1 ∈ fockA θ B A.rank l s ∧ Φ.1 0 ≠ 0 := by
  classical
  obtain ⟨f, hf⟩ := GlobalTheory.T.gaussian_is_schwartz_function D A.rank B l hl s hs
  let W : AddSubgroup (Matrix (Fin B.rank) (Fin A.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) :=
    { carrier := {a | ∀ i j, a i j ∈ intAE D}
      add_mem' := fun ha hb i j => (intAE D).add_mem (ha i j) (hb i j)
      zero_mem' := fun _ _ => (intAE D).zero_mem
      neg_mem' := fun ha i j => (intAE D).neg_mem (ha i j) }
  have hWe : (W : Set (Matrix (Fin B.rank) (Fin A.rank) (Af D.host.F ⊗[D.host.F] D.host.E))) =
      ⋂ i, ⋂ j, (fun a : Matrix (Fin B.rank) (Fin A.rank) (Af D.host.F ⊗[D.host.F] D.host.E) => a i j) ⁻¹'
        (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
    ext a
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rfl
  have hWo : IsOpen (W : Set (Matrix (Fin B.rank) (Fin A.rank) (Af D.host.F ⊗[D.host.F] D.host.E))) := by
    rw [hWe]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i))
  have hWc : IsCompact (W : Set (Matrix (Fin B.rank) (Fin A.rank) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D
  let g : (Fin B.rank → Fin A.rank → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun a =>
    if (QuotientAddGroup.mk (show Matrix (Fin B.rank) (Fin A.rank) _ from a) : _ ⧸ W) = 0 then (1 : ℂ) else 0
  have hg : g ∈ GlobalTheory.WeilM.SB (Fin B.rank → Fin A.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
    GlobalTheory.SchwartzBruhatTensor.coset_mem_SB W hWo hWc 0
  let φ : Mx D B.rank A.rank → ℂ := fun x =>
    f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))
  have hφ : φ ∈ schwartzA θ B.rank A.rank := Submodule.subset_span ⟨f, g, hg, rfl⟩
  refine ⟨⟨φ, hφ⟩, ?_, ?_⟩
  · refine Submodule.subset_span ⟨1, g, hg, ?_⟩
    funext x
    simp only [φ, hf, evalPoly, map_one, one_mul]
    rfl
  · show f _ * g _ ≠ 0
    rw [hf]
    simp [g, gauss, compAt]
    exact (QuotientAddGroup.eq_zero_iff (N := W) (0 : Matrix (Fin B.rank) (Fin A.rank) _)).2 W.zero_mem

theorem hypotheses_inhabited : ∀ (D : D7) (A B : HSp D), ∃ (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (m : Measure (Mx D B.rank A.rank)) (𝓕 : Set (Mx D B.rank A.rank)) (omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank)) (H : G D A.rank → ℝ≥0) (l : D.what₂.Tau → ℝ) (s : RealMat B) (Φ : schwartzA θ B.rank A.rank), IsCharAF D.host.F ψ ∧ IsHeckeChar D χ ∧ ResEta D χ B.rank ∧ IsInfFam θ ∧ IsCovolOne (ratMx D B.rank A.rank) m 𝓕 ∧ IsWeilSch ψ χ θ B m omS ∧ IsHeight H ∧ HasRealPar ψ θ l ∧ (∀ τ, IsCartanInv (gramAt D B τ) (s τ)) ∧ Φ.1 ∈ fockA θ B A.rank l s ∧ Φ.1 0 ≠ 0 := by
  intro D A B
  obtain ⟨-, ψ₀, χB, omh, -, ν, 𝓨, -, hω, -, -, hν⟩ :=
    GlobalTheory.SiegelFormula.Model.data_exist GlobalTheory.weilRepresentationUnitaryPair A B
  obtain ⟨θ, hθ⟩ := hω.std.2.1
  obtain ⟨μ, hμ, hp⟩ := GlobalTheory.T.exists_siegel_parabolic_conj_doubled_compact D
  obtain ⟨κ, hκ⟩ := GlobalTheory.StdUnn.chart_exists D A μ hμ
  obtain ⟨a, ha⟩ := exists_isMaj A
  obtain ⟨p, hpc⟩ := hp A a ha κ hκ
  obtain ⟨omS, hT⟩ := GlobalTheory.T.exists_weilDatum_transport_schwartzBruhat_standard D ψ₀ A B χB omh hω ν 𝓨 hν θ hθ κ
  obtain ⟨lam, hlam, hψ, l, hl, hla⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hω.std θ hθ μ hμ
  obtain ⟨hχ1, hχ2⟩ := GlobalTheory.StdUnn.isHeckeChar_resEta_inv D χB B.rank hω.hecT hω.resT
  have hc : ∀ τ, ∃ s, IsCartanInv (gramAt D B τ) s := fun τ =>
    GlobalTheory.Mem.ThetaNonzero.exists_isCartanInv (GlobalTheory.SmoothForms.RealPts.gramAt_herm B τ)
      (GlobalTheory.SmoothForms.RealPts.gramAt_unit B τ)
  choose s hs using hc
  have hl0 : ∀ τ, l τ ≠ 0 := fun τ h => by
    have e := hla τ
    rw [h, abs_zero] at e
    have h1 : tauE D τ D.host.xi0 ≠ 0 := (map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
    have h2 : tauE D τ μ ≠ 0 := (map_ne_zero _).2 hμ.1
    exact div_ne_zero (norm_ne_zero_iff.2 h1) (norm_ne_zero_iff.2 h2) e.symm
  obtain ⟨Φ, hΦ, hΦ0⟩ := exists_gauss_indicator D θ A B l hl0 s hs
  refine ⟨shift ψ₀ lam, χB⁻¹, θ, ν, 𝓨, omS, hgtStd A a κ p, l, s, Φ, hψ, hχ1, hχ2, hθ, hν, ⟨?_, ?_, ?_⟩,
    GlobalTheory.T.standardUnitaryHeight_isSiegelHeightFunction D A μ hμ κ hκ a p hpc, hl, hs, hΦ, hΦ0⟩
  · exact GlobalTheory.T.transportedSchrodinger_standardLeviAction D ψ₀ A B χB omh hω ν 𝓨 hν θ hθ μ hμ κ hκ omS hT lam hlam
  · exact GlobalTheory.T.transportedSchrodinger_siegelUnipotentAction D ψ₀ A B χB omh hω ν 𝓨 hν θ hθ μ hμ κ hκ omS hT lam hlam
  · exact GlobalTheory.T.weyl_formula_standardUnitaryGroup_weilDatum D ψ₀ A B χB omh hω ν 𝓨 hν θ hθ μ hμ κ hκ omS hT lam hlam

end GlobalTheory.StdUnn.Inhab

end
