import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatTuple
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SchwartzBruhatEqSumPure
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterArchimedeanFormStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl

theorem exists_cube_subset_of_mem_nhds_zero {ι X : Type*} [Finite ι] [TopologicalSpace X] [Zero X]
    {V : Set (ι → X)} (hV : V ∈ nhds (0 : ι → X)) :
    ∃ W ∈ nhds (0 : X), ∀ Y : ι → X, (∀ i, Y i ∈ W) → Y ∈ V := by
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, -, t, ht, hsub⟩ := hV
  refine ⟨⋂ i, t i, Filter.iInter_mem.mpr (fun i => by simpa using ht i), fun Y hY => hsub ?_⟩
  intro i _
  exact Set.mem_iInter.mp (hY i) i

theorem latN_small : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ),
    ∀ U ∈ nhds (0 : Fin n → Fin M → Af F ⊗[F] E), ∃ N : ℕ, 0 < N ∧
      (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) ⊆ U := by
  intro F E _ _ _ _ _ σ _ d b n M U hU
  let bb := Algebra.TensorProduct.basis (Af F) b
  obtain ⟨W1, hW1, hW1U⟩ := exists_cube_subset_of_mem_nhds_zero hU
  obtain ⟨W, hW, hWW1⟩ := exists_cube_subset_of_mem_nhds_zero hW1
  have hcont : Continuous (fun c : Fin d → Af F => ∑ k, c k • bb k) :=
    continuous_finsetSum _ (fun k _ => (continuous_apply k).smul continuous_const)
  have hV : (fun c : Fin d → Af F => ∑ k, c k • bb k) ⁻¹' W ∈ nhds (0 : Fin d → Af F) := by
    apply hcont.continuousAt.preimage_mem_nhds
    simpa using hW
  obtain ⟨V0, hV0, hV0V⟩ := exists_cube_subset_of_mem_nhds_zero hV
  obtain ⟨-, -, -, -, -, -, -, hN, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨N, hNpos, hNV0⟩ := hN V0 hV0
  refine ⟨N, hNpos, fun X hX => hW1U X fun a => hWW1 (X a) fun i => ?_⟩
  have hXai : InNOh b N (X a i) :=
    (show ∀ (a : Fin n) (i : Fin M), InNOh b N (X a i) from hX) a i
  have hmem : (⇑(bb.repr (X a i))) ∈ (fun c : Fin d → Af F => ∑ k, c k • bb k) ⁻¹' W := by
    apply hV0V
    intro k
    obtain ⟨y, hy, hk⟩ := hXai k
    rw [hk]
    exact hNV0 y hy
  simp only [Set.mem_preimage] at hmem
  rwa [bb.sum_repr] at hmem

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
