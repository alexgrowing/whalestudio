import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordForm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAdelicHaarCovolumeOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualProdIff
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.MatInt

theorem algebraMap_mem_integers_of_not_mem_support (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (a : F) (h : v ∉ HeightOneSpectrum.Support (𝓞 F) a) :
    algebraMap F (Fv F v) a ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have e : Valued.v (algebraMap F (Fv F v) a) = v.valuation F a :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a
  rw [e]
  simpa [HeightOneSpectrum.Support] using h

theorem mulVec_mem_integers (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    (v : HeightOneSpectrum (𝓞 F)) (B : Matrix ι ι (Fv F v)) (y : ι → Fv F v)
    (hB : ∀ i j, B i j ∈ v.adicCompletionIntegers F)
    (hy : ∀ i, y i ∈ v.adicCompletionIntegers F) (i : ι) :
    B.mulVec y i ∈ v.adicCompletionIntegers F := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => mul_mem (hB i j) (hy j)

theorem exists_finset_mulVec_integral_iff : ∀ (F : Type) [Field F] [NumberField F] (ι : Type)
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 →
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ v, v ∉ T → ∀ x : ι → Fv F v,
      (∀ i, (A.map (algebraMap F (Fv F v))).mulVec x i ∈ v.adicCompletionIntegers F) ↔
        ∀ i, x i ∈ v.adicCompletionIntegers F := by
  intro F _ _ ι _ _ A hA
  classical
  have hfin : ∀ a : F, (HeightOneSpectrum.Support (𝓞 F) a).Finite :=
    HeightOneSpectrum.Support.finite (𝓞 F)
  refine ⟨Finset.univ.biUnion fun p : ι × ι =>
    (hfin (A p.1 p.2)).toFinset ∪ (hfin (A⁻¹ p.1 p.2)).toFinset, fun v hv x => ?_⟩
  have hout : ∀ i j, v ∉ HeightOneSpectrum.Support (𝓞 F) (A i j) ∧
      v ∉ HeightOneSpectrum.Support (𝓞 F) (A⁻¹ i j) := by
    intro i j
    constructor
    · intro h
      exact hv (Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _,
        Finset.mem_union_left _ ((hfin _).mem_toFinset.2 h)⟩)
    · intro h
      exact hv (Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _,
        Finset.mem_union_right _ ((hfin _).mem_toFinset.2 h)⟩)
  have hinv : (A⁻¹.map (algebraMap F (Fv F v))) * (A.map (algebraMap F (Fv F v))) = 1 := by
    have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hA
    have h1 := congrArg (fun M : Matrix ι ι F => M.map (algebraMap F (Fv F v)))
      (Matrix.nonsing_inv_mul A hu)
    simpa [Matrix.map_mul] using h1
  constructor
  · intro h i
    have e : (A⁻¹.map (algebraMap F (Fv F v))).mulVec
        ((A.map (algebraMap F (Fv F v))).mulVec x) = x := by
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    rw [← e]
    exact mulVec_mem_integers F ι v _ _
      (fun i j => algebraMap_mem_integers_of_not_mem_support F v _ (hout i j).2) h i
  · intro h i
    exact mulVec_mem_integers F ι v _ _
      (fun i j => algebraMap_mem_integers_of_not_mem_support F v _ (hout i j).1) h i

end GlobalTheory.CompanionTheory.MatInt
