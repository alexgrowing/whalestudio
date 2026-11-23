import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteAdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.GA
open scoped NumberField.AdeleRing Classical

namespace GlobalTheory.CompanionTheory.Adelic

theorem exists_integer_of_mem_integralFiniteAdeles (K : Type) [Field K] [NumberField K] (x : K)
    (hx : algebraMap K (FiniteAdeleRing (𝓞 K) K) x ∈ integralFiniteAdeles (𝓞 K) K) :
    ∃ a : 𝓞 K, (a : K) = x := by
  have hv : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K x ≤ 1 := by
    intro v
    have h : Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) x) v) ≤ 1 :=
      mem_integralFiniteAdeles.1 hx v
    have h2 : Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) x) v) = v.valuation K x :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
    rwa [h2] at h
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K x hv
  exact ⟨a, ha⟩

end GlobalTheory.CompanionTheory.Adelic
