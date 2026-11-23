import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin

theorem not_isUnit_natCast_prime_ringOfIntegers (K : Type*) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    ¬ IsUnit ((p : ℕ) : 𝓞 K) := by
  intro h
  have h1 : IsUnit (algebraMap ℤ (𝓞 K) (p : ℤ)) := by simpa using h
  have h2 : IsUnit (p : ℤ) := (isUnit_map_iff (algebraMap ℤ (𝓞 K)) _).1 h1
  exact (Nat.prime_iff_prime_int.1 hp).not_unit h2

theorem exists_prime_bar_piG (D : D7) (EX : ErrX D) (i : Fin 2) :
    ∃ P : HeightOneSpectrum (𝓞 D.host.K), ((D.host.g i : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal ∧
      barE D (EX.piG i) ∈ P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := by
  set x := toOK (EX.piG i) (EX.piG_K i)
  set y := toOK (barE D (EX.piG i)) (barE_piG_mem EX i)
  have hxy : y * x = ((D.host.g i : ℕ) : 𝓞 D.host.K) := by
    apply FaithfulSMul.algebraMap_injective (𝓞 D.host.K) (𝓞 D.host.E)
    rw [map_mul, map_natCast, algebraMap_toOK, algebraMap_toOK, mul_comm]
    exact piG_mul_barE EX i
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, zero_mul] at hxy
    exact (D.host.g_prime i).ne_zero (Nat.cast_eq_zero.mp hxy.symm)
  have hyu : ¬ IsUnit y := by
    intro h
    have u2 : IsUnit (barE D (EX.piG i)) := by
      have := h.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))
      rwa [algebraMap_toOK] at this
    have u1 : IsUnit (EX.piG i) := by
      have := u2.map (barE D)
      rwa [barE_barE] at this
    have u3 : IsUnit ((D.host.g i : ℕ) : 𝓞 D.host.E) := by
      rw [← piG_mul_barE EX i]; exact u1.mul u2
    exact not_isUnit_natCast_prime_ringOfIntegers D.host.E (D.host.g_prime i) u3
  obtain ⟨M, hM, hyM⟩ := Ideal.exists_le_maximal (Ideal.span {y}) (by
    rw [Ne, Ideal.span_singleton_eq_top]; exact hyu)
  have hmem : y ∈ M := hyM (Ideal.mem_span_singleton_self y)
  refine ⟨⟨M, hM.isPrime, fun h => hy0 (by simpa [h] using hmem)⟩, ?_, ?_⟩
  · rw [← hxy]; exact M.mul_mem_right x hmem
  · have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) hmem
    rwa [algebraMap_toOK] at this

end GlobalTheory.FinalJoin
