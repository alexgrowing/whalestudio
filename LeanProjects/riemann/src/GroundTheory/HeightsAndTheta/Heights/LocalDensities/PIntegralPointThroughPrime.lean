import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsIntegralPoint
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsClosedPointGenericFibre
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsIntegralPointAlgebraic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open IsDedekindDomain NumberField

theorem exists_maximal_of_fibre (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R]
    [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] (v : HeightOneSpectrum (𝓞 F)) (P : Ideal R)
    (u : R) (hP : P.IsPrime) (hPv : P.comap (algebraMap (𝓞 F) R) = v.asIdeal) (hu : u ∉ P) :
    ∃ M : Ideal R, M.IsMaximal ∧ P ≤ M ∧ u ∉ M := by
  have hc : (P.comap (algebraMap (𝓞 F) R)).IsMaximal := hPv ▸ v.isMaximal
  let : Field (𝓞 F ⧸ P.comap (algebraMap (𝓞 F) R)) := Ideal.Quotient.field _
  have : Algebra.FiniteType (𝓞 F) (R ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ (𝓞 F) P)
      (Ideal.Quotient.mkₐ_surjective (𝓞 F) P)
  have : Algebra.FiniteType (𝓞 F ⧸ P.comap (algebraMap (𝓞 F) R)) (R ⧸ P) :=
    Algebra.FiniteType.of_restrictScalars_finiteType (𝓞 F) _ _
  have : IsJacobsonRing (R ⧸ P) :=
    isJacobsonRing_of_finiteType (A := 𝓞 F ⧸ P.comap (algebraMap (𝓞 F) R))
  have hbot : (⊥ : Ideal (R ⧸ P)).jacobson = ⊥ :=
    isJacobsonRing_iff_prime_eq.1 inferInstance ⊥ Ideal.isPrime_bot
  have hu' : Ideal.Quotient.mk P u ∉ (⊥ : Ideal (R ⧸ P)).jacobson := by
    rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact hu
  rw [Ideal.jacobson, Ideal.mem_sInf] at hu'
  push Not at hu'
  obtain ⟨J, ⟨-, hJ⟩, huJ⟩ := hu'
  refine ⟨J.comap (Ideal.Quotient.mk P),
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective, ?_, huJ⟩
  intro a ha
  rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
  exact J.zero_mem

theorem IntegralPointThroughPrime.proof (h₁ : ClosedPointOfGenericFibre.Statement)
    (h₂ : IntegralPointOfAlgebraicDomain.Statement) : IntegralPointThroughPrime.Statement := by
  intro F _ _ R _ _ _ _ _ v P u g ⟨hP, hPv, hu, hg⟩
  obtain ⟨M, hM, hPM, huM⟩ := exists_maximal_of_fibre F R v P u hP hPv hu
  have hMv : M.comap (algebraMap (𝓞 F) R) = v.asIdeal :=
    ((v.isMaximal.eq_of_le (Ideal.IsPrime.comap (algebraMap (𝓞 F) R) (hK := hM.isPrime)).ne_top
      (hPv ▸ Ideal.comap_mono hPM))).symm
  obtain ⟨Q, hQ, hQM, hQ0, hgQ, hQalg⟩ := h₁ F R M g ⟨hM, hg⟩
  have := hQ
  have : Algebra.FiniteType (𝓞 F) (R ⧸ Q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ (𝓞 F) Q)
      (Ideal.Quotient.mkₐ_surjective (𝓞 F) Q)
  set M' : Ideal (R ⧸ Q) := M.map (Ideal.Quotient.mk Q)
  have hcomap : M'.comap (Ideal.Quotient.mk Q) = M := by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.2 hQM]
  have hM' : M'.IsMaximal := hM.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hQM)
  have hq : algebraMap (𝓞 F) (R ⧸ Q) = (Ideal.Quotient.mk Q).comp (algebraMap (𝓞 F) R) := rfl
  have hinj : Function.Injective (algebraMap (𝓞 F) (R ⧸ Q)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hq, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
      ← Ideal.mem_comap, hQ0, Ideal.mem_bot] at hx
    exact hx
  have hM'v : M'.comap (algebraMap (𝓞 F) (R ⧸ Q)) = v.asIdeal := by
    rw [hq, ← Ideal.comap_comap, hcomap, hMv]
  obtain ⟨L, iL, aL, fL, y, hy, hyinj, hint, hunit, hnon⟩ :=
    h₂ F (R ⧸ Q) v M' ⟨hinj, hQalg, hM', hM'v⟩
  refine ⟨L, iL, aL, fL, y.comp (Ideal.Quotient.mk Q), ?_, fun a => hint _, ?_, ?_, ?_⟩
  · rw [RingHom.comp_assoc, ← hq, hy]
  · intro h
    apply hgQ
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hyinj (by rw [map_zero]; exact h)
  · refine hunit _ fun h => huM ?_
    rw [← hcomap]
    exact h
  · intro a ha
    exact hnon _ (Ideal.mem_map_of_mem _ (hPM ha))

end GroundTheory.Heights₂.Heights.FourB
