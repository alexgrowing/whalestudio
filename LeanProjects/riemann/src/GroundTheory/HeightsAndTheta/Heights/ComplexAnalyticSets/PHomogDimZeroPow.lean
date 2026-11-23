import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHomogDimZeroPow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

theorem le_originIdeal_of_isHomogeneous {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ)) (hne : I ≠ ⊤) : I ≤ originIdeal n := by
  intro f hf
  rw [originIdeal_eq_ker, RingHom.mem_ker]
  by_contra h0
  have h1 : homogeneousComponent 0 f ∈ I := by
    have := hI 0 hf
    rwa [show (DirectSum.decompose (homogeneousSubmodule (Fin n) ℂ) f 0 : MvPolynomial (Fin n) ℂ)
      = homogeneousComponent 0 f from decomposition.decompose'_apply _ _] at this
  rw [homogeneousComponent_zero, ← constantCoeff_eq] at h1
  exact hne (I.eq_top_of_isUnit_mem h1 (isUnit_iff_ne_zero.2 h0 |>.map C))

theorem isMaximal_of_isPrime_of_quotient_dim_le_zero {R : Type*} [CommRing R] {K Q : Ideal R}
    (hK : ringKrullDim (R ⧸ K) ≤ 0) (hQ : Q.IsPrime) (hKQ : K ≤ Q) : Q.IsMaximal := by
  have : Ring.KrullDimLE 0 (R ⧸ K) := Ring.krullDimLE_iff.2 (by exact_mod_cast hK)
  have hsurj := Ideal.Quotient.mk_surjective (I := K)
  have : (Q.map (Ideal.Quotient.mk K)).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (by rwa [Ideal.mk_ker])
  have hmax := Ideal.isMaximal_of_isPrime (Q.map (Ideal.Quotient.mk K))
  have := Ideal.comap_isMaximal_of_surjective _ hsurj (K := Q.map (Ideal.Quotient.mk K))
  rwa [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
    sup_eq_left.2 hKQ] at this

theorem HomogDimZeroPow.proof : HomogDimZeroPow.Statement := by
  intro n K hK hdim
  apply Ideal.exists_pow_le_of_le_radical_of_fg _ (Submodule.fg_span (Set.finite_range _))
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun P ⟨hKP, hP⟩ => ?_
  set 𝒜 := homogeneousSubmodule (Fin n) ℂ
  have hcP : (P.homogeneousCore 𝒜).toIdeal.IsPrime := hP.homogeneousCore
  have hKc : K ≤ (P.homogeneousCore 𝒜).toIdeal := by
    rw [← hK.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono 𝒜 hKP
  have hmax := isMaximal_of_isPrime_of_quotient_dim_le_zero hdim hcP hKc
  have hle := le_originIdeal_of_isHomogeneous (P.homogeneousCore 𝒜).isHomogeneous hmax.ne_top
  exact ((hmax.eq_of_le (originIdeal_isMaximal n).ne_top hle).symm.le).trans
    (Ideal.toIdeal_homogeneousCore_le 𝒜 P)

end

end GroundTheory.Heights₂.Heights.ComplexSets
