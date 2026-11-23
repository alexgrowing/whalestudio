import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LocalizeSubvarSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

theorem LocalizeSubvar.homogeneousComponent_map {R A σ : Type*} [CommSemiring R] [CommSemiring A]
    (f : R →+* A) (d : ℕ) (g : MvPolynomial σ R) :
    homogeneousComponent d (map f g) = map f (homogeneousComponent d g) := by
  ext m
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp

theorem LocalizeSubvar.quotientMap_surjective (S : Type) [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal]
    (O : Type) [CommRing O] [Algebra S O] [IsLocalization.AtPrime O 𝔪] (N : ℕ)
    (pp' : Ideal (Kleiman.Poly O N))
    (hle : (𝔪.map (algebraMap S O)).map (C : O →+* Kleiman.Poly O N) ≤ pp') :
    Function.Surjective (Ideal.quotientMap pp'
      (MvPolynomial.map (algebraMap S O) : Kleiman.Poly S N →+* Kleiman.Poly O N) le_rfl) := by
  set φ := Ideal.quotientMap pp'
    (MvPolynomial.map (algebraMap S O) : Kleiman.Poly S N →+* Kleiman.Poly O N) le_rfl with hφ
  have key : ∀ q : Kleiman.Poly O N, Ideal.Quotient.mk pp' q ∈ φ.range := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C o =>
      obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔪.primeCompl o
      obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv (inferInstance : 𝔪.IsMaximal) t.2
      refine ⟨Ideal.Quotient.mk _ (C (s * y)), ?_⟩
      rw [Ideal.quotientMap_mk, map_C, Ideal.Quotient.eq]
      set v : O := IsLocalization.mk' O (1 : S) t
      have h1 : algebraMap S O t * v = 1 := by rw [IsLocalization.mk'_spec', map_one]
      have h2 : algebraMap S O y * algebraMap S O t + algebraMap S O i = 1 := by
        rw [← map_mul, ← map_add, hyi, map_one]
      have ho : IsLocalization.mk' O s t = algebraMap S O s * v := IsLocalization.mk'_eq_mul_mk'_one s t
      have hd : algebraMap S O (s * y) - IsLocalization.mk' O s t =
          -(algebraMap S O i * (algebraMap S O s * v)) := by
        rw [ho, map_mul]
        linear_combination (-(algebraMap S O y * algebraMap S O s)) * h1 +
          (algebraMap S O s * v) * h2
      rw [← map_sub, hd, map_neg, map_mul]
      refine neg_mem (Ideal.mul_mem_right _ _ (hle ?_))
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hi)
    | add p q hp hq => rw [map_add]; exact Subring.add_mem _ hp hq
    | mul_X p j hp =>
      rw [map_mul]
      refine Subring.mul_mem _ hp ⟨Ideal.Quotient.mk _ (X j), ?_⟩
      rw [Ideal.quotientMap_mk, map_X]
  intro z
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact key q

theorem LocalizeSubvar.proof : LocalizeSubvar.Statement := by
  intro S _ 𝔪 _ O _ _ _ Ω _ _ _ _ N x pp' e hle h
  have := h.isPrime
  refine
    { isPrime := Ideal.comap_isPrime _ _
      homog := ?_
      le := ?_
      relevant := ?_
      dim := ?_ }
  · intro g hg d
    rw [Ideal.mem_comap, ← LocalizeSubvar.homogeneousComponent_map]
    exact h.homog _ hg d
  · intro g hg
    rw [Kleiman.primeOf_eq, RingHom.mem_ker] at hg
    rw [Ideal.mem_comap]
    apply h.le
    rw [Kleiman.primeOf_eq, RingHom.mem_ker, Kleiman.cone_eq, Kleiman.coneGen, aeval_map_algebraMap]
    rw [Kleiman.cone_eq, Kleiman.coneGen] at hg
    exact hg
  · obtain ⟨i, hi⟩ := h.relevant
    exact ⟨i, by rw [Ideal.mem_comap, map_X]; exact hi⟩
  · rw [← h.dim]
    exact ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _
      ⟨Ideal.quotientMap_injective, LocalizeSubvar.quotientMap_surjective S 𝔪 O N pp' hle⟩)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
