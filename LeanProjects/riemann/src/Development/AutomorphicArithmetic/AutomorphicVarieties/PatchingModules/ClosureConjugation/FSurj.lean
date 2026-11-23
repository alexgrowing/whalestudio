import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.f_surj :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), Function.Surjective P.f ∧ IsLocalHom P.f.toRingHom := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P
  have hK : IsCO O x.K := by
    refine IsCO.mk ?_ ?_ ?_
    · rw [IsLocalRing.maximalIdeal_eq_bot]
      infer_instance
    · constructor
      intro a ha
      by_contra hna
      have hm : a ∈ maximalIdeal O := hna
      have hker : RingHom.ker (algebraMap O x.K) = maximalIdeal O :=
        eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ P.surj)
      have h0 : algebraMap O x.K a = 0 := by
        rw [← RingHom.mem_ker, hker]
        exact hm
      rw [h0] at ha
      exact not_isUnit_zero ha
    · intro y
      obtain ⟨a, rfl⟩ := P.surj y
      exact ⟨a, by rw [sub_self]; exact Ideal.zero_mem _⟩
  have hA : IsCO O x.A := co_mvps O x.K Unit
  have hs : P.s ∈ maximalIdeal B := by
    rw [← res_eq_zero_iff O B, ← res_map P.f, P.f_s, res_eq_zero_iff,
      PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.subset_span rfl
  have hsurj : Function.Surjective P.f := by
    apply co_surj O B x.A P.f
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hm := Ideal.mem_map_of_mem P.f hs
    rw [P.f_s] at hm
    exact Ideal.mem_sup_left hm
  exact ⟨hsurj, IsLocalHom.of_surjective P.f.toRingHom hsurj⟩
