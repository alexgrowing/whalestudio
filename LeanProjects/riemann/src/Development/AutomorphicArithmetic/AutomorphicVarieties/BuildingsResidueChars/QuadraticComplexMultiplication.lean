import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

theorem UpperTheory.quadratic_complex_multiplication :
    UpperTheory.V.Af.Cr.QuadCM := by
  intro F Ω _ _ _ _ _ _ d δ hδ hd
  have halg : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral F δ := (halg.isAlgebraic δ).isIntegral
  let K : IntermediateField F Ω := IntermediateField.adjoin F {δ}
  haveI : FiniteDimensional F K := IntermediateField.adjoin.finiteDimensional hint
  haveI : NumberField K := NumberField.of_module_finite F K
  let y : K := IntermediateField.AdjoinSimple.gen F δ
  have hy : algebraMap K Ω y = δ := rfl
  have hy2 : y ^ 2 = algebraMap F K d := by
    apply (algebraMap K Ω).injective
    rw [map_pow, hy, hδ, ← IsScalarTower.algebraMap_apply]
  have hle : (minpoly F δ).natDegree ≤ 2 := by
    have hm : (X ^ 2 - C d : F[X]).Monic := monic_X_pow_sub_C d (by norm_num)
    have h1 := minpoly.min F δ hm (by simp [hδ])
    have h2 := natDegree_le_natDegree h1
    rwa [natDegree_X_pow_sub_C] at h2
  have hne : (minpoly F δ).natDegree ≠ 1 := by
    intro h
    obtain ⟨c, hc⟩ := (minpoly.natDegree_eq_one_iff).1 h
    have hcd : c ^ 2 = d := by
      apply (algebraMap F Ω).injective
      rw [map_pow, hc, hδ]
    let v : InfinitePlace F := Classical.arbitrary _
    have h3 := hd (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v))
    rw [← hcd, map_pow] at h3
    exact absurd h3 (not_lt.2 (sq_nonneg _))
  have hpos := minpoly.natDegree_pos hint
  have hdeg : (minpoly F δ).natDegree = 2 := by omega
  have hrk : Module.finrank F K = 2 := by
    rw [← hdeg]; exact IntermediateField.adjoin.finrank hint
  haveI : IsTotallyComplex K := by
    refine ⟨fun v => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    have h3 := hd ((InfinitePlace.embedding_of_isReal hv).comp (algebraMap F K))
    rw [RingHom.comp_apply, ← hy2, map_pow] at h3
    exact absurd h3 (not_lt.2 (sq_nonneg _))
  haveI : Algebra.IsQuadraticExtension F K := { finrank_eq_two' := hrk }
  haveI : IsAlgClosure K Ω :=
    { isAlgClosed := IsAlgClosure.isAlgClosed F
      isAlgebraic := Algebra.IsAlgebraic.tower_top (K := F) K }
  refine ⟨K, inferInstance, inferInstance, IsCMField.ofCMExtension F K, inferInstance, inferInstance,
    inferInstance, inferInstance, hrk, y, hy, fun x => ?_⟩
  obtain ⟨f, hf, hx⟩ := (IntermediateField.adjoin.powerBasis hint).exists_eq_aeval x
  rw [IntermediateField.adjoin.powerBasis_dim, hdeg] at hf
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  rw [hx, IntermediateField.adjoin.powerBasis_gen]
  conv_lhs => rw [eq_X_add_C_of_natDegree_le_one (p := f) (by omega)]
  simp only [map_add, map_mul, aeval_C, aeval_X]
  exact add_comm _ _
