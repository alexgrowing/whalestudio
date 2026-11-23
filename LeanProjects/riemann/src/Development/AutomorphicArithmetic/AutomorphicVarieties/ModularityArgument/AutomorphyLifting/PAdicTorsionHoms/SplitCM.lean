import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PlainAtR
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ExistsInfiniteQcmSplitRam
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticSignCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.TwCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ResTwo
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StarEqOfSq

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Gam UpperTheory.V.Z.Win
open GroundTheory.Global.SemiLocal UpperTheory.V.Published GlobalTheory.RealGal

namespace UpperTheory.V.Z.Win.SplitCMExtensionExistence

private theorem exists_isCMExt (F K : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K]
    [IsCMField K] [Algebra F K] (h : Module.finrank F K = 2) :
    ∃ σ : K →ₐ[F] K, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F K σ := by
  have hc : ∀ x : F, IsCMField.complexConj K (algebraMap F K x) = algebraMap F K x := by
    intro x
    let τ : K →+* ℂ := (Classical.arbitrary (InfinitePlace K)).embedding
    apply τ.injective
    rw [IsCMField.complexEmbedding_complexConj]
    have hr : ComplexEmbedding.IsReal (τ.comp (algebraMap F K)) := by
      rw [← InfinitePlace.isReal_mk_iff]
      exact IsTotallyReal.isReal _
    exact RingHom.congr_fun (ComplexEmbedding.isReal_iff.1 hr) x
  exact ⟨{ (IsCMField.complexConj K).toRingEquiv.toRingHom with commutes' := hc }, inferInstance, inferInstance, h,
    fun τ x => IsCMField.complexEmbedding_complexConj K τ x⟩

private theorem compl_of_alg (F K : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K]
    [IsCMField K] [Algebra F K] (h : Module.finrank F K = 2) (v : HeightOneSpectrum (𝓞 F))
    (τ : K →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (w : HeightOneSpectrum (𝓞 K)) (hw : w.under (𝓞 F) = v) :
    ∃ i : v.adicCompletion F ≃+* w.adicCompletion K, IsCompl i := by
  obtain ⟨σ, hσ⟩ := exists_isCMExt F K h
  obtain ⟨ρ, rfl⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq hσ (GlobalTheory.LFun.SplitChart.isSplit_of_algHom hσ τ) hw
  obtain ⟨ψ, h1, -, -, h4, -⟩ := GlobalTheory.LFun.SplitChart.exists_equiv_complMap ρ hw
  exact ⟨ψ, h4, fun x => by rw [h1]; exact GlobalTheory.LFun.complMap_algebraMap hw x⟩

private theorem exists_padic_hom (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ q : Nat.Primes, Nonempty (ℚ_[(q : ℕ)] →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :=
  ⟨Rat.HeightOneSpectrum.primesEquiv (v.under (𝓞 ℚ)),
    ⟨(GlobalTheory.LFun.complMap (F := ℚ) (E := F) (w := v)
        (Equiv.symm_apply_apply Rat.HeightOneSpectrum.primesEquiv (v.under (𝓞 ℚ))).symm).comp
      (RingHomClass.toRingHom (Padic.adicCompletionEquiv (𝓞 ℚ) (Rat.HeightOneSpectrum.primesEquiv (v.under (𝓞 ℚ)))))⟩⟩

private theorem family (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (v : HeightOneSpectrum (𝓞 F)) :
    {Q : QCM F Ω | Nonempty (↥Q.K →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)}.Infinite := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have halg : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  obtain ⟨q, ⟨f⟩⟩ := exists_padic_hom F v
  have hsq : ∀ p : ℕ, ∃ δ : Ω, δ ^ 2 = -(p : Ω) := fun p =>
    IsAlgClosed.exists_pow_nat_eq (-(p : Ω)) two_pos
  choose δ hδ using hsq
  let Good : Set ℕ := {p | p.Prime ∧ IsSquare (-(p : ℚ_[(q : ℕ)])) ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr F}
  have hGood : Good.Infinite := by
    have hbad : ({2} ∪ {p : ℕ | p ∣ (discr F).natAbs}).Finite := by
      refine (Set.finite_singleton 2).union ?_
      exact (Nat.divisors (discr F).natAbs).finite_toSet.subset fun p hp =>
        Nat.mem_divisors.2 ⟨hp, Int.natAbs_ne_zero.2 (discr_ne_zero F)⟩
    refine ((GlobalTheory.T.infinite_primes_neg_square_padic (q : ℕ)).diff hbad).mono ?_
    rintro p ⟨⟨hp, hs⟩, hn⟩
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, not_or] at hn
    exact ⟨hp, hs, hn.1, fun h => hn.2 (Int.natCast_dvd.1 h)⟩
  have hQ : ∀ p ∈ Good, ∃ Q : QCM F Ω, Q.K = IntermediateField.adjoin F {δ p} := by
    intro p hp
    refine GlobalTheory.ExSplitCM.exists_qcm (-(p : F)) (δ p) (by simp [hδ p]) fun φ => ?_
    simp only [map_neg, map_natCast, neg_lt_zero]
    exact_mod_cast hp.1.pos
  have hmove : ∀ p ∈ Good, ∀ Q : QCM F Ω, Q.K = IntermediateField.adjoin F {δ p} →
      ∀ (u : HeightOneSpectrum (𝓞 F)) (A' : ValuationSubring Ω), ((p : ℕ) : 𝓞 F) ∈ u.asIdeal →
        IsPlaceOver A' u → ¬ Ine (F := F) A' ≤ (UpperTheory.V.Af.Bc.res F Ω ↥Q.K).range := by
    intro p hp Q hQK u A' hu hA' hle
    obtain ⟨s, hs, hne⟩ := GlobalTheory.T.inertia_moves_square_root F Ω p hp.1 hp.2.2.1 hp.2.2.2 (δ p) (hδ p) u A' hu hA'
    refine hne ((GlobalTheory.ExSplitCM.mem_range_res_iff Q.K s).1 (hle hs) (δ p) ?_)
    rw [hQK]
    exact IntermediateField.mem_adjoin_simple_self F (δ p)
  have hmem : ∀ p ∈ Good, ∀ Q : QCM F Ω, Q.K = IntermediateField.adjoin F {δ p} →
      Nonempty (↥Q.K →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) := by
    intro p hp Q hQK
    obtain ⟨c, hc⟩ := hp.2.1
    have hc' : f c ^ 2 = -(p : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) := by
      rw [pow_two, ← map_mul, ← hc]
      simp
    have hint : IsIntegral F (δ p) := (halg.isAlgebraic (δ p)).isIntegral
    have hdeg : (minpoly F (δ p)).natDegree = 2 := by
      rw [← IntermediateField.adjoin.finrank hint, ← hQK]
      exact Q.two
    have hm : (X ^ 2 + C (p : F) : F[X]).Monic := monic_X_pow_add_C _ two_ne_zero
    have hdvd : minpoly F (δ p) ∣ X ^ 2 + C (p : F) := minpoly.dvd F _ (by simp [hδ p])
    have hmin : X ^ 2 + C (p : F) = minpoly F (δ p) :=
      eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hm hdvd
        (by rw [hdeg, natDegree_X_pow_add_C])
    rw [hQK]
    refine ⟨(IntermediateField.algHomAdjoinIntegralEquiv F hint).symm ⟨f c, ?_⟩⟩
    refine mem_aroots.2 ⟨minpoly.ne_zero hint, ?_⟩
    rw [← hmin]
    simp [hc']
  intro hfin
  apply hGood
  refine (hfin.biUnion (t := fun Q : QCM F Ω => {p : ℕ | p.Prime ∧ ∃ u ∈ {u : HeightOneSpectrum (𝓞 F) |
      ¬ ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → Ine (F := F) A' ≤ (UpperTheory.V.Af.Bc.res F Ω ↥Q.K).range},
      ((p : ℕ) : 𝓞 F) ∈ u.asIdeal})
    fun Q _ => GlobalTheory.ExSplitCM.finite_primes_of_finite (Filter.eventually_cofinite.1 (UpperTheory.cm_inertia_restriction_holds F ↥Q.K Ω))).subset ?_
  intro p hp
  obtain ⟨Q, hQK⟩ := hQ p hp
  refine Set.mem_biUnion (hmem p hp Q hQK) ⟨hp.1, ?_⟩
  obtain ⟨u, hu⟩ := GlobalTheory.ExSplitCM.exists_mem_of_prime (F := F) hp.1
  obtain ⟨A', hA'⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
  exact ⟨u, fun hall => hmove p hp Q hQK u A' hu hA' (hall A' hA'), hu⟩

private theorem star_eq_of_sq {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : z * z = r) : star z = z :=
  _root_.UpperTheory.Reformulated.B.Ra8.star_eq_of_sq hr h

private theorem exists_real_emb (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ψ : F →+* ℂ) :
    ∃ φ : F →+* ℝ, ∀ x, ψ x = (φ x : ℂ) := by
  have hr : ComplexEmbedding.IsReal ψ := by
    rw [← InfinitePlace.isReal_mk_iff]
    exact IsTotallyReal.isReal _
  exact ⟨hr.embedding, fun x => (hr.coe_embedding_apply x).symm⟩

private theorem exists_sq_neg (F K : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K]
    [IsCMField K] [Algebra F K] (h : Module.finrank F K = 2) :
    ∃ (t : K) (d : F), t * t = algebraMap F K d ∧ (∀ φ : F →+* ℝ, φ d < 0) ∧
      ∀ x : K, ∃ a b : F, x = algebraMap F K a + algebraMap F K b * t := by
  haveI : Algebra.IsQuadraticExtension F K := ⟨h⟩
  obtain ⟨d, e, hd, h0, h1⟩ := GlobalTheory.QuadSymbol.AlmostNorm.exists_basis_sq F K
  have hx : ∀ x : K, ∃ a b : F, x = algebraMap F K a + algebraMap F K b * e 1 := fun x => by
    refine ⟨e.repr x 0, e.repr x 1, ?_⟩
    conv_lhs => rw [← e.sum_repr x]
    rw [Fin.sum_univ_two, h0, Algebra.smul_def, Algebra.smul_def, mul_one]
  refine ⟨e 1, d, h1, fun φ => ?_, hx⟩
  by_contra hnn
  letI : Algebra F ℂ := ((algebraMap ℝ ℂ).comp φ).toAlgebra
  haveI : Algebra.IsAlgebraic F K := inferInstance
  let τ : K →ₐ[F] ℂ := IsAlgClosed.lift
  have hF : ∀ a : F, τ (algebraMap F K a) = (φ a : ℂ) := fun a => τ.commutes a
  have ht : star (τ (e 1)) = τ (e 1) := by
    refine star_eq_of_sq (not_lt.1 hnn) ?_
    rw [← map_mul, h1, hF]
  have hall : ∀ x, star (τ x) = τ x := fun x => by
    obtain ⟨a, b, rfl⟩ := hx x
    simp only [map_add, map_mul, hF, ht, star_add, star_mul', Complex.star_def, Complex.conj_ofReal]
  have hreal : ComplexEmbedding.IsReal (τ : K →+* ℂ) :=
    ComplexEmbedding.isReal_iff.2 (RingHom.ext hall)
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk (τ : K →+* ℂ))))
    (InfinitePlace.isReal_mk_iff.2 hreal)

private theorem cm_of_sq (F M : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field M] [NumberField M] [Algebra F M]
    (a b : M) (α β : F) (ha : a * a = algebraMap F M α) (hb : b * b = algebraMap F M β)
    (hα : ∀ φ : F →+* ℝ, φ α < 0) (hβ : ∀ φ : F →+* ℝ, φ β < 0)
    (hgen : ∀ L : IntermediateField F M, a ∈ L → b ∈ L → L = ⊤) : IsCMField M := by
  haveI : FiniteDimensional F M := Module.Finite.of_restrictScalars_finite ℚ F M
  let K : IntermediateField F M := IntermediateField.adjoin F {a * b}
  haveI : NumberField K := NumberField.of_module_finite F K
  have hc : a * b ∈ K := IntermediateField.mem_adjoin_simple_self F _
  have hreal : ∀ (ρ : K →+* ℂ) (x : K), star (ρ x) = ρ x := by
    intro ρ
    obtain ⟨φ, hφ⟩ := exists_real_emb F (ρ.comp (algebraMap F K))
    letI : Algebra F ℂ := (ρ.comp (algebraMap F K)).toAlgebra
    let f : K →ₐ[F] ℂ := { ρ with commutes' := fun _ => rfl }
    let g : K →ₐ[F] ℂ := { (starRingEnd ℂ).comp ρ with
      commutes' := fun x => by
        show star (ρ (algebraMap F K x)) = ρ (algebraMap F K x)
        have := hφ x
        simp only [RingHom.comp_apply] at this
        rw [this, Complex.star_def, Complex.conj_ofReal] }
    have hfg : f = g := by
      refine IntermediateField.algHom_ext_of_eq_adjoin F rfl ?_
      rintro x rfl
      show ρ ⟨a * b, hc⟩ = star (ρ ⟨a * b, hc⟩)
      symm
      refine star_eq_of_sq (r := φ α * φ β) (mul_nonneg_of_nonpos_of_nonpos (hα φ).le (hβ φ).le) ?_
      have h2 : (⟨a * b, hc⟩ : K) * ⟨a * b, hc⟩ = algebraMap F K (α * β) := by
        apply Subtype.ext
        show a * b * (a * b) = algebraMap F M (α * β)
        rw [map_mul, ← ha, ← hb]
        ring
      rw [← map_mul, h2]
      have := hφ (α * β)
      simp only [RingHom.comp_apply, map_mul] at this
      simpa using this
    intro x
    exact (DFunLike.congr_fun hfg x).symm
  haveI : IsTotallyReal K := ⟨fun w => by
    rw [← InfinitePlace.mk_embedding w, InfinitePlace.isReal_mk_iff]
    exact ComplexEmbedding.isReal_iff.2 (RingHom.ext (hreal w.embedding))⟩
  have hα0 : α ≠ 0 := fun h0 => by
    have := hα (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal (Classical.arbitrary (InfinitePlace F))))
    simp [h0] at this
  have ha0 : a ≠ 0 := fun h0 => hα0 (by simpa [h0] using ha.symm)
  have hnot : a ∉ K := fun haK => by
    let ρ : K →+* ℂ := (Classical.arbitrary (InfinitePlace K)).embedding
    obtain ⟨φ, hφ⟩ := exists_real_emb F (ρ.comp (algebraMap F K))
    have h2 : (⟨a, haK⟩ : K) * ⟨a, haK⟩ = algebraMap F K α := Subtype.ext ha
    have h3 := hφ α
    simp only [RingHom.comp_apply] at h3
    rw [← h2, map_mul] at h3
    have him : (ρ ⟨a, haK⟩).im = 0 := Complex.conj_eq_iff_im.1 (hreal ρ _)
    have h4 := congrArg Complex.re h3
    simp only [Complex.mul_re, him, Complex.ofReal_re, mul_zero, sub_zero] at h4
    have := hα φ
    nlinarith [mul_self_nonneg (ρ ⟨a, haK⟩).re]
  have hint : IsIntegral K a := Algebra.IsIntegral.isIntegral a
  have hle : (minpoly K a).natDegree ≤ 2 := by
    have hm : (X ^ 2 - C (algebraMap F K α) : K[X]).Monic := monic_X_pow_sub_C _ (by norm_num)
    have h1 := minpoly.min K a hm (by
      simp only [map_sub, map_pow, aeval_X, aeval_C]
      rw [pow_two, ha]
      exact sub_eq_zero.2 rfl)
    have h2 := natDegree_le_natDegree h1
    rwa [natDegree_X_pow_sub_C] at h2
  have hne : (minpoly K a).natDegree ≠ 1 := fun h => by
    obtain ⟨c, hc'⟩ := minpoly.natDegree_eq_one_iff.1 h
    exact hnot (hc' ▸ c.2)
  have hdeg : (minpoly K a).natDegree = 2 := by
    have := minpoly.natDegree_pos hint
    omega
  have htop : IntermediateField.adjoin K {a} = ⊤ := by
    have hL := hgen ((IntermediateField.adjoin K {a}).restrictScalars F)
      (IntermediateField.mem_adjoin_simple_self K a) (by
        have hA : a ∈ IntermediateField.adjoin K {a} := IntermediateField.mem_adjoin_simple_self K a
        have hC : a * b ∈ IntermediateField.adjoin K {a} := (IntermediateField.adjoin K {a}).algebraMap_mem ⟨a * b, hc⟩
        have e : b = (a * b) * a⁻¹ := by field_simp
        show b ∈ IntermediateField.adjoin K {a}
        rw [e]
        exact mul_mem hC (inv_mem hA))
    exact IntermediateField.restrictScalars_injective F (hL.trans (IntermediateField.restrictScalars_top).symm)
  have h2 : Module.finrank K M = 2 := by
    rw [← hdeg, ← IntermediateField.adjoin.finrank hint, htop, IntermediateField.finrank_top']
  haveI : IsTotallyComplex M := ⟨fun w => by
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hw
    have h3 := hα ((InfinitePlace.embedding_of_isReal hw).comp (algebraMap F M))
    rw [RingHom.comp_apply, ← ha, map_mul] at h3
    exact absurd h3 (not_lt.2 (mul_self_nonneg _))⟩
  haveI : Algebra.IsQuadraticExtension K M := ⟨h2⟩
  exact IsCMField.ofCMExtension K M

private theorem compositum (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsCMField E]
    [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] (hE : Module.finrank F E = 2)
    (Q : QCM F Ω) (hne : (IsScalarTower.toAlgHom F E Ω).fieldRange ≠ Q.K) :
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra F M) (_ : Algebra E M)
      (_ : Algebra ↥Q.K M) (_ : Algebra M Ω) (_ : IsScalarTower F E M) (_ : IsScalarTower F ↥Q.K M)
      (_ : IsScalarTower F M Ω) (_ : IsScalarTower E M Ω) (_ : IsScalarTower ↥Q.K M Ω),
      Module.finrank E M = 2 ∧ Module.finrank ↥Q.K M = 2 ∧
      ∀ s : G F Ω, (∀ x : E, s (algebraMap E Ω x) = algebraMap E Ω x) →
        (∀ x : ↥Q.K, s (algebraMap ↥Q.K Ω x) = algebraMap ↥Q.K Ω x) →
        ∀ x : M, s (algebraMap M Ω x) = algebraMap M Ω x := by
  let a := IsScalarTower.toAlgHom F E Ω
  let A : IntermediateField F Ω := a.fieldRange
  let M : IntermediateField F Ω := A ⊔ Q.K
  have ha : ∀ x, a x ∈ M := fun x => (le_sup_left : A ≤ M) ⟨x, rfl⟩
  have hBM : Q.K ≤ M := le_sup_right
  letI iE : Algebra E M := (a.toRingHom.codRestrict M ha).toAlgebra
  letI iB : Algebra ↥Q.K M := (IntermediateField.inclusion hBM).toRingHom.toAlgebra
  haveI t1 : IsScalarTower F E M := IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (a.commutes x).symm
  haveI t2 : IsScalarTower F ↥Q.K M := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI t3 : IsScalarTower E M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI t4 : IsScalarTower ↥Q.K M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : FiniteDimensional F A := a.equivFieldRange.toLinearEquiv.finiteDimensional
  have hA2 : Module.finrank F A = 2 := a.equivFieldRange.toLinearEquiv.finrank_eq ▸ hE
  have hB2 : Module.finrank F Q.K = 2 := Q.two
  haveI : FiniteDimensional F Q.K := Module.finite_of_finrank_pos (by rw [hB2]; norm_num)
  haveI : Algebra.IsQuadraticExtension F A := ⟨hA2⟩
  have hinf : A ⊓ Q.K = ⊥ := by
    by_contra hbot
    have h1 : Module.finrank F ↥(A ⊓ Q.K) ∣ 2 := hA2 ▸ IntermediateField.finrank_dvd_of_le_right inf_le_left
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact hbot (IntermediateField.finrank_eq_one_iff.1 h)
    · exact hne ((IntermediateField.eq_of_le_of_finrank_eq inf_le_left (h.trans hA2.symm)).symm.trans
        (IntermediateField.eq_of_le_of_finrank_eq inf_le_right (h.trans hB2.symm)))
  have hM4 : Module.finrank F M = 4 := by
    rw [(IntermediateField.LinearDisjoint.of_inf_eq_bot hinf).finrank_sup, hA2, hB2]
  haveI : FiniteDimensional F M := IntermediateField.finiteDimensional_sup _ _
  haveI nM : NumberField M := NumberField.of_module_finite F M
  have h1 : Module.finrank E M = 2 := by
    have := Module.finrank_mul_finrank F E M
    rw [hE, hM4] at this
    omega
  have h2 : Module.finrank ↥Q.K M = 2 := by
    haveI : Module.Free ↥Q.K M := Module.Free.of_divisionRing _ _
    have := Module.finrank_mul_finrank F ↥Q.K M
    rw [hB2, hM4] at this
    omega
  obtain ⟨t, d, ht, hd, hx⟩ := exists_sq_neg F E hE
  obtain ⟨u, e, hu, he, hx'⟩ := exists_sq_neg F ↥Q.K hB2
  have cM : IsCMField M := by
    refine cm_of_sq F M (algebraMap E M t) (algebraMap ↥Q.K M u) d e ?_ ?_ hd he fun L haL hbL => ?_
    · rw [← map_mul, ht, ← IsScalarTower.algebraMap_apply]
    · rw [← map_mul, hu, ← IsScalarTower.algebraMap_apply]
    · have hE' : ∀ x : E, algebraMap E M x ∈ L := fun x => by
        obtain ⟨y, z, rfl⟩ := hx x
        rw [map_add, map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
        exact add_mem (L.algebraMap_mem y) (mul_mem (L.algebraMap_mem z) haL)
      have hB' : ∀ x : ↥Q.K, algebraMap ↥Q.K M x ∈ L := fun x => by
        obtain ⟨y, z, rfl⟩ := hx' x
        rw [map_add, map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
        exact add_mem (L.algebraMap_mem y) (mul_mem (L.algebraMap_mem z) hbL)
      have hle : M ≤ L.map M.val := sup_le
        (by rintro _ ⟨x, rfl⟩; exact ⟨algebraMap E M x, hE' x, rfl⟩)
        (fun x hx0 => ⟨algebraMap ↥Q.K M ⟨x, hx0⟩, hB' _, rfl⟩)
      refine eq_top_iff.2 fun y _ => ?_
      obtain ⟨y', hy', hyy⟩ := hle y.2
      rwa [show y' = y from Subtype.ext hyy] at hy'
  refine ⟨M, inferInstance, nM, cM, inferInstance, iE, iB, inferInstance, t1, t2, inferInstance, t3, t4, h1, h2, ?_⟩
  intro s hs1 hs2 x
  have hext : (s : Ω →ₐ[F] Ω).comp M.val = M.val := by
    refine IntermediateField.algHom_ext_of_eq_adjoin F (IntermediateField.sup_def A Q.K) ?_
    rintro y (⟨y, rfl⟩ | hy)
    · exact hs1 y
    · exact hs2 ⟨y, hy⟩
  exact DFunLike.congr_fun hext x

private theorem eq_of_res {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] (φ : Γ' →* Γ) (ε : Γ →* kˣ)
    (h1 : ∀ s, ε s = 1 ↔ s ∈ φ.range) (h2 : ∀ s, ε s = 1 ∨ ε s = -1) (t : Γ) (ht : ε t ≠ 1) (a b : Γ →* kˣ)
    (hab : a.comp φ = b.comp φ) (hc : a t = b t) : a = b := by
  have h0 : ∀ s, ε s = 1 → a s = b s := fun s hs => by
    obtain ⟨x, rfl⟩ := (h1 s).1 hs
    exact DFunLike.congr_fun hab x
  refine MonoidHom.ext fun s => ?_
  rcases h2 s with hs | hs
  · exact h0 s hs
  · have e := h0 (t⁻¹ * s) (by simp [hs, (h2 t).resolve_left ht])
    rw [map_mul, map_mul, map_inv, map_inv, hc] at e
    exact mul_left_cancel e

open Classical in
private theorem card_bad {Γ Γ' k I : Type} [Group Γ] [Group Γ'] [Field k] [Fintype I] {n : ℕ} (φ : Γ' →* Γ) (ε : Γ →* kˣ)
    (h1 : ∀ s, ε s = 1 ↔ s ∈ φ.range) (h2 : ∀ s, ε s = 1 ∨ ε s = -1) (h3 : ε ≠ 1) (δ : I → Γ →* kˣ)
    (hi : Function.Injective δ) (hδ : ∀ i s, δ i s = 1 ∨ δ i s = -1) (r : Γ' →* GL (Fin n) k) (hr : IsIrr r) :
    (Finset.univ.filter fun i => RepIso r (tw r ((δ i).comp φ))).card ≤ 2 * n ^ 2 := by
  obtain ⟨t, ht⟩ : ∃ t, ε t ≠ 1 := by
    by_contra h
    exact h3 (MonoidHom.ext fun s => by_contra fun hs => h ⟨s, hs⟩)
  have key : ∀ c : kˣ,
      ((Finset.univ.filter fun i => RepIso r (tw r ((δ i).comp φ))).filter fun i => δ i t = c).card ≤ n ^ 2 := by
    intro c
    rw [← Finset.card_image_of_injOn (f := fun i => (δ i).comp φ)]
    · refine Br.twCard _ _ n r hr _ fun d hd => ?_
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hd
      exact (Finset.mem_filter.1 (Finset.mem_filter.1 hi).1).2
    · intro i hi' j hj hij
      exact hi (eq_of_res φ ε h1 h2 t ht _ _ hij
        ((Finset.mem_filter.1 hi').2.trans (Finset.mem_filter.1 hj).2.symm))
  refine le_trans (Finset.card_le_card (t := _ ∪ _) ?_) ((Finset.card_union_le _ _).trans
    ((add_le_add (key 1) (key (-1))).trans (two_mul _).ge))
  intro i hi
  exact Finset.mem_union.2 ((hδ i t).imp (fun h => Finset.mem_filter.2 ⟨hi, h⟩) fun h => Finset.mem_filter.2 ⟨hi, h⟩)

private theorem irr_inf {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ} (φ : Γ' →* Γ)
    (H : Subgroup Γ) (δ : Γ →* kˣ) (h1 : ∀ s, δ s = 1 ↔ s ∈ H) (h2 : ∀ s, δ s = 1 ∨ δ s = -1) (r : Γ →* GL (Fin n) k)
    (hr : IsIrr (r.comp φ)) (hn : ¬ RepIso (r.comp φ) (tw (r.comp φ) (δ.comp φ))) :
    IsIrr (r.comp (φ.range ⊓ H).subtype) := by
  have h := (Br.resTwo _ _ k n (δ.comp φ).ker.subtype (δ.comp φ) (fun s => by rw [Subgroup.range_subtype]; rfl)
    (fun s => h2 _) (r.comp φ)).1 hr hn
  refine ⟨h.1, fun _ _ _ => trivial, fun W hW hst => h.2.2 W hW fun s v hv => ?_⟩
  exact hst ⟨φ s, ⟨s, rfl⟩, (h1 _).1 s.2⟩ v hv

private theorem qcm_ext {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {Q Q' : QCM F Ω}
    (h : Q.K = Q'.K) : Q = Q' := by
  cases Q
  cases Q'
  cases h
  rfl

private theorem k_eq_of_range {F Ω : Type} [Field F] [Field Ω] [NumberField F] [Algebra F Ω] [IsGalois F Ω]
    (K K' : IntermediateField F Ω) (h : (UpperTheory.V.Af.Bc.res F Ω ↥K).range = (UpperTheory.V.Af.Bc.res F Ω ↥K').range) :
    K = K' := by
  have hf : K.fixingSubgroup = K'.fixingSubgroup := by
    ext s
    rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff,
      ← GlobalTheory.ExSplitCM.mem_range_res_iff, ← GlobalTheory.ExSplitCM.mem_range_res_iff, h]
  rw [← InfiniteGalois.fixedField_fixingSubgroup K, hf, InfiniteGalois.fixedField_fixingSubgroup]

end UpperTheory.V.Z.Win.SplitCMExtensionExistence

open UpperTheory.V.Z.Win.SplitCMExtensionExistence in
theorem UpperTheory.V.Z.Win.splitCM :
    SplitCM := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ _ _ hE l _ n r hr v
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI hal : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  haveI : IsAlgClosure E Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := F) _⟩
  have hS := family F Ω v
  let Q : Fin (2 * n ^ 2 + 1) → QCM F Ω := fun i => (hS.natEmbedding _ (i : ℕ)).1
  have hQi : Function.Injective Q := fun i j h =>
    Fin.ext (hS.natEmbedding _ |>.injective (Subtype.ext h))
  haveI clo : ∀ i, IsAlgClosure ↥(Q i).K Ω := fun i =>
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := F) _⟩
  choose δ _ _ hδ _ using fun i => UpperTheory.exists_quadratic_sign_character F ↥(Q i).K Ω l (Q i).two
  have hδi : Function.Injective δ := fun i j hij => hQi (qcm_ext (k_eq_of_range _ _ (Subgroup.ext fun s => by
    rw [← (hδ i).1, ← (hδ j).1, hij])))
  obtain ⟨ε, -, e0, he, -⟩ := UpperTheory.exists_quadratic_sign_character F E Ω l hE
  have c1 := card_bad (resG F E Ω) ε he.1 he.2 e0 δ hδi (fun i => (hδ i).2) _ hr
  obtain ⟨i, hi⟩ : ∃ i, ¬ RepIso (r.comp (resG F E Ω)) (tw (r.comp (resG F E Ω)) ((δ i).comp (resG F E Ω))) := by
    by_contra hall
    push_neg at hall
    rw [Finset.filter_true_of_mem fun i _ => hall i, Finset.card_univ, Fintype.card_fin] at c1
    omega
  have hne : (IsScalarTower.toAlgHom F E Ω).fieldRange ≠ (Q i).K := fun heq => hi (by
    have h1 : (δ i).comp (resG F E Ω) = 1 := MonoidHom.ext fun s => (hδ i).1 _ |>.2 <|
      (GlobalTheory.ExSplitCM.mem_range_res_iff (Q i).K _).2 fun x hx => by
        rw [← heq] at hx
        obtain ⟨y, rfl⟩ := hx
        exact s.commutes y
    rw [h1]
    exact ⟨1, fun s => Units.ext (by rw [tw_val]; simp)⟩)
  obtain ⟨M, fM, nM, cM, aFM, aEM, aBM, aMΩ, t1, t2, t3, t4, t5, h1, h2, hfix⟩ := compositum F E Ω hE (Q i) hne
  obtain ⟨τ⟩ := (hS.natEmbedding _ (i : ℕ)).2
  refine ⟨↥(Q i).K, M, inferInstance, inferInstance, inferInstance, fM, nM, cM, inferInstance, inferInstance, inferInstance,
    aFM, aEM, aBM, aMΩ, t1, t2, t3, t4, t5, (Q i).two, h1, h2, ?_, fun w hw => compl_of_alg F _ (Q i).two v τ w hw⟩
  have h := irr_inf (resG F E Ω) _ (δ i) (hδ i).1 (hδ i).2 r hr hi
  refine ⟨h.1, fun _ _ _ => trivial, fun W hW hst => h.2.2 W hW fun s u hu => ?_⟩
  obtain ⟨s₀, ⟨t, rfl⟩, hm⟩ := s
  have hfx := hfix (resG F E Ω t) t.commutes fun x =>
    (GlobalTheory.ExSplitCM.mem_range_res_iff (Q i).K _).1 hm x.1 x.2
  have hr' : resG F E Ω t ∈ (resG F M Ω).range :=
    ⟨{ (resG F E Ω t).toRingEquiv with commutes' := hfx }, AlgEquiv.ext fun _ => rfl⟩
  obtain ⟨s', hs'⟩ := hr'
  have := hst s' u hu
  simp only [MonoidHom.comp_apply] at this
  rw [hs'] at this
  exact this
