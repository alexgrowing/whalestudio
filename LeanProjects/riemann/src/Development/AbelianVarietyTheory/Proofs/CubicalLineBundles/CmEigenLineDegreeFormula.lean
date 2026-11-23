import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ConclusionsAtIdentity
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegreeLieLatticesCmTripleBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmEllipticCurveIntegersWithPeriodStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTensorDecompositionPureTypeCmTripleStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TwoMulDegreeEigenLatticeTensorRankOneStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllPullExistsOAct
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyPolAVGenericFibreWithLieBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LinearIndependentOfIsLieBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HasPeriodOfEllMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueExtendRingOfIntegersHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HasTypeBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.PureDeg

theorem exists_compositum (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] :
    ∃ (k : IntermediateField ℚ ℂ) (_ : NumberField k) (j : K →+* k) (i : M →+* k),
      (∀ x, (j x : ℂ) = σ x) ∧ ∀ x, (i x : ℂ) = x := by
  let f : K →ₐ[ℚ] ℂ := σ.toRatAlgHom
  let k : IntermediateField ℚ ℂ := f.fieldRange ⊔ M
  have : FiniteDimensional ℚ f.fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField f).toLinearEquiv
  have : FiniteDimensional ℚ k := IntermediateField.finiteDimensional_sup _ _
  have : NumberField k := NumberField.mk
  have hmem : ∀ x, σ x ∈ k := fun x => le_sup_left (a := f.fieldRange) ⟨x, rfl⟩
  refine ⟨k, inferInstance, σ.codRestrict k hmem, (IntermediateField.inclusion le_sup_right).toRingHom,
    fun x => rfl, fun x => rfl⟩

theorem mapRingHom_injective {K K' : Type} [Field K] [Field K'] (j : K →+* K') :
    Function.Injective (RingOfIntegers.mapRingHom j) := by
  intro a b h
  apply RingOfIntegers.ext
  apply j.injective
  exact congrArg (fun x : 𝓞 K' => (x : K')) h

theorem degSt : CMCurve → ThetaUnifAV → Out.Laws → HomExtDvr → DegSt := by
  intro hC hU hL hX
  have hB : Out.PolBaseChangeSt := hL.polBaseChange
  intro E _ _ _ H _ χ hχ K _ _ ρ T hsp hρ htype F h hh τ hτ
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := ⟨(IsAlgClosed.lift : K →ₐ[ℚ] ℂ).toRingHom⟩
  have hρc : σ (ρ : K) ^ 2 = -(H.d : ℂ) := by
    have e := congrArg (fun a : 𝓞 K => σ (a : K)) hρ
    simpa using e
  obtain ⟨M, _, ω, C, x, hωρ, hprin, hper, hx⟩ := GlobalTheory.T.exists_cmEllipticCurve_integers_with_period hC hU hL hX E H χ hχ (σ (ρ : K)) hρc
  obtain ⟨k, _, j, i, hj, hi⟩ := exists_compositum K σ M

  obtain ⟨C', φC, hCC'⟩ := exists_ellMap hB E H (𝓞 M) ω C (𝓞 k) (RingOfIntegers.mapRingHom i)
  have hCm := EllComp.ellMap_comp E H (𝓞 M) ω C (𝓞 k) _ C' (RingOfIntegers.mapRingHom i) φC hCC'
  have hemb : ((algebraMap k ℂ).comp (algebraMap (𝓞 k) k)).comp (RingOfIntegers.mapRingHom i) =
      (algebraMap M ℂ).comp (algebraMap (𝓞 M) M) := RingHom.ext fun a => hi (a : M)
  have hprin' : C'.IsPrincipalAt ((algebraMap k ℂ).comp (algebraMap (𝓞 k) k)) := by
    apply hCm.2.1
    rw [hemb]
    exact hprin
  have hper' : C'.HasPeriod x := hasPeriod_of_ellMap hB E H M k i ω _ C C' φC x hCC' hper

  obtain ⟨T', mT, -⟩ := PAT.exists_pullback E H _ _ (spMap (RingOfIntegers.mapRingHom j)) T
  have htype' : HasType H T'.t.act (RingOfIntegers.mapRingHom j ρ) 1 0 :=
    (hasType_baseChange E H (𝓞 K) (𝓞 k) (RingOfIntegers.mapRingHom j) T.t T'.t mT ρ 1 0).1
      (mapRingHom_injective j) htype
  have hinjk : Function.Injective ((algebraMap k ℂ).comp (algebraMap (𝓞 k) k)) :=
    (algebraMap k ℂ).injective.comp RingOfIntegers.coe_injective
  have hρω : RingOfIntegers.mapRingHom j ρ = 2 * RingOfIntegers.mapRingHom i ω - 1 := by
    apply hinjk
    have e1 : (((RingOfIntegers.mapRingHom j ρ : 𝓞 k) : k) : ℂ) = σ (ρ : K) := hj _
    have e2 : (((RingOfIntegers.mapRingHom i ω : 𝓞 k) : k) : ℂ) = ((ω : M) : ℂ) := hi _
    change (((RingOfIntegers.mapRingHom j ρ : 𝓞 k) : k) : ℂ) =
      (((2 * RingOfIntegers.mapRingHom i ω - 1 : 𝓞 k) : k) : ℂ)
    rw [e1]
    push_cast
    rw [e2]
    exact hωρ.symm
  obtain ⟨k₁, _, hk, ω₁, C₁, φ₁, T₁, m₁, D, ε, hD, hE1, hpq, hKF, hpos, hten⟩ :=
    GlobalTheory.T.exists_tensor_decomposition_pure_type_cm_triple hU hL hX E H k (RingOfIntegers.mapRingHom i ω) C' T' 1 hprin' (by rw [← hρω]; exact htype')
  have hper₁ : C₁.HasPeriod x :=
    hasPeriod_of_ellMap hB E H k k₁ (IntermediateField.inclusion hk).toRingHom _ ω₁ C' C₁ φ₁ x hE1 hper'
  have hsp₁ : Splits E k₁ :=
    (((splits_basic E).2.2 K).2.2 k₁ ((IntermediateField.inclusion hk).toRingHom.comp j) hsp).1

  obtain ⟨F'⟩ := GenFib.nonempty_of_baseChange hB k T'.pol
  obtain ⟨F₁⟩ := GenFib.nonempty_of_baseChange hB k₁ T₁.pol
  obtain ⟨⟨h', hh'⟩, -⟩ := LieMetric.exists_unique_isHerm hU hL k T'.pol F'
  obtain ⟨⟨h₁, hh₁⟩, -⟩ := LieMetric.exists_unique_isHerm hU hL k₁ T₁.pol F₁

  have d1 := (GlobalTheory.T.degree_lieLattices_cmTriple_baseChange hU hL E H K k j T T' mT F F' h h' hh hh').2 τ
  have d2 := (GlobalTheory.T.degree_lieLattices_cmTriple_baseChange hU hL E H k k₁ (IntermediateField.inclusion hk).toRingHom T' T₁ m₁ F' F₁ h' h₁
    hh' hh₁).2 ((RingOfIntegers.mapRingHom j).comp τ)

  have h2 : 2 * τ H.w0 = 1 + ρ := by
    have e := congrArg τ H.two_weight_eq_one_add_root
    rw [map_mul, map_add, map_one, map_ofNat, hτ] at e
    exact e
  have two : (2 : 𝓞 k) ≠ 0 := two_ne_zero
  have h3 : (2 : 𝓞 k) * RingOfIntegers.mapRingHom j (τ H.w0) = 2 * RingOfIntegers.mapRingHom i ω := by
    have e := congrArg (RingOfIntegers.mapRingHom j) h2
    rw [map_mul, map_add, map_one, map_ofNat, hρω] at e
    rw [e]
    ring
  have h4 := mul_left_cancel₀ two h3
  have hw : ((RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom).comp
      ((RingOfIntegers.mapRingHom j).comp τ)) H.w0 = ω₁ := by
    simp only [RingHom.comp_apply]
    rw [h4]
    exact hE1.1
  have key := GlobalTheory.T.two_mul_degree_eigenLattice_tensor_rankOne hU hL E H k₁ ω₁ C₁ D ε hD T₁ x hsp₁ hpq hKF hpos hten hper₁ F₁ h₁ hh₁ _ hw

  have hd : (0 : ℝ) < H.d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne _)
  have hrd : 0 < NumberField.rootDiscr E := by
    rw [NumberField.rootDiscr_def]
    apply Real.rpow_pos_of_pos
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero E)
  have hr : Real.log (2 * Real.pi / √(H.d : ℝ)) + Real.log H.d / 2 - Real.log (NumberField.rootDiscr E) =
      Real.log (2 * Real.pi / NumberField.rootDiscr E) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) hrd.ne', Real.log_sqrt hd.le]
    ring
  rw [← d2.trans d1, key, logOm, ← hr]
  push_cast at hx ⊢
  linear_combination hx

end GlobalTheory.CM.PureDeg
end
