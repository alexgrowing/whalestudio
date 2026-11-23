import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.EdgesRouteSmall
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import ReciprocityTheory.Chebotarev.StatementHolds
import Formalism.LocalRingCardinality.SpanPowerMembership.Adelic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open Formalism.IndefR.Mult IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.CompanionTheory.Ar.RT
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RT.SplitPl

open Polynomial

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_integer_generator : ∃ θ : 𝓞 E, IntermediateField.adjoin F {((θ : 𝓞 E) : E)} = ⊤ := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  obtain ⟨d, hd, hi⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) (z := α) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic α))
  refine ⟨⟨d • α, hi⟩, ?_⟩
  rw [eq_top_iff, ← hα, IntermediateField.adjoin_simple_le_iff]
  have hd' : (d : F) ≠ 0 := by exact_mod_cast hd
  have h1 : d • α ∈ IntermediateField.adjoin F {d • α} := IntermediateField.mem_adjoin_simple_self F _
  have h2 : α = algebraMap F E (d : F)⁻¹ * (d • α) := by
    rw [zsmul_eq_mul, ← mul_assoc, map_inv₀, map_intCast, inv_mul_cancel₀ (by exact_mod_cast hd), one_mul]
  have h3 := mul_mem (IntermediateField.algebraMap_mem (IntermediateField.adjoin F {d • α}) (d : F)⁻¹) h1
  rw [← h2] at h3
  exact h3

theorem map_mem_maximalIdeal_iff (v : HeightOneSpectrum (𝓞 F)) (c : 𝓞 F) :
    algebraMap (𝓞 F) (v.adicCompletionIntegers F) c ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ↔
      c ∈ v.asIdeal := by
  have e : ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) c : v.adicCompletionIntegers F) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F c) := rfl
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one, e,
    Formalism.BasicNotions.Examples₂.adicCompl_val_algebraMap, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F)]
  exact ⟨fun h => lt_of_le_of_ne (v.valuation_le_one c) h, fun h => h.ne⟩

theorem nonempty_algHom_of_congr (θ : 𝓞 E) (hθ : IntermediateField.adjoin F {(θ : E)} = ⊤)
    (v : HeightOneSpectrum (𝓞 F)) (P : Ideal (𝓞 E))
    (hv : ∀ c, algebraMap (𝓞 F) (𝓞 E) c ∈ P ↔ c ∈ v.asIdeal) (a : 𝓞 F)
    (ha : θ - algebraMap (𝓞 F) (𝓞 E) a ∈ P)
    (hd : aeval θ (derivative (minpoly (𝓞 F) (θ : E))) ∉ P) : Nonempty (E →ₐ[F] Fv F v) := by
  haveI := Formalism.BasicNotions.Examples₂.adicInt_henselian (K := F) v
  have hint : IsIntegral (𝓞 F) (θ : E) := IsIntegral.tower_top (R := ℤ) θ.2
  set G := minpoly (𝓞 F) (θ : E) with hG
  have hmon : G.Monic := minpoly.monic hint
  have hG0 : aeval θ G = 0 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    rw [map_zero, ← aeval_algebraMap_apply]
    exact minpoly.aeval _ _
  have cong : ∀ Q : (𝓞 F)[X], algebraMap (𝓞 F) (𝓞 E) (Q.eval a) - aeval θ Q ∈ P := fun Q => by
    obtain ⟨c, hc⟩ := Polynomial.sub_dvd_eval_sub (algebraMap (𝓞 F) (𝓞 E) a) θ (Q.map (algebraMap (𝓞 F) (𝓞 E)))
    rw [eval_map_apply, eval_map_algebraMap] at hc
    rw [hc, ← neg_sub, neg_mul]
    exact P.neg_mem (P.mul_mem_right _ ha)
  have h1 : G.eval a ∈ v.asIdeal := (hv _).1 (by simpa [hG0] using cong G)
  have h2 : (derivative G).eval a ∉ v.asIdeal := fun h => hd (by
    simpa using P.sub_mem ((hv _).2 h) (cong (derivative G)))
  let φ := algebraMap (𝓞 F) (v.adicCompletionIntegers F)
  obtain ⟨x, hx, -⟩ := HenselianLocalRing.is_henselian (G.map φ) (hmon.map _) (φ a)
    (by rw [eval_map_apply]; exact (map_mem_maximalIdeal_iff v _).2 h1)
    (by
      rw [derivative_map, eval_map_apply]
      by_contra hu
      exact h2 ((map_mem_maximalIdeal_iff v _).1 ((IsLocalRing.mem_maximalIdeal _).2 hu)))
  have hroot : aeval (x : v.adicCompletion F) (minpoly F (θ : E)) = 0 := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' F hint, aeval_map_algebraMap]
    haveI : IsScalarTower (𝓞 F) (v.adicCompletionIntegers F) (v.adicCompletion F) :=
      IsScalarTower.of_algebraMap_eq fun c => rfl
    have h3 := aeval_algebraMap_apply (v.adicCompletion F) x G
    have h4 : aeval x G = 0 := by rw [← eval_map_algebraMap]; exact hx
    rw [h4, map_zero] at h3
    exact h3
  have hi : IsIntegral F (θ : E) := Algebra.IsIntegral.isIntegral _
  have hadj : Algebra.adjoin F {(θ : E)} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hi.isAlgebraic, hθ,
      IntermediateField.top_toSubalgebra]
  let pb := PowerBasis.ofAdjoinEqTop' hi hadj
  exact ⟨pb.lift (x : v.adicCompletion F) (by rw [PowerBasis.ofAdjoinEqTop'_gen]; exact hroot)⟩

theorem split_of_frob_one [IsGalois ℚ E] {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 E)) [hP : P.IsPrime]
    [hl : P.LiesOver (Ideal.span {(p : ℤ)})] (hu : Algebra.IsUnramifiedAt ℤ P)
    (hf : IsArithFrobAt ℤ (1 : Gal(E/ℚ)) P) :
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)).ncard = Module.finrank ℚ E ∧
      ∀ x : 𝓞 E, ∃ a : ℤ, x - algebraMap ℤ (𝓞 E) a ∈ P := by
  have hp1 : 1 < p := hp.one_lt
  have hunder : P.under ℤ = Ideal.span {(p : ℤ)} := hl.over.symm
  have hcard : Nat.card (ℤ ⧸ P.under ℤ) = p := by
    rw [hunder, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  have hfrob : ∀ x : 𝓞 E, x - x ^ p ∈ P := fun x => by
    have h := hf x
    rw [hcard] at h
    simpa using h
  haveI hpr : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
  have hpP : (p : 𝓞 E) ∈ P := by
    have h : (p : ℤ) ∈ P.under ℤ := hunder ▸ Ideal.mem_span_singleton_self _
    simpa using h
  have hne : P ≠ ⊥ := fun e => hp.ne_zero (by
    rw [e, Ideal.mem_bot] at hpP
    exact_mod_cast hpP)
  haveI hmax : P.IsMaximal := hP.isMaximal hne
  letI := Ideal.Quotient.field P
  haveI : Finite (𝓞 E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hne
  letI := Fintype.ofFinite (𝓞 E ⧸ P)
  have hle : Nat.card (𝓞 E ⧸ P) ≤ p := by
    classical
    have hQ : (X ^ p - X : (𝓞 E ⧸ P)[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hp1
    have hsub : (Finset.univ : Finset (𝓞 E ⧸ P)).val ⊆ (X ^ p - X : (𝓞 E ⧸ P)[X]).roots := by
      intro y _
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [mem_roots hQ, IsRoot.def, eval_sub, eval_pow, eval_X, ← map_pow, ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem, ← neg_sub]
      exact P.neg_mem (hfrob x)
    have h := card_le_degree_of_subset_roots hsub
    rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ hp1, Finset.card_univ] at h
    rwa [Nat.card_eq_fintype_card]
  constructor
  · have e1 : P.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one P ℤ
    have e2 : P.inertiaDeg ℤ = 1 := by
      have h := Ideal.absNorm_pow_inertiaDeg (Ideal.span {(p : ℤ)}) P
      have h0 : Ideal.absNorm (Ideal.span {(p : ℤ)}) = p := by
        rw [Ideal.absNorm_span_singleton]
        simp
      have h1 : Ideal.absNorm P = Nat.card (𝓞 E ⧸ P) := by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rw [h0, h1] at h
      have h2 : p ^ P.inertiaDeg ℤ ≤ p ^ 1 := by rw [h, pow_one]; exact hle
      have h3 := (Nat.pow_le_pow_iff_right hp1).1 h2
      have h4 := Ideal.inertiaDeg_pos P ℤ
      omega
    have hm := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (Ideal.span {(p : ℤ)}) (𝓞 E) Gal(E/ℚ)
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P Gal(E/ℚ),
      Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P Gal(E/ℚ), e1, e2, mul_one, mul_one,
      IsGaloisGroup.card_eq_finrank Gal(E/ℚ) ℚ E] at hm
    exact hm
  · intro x
    have hinj : Function.Injective (Ideal.quotientMap P (algebraMap ℤ (𝓞 E))
        (le_refl (P.comap (algebraMap ℤ (𝓞 E))))) := Ideal.quotientMap_injective
    have hbij := hinj.bijective_of_nat_card_le (by
      change Nat.card (𝓞 E ⧸ P) ≤ Nat.card (ℤ ⧸ P.under ℤ)
      rw [hcard]
      exact hle)
    obtain ⟨q, hq⟩ := hbij.2 (Ideal.Quotient.mk P x)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨a, ?_⟩
    rw [Ideal.quotientMap_mk] at hq
    exact Ideal.Quotient.eq.1 hq.symm

end GlobalTheory.CompanionTheory.Ar.RT.SplitPl

namespace GlobalTheory.CompanionTheory.Ar.RT

open Polynomial GlobalTheory.CompanionTheory.Ar.RT.SplitPl

theorem exists_splitsFully_notMem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois ℚ E] (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)),
    ∃ v ∉ S, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully E v ∧ Nonempty (E →ₐ[F] Fv F v) := by
  intro F E _ _ _ _ _ _ S
  classical
  obtain ⟨θ, hθ⟩ := exists_integer_generator (F := F) (E := E)
  have hint : IsIntegral (𝓞 F) (θ : E) := IsIntegral.tower_top (R := ℤ) θ.2
  have hD : aeval θ (derivative (minpoly (𝓞 F) (θ : E))) ≠ 0 := fun e => by
    have h1 : aeval (θ : E) (derivative (minpoly F (θ : E))) ≠ 0 :=
      (minpoly.irreducible (Algebra.IsIntegral.isIntegral (R := F) (θ : E))).separable.aeval_derivative_ne_zero
        (minpoly.aeval _ _)
    apply h1
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' F hint, derivative_map, aeval_map_algebraMap,
      aeval_algebraMap_apply E θ, e, map_zero]
  set D : 𝓞 E := aeval θ (derivative (minpoly (𝓞 F) (θ : E))) with hDdef
  set N : ℕ := Ideal.absNorm (Ideal.span {D}) with hN
  have hN0 : N ≠ 0 := fun e => hD (by
    rwa [hN, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] at e)
  obtain ⟨p, hp, hpT, P, hP, hl, hu, hf⟩ := ReciprocityTheory.Cheb.statement_holds E 1
    (S.image (fun v => Ideal.absNorm (v.asIdeal.under ℤ)) ∪ N.primeFactors)
  obtain ⟨hcount, hres⟩ := split_of_frob_one hp P hu hf
  have hunder : P.under ℤ = Ideal.span {(p : ℤ)} := hl.over.symm
  have hpP : (p : 𝓞 E) ∈ P := by
    have h : (p : ℤ) ∈ P.under ℤ := hunder ▸ Ideal.mem_span_singleton_self _
    simpa using h
  have hvb : P.under (𝓞 F) ≠ ⊥ := fun e => hp.ne_zero (by
    have h : (p : 𝓞 F) ∈ P.under (𝓞 F) := by
      change algebraMap (𝓞 F) (𝓞 E) (p : 𝓞 F) ∈ P
      simpa using hpP
    rw [e, Ideal.mem_bot] at h
    exact_mod_cast h)
  let v : HeightOneSpectrum (𝓞 F) := ⟨P.under (𝓞 F), inferInstance, hvb⟩
  have hvu : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
    rw [← hunder]
    exact Ideal.under_under P
  refine ⟨v, fun hv => hpT (Finset.mem_union_left _ (Finset.mem_image.2 ⟨v, hv, ?_⟩)), ?_, ?_⟩
  · rw [hvu, Ideal.absNorm_span_singleton]
    simp
  · change ((v.asIdeal.under ℤ).primesOver (𝓞 E)).ncard = _
    rw [hvu]
    exact hcount
  · obtain ⟨a, ha⟩ := hres θ
    refine nonempty_algHom_of_congr θ hθ v P (fun c => Iff.rfl) (a : 𝓞 F) (by simpa using ha) fun hDP => ?_
    have h1 : (N : 𝓞 E) ∈ P := (Ideal.span_singleton_le_iff_mem P).2 hDP (Ideal.absNorm_mem _)
    have h2 : (N : ℤ) ∈ P.under ℤ := by
      change algebraMap ℤ (𝓞 E) (N : ℤ) ∈ P
      simpa using h1
    rw [hunder, Ideal.mem_span_singleton] at h2
    exact hpT (Finset.mem_union_right _ (Nat.mem_primeFactors.2 ⟨hp, Int.natCast_dvd_natCast.1 h2, hN0⟩))

end GlobalTheory.CompanionTheory.Ar.RT
