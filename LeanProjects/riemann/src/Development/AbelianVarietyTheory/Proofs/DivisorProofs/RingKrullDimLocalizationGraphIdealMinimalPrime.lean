import Mathlib
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToQMemMaximalIdealIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoePolyMapX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphIdealLocalizationMaximalIdealEqSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingOfVarietyPointLocalizationPlaceTensorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrBasisInImageOfFractionFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatAevalDvrPlaceRingUniformiserResidueLiftsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorSubalgebraMvPolynomialEvalOfFlatAevalStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.GraphLocal

theorem height_ge_of_X_sub_C_mem : ∀ {F : Type} [Field F] (m : ℕ) (c : Fin m → F) (P : Ideal (MvPolynomial (Fin m) F))
    [P.IsPrime], (∀ i, MvPolynomial.X i - MvPolynomial.C (c i) ∈ P) → (m : ℕ∞) ≤ P.height := by
  intro F _ m c P _ hP
  have hmk : ∀ f : MvPolynomial (Fin m) F,
      Ideal.Quotient.mk P f = Ideal.Quotient.mk P (MvPolynomial.C (MvPolynomial.eval c f)) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add, hp, hq, map_add, map_add, map_add]
    | mul_X p i hp =>
      have hi : Ideal.Quotient.mk P (MvPolynomial.X i) = Ideal.Quotient.mk P (MvPolynomial.C (c i)) :=
        Ideal.Quotient.eq.2 (hP i)
      rw [map_mul, hp, hi, ← map_mul, ← map_mul, MvPolynomial.eval_mul, MvPolynomial.eval_X,
        MvPolynomial.C_mul]
  have hsurj : Function.Surjective ((Ideal.Quotient.mk P).comp MvPolynomial.C) := by
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨MvPolynomial.eval c f, (hmk f).symm⟩
  have hmax : P.IsMaximal := by
    let e := RingEquiv.ofBijective _ ⟨((Ideal.Quotient.mk P).comp MvPolynomial.C).injective, hsurj⟩
    exact Ideal.Quotient.maximal_of_isField P (MulEquiv.isField (Field.toIsField F) e.symm.toMulEquiv)
  have htr : Algebra.trdeg F (MvPolynomial (Fin m) F) = m := by
    have h2 := (IsTranscendenceBasis.mvPolynomial (Fin m) F).cardinalMk_eq_trdeg
    rw [Cardinal.mk_fin] at h2
    exact h2.symm
  rw [ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field m htr P]

variable {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ']
  [Algebra (K ⊗[ℂ] κ') L]

theorem height_le_height_of_flat {A : Subalgebra ℂ K} {m : ℕ} (v : Fin m → A)
    (hf : (polyMap (κ' := κ') A v).Flat) (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime] :
    (𝔭.comap (polyMap A v)).height ≤ 𝔭.height := by
  letI := (polyMap (κ' := κ') A v).toAlgebra
  haveI : Module.Flat (MvPolynomial (Fin m) κ') (tens (κ' := κ') A) := hf
  haveI : Algebra.HasGoingDown (MvPolynomial (Fin m) κ') (tens (κ' := κ') A) :=
    Algebra.HasGoingDown.of_flat
  set q := 𝔭.comap (polyMap (κ' := κ') A v) with hq
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  haveI : 𝔭.LiesOver q := ⟨rfl⟩
  obtain ⟨l, hl, hlen⟩ := q.exists_ltSeries_length_eq_height
  haveI : 𝔭.LiesOver l.last.asIdeal := by rw [hl]; infer_instance
  obtain ⟨L', hlen', hlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l 𝔭
  rw [← hlen, ← hlen', (⟨𝔭, ‹_›⟩ : PrimeSpectrum (tens (κ' := κ') A)).height_eq_orderHeight]
  exact Order.length_le_height (le_of_eq hlast)

theorem ringKrullDim_locAt {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime]
    (hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L)) :
    ringKrullDim (locAt (L := L) 𝔭) = 𝔭.height := by
  letI := (toQ (L := L) 𝔭).toAlgebra
  haveI : IsLocalization.AtPrime (locAt (L := L) 𝔭) 𝔭 :=
    { map_units := fun s => isUnit_toQ 𝔭 hinj s.2
      surj := fun x => by
        obtain ⟨a, s, hs, e⟩ := exists_mul_toQ 𝔭 x
        exact ⟨(a, ⟨s, hs⟩), e⟩
      exists_of_eq := fun {a b} e => ⟨1, by
        have : a = b := Subtype.ext (hinj (congrArg Subtype.val e))
        rw [this]⟩ }
  exact IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭 _

theorem dim_locAt_graph : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    [Algebra (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (k : ℕ) (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  𝔭 ∈ (graphIdeal E R π ρ).minimalPrimes →
  ringKrullDim (locAt (L := L) 𝔭) = k + 1 := by
  intro K κ κ' L _ _ _ _ _ _ _ _ _ k R π ρ E 𝔭 _ hO' hc1 hc2 hfrac hER hcent hz h𝔭
  have hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L) := IsFractionRing.injective _ L
  obtain ⟨zR, hzR⟩ := GlobalTheory.T.exists_trBasis_in_image_of_fractionField k R π hfrac hz
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  rw [ringKrullDim_locAt 𝔭 hinj]
  apply le_antisymm
  ·
    rw [← ringKrullDim_locAt 𝔭 hinj]
    letI : Algebra ℂ L := ((algebraMap (K ⊗[ℂ] κ') L).comp (algebraMap ℂ (K ⊗[ℂ] κ'))).toAlgebra
    haveI : IsScalarTower ℂ (K ⊗[ℂ] κ') L := IsScalarTower.of_algebraMap_eq' rfl
    have hQ := GlobalTheory.T.isLocalRingOfVarietyPoint_localization_placeTensor (L := L) E 𝔭 hO'
    letI : IsLocalRing (locAt (L := L) 𝔭) := isLocalRing_locAt 𝔭 hinj
    letI : Algebra ℂ (locAt (L := L) 𝔭) :=
      ((algebraMap ℂ L).codRestrict _ hQ.const_mem).toAlgebra
    haveI : Algebra.EssFiniteType ℂ (locAt (L := L) 𝔭) := hQ.essFiniteType
    haveI : IsNoetherianRing (locAt (L := L) 𝔭) := Algebra.EssFiniteType.isNoetherianRing ℂ _
    have hmax := GlobalTheory.T.graphIdeal_localization_maximalIdeal_eq_span (L := L) k R π ρ E hER t zR 𝔭 hO' hc1 hc2 hfrac hcent ht hzR h𝔭
    refine (ringKrullDim_le_spanFinrank_maximalIdeal _).trans ?_
    rw [hmax]
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := locAt (L := L) 𝔭)
      (Set.finite_range fun i => toQ (L := L) 𝔭 (gens E R π ρ hER t zR i))
    have h2 : (Set.range fun i => toQ (L := L) 𝔭 (gens E R π ρ hER t zR i)).ncard ≤ k + 1 := by
      rw [← Set.image_univ]
      refine (Set.ncard_image_le Set.finite_univ).trans ?_
      simp [Set.ncard_univ]
    have h3 := h1.trans h2
    exact_mod_cast h3
  ·
    have e : (algebraMap ℂ κ).toAlgebra = (inferInstance : Algebra ℂ κ) :=
      Algebra.algebra_ext _ _ fun _ => rfl
    have hzR' : IsTranscendenceBasis ℂ (fun i => π (zR i)) := by
      unfold TrBasis at hzR; rw [e] at hzR; exact hzR
    let v : Fin (k + 1) → placeAlg E := Fin.cons (⟨(t : K), t.2⟩ : placeAlg E)
        (fun i => (⟨(zR i : K), hER _ (zR i).2⟩ : placeAlg E))
    have hf := GlobalTheory.T.flat_tensorSubalgebraMvPolynomialEval_of_flat_aeval (κ' := κ') (placeAlg E) (k + 1) v
      (GlobalTheory.T.flat_aeval_dvrPlaceRing_uniformiser_residueLifts k R π E hER t zR hc1 hc2 hcent ht hzR'.1)
    have hle := height_le_height_of_flat v hf 𝔭
    have hgr : graphIdeal E R π ρ ≤ 𝔭 := h𝔭.1.2
    have hX : ∀ i, MvPolynomial.X i - MvPolynomial.C ((Fin.cons (0 : κ') fun j => ρ (π (zR j)) :
        Fin (k + 1) → κ') i) ∈ 𝔭.comap (polyMap (κ' := κ') (placeAlg E) v) := by
      intro i
      rw [Ideal.mem_comap]
      apply hgr
      apply Ideal.subset_span
      refine Fin.cases ?_ (fun j => ?_) i
      · left
        refine ⟨(t : K), ?_, ?_⟩
        · rw [E.ord_irreducible ht]; exact one_pos
        · simp [v]
      · right
        refine ⟨zR j, ?_⟩
        simp [v]
    have hB3 := height_ge_of_X_sub_C_mem (k + 1) _ _ hX
    have := hB3.trans hle
    exact_mod_cast this

end GlobalTheory.GraphLocal
