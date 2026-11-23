import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToQMemMaximalIdealIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrBasisInImageOfFractionFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceGraphIdealTensorNeTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingOfVarietyPointLocalizationPlaceTensorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitMulZpowUniformiserTmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTmulNotMemPrimeOfGraphImageNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphJetsMemPowSupUniformiserStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphIdealLocalizationMaximalIdealEqSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimLocalizationGraphIdealMinimalPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeGeneratorTopFormsTensorLocalizationOrdStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

theorem GlobalTheory.GraphLocal.exists_locModel_graph : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ'),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' → (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  ∀ (E : Place (algebraMap ℂ K)), E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  ∃ (Q : Subring L) (hQ : IsLocModel (algebraMap ℂ L) Q), letI := hQ.isLocalRing; ∃ z : Fin (k + 1) → Q,
    IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) ∧ ringKrullDim Q = k + 1 ∧
    (∀ e ∈ E.ring, algebraMap (K ⊗[ℂ] κ') L (e ⊗ₜ 1) ∈ Q) ∧
    (∀ g : K, g ≠ 0 → ∃ q : Q, IsUnit q ∧ algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1) = q * (z 0 : L) ^ E.ord g) ∧
    (∀ b : κ', b ≠ 0 → ∃ q : Q, IsUnit q ∧ (q : L) = algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ b)) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, ρ (π (a i)) * b i ≠ 0 →
      ∃ q : Q, IsUnit q ∧ (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b) ∧
    (∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
      ∃ q : Q, (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ∧ q ∈ IsLocalRing.maximalIdeal Q ^ M ⊔ Ideal.span {z 0}) ∧
    ∃ (y : Fin (k' + n) → Q) (q : Q), IsFreeGen Q (dForm ((algebraMap ℂ L).codRestrict Q hQ.const_mem) y) ∧ IsUnit q ∧
      dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
        (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1))) =
        ((q : L) * (z 0 : L) ^ E.formOrd (dForm (algebraMap ℂ K) x)) • dForm (algebraMap ℂ L) (fun i => (y i : L)) := by
  intro K κ κ' L _ _ _ _ _ _ _ _ _ _ _ n k k' x τ' R π ρ hx hτ hO' hz hcompat hC hfrac E hER hcentre
  have hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L) := IsFractionRing.injective _ _
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  obtain ⟨zR, hzR⟩ := GlobalTheory.T.exists_trBasis_in_image_of_fractionField k R π hfrac hz
  obtain ⟨𝔭, h𝔭⟩ := Ideal.nonempty_minimalPrimes (GlobalTheory.T.placeGraphIdealTensor_ne_top (κ' := κ') R π ρ E hcompat hC hfrac hER hcentre)
  haveI : 𝔭.IsPrime := h𝔭.1.1
  have hle : graphIdeal E R π ρ ≤ 𝔭 := h𝔭.1.2
  have hQ : IsLocModel (algebraMap ℂ L) (locAt (L := L) 𝔭) := GlobalTheory.T.isLocalRingOfVarietyPoint_localization_placeTensor E 𝔭 hO'
  letI := hQ.isLocalRing
  have hmax := GlobalTheory.T.graphIdeal_localization_maximalIdeal_eq_span (L := L) k R π ρ E hER t zR 𝔭 hO' hcompat hC hfrac hcentre ht hzR h𝔭
  have hdim := GlobalTheory.T.ringKrullDim_localization_graphIdeal_minimalPrime (L := L) k R π ρ E 𝔭 hO' hcompat hC hfrac hER hcentre hz h𝔭
  have hz0 : ((toQ (L := L) 𝔭 (gens E R π ρ hER t zR 0) : locAt (L := L) 𝔭) : L) =
      algebraMap (K ⊗[ℂ] κ') L ((t : K) ⊗ₜ 1) := by
    simp [gens]
  refine ⟨locAt (L := L) 𝔭, hQ, fun i => toQ 𝔭 (gens E R π ρ hER t zR i), hmax, hdim, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    exact (toQ (L := L) 𝔭 ⟨e ⊗ₜ 1, tmul_mem (A := placeAlg E) he 1⟩).2
  · intro g hg
    rw [hz0]
    exact GlobalTheory.T.exists_isUnit_mul_zpow_uniformiser_tmul E 𝔭 t hinj ht g hg
  · intro b hb
    refine ⟨toQ 𝔭 ⟨1 ⊗ₜ b, tmul_mem (one_mem (placeAlg E)) b⟩, isUnit_toQ 𝔭 hinj ?_, rfl⟩
    intro h
    apply one_notMem 𝔭
    have h2 := 𝔭.mul_mem_right ⟨(1 : K) ⊗ₜ b⁻¹, tmul_mem (one_mem (placeAlg E)) b⁻¹⟩ h
    convert h2 using 1
    apply Subtype.ext
    simp [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hb, Algebra.TensorProduct.one_def]
  · intro l a b hs
    have hw : ∑ i, (a i : K) ⊗ₜ[ℂ] b i ∈ tens (κ' := κ') (placeAlg E) :=
      Subalgebra.sum_mem _ fun i _ => tmul_mem (hER _ (a i).2) (b i)
    refine ⟨toQ 𝔭 ⟨_, hw⟩, isUnit_toQ 𝔭 hinj (GlobalTheory.T.sum_tmul_notMem_prime_of_graph_image_ne_zero R π ρ E 𝔭 hle hER l a b ⟨_, hw⟩ rfl hs), ?_⟩
    simp [map_sum]
  · intro M l a b hJ
    have hw : ∑ i, (a i : K) ⊗ₜ[ℂ] b i ∈ tens (κ' := κ') (placeAlg E) :=
      Subalgebra.sum_mem _ fun i _ => tmul_mem (hER _ (a i).2) (b i)
    refine ⟨toQ 𝔭 ⟨_, hw⟩, by simp [map_sum], ?_⟩
    have h1 := GlobalTheory.T.graphJets_mem_pow_sup_uniformiser R π ρ E 𝔭 t hle ht hcompat hC hfrac hER hcentre M l a b ⟨_, hw⟩ rfl hJ
    have h2 := Ideal.mem_map_of_mem (toQ (L := L) 𝔭) h1
    rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span, Set.image_singleton] at h2
    have h3 : Ideal.map (toQ (L := L) 𝔭) 𝔭 ^ M ⊔ Ideal.span {toQ (L := L) 𝔭 ⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩} ≤
        IsLocalRing.maximalIdeal (locAt (L := L) 𝔭) ^ M ⊔
          Ideal.span {toQ (L := L) 𝔭 (gens E R π ρ hER t zR 0)} :=
      sup_le_sup (Ideal.pow_right_mono (map_le_maximalIdeal 𝔭 hinj) M) le_rfl
    exact h3 h2
  · obtain ⟨y, q, hy, hq, e⟩ := GlobalTheory.T.exists_freeGenerator_topForms_tensorLocalization_order n k' x τ' E 𝔭 t hQ.const_mem hx hτ hO' ht
    refine ⟨y, q, hy, hq, ?_⟩
    rw [hz0]
    exact e
