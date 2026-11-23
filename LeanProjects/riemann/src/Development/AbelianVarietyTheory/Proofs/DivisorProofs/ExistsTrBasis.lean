import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightedMonomialValuationOfParametersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingGraphGenericPointOfInjectiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.GraphPlace

section Gen

variable {K L F W : Type} [Field K] [Field L] [Field F] [Field W] [Algebra K L] [Algebra K F] [Algebra L W]
  [Algebra K W] [IsScalarTower K L W]

omit [Algebra K W] [IsScalarTower K L W] in

theorem indep_of_lift {ι : Type} (ψ : L ⊗[K] F →ₐ[L] W) (hψ : Function.Injective ψ) {x : ι → F}
    (hx : AlgebraicIndependent K x) : AlgebraicIndependent L fun i => ψ (1 ⊗ₜ x i) := by
  rw [algebraicIndependent_iff_injective_aeval]
  have h1 : Function.Injective (Algebra.TensorProduct.map (AlgHom.id L L) (MvPolynomial.aeval (R := K) x)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := L) (MvPolynomial.aeval (R := K) x).toLinearMap
      (algebraicIndependent_iff_injective_aeval.1 hx)
  have e : (MvPolynomial.aeval (R := L) fun i => ψ (1 ⊗ₜ x i)) =
      (ψ.comp (Algebra.TensorProduct.map (AlgHom.id L L) (MvPolynomial.aeval (R := K) x))).comp
        (MvPolynomial.algebraTensorAlgEquiv (σ := ι) K L).symm.toAlgHom := by
    ext i
    simp
  rw [e]
  exact (hψ.comp h1).comp (MvPolynomial.algebraTensorAlgEquiv (σ := ι) K L).symm.injective

theorem trdeg_of_lift (ψ : L ⊗[K] F →ₐ[L] W) (hψ : Function.Injective ψ) (M : IntermediateField L W)
    (h1 : ∀ f, ψ (1 ⊗ₜ f) ∈ M) (h2 : M ≤ IntermediateField.adjoin L (Set.range fun f => ψ (1 ⊗ₜ f))) :
    Algebra.trdeg L M = Algebra.trdeg K F := by
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' K F
  have hy := indep_of_lift ψ hψ hx.1
  rw [← hx.cardinalMk_eq_trdeg]
  apply le_antisymm
  · let E := IntermediateField.adjoin L (Set.range fun i => ψ (1 ⊗ₜ x i))
    let A := (algebraicClosure E W).restrictScalars L
    have hA : M ≤ A := by
      refine h2.trans (IntermediateField.adjoin_le_iff.2 ?_)
      rintro _ ⟨f, rfl⟩
      show ψ (1 ⊗ₜ f) ∈ algebraicClosure E W
      rw [mem_algebraicClosure_iff]
      let φ : F →ₐ[K] W := (ψ.restrictScalars K).comp Algebra.TensorProduct.includeRight
      have hf : IsAlgebraic (Algebra.adjoin K (Set.range x)) f := hx.isAlgebraic.isAlgebraic f
      have hm : ∀ a ∈ Algebra.adjoin K (Set.range x), φ a ∈ E := by
        intro a ha
        have : Algebra.adjoin K (Set.range x) ≤ ((E.restrictScalars K).toSubalgebra).comap φ := by
          refine Algebra.adjoin_le ?_
          rintro _ ⟨i, rfl⟩
          exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
        exact this ha
      let g : Algebra.adjoin K (Set.range x) →+* E :=
        (φ.toRingHom.comp (Algebra.adjoin K (Set.range x)).val.toRingHom).codRestrict E fun a => hm a a.2
      have hg : Function.Injective g := fun a b h =>
        Subtype.ext (φ.toRingHom.injective (congrArg Subtype.val h))
      exact hf.ringHom_of_comp_eq g φ.toRingHom hg rfl
    have hE : Algebra.trdeg L E ≤ Cardinal.mk ι := by
      have : Algebra.IsAlgebraic (Algebra.adjoin L (Set.range fun i => (⟨ψ (1 ⊗ₜ x i),
          IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : E))) E := by
        rw [← IntermediateField.isAlgebraic_adjoin_iff_top]
        have htop : IntermediateField.adjoin L (Set.range fun i => (⟨ψ (1 ⊗ₜ x i),
          IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : E)) = ⊤ := by
          apply IntermediateField.lift_injective
          rw [IntermediateField.lift_adjoin, IntermediateField.lift_top, ← Set.range_comp]
          rfl
        rw [htop]
        infer_instance
      exact (Algebra.IsAlgebraic.trdeg_le_cardinalMk L _ (alg := this)).trans Cardinal.mk_range_le
    calc Algebra.trdeg L M ≤ Algebra.trdeg L A :=
          trdeg_le_of_injective (IntermediateField.inclusion hA) (IntermediateField.inclusion_injective hA)
      _ = Algebra.trdeg L (algebraicClosure E W) := rfl
      _ = Algebra.trdeg L E := by
          haveI : FaithfulSMul E (algebraicClosure E W) :=
            (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap E (algebraicClosure E W)).injective
          rw [← trdeg_add_eq L E (A := algebraicClosure E W), trdeg_eq_zero (R := E) (A := algebraicClosure E W), add_zero]
      _ ≤ _ := hE
  · have : AlgebraicIndependent L fun i => (⟨ψ (1 ⊗ₜ x i), h1 _⟩ : M) :=
      AlgebraicIndependent.of_comp M.val hy
    exact this.cardinalMk_le_trdeg

end Gen

theorem exists_trBasis {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ']
    [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]
    [IsFractionRing (K ⊗[ℂ] κ') L] {n k' : ℕ} {x : Fin n → K} {τ' : Fin k' → κ'}
    (hx : TrBasis (algebraMap ℂ K) x) (hτ : TrBasis (algebraMap ℂ κ') τ') :
    ∃ w : Fin (k' + n) → L, TrBasis (algebraMap ℂ L) w := by
  have e1 : (algebraMap ℂ K).toAlgebra = (inferInstance : Algebra ℂ K) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have e2 : (algebraMap ℂ κ').toAlgebra = (inferInstance : Algebra ℂ κ') :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have e3 : (algebraMap ℂ L).toAlgebra = (inferInstance : Algebra ℂ L) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  unfold TrBasis at *
  rw [e1] at hx
  rw [e2] at hτ
  rw [e3]
  letI : Algebra K L := ((algebraMap (K ⊗[ℂ] κ') L).comp (algebraMap K (K ⊗[ℂ] κ'))).toAlgebra
  haveI : IsScalarTower K (K ⊗[ℂ] κ') L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply ℂ (K ⊗[ℂ] κ') L,
      IsScalarTower.algebraMap_apply ℂ K (K ⊗[ℂ] κ')]
    rfl
  have h1 : Algebra.trdeg K L = Algebra.trdeg ℂ κ' := by
    let ψ := IsScalarTower.toAlgHom K (K ⊗[ℂ] κ') L
    rw [← trdeg_of_lift ψ (IsFractionRing.injective _ _) ⊤ (fun _ => trivial) ?_]
    · exact (IntermediateField.topEquiv (F := K) (E := L)).trdeg_eq.symm
    · intro z _
      have hm : ∀ a, ψ a ∈ IntermediateField.adjoin K (Set.range fun f => ψ (1 ⊗ₜ f)) := by
        intro a
        induction a using TensorProduct.induction_on with
        | zero => rw [map_zero]; exact zero_mem _
        | add a b ha hb => rw [map_add]; exact add_mem ha hb
        | tmul l f =>
          have : l ⊗ₜ[ℂ] f = l • ((1 : K) ⊗ₜ[ℂ] f) := by simp [TensorProduct.smul_tmul']
          rw [this, map_smul]
          exact IntermediateField.smul_mem _
            (IntermediateField.subset_adjoin K _ (Set.mem_range_self f))
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := K ⊗[ℂ] κ') z
      exact div_mem (hm a) (hm b)
  haveI : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap K L).injective
  have h2 := trdeg_add_eq ℂ K (A := L)
  rw [h1, ← hx.cardinalMk_eq_trdeg, ← hτ.cardinalMk_eq_trdeg] at h2
  obtain ⟨ι, w, hw⟩ := exists_isTranscendenceBasis' ℂ L
  have h3 : Cardinal.mk (Fin (k' + n)) = Cardinal.mk ι := by
    rw [hw.cardinalMk_eq_trdeg, ← h2]
    simp [add_comm]
  obtain ⟨e⟩ := Cardinal.eq.1 h3
  exact ⟨w ∘ e, hw.comp_equiv e⟩

theorem exists_place : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ'),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' → (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  IsLocModel (algebraMap ℂ K) R → Function.Injective π → (∀ g : K, ∃ a b : R, (b : K) ≠ 0 ∧ g * b = a) →
  ∀ M : ℕ, 1 ≤ k → 1 ≤ M → ∃ V : Place (algebraMap ℂ L),
    (∀ g : K, algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1) ∈ V.ring) ∧
    (∀ b : κ', b ≠ 0 → V.ord (algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ b)) = 0) ∧
    (∀ g : K, g ≠ 0 → V.ord (algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1)) = 0) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, ρ (π (a i)) * b i ≠ 0 →
      (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ≠ 0 ∧ V.ord ((fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b) = 0) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ≠ 0 →
      ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M → (M : ℤ) ≤ V.ord ((fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b)) ∧
    V.formOrd (dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
      (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1)))) + 1 ≤ k := by
  intro K κ κ' L _ _ _ _ _ _ _ _ _ _ _ n k k' x τ' R π ρ hx hτ hO hz hc hπ hR hinj hfr M hk _
  obtain ⟨Q, hQ, z, hm, hdim, hg, hb, hu, hJ, y, q, hy, hq, hform⟩ :=
    GlobalTheory.T.localRing_graph_generic_point_of_injective (L := L) n k k' x τ' R π ρ hx hτ hz hc hπ hinj hfr hR hO hk
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
  obtain ⟨w, hw⟩ := exists_trBasis (L := L) hx hτ
  obtain ⟨V, hV, hunit, -, hpow, hfo⟩ := GlobalTheory.T.exists_weighted_monomial_valuation_of_parameters (algebraMap ℂ L) Q hQ r (k' + n) z (fun _ => 1)
    hm (by rw [hdim]; push_cast; rfl) rfl (fun _ => le_rfl) ⟨w, hw⟩
  have hne : ∀ q : Q, IsUnit q → (q : L) ≠ 0 := fun q hq => (hq.map Q.subtype).ne_zero
  refine ⟨V, fun g => ?_, fun b h => ?_, fun g h => ?_, fun l a b h => ?_, fun l a b h0 h => ?_, ?_⟩
  · by_cases h : g = 0
    · subst h
      rw [TensorProduct.zero_tmul, map_zero]
      exact zero_mem _
    · obtain ⟨q, -, e⟩ := hg g h
      exact e ▸ hV _ q.2
  · obtain ⟨q, hq, e⟩ := hb b h
    exact e ▸ hunit q hq
  · obtain ⟨q, hq, e⟩ := hg g h
    exact e ▸ hunit q hq
  · obtain ⟨q, hq, e⟩ := hu l a b h
    exact e ▸ ⟨hne q hq, hunit q hq⟩
  · obtain ⟨q, e, hq⟩ := hJ M l a b h
    rw [← e] at h0 ⊢
    exact hpow M q h0 hq
  · have h := hfo y hy
    have hs : V.formOrd ((q : L) • dForm (algebraMap ℂ L) (fun i => (y i : L))) =
        V.formOrd (dForm (algebraMap ℂ L) (fun i => (y i : L))) := by
      by_cases h0 : dForm (algebraMap ℂ L) (fun i => (y i : L)) = 0
      · rw [h0, smul_zero]
      · rw [V.formOrd_smul hw h0 (hne q hq), hunit q hq, zero_add]
    rw [hform, hs]
    simpa using h

end GlobalTheory.FieldPair.GraphPlace
