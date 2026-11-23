import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceTopFormOrdersApi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightedMonomialValuationOfParametersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularLocalModelGraphOfPlaceStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair

theorem isTranscendenceBasis_one_tmul {k K F W ι : Type} [Field k] [Field K] [Field F] [Field W]
    [Algebra k K] [Algebra k F] [Algebra K W] [Algebra (K ⊗[k] F) W]
    [IsScalarTower K (K ⊗[k] F) W] [IsFractionRing (K ⊗[k] F) W] {x : ι → F}
    (hx : IsTranscendenceBasis k x) :
    IsTranscendenceBasis K fun i => algebraMap (K ⊗[k] F) W (1 ⊗ₜ x i) := by
  let ψ : K ⊗[k] F →ₐ[K] W := IsScalarTower.toAlgHom K (K ⊗[k] F) W
  have hψ : Function.Injective ψ := IsFractionRing.injective (K ⊗[k] F) W
  have hy : AlgebraicIndependent K fun i => ψ (1 ⊗ₜ x i) := by
    rw [algebraicIndependent_iff_injective_aeval]
    have h1 : Function.Injective
        (Algebra.TensorProduct.map (AlgHom.id K K) (MvPolynomial.aeval (R := k) x)) :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := K)
        (MvPolynomial.aeval (R := k) x).toLinearMap
        (algebraicIndependent_iff_injective_aeval.1 hx.1)
    have e : (MvPolynomial.aeval (R := K) fun i => ψ (1 ⊗ₜ x i)) =
        (ψ.comp (Algebra.TensorProduct.map (AlgHom.id K K) (MvPolynomial.aeval (R := k) x))).comp
          (MvPolynomial.algebraTensorAlgEquiv (σ := ι) k K).symm.toAlgHom := by
      ext i
      simp
    rw [e]
    exact (hψ.comp h1).comp (MvPolynomial.algebraTensorAlgEquiv (σ := ι) k K).symm.injective
  change IsTranscendenceBasis K fun i => ψ (1 ⊗ₜ x i)
  rw [hy.isTranscendenceBasis_iff_isAlgebraic, ← IntermediateField.isAlgebraic_adjoin_iff_top]
  let E := IntermediateField.adjoin K (Set.range fun i => ψ (1 ⊗ₜ x i))
  let φ : F →+* W := (ψ : K ⊗[k] F →+* W).comp
    (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := F)).toRingHom
  have hm : ∀ a ∈ Algebra.adjoin k (Set.range x), φ a ∈ E := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨i, rfl⟩ := ha
      exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
    | algebraMap r =>
      have : φ (algebraMap k F r) = algebraMap K W (algebraMap k K r) := by
        rw [← ψ.commutes]
        change ψ (1 ⊗ₜ algebraMap k F r) = ψ (algebraMap k K r ⊗ₜ 1)
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          TensorProduct.smul_tmul]
      rw [this]
      exact E.algebraMap_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let g : Algebra.adjoin k (Set.range x) →+* E :=
    (φ.comp (Algebra.adjoin k (Set.range x)).val.toRingHom).codRestrict E fun a => hm a a.2
  have hg : Function.Injective g := fun a b h =>
    Subtype.ext (φ.injective (congrArg Subtype.val h))
  have hT : ∀ a, ψ a ∈ algebraicClosure E W := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
    | tmul l f =>
      have : l ⊗ₜ[k] f = algebraMap K _ l * ((1 : K) ⊗ₜ[k] f) := by simp
      rw [this, map_mul, ψ.commutes]
      refine mul_mem ((algebraicClosure E W).algebraMap_mem (algebraMap K E l)) ?_
      rw [mem_algebraicClosure_iff]
      exact (hx.isAlgebraic.isAlgebraic f).ringHom_of_comp_eq g φ hg rfl
  refine ⟨fun z => ?_⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := K ⊗[k] F) z
  exact mem_algebraicClosure_iff.1 (div_mem (hT a) (hT b))

theorem trBasis_append_tmul {k K F W : Type} [Field k] [Field K] [Field F] [Field W]
    [Algebra k K] [Algebra k F] [Algebra k W] [Algebra (K ⊗[k] F) W]
    [IsScalarTower k (K ⊗[k] F) W] [IsFractionRing (K ⊗[k] F) W] {n m : ℕ} {x : Fin n → K}
    {y : Fin m → F} (hx : TrBasis (algebraMap k K) x) (hy : TrBasis (algebraMap k F) y) :
    TrBasis (algebraMap k W) (Fin.append (fun i => algebraMap (K ⊗[k] F) W (1 ⊗ₜ y i))
      (fun i => algebraMap (K ⊗[k] F) W (x i ⊗ₜ 1))) := by
  have key : ∀ {A : Type} [Field A] [inst : Algebra k A] {l : ℕ} (u : Fin l → A),
      TrBasis (algebraMap k A) u ↔ IsTranscendenceBasis k u := by
    intro A _ inst l u
    have e : (algebraMap k A).toAlgebra = inst := Algebra.algebra_ext _ _ fun _ => rfl
    unfold TrBasis
    rw [e]
  rw [key] at hx hy ⊢
  letI : Algebra K W := ((algebraMap (K ⊗[k] F) W).comp (algebraMap K (K ⊗[k] F))).toAlgebra
  haveI : IsScalarTower K (K ⊗[k] F) W := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k K W := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k (K ⊗[k] F) W,
      IsScalarTower.algebraMap_apply k K (K ⊗[k] F), ← IsScalarTower.algebraMap_apply]
  have h := hx.sumElim_comp (isTranscendenceBasis_one_tmul (K := K) (W := W) hy)
  rw [← isTranscendenceBasis_equiv finSumFinEquiv]
  convert h using 1
  funext i
  rcases i with i | i
  · simp
  · simp
    rfl

theorem Place.le_ord_iff_div_mem {k K : Type} [Field k] [Field K] {c : k →+* K} (V : Place c)
    {f t : K} (hf : f ≠ 0) (ht : t ≠ 0) : V.ord t ≤ V.ord f ↔ f / t ∈ V.ring := by
  rw [← V.ord_nonneg_iff (div_ne_zero hf ht), div_eq_mul_inv, V.ord_mul hf (inv_ne_zero ht),
    V.ord_inv]
  omega

theorem exists_place_weighted_over_place : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ'),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' → (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  ∀ (E : Place (algebraMap ℂ K)), E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  ∀ M : ℕ, 1 ≤ k → 1 ≤ M → ∃ V : Place (algebraMap ℂ L),
    (∀ r : R, algebraMap (K ⊗[ℂ] κ') L ((r : K) ⊗ₜ 1) ∈ V.ring) ∧
    (∀ b : κ', b ≠ 0 → V.ord (algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ b)) = 0) ∧
    (∀ g : K, g ≠ 0 → V.ord (algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1)) = M * E.ord g) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, ρ (π (a i)) * b i ≠ 0 →
      (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ≠ 0 ∧ V.ord ((fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b) = 0) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ≠ 0 →
      ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M → (M : ℤ) ≤ V.ord ((fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b)) ∧
    V.formOrd (dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
      (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1)))) + 1 ≤ M * (E.formOrd (dForm (algebraMap ℂ K) x) + 1) + k := by
  intro K κ κ' L _ _ _ _ _ _ _ _ _ _ _ n k k' x τ' R π ρ hx hτ hO hz hc hR hπ E hER hE M hk hM
  obtain ⟨Q, hQ, z, hm, hdim, hEQ, hg, hb, hu, hJ, y, q, hy, hq, hform⟩ :=
    GlobalTheory.T.exists_regular_localModel_graph_of_place (L := L) n k k' x τ' R π ρ hx hτ hO hz hc hR hπ E hER hE
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hw := trBasis_append_tmul (W := L) hx hτ
  let σ : Equiv.Perm (Fin (k + 1 + 1)) := Equiv.swap 0 1
  let wt : Fin (k + 1 + 1) → ℕ := fun i => if i = 1 then M else 1
  obtain ⟨V, hVQ, hV0, hVz, hVd, hVf⟩ := GlobalTheory.T.exists_weighted_monomial_valuation_of_parameters (algebraMap ℂ L) Q hQ (k + 1) (k' + n)
    (z ∘ σ) wt (by rw [σ.surjective.range_comp]; exact hm) hdim (by simp [wt])
    (fun i => by simp only [wt]; split_ifs <;> omega) ⟨_, hw⟩
  have hz0 : V.ord (z 0) = M := by simpa [σ, wt] using hVz 1
  have hz0' : (z 0 : L) ≠ 0 := by
    intro h
    rw [h, Place.ord, map_zero, WithZero.log_zero] at hz0
    omega
  have hne : ∀ p : Q, IsUnit p → (p : L) ≠ 0 := fun p hp => (hp.map Q.subtype).ne_zero
  have hmul : ∀ (p : Q) (a : ℤ), IsUnit p → V.ord ((p : L) * (z 0 : L) ^ a) = M * a := by
    intro p a hp
    rw [V.ord_mul (hne p hp) (zpow_ne_zero _ hz0'), hV0 p hp, V.ord_zpow, hz0]
    ring
  refine ⟨V, fun r => hVQ _ (hEQ _ (hER _ r.2)), fun b hb0 => ?_, fun g hg0 => ?_,
    fun l a b h => ?_, fun l a b h0 h => ?_, ?_⟩
  · obtain ⟨p, hp, e⟩ := hb b hb0
    rw [← e, hV0 p hp]
  · obtain ⟨p, hp, e⟩ := hg g hg0
    rw [e, hmul p _ hp]
  · obtain ⟨p, hp, e⟩ := hu l a b h
    rw [← e]
    exact ⟨hne p hp, hV0 p hp⟩
  · obtain ⟨p, e, hp⟩ := hJ M l a b h
    rw [← e] at h0 ⊢
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hp
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ht
    rw [← hz0, V.le_ord_iff_div_mem h0 hz0']
    push_cast
    rw [add_div, mul_div_cancel_right₀ _ hz0']
    refine add_mem ?_ (hVQ _ u.2)
    by_cases hs0 : (s : L) = 0
    · rw [hs0, zero_div]
      exact zero_mem _
    · rw [← V.le_ord_iff_div_mem hs0 hz0', hz0]
      exact hVd M s hs0 hs
  · have hd : dForm (algebraMap ℂ L) (fun i => (y i : L)) ≠ 0 := by
      intro h
      have h1 := (isFreeGen_dForm_of_trBasis _ hw).1 (a₁ := 1) (a₂ := 0)
        (by simp only [hform, h, smul_zero])
      exact one_ne_zero h1
    have hs : ∑ i, (wt i : ℤ) = M + (k + 1) := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      have : ∀ i : Fin k, wt i.succ.succ = 1 := fun i =>
        if_neg (fun h => Fin.succ_ne_zero i (Fin.succ_injective _ h))
      simp [this, wt]
      ring
    have h1 := hVf y hy
    rw [hform, V.formOrd_smul hw hd (mul_ne_zero (hne q hq) (zpow_ne_zero _ hz0')), hmul q _ hq]
    rw [hs] at h1
    push_cast
    linarith

end GlobalTheory.FieldPair
