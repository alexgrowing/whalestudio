import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobeniusTwistedHilbertNinetyAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.NormFin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.NormAdic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.InflFacts
import GroundTheory.LocalFields.Uniqueness
import GroundTheory.LocalFields.UnitsPowers
import Development.AutomorphicArithmetic.FrobeniusTwistedNorms.IsAdicCompleteAdjoinRootOfMonic
import Development.AutomorphicArithmetic.FrobeniusTwistedNorms.ExistsTwistedTraceEqOneOfResidueFrobenius
import Development.AutomorphicArithmetic.FrobeniusTwistedNorms.ExistsFrobeniusTwistedNormDvdSubX
import Development.AutomorphicArithmetic.FrobeniusTwistedNorms.ExistsTwistedNormDvdSubXOfAdicComplete

noncomputable section

open ValuativeRel Polynomial

namespace UpperTheory.Gal.InertialTypesAlt.L

section

variable {k K : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K]

private theorem exists_image_add_valuation_lt_subset_iff {F : Type} [Field F] [ValuativeRel F] (x : F) (u : Set F) :
    (∃ γ : (ValueGroupWithZero F)ˣ, (fun y => x + y) '' {z | valuation F z < γ} ⊆ u) ↔
      ∃ c : F, c ≠ 0 ∧ ∀ z, valuation F z < valuation F c → x + z ∈ u := by
  constructor
  · rintro ⟨γ, hγ⟩
    obtain ⟨c, hc⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero F)
    refine ⟨c, ?_, fun z hz => hγ ⟨z, by simpa [hc] using hz, rfl⟩⟩
    rintro rfl
    rw [map_zero] at hc
    exact γ.ne_zero hc.symm
  · rintro ⟨c, hc, h⟩
    refine ⟨Units.mk0 (valuation F c) (by simpa using hc), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact h z hz

private theorem isNonarchimedeanLocalField_of_ringEquiv_of_isInducing {L M : Type} [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Field M] [ValuativeRel M] [TopologicalSpace M] (e : M ≃+* L)
    (hv : ∀ x y : M, x ≤ᵥ y ↔ e x ≤ᵥ e y) (he : Topology.IsInducing e) :
    IsNonarchimedeanLocalField M := by
  have hle : ∀ a b : M, valuation M a ≤ valuation M b ↔ valuation L (e a) ≤ valuation L (e b) := by
    intro a b
    rw [← Valuation.Compatible.vle_iff_le, ← Valuation.Compatible.vle_iff_le, hv]
  have hlt : ∀ a b : M, valuation M a < valuation M b ↔ valuation L (e a) < valuation L (e b) := by
    intro a b
    rw [← not_le, ← not_le, hle]
  haveI : IsValuativeTopology M := ⟨fun {u x} => by
    rw [exists_image_add_valuation_lt_subset_iff, he.nhds_eq_comap x, Filter.mem_comap]
    constructor
    · rintro ⟨t, ht, hts⟩
      rw [IsValuativeTopology.mem_nhds_iff, exists_image_add_valuation_lt_subset_iff] at ht
      obtain ⟨c₁, hc₁, h⟩ := ht
      refine ⟨e.symm c₁, by simpa using hc₁, fun z hz => hts ?_⟩
      rw [hlt, RingEquiv.apply_symm_apply] at hz
      show e (x + z) ∈ t
      rw [map_add]
      exact h _ hz
    · rintro ⟨c, hc, h⟩
      refine ⟨e '' u, ?_, fun z hz => ?_⟩
      · rw [IsValuativeTopology.mem_nhds_iff, exists_image_add_valuation_lt_subset_iff]
        refine ⟨e c, by simpa using hc, fun w hw => ?_⟩
        refine ⟨x + e.symm w, h _ ?_, ?_⟩
        · rw [hlt, RingEquiv.apply_symm_apply]
          exact hw
        · rw [map_add, RingEquiv.apply_symm_apply]
      · obtain ⟨z', hz', hzz⟩ := hz
        rw [e.injective hzz] at hz'
        exact hz'⟩
  haveI : LocallyCompactSpace M := he.locallyCompactSpace (by
    rw [Set.range_eq_univ.mpr e.surjective]
    exact isOpen_univ.isLocallyClosed)
  haveI : IsNontrivial M := by
    obtain ⟨γ, h0, h1⟩ := (inferInstance : IsNontrivial L).condition
    obtain ⟨a, rfl⟩ := ValuativeRel.valuation_surjective γ
    refine ⟨⟨valuation M (e.symm a), ?_, ?_⟩⟩
    · simpa using h0
    · intro h
      apply h1
      have h' : valuation M (e.symm a) = valuation M 1 := by rw [h, map_one]
      have h2 := le_antisymm ((hle _ _).1 h'.le) ((hle _ _).1 h'.ge)
      simpa using h2
  exact ⟨⟩

private theorem valuation_algEquiv_le_one_of_le_one {F L : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L]
    (s : L ≃ₐ[F] L) (y : L) (hy : valuation L y ≤ 1) : valuation L (s y) ≤ 1 := by
  have h2 := @isNonarchimedeanLocalField_of_ringEquiv_of_isInducing L L _ _ _ _ _
    (ValuativeRel.ofValuation ((valuation L).comap (s : L →+* L))) (TopologicalSpace.induced s ‹_›)
    (s : L ≃+* L) (fun a b => (Valuation.Compatible.vle_iff_le (v := valuation L) (s a) (s b)).symm)
    (@Topology.IsInducing.induced L L _ s)
  have hext : @ValuativeExtension F L _ _ _
      (ValuativeRel.ofValuation ((valuation L).comap (s : L →+* L))) _ := by
    refine @ValuativeExtension.mk F L _ _ _
      (ValuativeRel.ofValuation ((valuation L).comap (s : L →+* L))) _ (fun a b => ?_)
    show valuation L (s (algebraMap F L a)) ≤ valuation L (s (algebraMap F L b)) ↔ a ≤ᵥ b
    rw [AlgEquiv.commutes, AlgEquiv.commutes, ← Valuation.Compatible.vle_iff_le,
      ValuativeExtension.vle_iff_vle]
  have heq := GroundTheory.LocalField.valuativeRel_unique F (L := L) (v₁ := ‹ValuativeRel L›)
    (t₁ := ‹TopologicalSpace L›) inferInstance h2 inferInstance hext
  have hx1 : y ≤ᵥ 1 := by
    rw [Valuation.Compatible.vle_iff_le (v := valuation L), map_one]
    exact hy
  have h3 : @ValuativeRel.vle L _ (ValuativeRel.ofValuation ((valuation L).comap (s : L →+* L))) y 1 :=
    cast (congrArg (fun V : ValuativeRel L => @ValuativeRel.vle L _ V y 1) heq) hx1
  have h4 : valuation L (s y) ≤ valuation L (s 1) := h3
  rw [map_one, map_one] at h4
  exact h4

private theorem mem_int (s : K ≃ₐ[k] K) (x : 𝒪[K]) : s (x : K) ∈ 𝒪[K] := by
  exact (Valuation.mem_integer_iff _ _).2
    (valuation_algEquiv_le_one_of_le_one s (x : K) ((Valuation.mem_integer_iff _ _).1 x.2))

private def resE (s : K ≃ₐ[k] K) : 𝒪[K] ≃+* 𝒪[K] where
  toFun x := ⟨s (x : K), mem_int s x⟩
  invFun x := ⟨s.symm (x : K), mem_int s.symm x⟩
  left_inv x := Subtype.ext (s.symm_apply_apply (x : K))
  right_inv x := Subtype.ext (s.apply_symm_apply (x : K))
  map_mul' x y := Subtype.ext (map_mul s (x : K) (y : K))
  map_add' x y := Subtype.ext (map_add s (x : K) (y : K))

private theorem resE_coe (s : K ≃ₐ[k] K) (x : 𝒪[K]) : ((resE s x : 𝒪[K]) : K) = s (x : K) := rfl

end

end UpperTheory.Gal.InertialTypesAlt.L

private theorem linearMap_apply_mem_ideal_smul_of_mem {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (J : Ideal R) (g : M →ₗ[R] N) (x : M)
    (hx : x ∈ (J • ⊤ : Submodule R M)) : g x ∈ (J • ⊤ : Submodule R N) := by
  have h : g x ∈ Submodule.map g (J • ⊤ : Submodule R M) := Submodule.mem_map_of_mem hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

private theorem isPrecomplete_of_linearEquiv {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (I : Ideal R) (e : M ≃ₗ[R] N) [hM : IsPrecomplete I M] :
    IsPrecomplete I N := by
  refine ⟨fun f hf => ?_⟩
  obtain ⟨L, hL⟩ := hM.prec (f := fun n => e.symm (f n)) (fun {m n} hmn => by
    have h := hf hmn
    rw [SModEq.sub_mem] at h ⊢
    rw [← map_sub]
    exact linearMap_apply_mem_ideal_smul_of_mem _ e.symm.toLinearMap _ h)
  refine ⟨e L, fun n => ?_⟩
  have h := hL n
  rw [SModEq.sub_mem] at h ⊢
  have h2 := linearMap_apply_mem_ideal_smul_of_mem _ e.toLinearMap _ h
  simpa using h2

private theorem isPrecomplete_pi_of_fintype {R ι : Type*} [CommRing R] [Fintype ι] (I : Ideal R)
    [hR : IsPrecomplete I R] : IsPrecomplete I (ι → R) := by
  classical
  refine ⟨fun f hf => ?_⟩
  have hc : ∀ i : ι, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro i
    exact hR.prec (f := fun n => f n i) (fun {m n} hmn => by
      have h := hf hmn
      rw [SModEq.sub_mem] at h ⊢
      exact linearMap_apply_mem_ideal_smul_of_mem _ (LinearMap.proj i) _ h)
  choose L hL using hc
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem]
  have hx : f n - L = ∑ i, (f n i - L i) • (Pi.single i (1 : R) : ι → R) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hx]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  have hi := hL i n
  rw [SModEq.sub_mem] at hi
  have hi' : f n i - L i ∈ I ^ n := by simpa using hi
  exact Submodule.smul_mem_smul hi' Submodule.mem_top

private theorem isAdicComplete_map_maximalIdeal_adjoinRoot_of_monic {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (ψ : R[X]) (hψ : ψ.Monic) :
    IsAdicComplete ((IsLocalRing.maximalIdeal R).map (algebraMap R (AdjoinRoot ψ)))
      (AdjoinRoot ψ) := by
  have pb := AdjoinRoot.powerBasis' hψ
  haveI : Module.Finite R (AdjoinRoot ψ) := pb.finite
  haveI : IsPrecomplete (IsLocalRing.maximalIdeal R) (Fin pb.dim → R) := isPrecomplete_pi_of_fintype _
  have h2 : IsPrecomplete (IsLocalRing.maximalIdeal R) (AdjoinRoot ψ) :=
    isPrecomplete_of_linearEquiv _ pb.basis.equivFun.symm
  exact { toIsHausdorff := IsHausdorff.map_algebraMap_iff.mpr inferInstance
          toIsPrecomplete := IsPrecomplete.map_algebraMap_iff.mpr h2 }

private theorem exists_adjoinRoot_ringEquiv_iterate_mk_of_map_eq {R : Type*} [CommRing R] (ψ : R[X]) (φ : R ≃+* R)
    (hψ : ψ.map (φ : R →+* R) = ψ) :
    ∃ τ : AdjoinRoot ψ ≃+* AdjoinRoot ψ, ∀ (j : ℕ) (g : R[X]),
      (⇑τ)^[j] (AdjoinRoot.mk ψ g) = AdjoinRoot.mk ψ (g.map ((φ : R →+* R) ^ j)) := by
  have key : ∀ φ' : R →+* R, ψ.map φ' = ψ → ∃ f : AdjoinRoot ψ →+* AdjoinRoot ψ,
      ∀ g, f (AdjoinRoot.mk ψ g) = AdjoinRoot.mk ψ (g.map φ') := by
    intro φ' h
    refine ⟨AdjoinRoot.lift ((AdjoinRoot.of ψ).comp φ') (AdjoinRoot.root ψ) ?_, fun g => ?_⟩
    · rw [← Polynomial.eval₂_map, h]
      exact AdjoinRoot.eval₂_root ψ
    · rw [AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.aeval_eq, Polynomial.aeval_def]
      rfl
  have hψ' : ψ.map (φ.symm : R →+* R) = ψ := by
    conv_lhs => rw [← hψ]
    rw [Polynomial.map_map]
    convert Polynomial.map_id
    ext x
    simp
  obtain ⟨f, hf⟩ := key _ hψ
  obtain ⟨f', hf'⟩ := key _ hψ'
  have e1 : f'.comp f = RingHom.id _ := by
    refine RingHom.ext fun x => ?_
    induction x using AdjoinRoot.induction_on with
    | ih g =>
      simp only [RingHom.comp_apply, hf, hf', Polynomial.map_map, RingHom.id_apply]
      congr 1
      convert Polynomial.map_id
      ext x
      simp
  have e2 : f.comp f' = RingHom.id _ := by
    refine RingHom.ext fun x => ?_
    induction x using AdjoinRoot.induction_on with
    | ih g =>
      simp only [RingHom.comp_apply, hf, hf', Polynomial.map_map, RingHom.id_apply]
      congr 1
      convert Polynomial.map_id
      ext x
      simp
  refine ⟨RingEquiv.ofRingHom f f' e2 e1, fun j => ?_⟩
  induction j with
  | zero =>
    intro g
    rw [Function.iterate_zero_apply, pow_zero]
    exact (congrArg (AdjoinRoot.mk ψ) (Polynomial.map_id (p := g))).symm
  | succ j ih =>
    intro g
    rw [Function.iterate_succ_apply]
    have : (RingEquiv.ofRingHom f f' e2 e1) (AdjoinRoot.mk ψ g) = AdjoinRoot.mk ψ (g.map (φ : R →+* R)) :=
      hf g
    rw [this, ih, Polynomial.map_map, pow_succ]
    rfl

private theorem isUnit_adjoinRoot_root_of_isUnit_coeff_zero {R : Type*} [CommRing R] (ψ : R[X]) (hc : IsUnit (ψ.coeff 0)) :
    IsUnit (AdjoinRoot.root ψ) := by
  obtain ⟨q, hq⟩ : X ∣ ψ - C (ψ.coeff 0) := Polynomial.X_dvd_iff.mpr (by simp)
  have h : AdjoinRoot.root ψ * AdjoinRoot.mk ψ q = -(AdjoinRoot.of ψ (ψ.coeff 0)) := by
    rw [← AdjoinRoot.mk_X, ← map_mul, ← hq, map_sub, AdjoinRoot.mk_self, AdjoinRoot.mk_C, zero_sub]
  refine isUnit_of_mul_isUnit_left (y := AdjoinRoot.mk ψ q) ?_
  rw [h]
  exact (hc.map (AdjoinRoot.of ψ)).neg

private theorem normPoly_lemma_8 {R S : Type*} [CommRing R] [CommRing S] (r : R →+* S) (ψ : R[X]) :
    ∃ ρ : AdjoinRoot ψ →+* AdjoinRoot (ψ.map r),
      ∀ g, ρ (AdjoinRoot.mk ψ g) = AdjoinRoot.mk (ψ.map r) (g.map r) := by
  refine ⟨AdjoinRoot.lift ((AdjoinRoot.of (ψ.map r)).comp r) (AdjoinRoot.root (ψ.map r)) ?_,
    fun g => ?_⟩
  · rw [← Polynomial.eval₂_map]
    exact AdjoinRoot.eval₂_root _
  · rw [AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.aeval_eq, Polynomial.aeval_def]
    rfl

private theorem gal_pow_finrank_eq_one_of_eq_pow_card {F₀ F₁ : Type*} [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁]
    [Algebra F₀ F₁] (sb : Gal(F₁/F₀)) (hfrob : ∀ z, sb z = z ^ Fintype.card F₀) :
    ((sb.toRingEquiv : F₁ →+* F₁)) ^ Module.finrank F₀ F₁ = 1 := by
  have hit : ∀ (j : ℕ) (z : F₁), (((sb.toRingEquiv : F₁ →+* F₁)) ^ j) z = z ^ (Fintype.card F₀ ^ j) := by
    intro j
    induction j with
    | zero => intro z; simp
    | succ j ih =>
      intro z
      rw [pow_succ, RingHom.mul_def, RingHom.comp_apply, ih]
      show (sb z) ^ _ = _
      rw [hfrob, ← pow_mul, pow_succ, mul_comm (Fintype.card F₀ ^ j)]
  refine RingHom.ext fun z => ?_
  rw [hit, ← Module.card_eq_pow_finrank, FiniteField.pow_card]
  rfl

private theorem exists_sum_pow_apply_eq_one_of_lift_frobenius {R F₀ F₁ : Type*} [CommRing R] [IsLocalRing R] [Field F₀] [Fintype F₀]
    [Field F₁] [Fintype F₁] [Algebra F₀ F₁]
    (r : R →+* F₁) (hr : Function.Surjective r)
    (hker : ∀ x, r x = 0 ↔ x ∈ IsLocalRing.maximalIdeal R)
    (φ : R ≃+* R) (sb : Gal(F₁/F₀)) (hfrob : ∀ z, sb z = z ^ Fintype.card F₀)
    (hcomm : ∀ x, r (φ x) = sb (r x)) (hper : ((φ : R →+* R)) ^ Module.finrank F₀ F₁ = 1) :
    ∃ a : R, ∑ i ∈ Finset.range (Module.finrank F₀ F₁), (((φ : R →+* R)) ^ i) a = 1 := by
  set n := Module.finrank F₀ F₁ with hn
  set f : R →+* R := (φ : R →+* R) with hf
  obtain ⟨b, hb⟩ : ∃ b : F₁, Algebra.trace F₀ F₁ b ≠ 0 := by
    by_contra! h
    have h1 := (traceForm_nondegenerate F₀ F₁).1 1 (fun b => by
      simpa [Algebra.traceForm_apply] using h b)
    exact one_ne_zero h1
  set c := Algebra.trace F₀ F₁ b
  have hz : algebraMap F₀ F₁ (Algebra.trace F₀ F₁ (algebraMap F₀ F₁ c⁻¹ * b)) = 1 := by
    rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, inv_mul_cancel₀ hb, map_one]
  rw [FiniteField.algebraMap_trace_eq_sum_pow, Nat.card_eq_fintype_card] at hz
  obtain ⟨a₀, ha₀⟩ := hr (algebraMap F₀ F₁ c⁻¹ * b)
  have hri : ∀ (i : ℕ) (x : R), r ((f ^ i) x) = (r x) ^ (Fintype.card F₀ ^ i) := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ i ih =>
      intro x
      rw [pow_succ, RingHom.mul_def, RingHom.comp_apply, ih, hf, RingEquiv.coe_toRingHom, hcomm, hfrob,
        ← pow_mul, pow_succ, mul_comm (Fintype.card F₀ ^ i)]
  set t := ∑ i ∈ Finset.range n, (f ^ i) a₀ with ht
  have hrt : r t = 1 := by
    rw [ht, map_sum]
    simp_rw [hri, ha₀]
    exact hz
  have htu : IsUnit t := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← hker, hrt]
    exact one_ne_zero
  have hft : f t = t := by
    rw [ht, map_sum]
    have e : ∀ i, f ((f ^ i) a₀) = (f ^ (i + 1)) a₀ := by
      intro i
      rw [pow_succ', RingHom.mul_def, RingHom.comp_apply]
    simp_rw [e]
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0]
      simp
    · obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [hm, Finset.sum_range_succ, Finset.sum_range_succ' (fun i => (f ^ i) a₀), ← hm, hper,
        pow_zero]
  have hfit : ∀ i, (f ^ i) t = t := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, ih, hft]
  obtain ⟨u, hu⟩ := htu
  refine ⟨a₀ * ↑u⁻¹, ?_⟩
  have hinv : ∀ i, (f ^ i) (↑u⁻¹ : R) = ↑u⁻¹ := by
    intro i
    have h1 : (f ^ i) (↑u⁻¹ : R) * t = 1 := by
      rw [← hfit i, ← map_mul, ← hu, Units.inv_mul, map_one]
    calc (f ^ i) (↑u⁻¹ : R) = (f ^ i) (↑u⁻¹ : R) * t * ↑u⁻¹ := by
          rw [← hu, mul_assoc, Units.mul_inv, mul_one]
      _ = ↑u⁻¹ := by rw [h1, one_mul]
  simp_rw [map_mul, hinv]
  rw [← Finset.sum_mul, ← ht, ← hu, Units.mul_inv]

private theorem mem_map_of_adjoinRoot_hom_eq_zero_of_ker_le {R S : Type*} [CommRing R] [CommRing S] (r : R →+* S)
    (hr : Function.Surjective r) (J : Ideal R) (hker : ∀ x, r x = 0 → x ∈ J) (ψ : R[X])
    (ρ : AdjoinRoot ψ →+* AdjoinRoot (ψ.map r))
    (hρ : ∀ g, ρ (AdjoinRoot.mk ψ g) = AdjoinRoot.mk (ψ.map r) (g.map r))
    (z : AdjoinRoot ψ) (hz : ρ z = 0) : z ∈ J.map (algebraMap R (AdjoinRoot ψ)) := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
    rw [hρ, AdjoinRoot.mk_eq_zero] at hz
    obtain ⟨hb, hhb⟩ := hz
    obtain ⟨h, rfl⟩ := Polynomial.map_surjective r hr hb
    set g' := g - ψ * h with hg'
    have hg'0 : ∀ i, g'.coeff i ∈ J := by
      intro i
      apply hker
      rw [← Polynomial.coeff_map, hg', Polynomial.map_sub, Polynomial.map_mul, hhb, sub_self,
        Polynomial.coeff_zero]
    have hmk : AdjoinRoot.mk ψ g = AdjoinRoot.mk ψ g' := by
      rw [hg', map_sub, map_mul, AdjoinRoot.mk_self, zero_mul, sub_zero]
    rw [hmk, g'.as_sum_range_C_mul_X_pow, map_sum]
    refine Ideal.sum_mem _ (fun i _ => ?_)
    rw [map_mul, AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hg'0 i))

private theorem normPoly_lemma_7 {R F₀ F₁ : Type} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁]
    [Algebra F₀ F₁] (r : R →+* F₁) (hr : Function.Surjective r)
    (hker : ∀ x, r x = 0 ↔ x ∈ IsLocalRing.maximalIdeal R)
    (φ : R ≃+* R) (sb : Gal(F₁/F₀)) (hfrob : ∀ z, sb z = z ^ Fintype.card F₀)
    (hcomm : ∀ x, r (φ x) = sb (r x)) (hper : ((φ : R →+* R)) ^ Module.finrank F₀ F₁ = 1)
    (ψ : R[X]) (hψ : ψ.Monic) (hψφ : ψ.map (φ : R →+* R) = ψ) (hψ0 : IsUnit (ψ.coeff 0))
    (hψr : ∀ i, ∃ c : F₀, r (ψ.coeff i) = algebraMap F₀ F₁ c) :
    ∃ p : R[X], ψ ∣ (∏ i ∈ Finset.range (Module.finrank F₀ F₁), p.map (((φ : R →+* R)) ^ i)) - X := by
  set n := Module.finrank F₀ F₁ with hn
  obtain ⟨τ, hτ⟩ := exists_adjoinRoot_ringEquiv_iterate_mk_of_map_eq ψ φ hψφ
  have hsbψ : (ψ.map r).map ((sb.toRingEquiv : F₁ →+* F₁)) = ψ.map r := by
    ext i
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    obtain ⟨c, hc⟩ := hψr i
    rw [hc]
    exact sb.commutes c
  obtain ⟨τ₀, hτ₀⟩ := exists_adjoinRoot_ringEquiv_iterate_mk_of_map_eq (ψ.map r) sb.toRingEquiv hsbψ
  have hsbn := gal_pow_finrank_eq_one_of_eq_pow_card sb hfrob
  haveI : Module.Finite F₁ (AdjoinRoot (ψ.map r)) := (AdjoinRoot.powerBasis' (hψ.map r)).finite
  haveI : Finite (AdjoinRoot (ψ.map r)) := Module.finite_of_finite F₁
  obtain ⟨y₀, hy₀⟩ := UpperTheory.Gal.InertialTypesAlt.L.normFin F₀ F₁ sb hfrob (AdjoinRoot (ψ.map r)) τ₀
    (fun z => by
      have h1 := hτ₀ 1 (C z)
      rw [Function.iterate_one, pow_one, Polynomial.map_C, AdjoinRoot.mk_C, AdjoinRoot.mk_C] at h1
      rw [AdjoinRoot.algebraMap_eq, h1]
      rfl)
    (fun x => by
      induction x using AdjoinRoot.induction_on with
      | ih g =>
        rw [hτ₀, hsbn]
        exact congrArg _ Polynomial.map_id)
    (AdjoinRoot.root (ψ.map r))
    (isUnit_adjoinRoot_root_of_isUnit_coeff_zero _ (by rw [Polynomial.coeff_map]; exact hψ0.map r))
    (by
      have h1 := hτ₀ 1 X
      rw [Function.iterate_one, Polynomial.map_X, AdjoinRoot.mk_X] at h1
      exact h1)
  obtain ⟨ρ, hρ⟩ := normPoly_lemma_8 r ψ
  have hρsurj : Function.Surjective ρ := by
    intro w
    induction w using AdjoinRoot.induction_on with
    | ih g =>
      obtain ⟨g', rfl⟩ := Polynomial.map_surjective r hr g
      exact ⟨_, hρ g'⟩
  have hrφ : r.comp (φ : R →+* R) = ((sb.toRingEquiv : F₁ →+* F₁)).comp r :=
    RingHom.ext fun x => hcomm x
  have hρτ : ∀ a, ρ (τ a) = τ₀ (ρ a) := by
    intro a
    induction a using AdjoinRoot.induction_on with
    | ih g =>
      have h1 := hτ 1 g
      have h2 := hτ₀ 1 (g.map r)
      rw [Function.iterate_one, pow_one] at h1 h2
      rw [h1, hρ, hρ, h2, Polynomial.map_map, Polynomial.map_map, hrφ]
  have hρit : ∀ i a, ρ ((⇑τ)^[i] a) = (⇑τ₀)^[i] (ρ a) := by
    intro i
    induction i with
    | zero => intro a; rfl
    | succ i ih =>
      intro a
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hρτ, ih]
  have hρN : ∀ a, ρ (UpperTheory.Gal.InertialTypesAlt.L.itN τ n a) = UpperTheory.Gal.InertialTypesAlt.L.itN τ₀ n (ρ a) := by
    intro a
    simp only [UpperTheory.Gal.InertialTypesAlt.L.itN, map_prod, hρit]
  obtain ⟨y, hy⟩ := hρsurj y₀
  have hdiff : ρ (UpperTheory.Gal.InertialTypesAlt.L.itN τ n y - AdjoinRoot.root ψ) = 0 := by
    have hr0 : ρ (AdjoinRoot.root ψ) = AdjoinRoot.root (ψ.map r) := by
      rw [← AdjoinRoot.mk_X, hρ, Polynomial.map_X, AdjoinRoot.mk_X]
    rw [map_sub, hρN, hy, hy₀, hr0, sub_self]
  have hI := mem_map_of_adjoinRoot_hom_eq_zero_of_ker_le r hr _ (fun x hx => (hker x).1 hx) ψ ρ hρ _ hdiff
  have hφJ : ∀ x ∈ IsLocalRing.maximalIdeal R, φ x ∈ IsLocalRing.maximalIdeal R := by
    intro x hx
    rw [← hker] at hx ⊢
    rw [hcomm, hx, map_zero]
  have hof : ∀ (i : ℕ) (a : R), (⇑τ)^[i] (AdjoinRoot.of ψ a) = AdjoinRoot.of ψ ((((φ : R →+* R)) ^ i) a) := by
    intro i a
    have h1 := hτ i (C a)
    rw [Polynomial.map_C, AdjoinRoot.mk_C, AdjoinRoot.mk_C] at h1
    exact h1
  have hτI : ∀ x ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R (AdjoinRoot ψ)),
      τ x ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R (AdjoinRoot ψ)) := by
    have hle : (IsLocalRing.maximalIdeal R).map (algebraMap R (AdjoinRoot ψ)) ≤
        ((IsLocalRing.maximalIdeal R).map (algebraMap R (AdjoinRoot ψ))).comap τ := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_comap, AdjoinRoot.algebraMap_eq]
      have h1 := hof 1 x
      rw [Function.iterate_one, pow_one] at h1
      rw [h1, ← AdjoinRoot.algebraMap_eq]
      exact Ideal.mem_map_of_mem _ (hφJ x hx)
    exact fun x hx => hle hx
  obtain ⟨a, ha⟩ := exists_sum_pow_apply_eq_one_of_lift_frobenius r hr hker φ sb hfrob hcomm hper
  have htr : ∑ i ∈ Finset.range n, (⇑τ)^[i] (AdjoinRoot.of ψ a) = 1 := by
    simp_rw [hof]
    rw [← map_sum, ha, map_one]
  have hper' : ∀ x, (⇑τ)^[n] x = x := by
    intro x
    induction x using AdjoinRoot.induction_on with
    | ih g =>
      rw [hτ, hper]
      exact congrArg _ Polynomial.map_id
  haveI := isAdicComplete_map_maximalIdeal_adjoinRoot_of_monic ψ hψ
  obtain ⟨y', hy'⟩ := UpperTheory.Gal.InertialTypesAlt.L.normAdic (AdjoinRoot ψ)
    ((IsLocalRing.maximalIdeal R).map (algebraMap R (AdjoinRoot ψ))) τ n hper' hτI
    (AdjoinRoot.of ψ a) htr (AdjoinRoot.root ψ) y (isUnit_adjoinRoot_root_of_isUnit_coeff_zero ψ hψ0)
    (by
      have h1 := hτ 1 X
      rw [Function.iterate_one, Polynomial.map_X, AdjoinRoot.mk_X] at h1
      exact h1)
    hI
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y'
  refine ⟨p, ?_⟩
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_prod, AdjoinRoot.mk_X, sub_eq_zero]
  simp_rw [← hτ]
  exact hy'

private theorem valuation_algebraMap_le_one_iff_and_eq_one_iff {F L : Type} [Field F] [ValuativeRel F] [Field L] [ValuativeRel L]
    [Algebra F L] [ValuativeExtension F L] (c : F) :
    (valuation L (algebraMap F L c) ≤ 1 ↔ valuation F c ≤ 1) ∧
      (valuation L (algebraMap F L c) = 1 ↔ valuation F c = 1) := by
  have hle : ∀ a b : F, valuation L (algebraMap F L a) ≤ valuation L (algebraMap F L b) ↔
      valuation F a ≤ valuation F b := by
    intro a b
    rw [← Valuation.Compatible.vle_iff_le, ← Valuation.Compatible.vle_iff_le,
      ValuativeExtension.vle_iff_vle]
  have h1 := hle c 1
  have h2 := hle 1 c
  rw [map_one, map_one] at h1 h2
  refine ⟨h1, ⟨fun h => le_antisymm (h1.1 h.le) (h2.1 h.ge), fun h => le_antisymm (h1.2 h.le) (h2.2 h.ge)⟩⟩

open UpperTheory.Gal.InertialTypesAlt.L in
theorem UpperTheory.Gal.InertialTypesAlt.L.normPoly :
    UpperTheory.Gal.InertialTypesAlt.L.NormPoly := by
  intro k K _ _ _ _ _ _ _ _ _ _ _ _ _ F₀ F₁ _ _ _ _ _ rk rK s sb hres χ hmon hint hunit
  have hmemK : ∀ c : k, valuation k c ≤ 1 → algebraMap k K c ∈ 𝒪[K] := fun c hc =>
    (Valuation.mem_integer_iff _ _).2 ((valuation_algebraMap_le_one_iff_and_eq_one_iff (L := K) c).1.2 hc)
  have hlift : χ.map (algebraMap k K) ∈ Polynomial.lifts (𝒪[K]).subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_map]
    exact ⟨⟨_, hmemK _ (hint i)⟩, rfl⟩
  obtain ⟨ψ, hψmap, -, hψmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift (hmon.map _)
  have hψc : ∀ i, ((ψ.coeff i : 𝒪[K]) : K) = algebraMap k K (χ.coeff i) := by
    intro i
    have := congrArg (fun q => q.coeff i) hψmap
    simpa [Polynomial.coeff_map] using this
  have hkerK : ∀ x : 𝒪[K], rK x = 0 ↔ x ∈ IsLocalRing.maximalIdeal 𝒪[K] := by
    have hmax : (RingHom.ker rK).IsMaximal := RingHom.ker_isMaximal_of_surjective rK hres.onto₁
    have h := IsLocalRing.eq_maximalIdeal hmax
    intro x
    rw [← h, RingHom.mem_ker]
  have hcomm : ∀ x, rK (UpperTheory.Gal.InertialTypesAlt.L.resE s x) = sb (rK x) := fun x =>
    hres.gal x (UpperTheory.Gal.InertialTypesAlt.L.resE s x) rfl
  have hsn : s ^ Module.finrank k K = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact pow_card_eq_one'
  have hφpow : ∀ (i : ℕ) (x : 𝒪[K]),
      (((((UpperTheory.Gal.InertialTypesAlt.L.resE s : 𝒪[K] ≃+* 𝒪[K]) : 𝒪[K] →+* 𝒪[K]) ^ i) x : 𝒪[K]) : K) =
        (s ^ i) (x : K) := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ i ih =>
      intro x
      rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, pow_succ', AlgEquiv.mul_apply, ← ih]
      rfl
  have hper : ((UpperTheory.Gal.InertialTypesAlt.L.resE s : 𝒪[K] ≃+* 𝒪[K]) : 𝒪[K] →+* 𝒪[K]) ^
      Module.finrank F₀ F₁ = 1 := by
    rw [hres.deg]
    refine RingHom.ext fun x => Subtype.ext ?_
    rw [hφpow, hsn]
    rfl
  have hψφ : ψ.map ((UpperTheory.Gal.InertialTypesAlt.L.resE s : 𝒪[K] ≃+* 𝒪[K]) : 𝒪[K] →+* 𝒪[K]) = ψ := by
    apply Polynomial.map_injective (𝒪[K]).subtype Subtype.val_injective
    ext i
    rw [Polynomial.coeff_map, Polynomial.coeff_map, Polynomial.coeff_map]
    show (((UpperTheory.Gal.InertialTypesAlt.L.resE s) (ψ.coeff i) : 𝒪[K]) : K) = ((ψ.coeff i : 𝒪[K]) : K)
    show s ((ψ.coeff i : 𝒪[K]) : K) = ((ψ.coeff i : 𝒪[K]) : K)
    rw [hψc, AlgEquiv.commutes]
  have hψ0 : IsUnit (ψ.coeff 0) := by
    rw [(Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one]
    show valuation K ((ψ.coeff 0 : 𝒪[K]) : K) = 1
    rw [hψc]
    exact (valuation_algebraMap_le_one_iff_and_eq_one_iff (L := K) _).2.2 hunit
  have hψr : ∀ i, ∃ c : F₀, rK (ψ.coeff i) = algebraMap F₀ F₁ c := fun i =>
    ⟨rk ⟨χ.coeff i, (Valuation.mem_integer_iff _ _).2 (hint i)⟩,
      hres.inc ⟨χ.coeff i, (Valuation.mem_integer_iff _ _).2 (hint i)⟩ (ψ.coeff i) (hψc i)⟩
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  obtain ⟨p, hp⟩ := normPoly_lemma_7 rK hres.onto₁ hkerK (UpperTheory.Gal.InertialTypesAlt.L.resE s) sb hres.frob hcomm
    hper ψ hψmon hψφ hψ0 hψr
  refine ⟨p.map (𝒪[K]).subtype, fun i => ?_, ?_⟩
  · rw [Polynomial.coeff_map]
    exact (Valuation.mem_integer_iff _ _).1 (p.coeff i).2
  · have h := Polynomial.map_dvd (𝒪[K]).subtype hp
    rw [hψmap, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_prod, hres.deg] at h
    refine h.trans (dvd_of_eq ?_)
    congr 1
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact RingHom.ext fun x => hφpow i x
