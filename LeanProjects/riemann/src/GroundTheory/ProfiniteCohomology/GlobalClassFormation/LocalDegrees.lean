import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalDegrees.Layers
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalDegrees.Decomposition
import GroundTheory.GlobalFields.SemilocalAlgebras.Finite
import GroundTheory.GlobalFields.CompletionAtPlace.Galois
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IntermediateField GroundTheory.Global GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract
  FiniteSubfield IsDedekindDomain

open scoped GroundTheory.LocalField.Abstract Pointwise GroundTheory.Global.SemiLocal

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace CyclotomicLayer

section TotallyReal

theorem isReal_zhatLayer (r : ℕ+) (φ : (zhatLayer r).1 →+* ℂ) : ComplexEmbedding.IsReal φ := by
  let _ : Algebra (zhatLayer r).1 ℂ := φ.toAlgebra
  have : Algebra.IsAlgebraic (zhatLayer r).1 ℚ̄ := Algebra.IsAlgebraic.tower_top (K := ℚ) (zhatLayer r).1
  let ι : ℚ̄ →ₐ[(zhatLayer r).1] ℂ := IsAlgClosed.lift
  obtain ⟨σ, hσ⟩ := exists_algEquiv_conj ι.toRingHom
  have hdeg : σ ∈ (degreeMod r).ker := by
    rw [MonoidHom.mem_ker, degreeMod, MonoidHom.comp_apply, degree_of_isComplexConjugation ⟨_, hσ⟩,
      map_one]
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  have hx : σ (x : ℚ̄) = x := (mem_fixedField_iff _ _).1 x.2 σ hdeg
  have h1 : ι (x : ℚ̄) = φ x := ι.commutes x
  have h2 := hσ (x : ℚ̄)
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hx, h1] at h2
  exact h2.symm

instance isTotallyReal_zhatLayer (r : ℕ+) : IsTotallyReal (zhatLayer r).1 :=
  ⟨fun _ => InfinitePlace.isReal_iff.2 (isReal_zhatLayer r _)⟩

end TotallyReal

section Order

theorem pow_dvd_addOrderOf_toZModPow {q : ℕ} [hq : Fact q.Prime] {n e a : ℕ} (hna : n + e ≤ a)
    {x : ℤ_[q]} (hx : PadicInt.toZModPow n x ≠ 0) :
    q ^ e ∣ addOrderOf (PadicInt.toZModPow a x) := by
  have hdvd : addOrderOf (PadicInt.toZModPow a x) ∣ q ^ a := by
    have := addOrderOf_dvd_natCard (PadicInt.toZModPow a x)
    rwa [Nat.card_zmod] at this
  obtain ⟨i, -, hieq⟩ := (Nat.dvd_prime_pow hq.out).1 hdvd
  rw [hieq]
  refine Nat.pow_dvd_pow q (not_lt.1 fun hie => hx ?_)
  have h0 : (q ^ (a - n)) • PadicInt.toZModPow a x = 0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.1 (hieq ▸ Nat.pow_dvd_pow q (by omega))
  have h1 : PadicInt.toZModPow a ((q : ℤ_[q]) ^ (a - n) * x) = 0 := by
    rw [nsmul_eq_mul, Nat.cast_pow] at h0
    rw [map_mul, map_pow, map_natCast]
    exact h0
  have h2 : (q : ℤ_[q]) ^ a ∣ (q : ℤ_[q]) ^ (a - n) * x := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
    exact h1
  have hsplit : (q : ℤ_[q]) ^ a = (q : ℤ_[q]) ^ (a - n) * (q : ℤ_[q]) ^ n := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit] at h2
  have h3 : (q : ℤ_[q]) ^ n ∣ x :=
    (mul_dvd_mul_iff_left (pow_ne_zero _ (Nat.cast_ne_zero.2 hq.out.ne_zero))).1 h2
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
  exact h3

theorem pow_dvd_orderOf_degreeMod (r : ℕ+) (q : Nat.Primes) {n e a : ℕ} (hqr : (q : ℕ) ^ a ∣ (r : ℕ))
    (hna : n + e ≤ a) {σ : Gal(ℚ̄/ℚ)}
    (hσ : PadicInt.toZModPow n (Multiplicative.toAdd (degreeComponent q σ)) ≠ 0) :
    (q : ℕ) ^ e ∣ orderOf (degreeMod r σ) := by
  let f : Multiplicative (ZMod r) →* Multiplicative (ZMod ((q : ℕ) ^ a)) :=
    AddMonoidHom.toMultiplicative (ZMod.castHom hqr (ZMod ((q : ℕ) ^ a))).toAddMonoidHom
  refine dvd_trans ?_ (orderOf_map_dvd f _)
  have hf : f (degreeMod r σ) = Multiplicative.ofAdd
      (PadicInt.toZModPow a (Multiplicative.toAdd (degreeComponent q σ))) := by
    rw [← toPadicInt_degree, toZModPow_toPadicInt]
    exact congrArg Multiplicative.ofAdd
      (ProfiniteInteger.castHom_proj (m := primePowPNat (q : ℕ) a) hqr (Multiplicative.toAdd (degree σ)))
  rw [hf, orderOf_ofAdd_eq_addOrderOf]
  exact pow_dvd_addOrderOf_toZModPow hna hσ

theorem dvd_natCard_of_forall_pow_dvd_orderOf {G : Type*} [Group G] [Finite G] (A : Subgroup G)
    {m : ℕ} (hm : m ≠ 0)
    (h : ∀ q : ℕ, q.Prime → q ∣ m → ∃ y ∈ A, q ^ m.factorization q ∣ orderOf y) :
    m ∣ Nat.card A := by
  have hA : Nat.card A ≠ 0 := Nat.card_pos.ne'
  refine (Nat.factorization_prime_le_iff_dvd hm hA).1 fun q hq => ?_
  by_cases hqm : q ∣ m
  · obtain ⟨y, hy, hdvd⟩ := h q hq hqm
    have h1 : orderOf y ∣ Nat.card A := by
      have := orderOf_dvd_natCard (⟨y, hy⟩ : A)
      rwa [Subgroup.orderOf_mk] at this
    exact (hq.pow_dvd_iff_le_factorization hA).1 (hdvd.trans h1)
  · rw [Nat.factorization_eq_zero_of_not_dvd hqm]
    exact Nat.zero_le _

end Order

section Primes

theorem exists_prime_comap_eq (E : FiniteSubfield) (w : HeightOneSpectrum (𝓞 E.1)) :
    ∃ P : Ideal (𝓞 ℚ̄), P.IsPrime ∧ P.comap (ringOfIntegersIncl E.1) = w.asIdeal := by
  let _ : Algebra (𝓞 E.1) (𝓞 ℚ̄) := (ringOfIntegersIncl E.1).toAlgebra
  have : IsScalarTower ℤ (𝓞 E.1) (𝓞 ℚ̄) := IsScalarTower.of_algebraMap_eq fun x => by simp
  have : Algebra.IsIntegral ℤ (𝓞 ℚ̄) := ⟨fun b => RingOfIntegers.isIntegral b⟩
  have : Algebra.IsIntegral (𝓞 E.1) (𝓞 ℚ̄) := Algebra.IsIntegral.tower_top ℤ
  have hinj : Function.Injective (ringOfIntegersIncl E.1) := fun a b h =>
    RingOfIntegers.ext (Subtype.ext (congrArg (fun y : 𝓞 ℚ̄ => (y : ℚ̄)) h))
  have hker : (⊥ : Ideal (𝓞 ℚ̄)).comap (ringOfIntegersIncl E.1) = ⊥ := by
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).1 hinj
  have := w.isPrime
  obtain ⟨P, -, hP, hPw⟩ := Ideal.exists_ideal_over_prime_of_isIntegral w.asIdeal (⊥ : Ideal (𝓞 ℚ̄))
    (hker.le.trans bot_le)
  exact ⟨P, hP, hPw⟩

theorem comap_eq_of_liesOver {K E : FiniteSubfield} [Fact (K ≤ E)] {v : HeightOneSpectrum (𝓞 K.1)}
    (w : HeightOneSpectrum (𝓞 E.1)) [w.asIdeal.LiesOver v.asIdeal] {P : Ideal (𝓞 ℚ̄)}
    (hP : P.comap (ringOfIntegersIncl E.1) = w.asIdeal) :
    P.comap (ringOfIntegersIncl K.1) = v.asIdeal := by
  have h : ringOfIntegersIncl K.1 = (ringOfIntegersIncl E.1).comp (algebraMap (𝓞 K.1) (𝓞 E.1)) :=
    RingHom.ext fun _ => rfl
  rw [h, ← Ideal.comap_comap, hP, Ideal.over_def w.asIdeal v.asIdeal]

variable (K : FiniteSubfield) (r : ℕ+)

theorem restrictHom_mem_stabilizer (P : Ideal (𝓞 ℚ̄)) (g : K.1.fixingSubgroup)
    (hg : (g : Gal(ℚ̄/ℚ)) ∈ MulAction.stabilizer Gal(ℚ̄/ℚ) P) :
    restrictHom (E := cyclotomicLayer K r) g ∈ MulAction.stabilizer Gal((cyclotomicLayer K r).1/K.1)
      (P.comap (ringOfIntegersIncl (cyclotomicLayer K r).1)) := by
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_comap, Ideal.mem_comap, ← map_inv]
  have hx : ringOfIntegersIncl (cyclotomicLayer K r).1 (restrictHom (E := cyclotomicLayer K r) g⁻¹ • x) =
      ((g : Gal(ℚ̄/ℚ)))⁻¹ • ringOfIntegersIncl (cyclotomicLayer K r).1 x :=
    RingOfIntegers.ext rfl
  rw [hx, ← Ideal.mem_pointwise_smul_iff_inv_smul_mem, hg]

end Primes

section Main

theorem exists_dvd_finrank_cyclotomicLayer (K : FiniteSubfield) (S : Finset (HeightOneSpectrum (𝓞 K.1)))
    {m : ℕ} (hm : m ≠ 0) :
    ∃ r : ℕ+, ∀ v ∈ S, ∀ w : SemiLocal.PlacesOver (cyclotomicLayer K r).1 v,
      m ∣ Module.finrank (v.adicCompletion K.1) (w.1.adicCompletion (cyclotomicLayer K r).1) := by
  choose n hn using fun (v : HeightOneSpectrum (𝓞 K.1)) (q : Nat.Primes) =>
    exists_mem_stabilizer_toZModPow_degreeComponent_ne_zero (K := K) v q
  let N : ℕ := S.sup fun v =>
    m.primeFactors.attach.sup fun q => n v ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩
  obtain ⟨r, hr⟩ : ∃ r : ℕ+, (r : ℕ) = m ^ (N + 1) :=
    ⟨⟨m ^ (N + 1), pow_pos (Nat.pos_of_ne_zero hm) _⟩, rfl⟩
  refine ⟨r, fun v hv w => ?_⟩
  rw [SemiLocal.finrank_eq_ramificationIdx_mul_inertiaDeg _ v w.1, ← card_decompositionGroup v w.1]
  refine dvd_trans ?_ (Subgroup.card_map_dvd _ (layerDegree K _))
  refine dvd_natCard_of_forall_pow_dvd_orderOf _ hm fun q hq hqm => ?_
  obtain ⟨P, hP, hPw⟩ := exists_prime_comap_eq (cyclotomicLayer K _) w.1
  have hPv : P.comap (ringOfIntegersIncl K.1) = v.asIdeal := comap_eq_of_liesOver w.1 hPw
  obtain ⟨σ, hσP, hσK, hσ⟩ := hn v ⟨q, hq⟩ P hP hPv
  refine ⟨degreeMod _ σ, Subgroup.mem_map.2 ⟨restrictHom (E := cyclotomicLayer K _) ⟨σ, hσK⟩, ?_,
    layerDegree_restrictHom K _ _⟩, ?_⟩
  · rw [← hPw]
    exact restrictHom_mem_stabilizer K _ P ⟨σ, hσK⟩ hσP
  · have hnN : n v ⟨q, hq⟩ ≤ N := by
      have hqmem : q ∈ m.primeFactors := Nat.mem_primeFactors.2 ⟨hq, hqm, hm⟩
      refine le_trans ?_ (Finset.le_sup (f := fun v =>
        m.primeFactors.attach.sup fun q => n v ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩) hv)
      exact Finset.le_sup (f := fun q : m.primeFactors => n v ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩)
        (Finset.mem_attach _ ⟨q, hqmem⟩)
    have he : 1 ≤ m.factorization q := (hq.dvd_iff_one_le_factorization hm).1 hqm
    have hqr : q ^ (N + m.factorization q) ∣ m ^ (N + 1) := by
      calc q ^ (N + m.factorization q) ∣ q ^ (m.factorization q * (N + 1)) :=
            Nat.pow_dvd_pow q (by nlinarith)
        _ = (q ^ m.factorization q) ^ (N + 1) := pow_mul _ _ _
        _ ∣ m ^ (N + 1) := pow_dvd_pow_of_dvd (Nat.ordProj_dvd m q) _
    exact pow_dvd_orderOf_degreeMod r ⟨q, hq⟩ (hr ▸ hqr) (by omega) hσ

theorem exists_cyclic_layer_dvd_localDegree (K : FiniteSubfield)
    (S : Finset (HeightOneSpectrum (𝓞 K.1))) {m : ℕ} (hm : m ≠ 0) :
    ∃ (E : FiniteSubfield) (_ : Fact (K ≤ E)), IsGalois K.1 E.1 ∧ IsCyclic Gal(E.1/K.1) ∧
      E.1 ≤ K.1 ⊔ zhatField ∧
      ∀ v ∈ S, ∀ w : SemiLocal.PlacesOver E.1 v,
        m ∣ Module.finrank (v.adicCompletion K.1) (w.1.adicCompletion E.1) := by
  obtain ⟨r, hr⟩ := exists_dvd_finrank_cyclotomicLayer K S hm
  exact ⟨cyclotomicLayer K r, inferInstance, inferInstance, inferInstance, cyclotomicLayer_le K r, hr⟩

end Main

end CyclotomicLayer

end

end GroundTheory.ProfCoh
