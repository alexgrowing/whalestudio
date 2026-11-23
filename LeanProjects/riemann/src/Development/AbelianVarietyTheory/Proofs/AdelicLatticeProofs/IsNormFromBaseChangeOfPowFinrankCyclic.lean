import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AlgebraMapNormTensorEqProdConjugatesStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TensorExistsOfGaloisFixedStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Hilbert90BaseChangeStatement
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm.LocStep

theorem iter_prod {A ι : Type} [CommMonoid A] (T : A →* A) (n : ℕ) (s : Finset ι) (f : ι → A) :
    T^[n] (∏ i ∈ s, f i) = ∏ i ∈ s, T^[n] (f i) := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply', ih, map_prod]

theorem prod_range_mul_iter {A : Type} [CommMonoid A] (T : A →* A) (d m : ℕ) (x : A) :
    ∏ i ∈ Finset.range (d * m), T^[i] x
      = ∏ k ∈ Finset.range m, (T^[d])^[k] (∏ j ∈ Finset.range d, T^[j] x) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.prod_range_add, ih, Finset.prod_range_succ, ← Function.iterate_mul,
      iter_prod]
    congr 1
    exact Finset.prod_congr rfl fun j _ => Function.iterate_add_apply _ _ _ _

theorem prod_cyc {G A : Type} [Group G] [Fintype G] [CommMonoid A] (σ : G)
    (h : ∀ g, g ∈ Subgroup.zpowers σ) (f : G → A) :
    ∏ g, f g = ∏ i ∈ Finset.range (Nat.card G), f (σ ^ i) := by
  classical
  have ho : orderOf σ = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers h
  symm
  refine Finset.prod_bij (fun i _ => σ ^ i) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro i hi j hj hij
    rw [← ho] at hi hj
    exact pow_injOn_Iio_orderOf (by simpa using hi) (by simpa using hj) hij
  · intro g _
    have := (mem_zpowers_iff_mem_range_orderOf).1 (h g)
    rw [Finset.mem_image] at this
    obtain ⟨i, hi, e⟩ := this
    exact ⟨i, ho ▸ hi, e⟩

theorem telescope {A : Type} [CommMonoid A] (T : A →* A) (d : ℕ) (z : A) :
    (∏ j ∈ Finset.range d, T^[j] (T z)) * z = (∏ j ∈ Finset.range d, T^[j] z) * T^[d] z := by
  rw [← Finset.prod_range_succ, Finset.prod_range_succ']
  rfl

theorem core {A : Type} [CommMonoid A] (T : A →* A) (d m : ℕ) (x a b : A) (hab : a * b = 1)
    (hb : T b = b) (ha : T a = a) (hx : ∏ i ∈ Finset.range (d * m), T^[i] x = a ^ m)
    (h90 : ∀ u : A, ∏ k ∈ Finset.range m, (T^[d])^[k] u = 1 → ∃ z : Aˣ, u * T^[d] z = z) :
    ∃ x' : A, T^[d] x' = x' ∧ ∏ j ∈ Finset.range d, T^[j] x' = a := by
  set P : A → A := fun u => ∏ j ∈ Finset.range d, T^[j] u with hP
  have Pmul : ∀ u v, P (u * v) = P u * P v := fun u v => by
    simp only [hP, iterate_map_mul, Finset.prod_mul_distrib]
  have Pone : P 1 = 1 := by simp only [hP, iterate_map_one, Finset.prod_const_one]
  have hbk : ∀ k, T^[k] b = b := fun k => Function.IsFixedPt.iterate hb k
  obtain ⟨z, hz⟩ := h90 (P x * b) (by
    rw [prod_range_mul_iter] at hx
    have : ∀ k, (T^[d])^[k] (P x * b) = (T^[d])^[k] (P x) * b := fun k => by
      rw [← Function.iterate_mul, iterate_map_mul, hbk]
    simp only [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [hx, ← mul_pow, hab, one_pow])
  have hzz : P z * P (z⁻¹ : Aˣ) = 1 := by rw [← Pmul, Units.mul_inv, Pone]
  have ht : ∀ u, P (T u) * u = P u * T^[d] u := fun u => telescope T d u
  have h1 : P (x * T z * (z⁻¹ : Aˣ)) = a := by
    rw [← Units.mul_left_inj z, Pmul, Pmul]
    calc P x * P (T z) * P (z⁻¹ : Aˣ) * z = P x * (P (T z) * z) * P (z⁻¹ : Aˣ) := by ac_rfl
      _ = P x * T^[d] z * (P z * P (z⁻¹ : Aˣ)) * (a * b) := by rw [ht, hab, mul_one]; ac_rfl
      _ = a * (P x * b * T^[d] z) := by rw [hzz, mul_one]; ac_rfl
      _ = a * z := by rw [hz]
  refine ⟨_, ?_, h1⟩
  generalize x * T z * (z⁻¹ : Aˣ) = w at h1
  have h2 : P (T w) = a := by
    rw [← ha, ← h1]
    simp only [hP, map_prod]
    exact Finset.prod_congr rfl fun j _ => Function.iterate_succ_apply' _ _ _
  have h3 := ht w
  rw [h1, h2] at h3
  calc T^[d] w = b * (a * T^[d] w) := by rw [← mul_assoc, mul_comm b, hab, one_mul]
    _ = w := by rw [← h3, ← mul_assoc, mul_comm b, hab, one_mul]

theorem map_pow_iter {F E K : Type} [Field F] [Field E] [Algebra F E] [CommRing K] [Algebra F K]
    (σ : E ≃ₐ[F] E) (i : ℕ) (y : K ⊗[F] E) :
    Algebra.TensorProduct.map (AlgHom.id K K) ((σ ^ i : E ≃ₐ[F] E) : E →ₐ[F] E) y
      = (Algebra.TensorProduct.map (AlgHom.id K K) (σ : E →ₐ[F] E))^[i] y := by
  induction i with
  | zero =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k e => simp
    | add u v hu hv => rw [map_add, hu, hv]; rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ← ih]
    clear ih
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k e => simp [pow_succ']
    | add u v hu hv => simp only [map_add, hu, hv]

theorem exists_pow_of_pow_eq_one {G : Type} [Group G] [Finite G] (σ : G) (d m : ℕ) (hm : m ≠ 0)
    (h : ∀ g, g ∈ Subgroup.zpowers σ) (ho : orderOf σ = d * m) (g : G) (hg : g ^ m = 1) :
    ∃ k : ℕ, g = σ ^ (d * k) := by
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 (h g))
  rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, ho] at hg
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero hm) hg
  exact ⟨k, rfl⟩

end GlobalTheory.CNorm.LocStep

namespace GlobalTheory.CNorm
open LocStep

theorem tnorm_of_tnorm_pow : ∀ (F M E K : Type) [Field F] [CharZero F] [Field M] [Field E] [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E] [FiniteDimensional F E] [IsGalois F E] [Field K] [Algebra F K], IsCyclic (E ≃ₐ[F] E) → ∀ a : F, a ≠ 0 → TNorm F E K (a ^ Module.finrank M E) → TNorm F M K a := by
  intro F M E K _ _ _ _ _ _ _ _ _ _ _ _ hc a ha ⟨x, hx⟩
  haveI : IsAbelianGalois F E := IsAbelianGalois.of_isCyclic F E
  haveI : IsGalois F M := (IsAbelianGalois.tower_bot F M E).toIsGalois
  haveI : IsGalois M E := IsGalois.tower_top_of_isGalois F M E
  haveI : FiniteDimensional M E := Module.Finite.of_restrictScalars_finite F M E
  haveI : FiniteDimensional F M := FiniteDimensional.left F M E
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := E ≃ₐ[F] E)
  set d := Module.finrank F M with hd
  set m := Module.finrank M E with hm
  have hd0 : d ≠ 0 := Module.finrank_pos.ne'
  have hm0 : m ≠ 0 := Module.finrank_pos.ne'
  have hcard : Nat.card (E ≃ₐ[F] E) = d * m := by
    rw [IsGalois.card_aut_eq_finrank, Module.finrank_mul_finrank]
  have ho : orderOf σ = d * m := (orderOf_eq_card_of_forall_mem_zpowers hσ).trans hcard
  have hτ : orderOf (σ ^ d) = m := by
    rw [orderOf_pow_of_dvd hd0 (ho ▸ dvd_mul_right d m), ho,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
  set S := Algebra.TensorProduct.map (AlgHom.id K K) (σ : E →ₐ[F] E) with hS
  let T : K ⊗[F] E →* K ⊗[F] E := S
  have hT : (T : K ⊗[F] E → K ⊗[F] E) = S := rfl
  have hSd : (Algebra.TensorProduct.map (AlgHom.id K K) ((σ ^ d : E ≃ₐ[F] E) : E →ₐ[F] E) :
      K ⊗[F] E → K ⊗[F] E) = S^[d] := funext fun y => map_pow_iter σ d y
  have haK : algebraMap F K a ≠ 0 := (_root_.map_ne_zero _).2 ha
  obtain ⟨w, hw, hw'⟩ := core T d m x (algebraMap K _ (algebraMap F K a))
    (algebraMap K _ (algebraMap F K a)⁻¹) (by rw [← map_mul, mul_inv_cancel₀ haK, map_one])
    (S.commutes _) (S.commutes _)
    (by
      have := GlobalTheory.T.algebraMap_norm_tensor_eq_prod_galois_conjugates F E K x
      rw [hx, prod_cyc σ hσ, hcard, map_pow, map_pow] at this
      rw [this]
      exact Finset.prod_congr rfl fun i _ => (map_pow_iter σ i x).symm)
    (by
      intro u hu
      have := GlobalTheory.T.hilbert90_baseChange' F E K (σ ^ d) m hτ u (by rw [hSd]; exact hu)
      rw [hSd] at this
      exact this)
  obtain ⟨z, rfl⟩ := GlobalTheory.T.exists_tensor_eq_of_fixed_by_algEquiv F M E K w (by
    intro h
    obtain ⟨k, hk⟩ := exists_pow_of_pow_eq_one σ d m hm0 hσ ho (h.restrictScalars F) (by
      have h1 : h ^ m = 1 := by
        rw [hm, ← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
      have := map_pow (AlgEquiv.restrictScalarsHom F (S := M) (A := E)) h m
      rw [h1, map_one] at this
      exact this.symm)
    rw [hk, map_pow_iter, Function.iterate_mul]
    exact Function.IsFixedPt.iterate hw k)
  set ι := Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom F M E) with hι
  have hinj : Function.Injective ι :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := K)
      (IsScalarTower.toAlgHom F M E).toLinearMap (algebraMap M E).injective
  let σ' : M ≃ₐ[F] M := AlgEquiv.restrictNormalHom M σ
  have hσ' : ∀ g, g ∈ Subgroup.zpowers σ' := by
    intro g
    obtain ⟨g', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := M) E g
    obtain ⟨k, rfl⟩ := hσ g'
    exact ⟨k, (map_zpow _ _ _).symm⟩
  have hcomm : ∀ u : K ⊗[F] M,
      ι (Algebra.TensorProduct.map (AlgHom.id K K) (σ' : M →ₐ[F] M) u) = S (ι u) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul k e =>
      have : algebraMap M E (σ' e) = σ (algebraMap M E e) :=
        AlgEquiv.restrictNormal_commutes σ M e
      simp [hι, hS, this]
    | add u v hu hv => simp only [map_add, hu, hv]
  refine ⟨z, ?_⟩
  apply (algebraMap K (K ⊗[F] M)).injective
  apply hinj
  rw [GlobalTheory.T.algebraMap_norm_tensor_eq_prod_galois_conjugates F M K z, prod_cyc σ' hσ', IsGalois.card_aut_eq_finrank, ι.commutes, ← hw',
    map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow_iter]
  exact Function.Semiconj.iterate_right hcomm i z

end GlobalTheory.CNorm
