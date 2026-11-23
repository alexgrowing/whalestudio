import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EqZeroOfNotPrimary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion

noncomputable section

namespace GlobalTheory.UnitLemma.Orbit

open GlobalTheory.UnitLemma Polynomial IsLocalRing ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion

theorem isLocalRing_of_idem {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (S : Type*) [CommRing S] [Nontrivial S] [Algebra R S]
    [Module.Finite R S] (hid : ∀ e : S, e * e = e → e = 0 ∨ e = 1) : IsLocalRing S := by
  classical
  by_contra hloc
  obtain ⟨M1, hM1⟩ := Ideal.exists_maximal S
  have hex : ∃ M2 : Ideal S, M2.IsMaximal ∧ M2 ≠ M1 := by
    by_contra h
    push Not at h
    exact hloc (IsLocalRing.of_unique_max_ideal ⟨M1, hM1, fun M hM => h M hM⟩)
  obtain ⟨M2, hM2, h12⟩ := hex
  set F := (finite_maximal_ideals_of_finite (R := R) S).toFinset.filter (· ≠ M1) with hF
  have hmemF : ∀ N : Ideal S, N.IsMaximal → N ≠ M1 → N ∈ F := by
    intro N hN hN1
    rw [hF, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨hN, hN1⟩
  have hcop : M1 ⊔ F.inf id = ⊤ := by
    by_contra hne
    have hle : F.inf id ≤ M1 := by
      rw [hM1.eq_of_le hne le_sup_left]; exact le_sup_right
    obtain ⟨N, hN, hNle⟩ := (hM1.isPrime.inf_le').1 hle
    rw [hF, Finset.mem_filter, Set.Finite.mem_toFinset] at hN
    exact hN.2 ((hN.1 : N.IsMaximal).eq_of_le hM1.ne_top hNle)
  have h1 : (1 : S) ∈ M1 ⊔ F.inf id := by rw [hcop]; exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
  have hx1 : ∀ N : Ideal S, N.IsMaximal → N ≠ M1 → x - 1 ∈ N := by
    intro N hN hN1
    have : y ∈ N := Finset.inf_le (f := id) (hmemF N hN hN1) hy
    have : x - 1 = -y := by rw [← hxy]; ring
    rw [this]; exact N.neg_mem (by assumption)
  have hall : ∀ N : Ideal S, N.IsMaximal → x * x - x ∈ N := by
    intro N hN
    by_cases hN1 : N = M1
    · subst hN1; exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hx) hx
    · have := hx1 N hN hN1
      have e : x * x - x = x * (x - 1) := by ring
      rw [e]; exact Ideal.mul_mem_left _ _ this
  obtain ⟨k, hk, hkJ⟩ := exists_pow_mem_map_maximalIdeal (R := R) S _ hall
  have : IsAdicComplete ((maximalIdeal R).map (algebraMap R S)) S := isAdicComplete_finite_algebra S
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  obtain ⟨e, s, hee, hes⟩ := exists_idempotent_henselian ((maximalIdeal R).map (algebraMap R S)) x k' hkJ
  have hxx1 : x * x - x ∈ M1 := hall M1 hM1
  have hxx2 : x * x - x ∈ M2 := hall M2 hM2
  rcases hid e hee with h0 | h0
  · apply hM2.ne_top
    rw [Ideal.eq_top_iff_one]
    have ha : -x ∈ M2 := by
      have : -x = s * (x * x - x) := by rw [← hes, h0]; ring
      rw [this]; exact Ideal.mul_mem_left _ _ hxx2
    have hb := hx1 M2 hM2 h12
    have : (1 : S) = -(x - 1) + -(-x) := by ring
    rw [this]; exact M2.add_mem (M2.neg_mem hb) (M2.neg_mem ha)
  · apply hM1.ne_top
    rw [Ideal.eq_top_iff_one]
    have : (1 : S) = s * (x * x - x) + x := by rw [← hes, h0]; ring
    rw [this]; exact M1.add_mem (Ideal.mul_mem_left _ _ hxx1) hx

variable {K : UQ}

theorem val_unit (u : K.O) (hu : IsUnit u) : val K.O (algebraMap K.O K.E u) = 0 := by
  unfold val
  have : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E u) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact fun h => (mem_maximalIdeal u).1 h hu
  rw [this]; simp

theorem charpoly_dvd_map_of_aeval_eq_zero (B : InvAlg K) (hs : B.P.Separable) (f : K.O[X]) (hf : aeval B.g f = 0) :
    B.P ∣ f.map (algebraMap K.O K.E) := by
  have h0 : aeval (LinearMap.mulLeft K.E B.g) (f.map (algebraMap K.O K.E)) = 0 := by
    have := Polynomial.aeval_algHom_apply (Algebra.lmul K.E B.A) B.g (f.map (algebraMap K.O K.E))
    rw [aeval_map_algebraMap K.E B.g f, hf, map_zero] at this
    exact this
  by_cases hz : f.map (algebraMap K.O K.E) = 0
  · rw [hz]; exact dvd_zero _
  classical
  have hP : B.P ≠ 0 := hs.ne_zero
  rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hP hz,
    Multiset.le_iff_subset ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP).1 hs.squarefree)]
  intro p hp
  rw [Polynomial.mem_normalizedFactors_iff hP] at hp
  rw [Polynomial.mem_normalizedFactors_iff hz]
  exact ⟨hp.1, hp.2.1, GlobalTheory.CuspGL.irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero _ _ _ hp.1 hp.2.2 h0⟩

theorem exists_monic_map_eq_charpoly₂ (B : InvAlg K) (hs : B.P.Separable) (hi : IsIntegral K.O B.g) :
    ∃ p : K.O[X], p.Monic ∧ p.map (algebraMap K.O K.E) = B.P := by
  obtain ⟨m, hm, hm0⟩ := hi
  have hP : B.P.Monic := LinearMap.charpoly_monic _
  obtain ⟨p, hp⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K.E hm (charpoly_dvd_map_of_aeval_eq_zero B hs m hm0)
  rw [hP.leadingCoeff, C_1, mul_one] at hp
  exact ⟨p, monic_of_injective (IsFractionRing.injective K.O K.E) (hp ▸ hP), hp⟩

theorem val_resultant (B C : InvAlg K) (hB : B.P.Separable) (hC : C.P.Separable) (iB : IsIntegral K.O B.g)
    (iC : IsIntegral K.O C.g) (f : K.O[X]) (h0 : aeval B.g f = 0) (h1 : aeval C.g f = 1) :
    val K.O (resultant B.P C.P) = 0 := by
  obtain ⟨p, hp, ep⟩ := exists_monic_map_eq_charpoly₂ B hB iB
  obtain ⟨q, hq, eq⟩ := exists_monic_map_eq_charpoly₂ C hC iC
  have hinj := IsFractionRing.injective K.O K.E
  have d1 : p ∣ f := (map_dvd_map _ hinj hp).1 (ep ▸ charpoly_dvd_map_of_aeval_eq_zero B hB f h0)
  have d2 : q ∣ 1 - f := (map_dvd_map _ hinj hq).1 (eq ▸ charpoly_dvd_map_of_aeval_eq_zero C hC (1 - f) (by simp [h1]))
  have hc : IsCoprime p q := by
    obtain ⟨a, ha⟩ := d1
    obtain ⟨b, hb⟩ := d2
    exact ⟨a, b, by linear_combination -ha - hb⟩
  rw [← ep, ← eq, resultant_map_map, natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj]
  exact val_unit _ ((isUnit_resultant_iff_isCoprime hp).2 hc)

def cut (B : InvAlg K) (e : B.A) (he : B.σ e = e) : InvAlg K where
  A := B.A ⧸ Ideal.span {e}
  σ := Ideal.quotientEquiv _ _ B.σ (by rw [Ideal.map_span]; simp [he])
  σ_σ := fun y => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp [B.σ_σ]
  σ_alg := fun a => by
    rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, Ideal.quotientEquiv_mk, B.σ_alg]
  g := Ideal.Quotient.mk _ B.g

theorem val_conj_le (x : K.E) (h : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x ≤ 1) :
    (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (K.c x) ≤ 1 := by
  obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h
  obtain ⟨b, hb⟩ := K.c_int a
  rw [hb]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _

theorem valuation_conj (x : K.E) : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (K.c x) =
    (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x := by
  set v := (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E with hv
  have hc : ∀ y : K.E, y ≠ 0 → K.c y ≠ 0 := fun y hy => by simpa using hy
  have hmono : ∀ a b : K.E, b ≠ 0 → v a ≤ v b → v (K.c a) ≤ v (K.c b) := by
    intro a b hb h
    have h1 : v (a / b) ≤ 1 := by
      rw [map_div₀]; exact div_le_one_of_le₀ h zero_le'
    have h2 := val_conj_le _ h1
    rw [map_div₀, map_div₀, div_le_one₀ (zero_lt_iff.2 (by simpa using hb))] at h2
    exact h2
  obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_exists_uniformizer K.E
  rw [← hv] at hπ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have h1 : v (K.c π) < 1 := by
    by_contra hn
    have := hmono 1 (K.c π) (hc π hπ0) (by simpa using hn)
    rw [K.c_c, map_one, map_one, hπ, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
    omega
  have h2 : v (K.c π) ≤ v π := by
    rw [hπ]
    have h0 : v (K.c π) ≠ 0 := by simpa using hπ0
    rw [← WithZero.exp_log h0] at h1 ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    rw [WithZero.exp_le_exp]
    omega
  have h3 : v (K.c π) = v π := le_antisymm h2 (by simpa [K.c_c] using hmono _ _ hπ0 h2)
  by_cases hx : x = 0
  · simp [hx]
  have h0 : v x ≠ 0 := by simpa using hx
  have h4 : v x = v (π ^ (-WithZero.log (v x))) := by
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]
    simp [WithZero.exp_log h0]
  have h5 := le_antisymm (hmono _ _ (zpow_ne_zero _ hπ0) h4.le) (hmono _ _ hx h4.ge)
  rw [h5, map_zpow₀, map_zpow₀, h3, ← map_zpow₀, ← h4]

theorem eta_norm_mul (d x : K.E) (hd : d ≠ 0) : K.eta (d * x * K.c d) = K.eta x := by
  by_cases hx : x = 0
  · simp [hx]
  unfold UQ.eta val
  have hd' : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E d ≠ 0 := by simpa using hd
  have hx' : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x ≠ 0 := by simpa using hx
  rw [map_mul, map_mul, valuation_conj, WithZero.log_mul (mul_ne_zero hd' hx') hd', WithZero.log_mul hd' hx']
  generalize WithZero.log ((IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E d) = a
  generalize WithZero.log ((IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x) = b
  rw [show -(a + b + a) = -b + 2 * (-a) by ring, zpow_add₀ (by norm_num), zpow_mul]
  norm_num

theorem eta_gram (B : InvAlg K) (x : B.A) (b : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A) :
    K.eta (Matrix.of fun i j => B.herm x (b i) (b j)).det = K.eta (B.gramDet x) := by
  set c := Module.finBasis K.E B.A
  set M := c.toMatrix b with hM
  have hb : ∀ i, b i = ∑ k, M k i • c k := fun i => (c.sum_toMatrix_smul_self b i).symm
  have e : (Matrix.of fun i j => B.herm x (b i) (b j)) =
      M.transpose * (Matrix.of fun i j => B.herm x (c i) (c j)) * (K.c : K.E →+* K.E).mapMatrix M := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, InvAlg.herm, RingHom.coe_coe]
    rw [hb i, hb j, map_sum, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def (M l j), map_mul B.σ, B.σ_alg, ← Algebra.smul_def, mul_smul_comm, mul_smul_comm,
      smul_mul_assoc, map_smul, map_smul]
    simp only [smul_eq_mul]
    ring
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det]
  exact eta_norm_mul _ _ (c.isUnit_det b).ne_zero

section Orb

variable {O : Type} [CommRing O] {A A' : Type} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A']

theorem mem_mulLat (t : Aˣ) (L : Submodule O A) (y : A) : y ∈ mulLat O (t : A) L ↔ ((t⁻¹ : Aˣ) : A) * y ∈ L := by
  unfold mulLat
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa using hz
  · intro h
    exact ⟨_, h, by simp⟩

theorem stabLat_mulLat (t : Aˣ) (L : Submodule O A) : stabLat O (mulLat O (t : A) L) = stabLat O L := by
  ext s
  change (∀ y, y ∈ mulLat O (t : A) L ↔ (s : A) * y ∈ mulLat O (t : A) L) ↔ ∀ y, y ∈ L ↔ (s : A) * y ∈ L
  simp only [mem_mulLat]
  constructor
  · intro h y
    have := h ((t : A) * y)
    rwa [Units.inv_mul_cancel_left, mul_left_comm, Units.inv_mul_cancel_left] at this
  · intro h y
    rw [mul_left_comm]
    exact h _

def orbWt (G : Subgroup Aˣ) (X : Set (Submodule O A)) : Orb O G X → ℚ :=
  Quot.lift (fun L => (((stabLat O L.1 ⊓ G).relIndex (intUnits O A ⊓ G) : ℕ) : ℚ)) (by
    rintro L M ⟨t, -, h⟩
    simp only [h, stabLat_mulLat])

theorem orbSum_eq (G : Subgroup Aˣ) (X : Set (Submodule O A)) :
    orbSum O G X (fun _ => 1) = ∑ᶠ o, orbWt G X o := by
  unfold orbSum
  refine finsum_congr fun o => ?_
  conv_rhs => rw [← Quot.out_eq o]
  rw [one_mul]
  rfl

theorem orbSum_equiv (φ : A ≃ₐ[O] A') (G : Subgroup Aˣ) (G' : Subgroup A'ˣ)
    (hG : ∀ t : Aˣ, t ∈ G ↔ Units.mapEquiv φ.toMulEquiv t ∈ G')
    (X : Set (Submodule O A)) (X' : Set (Submodule O A'))
    (hX : ∀ L, L ∈ X ↔ L.map φ.toLinearEquiv.toLinearMap ∈ X') :
    orbSum O G' X' (fun _ => 1) = orbSum O G X (fun _ => 1) := by
  rw [orbSum_eq, orbSum_eq]
  set ψ := Units.mapEquiv φ.toMulEquiv with hψ
  have hv : ∀ t : Aˣ, ((ψ t : A'ˣ) : A') = φ t := fun t => rfl
  have hm : ∀ (L : Submodule O A) (y : A), φ y ∈ L.map φ.toLinearEquiv.toLinearMap ↔ y ∈ L := by
    intro L y
    rw [Submodule.mem_map_equiv]
    simp
  let e : X ≃ X' := (Submodule.orderIsoMapComap φ.toLinearEquiv).toEquiv.subtypeEquiv hX
  have he : ∀ L : X, (e L).1 = L.1.map φ.toLinearEquiv.toLinearMap := fun L => rfl
  have hml : ∀ (t : Aˣ) (L : Submodule O A), (mulLat O (t : A) L).map φ.toLinearEquiv.toLinearMap =
      mulLat O ((ψ t : A'ˣ) : A') (L.map φ.toLinearEquiv.toLinearMap) := by
    intro t L
    ext y
    obtain ⟨y, rfl⟩ := φ.surjective y
    rw [hm, mem_mulLat, mem_mulLat, ← map_inv, hv, ← map_mul, hm]
  let q : Orb O G X ≃ Orb O G' X' := Quot.congr e (by
    intro L M
    constructor
    · rintro ⟨t, ht, h⟩
      exact ⟨ψ t, (hG t).1 ht, by rw [he, he, h, hml]⟩
    · rintro ⟨t, ht, h⟩
      obtain ⟨t, rfl⟩ := ψ.surjective t
      refine ⟨t, (hG t).2 ht, ?_⟩
      rw [he, he, ← hml] at h
      exact Submodule.map_injective_of_injective φ.injective h)
  rw [← finsum_comp_equiv q]
  refine finsum_congr fun o => ?_
  induction o using Quot.ind with
  | mk L =>
    change (((stabLat O (e L).1 ⊓ G').relIndex (intUnits O A' ⊓ G') : ℕ) : ℚ) =
      (((stabLat O L.1 ⊓ G).relIndex (intUnits O A ⊓ G) : ℕ) : ℚ)
    have h1 : stabLat O L.1 ⊓ G = (stabLat O (e L).1 ⊓ G').comap ψ.toMonoidHom := by
      ext t
      rw [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_inf, hG]
      refine and_congr_left' ?_
      change (∀ y, y ∈ L.1 ↔ (t : A) * y ∈ L.1) ↔ ∀ y, y ∈ (e L).1 ↔ φ t * y ∈ (e L).1
      rw [φ.surjective.forall]
      simp only [he, ← map_mul, hm]
    have h2 : intUnits O A ⊓ G = (intUnits O A' ⊓ G').comap ψ.toMonoidHom := by
      ext t
      rw [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_inf, hG]
      refine and_congr_left' ?_
      change (IsIntegral O (t : A) ∧ IsIntegral O ((t⁻¹ : Aˣ) : A)) ↔
        (IsIntegral O (φ t) ∧ IsIntegral O (φ ((t⁻¹ : Aˣ) : A)))
      simp only [isIntegral_algEquiv]
    rw [h1, h2, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective (f := ψ.toMonoidHom) ψ.surjective]

end Orb

def IsIso {B C : InvAlg K} (φ : B.A ≃ₐ[K.E] C.A) : Prop :=
  (∀ y, φ (B.σ y) = C.σ (φ y)) ∧ φ B.g = C.g

namespace IsIso

variable {B C : InvAlg K} {φ : B.A ≃ₐ[K.E] C.A}

theorem charpoly_eq_of_isIso (h : IsIso φ) : C.P = B.P := by
  unfold InvAlg.P
  rw [← LinearEquiv.charpoly_conj φ.toLinearEquiv]
  congr 1
  ext y
  simp [LinearEquiv.conj_apply, h.2]

theorem herm_eq (h : IsIso φ) (x y z : B.A) : C.herm (φ x) (φ y) (φ z) = B.herm x y z := by
  unfold InvAlg.herm
  rw [← h.1, ← map_mul, ← map_mul, Algebra.trace_eq_of_algEquiv]

theorem eta_eq (h : IsIso φ) (x : B.A) : K.eta (C.gramDet (φ x)) = K.eta (B.gramDet x) := by
  have hr : Module.finrank K.E B.A = Module.finrank K.E C.A := φ.toLinearEquiv.finrank_eq
  rw [← eta_gram C (φ x) (((Module.finBasis K.E B.A).map φ.toLinearEquiv).reindex (finCongr hr))]
  congr 1
  unfold InvAlg.gramDet
  rw [← Matrix.det_submatrix_equiv_self (finCongr hr)]
  congr 1
  ext i j
  simp [h.herm_eq]

theorem N_eq (h : IsIso φ) (x : B.A) : C.N (φ x) = B.N x := by
  have hm : ∀ (L : Submodule K.O B.A) (y : B.A),
      φ y ∈ L.map (φ.restrictScalars K.O).toLinearEquiv.toLinearMap ↔ y ∈ L := by
    intro L y
    rw [Submodule.mem_map_equiv]
    simp
  refine orbSum_equiv (φ.restrictScalars K.O) _ _ (fun t => ?_) _ _ (fun L => ?_)
  · change (t : B.A) * B.σ t = 1 ↔ φ t * C.σ (φ t) = 1
    rw [← h.1, ← map_mul, map_eq_one_iff _ φ.injective]
  · refine and_congr (and_congr ?_ ?_) (and_congr ?_ ?_)
    · exact (Submodule.fg_map_iff _ φ.injective).symm
    · rw [Submodule.map_coe]
      change _ ↔ Submodule.span K.E (φ.toLinearEquiv.toLinearMap '' (L : Set B.A)) = ⊤
      rw [← Submodule.map_span, Submodule.map_eq_top_iff]
    · rw [φ.surjective.forall]
      simp only [← h.2, ← map_mul, hm]
    · rw [φ.surjective.forall]
      refine forall_congr' fun y => ?_
      rw [φ.surjective.forall]
      simp only [hm, h.herm_eq]

theorem prod {B₂ C₂ : InvAlg K} {φ₂ : B₂.A ≃ₐ[K.E] C₂.A} (h : IsIso φ) (h₂ : IsIso φ₂) :
    IsIso (B := B.prod B₂) (C := C.prod C₂) (φ.prodCongr φ₂) :=
  ⟨fun y => Prod.ext (h.1 y.1) (h₂.1 y.2), Prod.ext h.2 h₂.2⟩

theorem finsum_eq (h : IsIso φ) (F : C.A → ℚ) (hF : ∀ (x : C.A) (u : C.Aˣ), F (x * (u * C.σ (u : C.A))) = F x) :
    ∑ᶠ k : C.Cl, F k.rep = ∑ᶠ k : B.Cl, F (φ k.rep) := by
  set ψ := Units.mapEquiv φ.toMulEquiv with hψ
  have hv : ∀ t : B.Aˣ, ((ψ t : C.Aˣ) : C.A) = φ t := fun t => rfl
  let e : {x : B.Aˣ // B.σ (x : B.A) = x} ≃ {x : C.Aˣ // C.σ (x : C.A) = x} :=
    ψ.toEquiv.subtypeEquiv fun t => by
      change _ ↔ C.σ (φ t) = φ t
      rw [← h.1, φ.injective.eq_iff]
  have he : ∀ x, (((e x).1 : C.Aˣ) : C.A) = φ x.1 := fun x => rfl
  let q : B.Cl ≃ C.Cl := Quot.congr e (by
    intro x y
    rw [ψ.surjective.exists]
    simp only [he, hv, ← h.1, ← map_mul, φ.injective.eq_iff])
  let W : C.Cl → ℚ := Quot.lift (fun x => F x.1) (by
    rintro x y ⟨u, hu⟩
    simp only [hu, hF])
  have hW : ∀ k : C.Cl, F k.rep = W k := fun k => by
    conv_rhs => rw [← Quot.out_eq k]
    rfl
  rw [← finsum_comp_equiv q]
  refine finsum_congr fun k => ?_
  rw [hW]
  conv_lhs => rw [← Quot.out_eq k]
  rfl

end IsIso

theorem prod_P (B₁ B₂ : InvAlg K) : (B₁.prod B₂).P = B₁.P * B₂.P := by
  have : LinearMap.mulLeft K.E ((B₁.g, B₂.g) : B₁.A × B₂.A) =
      (LinearMap.mulLeft K.E B₁.g).prodMap (LinearMap.mulLeft K.E B₂.g) := by
    ext <;> simp
  have h2 := LinearMap.charpoly_prodMap (LinearMap.mulLeft K.E B₁.g) (LinearMap.mulLeft K.E B₂.g)
  rw [← this] at h2
  exact h2

theorem one_sub_fixed (B : InvAlg K) {e : B.A} (he : B.σ e = e) : B.σ (1 - e) = 1 - e := by
  rw [map_sub, map_one, he]

theorem isIso_cut (B : InvAlg K) {e : B.A} (hi : IsIdempotentElem e) (he : B.σ e = e) :
    IsIso (B := B) (C := (cut B e he).prod (cut B (1 - e) (one_sub_fixed B he)))
      (AlgEquiv.prodQuotientOfIsIdempotentElem K.E hi hi.one_sub (by simp) (by simp [hi])) :=
  ⟨fun _ => rfl, rfl⟩

theorem cut_unitary (B : InvAlg K) (e : B.A) (he : B.σ e = e) (h : B.g * B.σ B.g = 1) :
    (cut B e he).g * (cut B e he).σ (cut B e he).g = 1 :=
  congrArg (Ideal.Quotient.mk (Ideal.span {e})) h

theorem cut_aeval (B : InvAlg K) (e : B.A) (he : B.σ e = e) (f : K.O[X]) :
    aeval (cut B e he).g f = Ideal.Quotient.mk (Ideal.span {e}) (aeval B.g f) :=
  aeval_algHom_apply (Ideal.Quotient.mkₐ K.O (Ideal.span {e})) B.g f

theorem cut_integral (B : InvAlg K) (e : B.A) (he : B.σ e = e) (h : IsIntegral K.O B.g) :
    IsIntegral K.O (cut B e he).g := by
  obtain ⟨p, hp, h0⟩ := h
  refine ⟨p, hp, ?_⟩
  rw [← aeval_def, cut_aeval, aeval_def, h0, map_zero]
  rfl

theorem adjoin_stable (B : InvAlg K) (hu : B.g * B.σ B.g = 1) (hi : IsIntegral K.O B.g) {y : B.A}
    (hy : y ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) : B.σ y ∈ Algebra.adjoin K.O ({B.g} : Set B.A) := by
  have hO : ∀ a : K.O, ∃ b : K.O, B.σ (algebraMap K.O B.A a) = algebraMap K.O B.A b := by
    intro a
    obtain ⟨b, hb⟩ := K.c_int a
    exact ⟨b, by rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, hb, ← IsScalarTower.algebraMap_apply]⟩
  have hσi : IsIntegral K.O (B.σ B.g) := by
    have hinj : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective _ _
    choose τ' hτ' using K.c_int
    let cO : K.O →+* K.O :=
      { toFun := τ'
        map_one' := hinj (by rw [← hτ']; simp)
        map_mul' := fun a b => hinj (by simp [← hτ'])
        map_zero' := hinj (by rw [← hτ']; simp)
        map_add' := fun a b => hinj (by simp [← hτ']) }
    refine IsIntegral.map_of_comp_eq cO (B.σ : B.A →+* B.A) ?_ hi
    ext a
    change algebraMap K.O B.A (τ' a) = B.σ (algebraMap K.O B.A a)
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A a, B.σ_alg, hτ', ← IsScalarTower.algebraMap_apply]
  have hg : B.σ B.g ∈ Algebra.adjoin K.O ({B.g} : Set B.A) := by
    obtain ⟨p, hp, h0⟩ := hσi
    let i : Invertible (B.σ B.g) := ⟨B.g, hu, by rw [mul_comm, hu]⟩
    have h1 : eval₂ (algebraMap K.O B.A) B.g p.reverse = 0 :=
      (eval₂_reverse_eq_zero_iff (algebraMap K.O B.A) (B.σ B.g) p).2 h0
    rw [← X_mul_divX_add p.reverse, coeff_zero_reverse, hp.leadingCoeff, ← aeval_def] at h1
    simp only [map_add, map_mul, aeval_X, map_one] at h1
    have h2 : B.σ B.g = -aeval B.g p.reverse.divX := by
      linear_combination B.σ B.g * h1 - aeval B.g p.reverse.divX * hu
    rw [h2]
    exact neg_mem (aeval_mem_adjoin_singleton _ _)
  induction hy using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hg
  | algebraMap a => obtain ⟨b, hb⟩ := hO a; rw [hb]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

end GlobalTheory.UnitLemma.Orbit
