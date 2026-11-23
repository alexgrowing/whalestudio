import Mathlib
import Formalism.FrobeniusOrbits.DiscrMaximalRealCyclotomic

open NumberField IntermediateField Polynomial

noncomputable section

namespace Formalism.FrobeniusOrbits

namespace Discr

lemma conj_root {z : ℂ} {m : ℕ} (hm : m ≠ 0) (hz : z ^ m = 1) : starRingEnd ℂ z = z⁻¹ := by
  have h1 : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz hm
  have h2 : z * starRingEnd ℂ z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
    norm_num
  exact eq_inv_of_mul_eq_one_right h2

lemma real_theta {K : Type*} [Field K] {m : ℕ} (hm : m ≠ 0) {ζ : K} (hζ : IsPrimitiveRoot ζ m)
    (ψ : K →+* ℂ) : starRingEnd ℂ (ψ (ζ + ζ⁻¹)) = ψ (ζ + ζ⁻¹) := by
  have hw : (ψ ζ) ^ m = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have hc := conj_root hm hw
  simp only [map_add, map_inv₀, hc, inv_inv, add_comm]

lemma not_real_zeta {K : Type*} [Field K] {m : ℕ} (hm : m ≠ 0) (h2 : ¬ m ∣ 2) {ζ : K}
    (hζ : IsPrimitiveRoot ζ m) (ψ : K →+* ℂ) : starRingEnd ℂ (ψ ζ) ≠ ψ ζ := by
  intro h
  have hp : IsPrimitiveRoot (ψ ζ) m := hζ.map_of_injective ψ.injective
  have hc := conj_root hm hp.pow_eq_one
  have h0 : ψ ζ ≠ 0 := hp.ne_zero hm
  have h1 : ψ ζ = (ψ ζ)⁻¹ := h.symm.trans hc
  have hsq : (ψ ζ) ^ 2 = 1 := by
    rw [sq]
    calc ψ ζ * ψ ζ = ψ ζ * (ψ ζ)⁻¹ := congrArg (HMul.hMul (ψ ζ)) h1
      _ = 1 := mul_inv_cancel₀ h0
  exact h2 (hp.dvd_of_pow_eq_one 2 hsq)

lemma real_on_adjoin {K : Type*} [Field K] [Algebra ℚ K] (t : K) (φ : K →+* ℂ)
    (ht : starRingEnd ℂ (φ t) = φ t) : ∀ x ∈ ℚ⟮t⟯, starRingEnd ℂ (φ x) = φ x := by
  intro x hx
  have hS : Set.range (algebraMap ℚ K) ∪ {t} ⊆
      (((starRingEnd ℂ).comp φ).eqLocusField φ : Subfield K) := by
    rintro y (⟨q, rfl⟩ | rfl)
    · exact RingHom.congr_fun
        (RingHom.ext_rat ((starRingEnd ℂ).comp (φ.comp (algebraMap ℚ K))) (φ.comp (algebraMap ℚ K))) q
    · exact ht
  exact (Subfield.closure_le.mpr hS) hx

lemma two_pow_not_dvd (e : ℕ) : ¬ (2 ^ (e + 2)) ∣ 2 := by
  intro h
  have h1 := Nat.le_of_dvd (by norm_num) h
  have h2 : 4 ≤ 2 ^ (e + 2) := by
    have := Nat.one_le_two_pow (n := e)
    rw [pow_succ, pow_succ]
    omega
  omega

section Cyc

variable {K : Type*} [Field K] [NumberField K] {e : ℕ} {z : K}

lemma zeta_not_mem (hz : IsPrimitiveRoot z (2 ^ (e + 2))) : z ∉ ℚ⟮z + z⁻¹⟯ := by
  intro h
  have hm : 2 ^ (e + 2) ≠ 0 := by positivity
  let φ : K →+* ℂ := ((IsAlgClosed.lift : K →ₐ[ℚ] ℂ) : K →+* ℂ)
  have h1 := real_theta hm hz φ
  have h2 := real_on_adjoin (z + z⁻¹) φ h1 z h
  exact not_real_zeta hm (two_pow_not_dvd e) hz φ h2

def th (z : K) : ℚ⟮z + z⁻¹⟯ := AdjoinSimple.gen ℚ (z + z⁻¹)

lemma th_coe (z : K) : ((th z : ℚ⟮z + z⁻¹⟯) : K) = z + z⁻¹ := rfl

lemma isIntegral_over_adjoin_add_inv_of_isPrimitiveRoot (hz : IsPrimitiveRoot z (2 ^ (e + 2))) : IsIntegral ℚ⟮z + z⁻¹⟯ z :=
  (Algebra.IsIntegral.isIntegral (R := ℚ) z).tower_top

lemma minpoly_eq (hz : IsPrimitiveRoot z (2 ^ (e + 2))) :
    minpoly ℚ⟮z + z⁻¹⟯ z = X ^ 2 - C (th z) * X + 1 := by
  have hm : 2 ^ (e + 2) ≠ 0 := by positivity
  have hz0 : z ≠ 0 := hz.ne_zero hm
  have hq : (X ^ 2 - C (th z) * X + 1 : ℚ⟮z + z⁻¹⟯[X]).Monic := by monicity!
  have hev : aeval z (X ^ 2 - C (th z) * X + 1 : ℚ⟮z + z⁻¹⟯[X]) = 0 := by
    simp only [map_add, map_sub, map_mul, aeval_X, aeval_C, map_pow, map_one]
    rw [IntermediateField.algebraMap_apply, th_coe, add_mul, inv_mul_cancel₀ hz0]
    ring
  have hdeg : (X ^ 2 - C (th z) * X + 1 : ℚ⟮z + z⁻¹⟯[X]).natDegree = 2 := by compute_degree!
  have hint := isIntegral_over_adjoin_add_inv_of_isPrimitiveRoot hz
  have hmin2 : 2 ≤ (minpoly ℚ⟮z + z⁻¹⟯ z).natDegree := by
    have h0 := minpoly.natDegree_pos hint
    have h1 : (minpoly ℚ⟮z + z⁻¹⟯ z).natDegree ≠ 1 := by
      rw [Ne, minpoly.natDegree_eq_one_iff]
      rintro ⟨y, hy⟩
      have h3 := y.2
      rw [show (y : K) = z from hy] at h3
      exact zeta_not_mem hz h3
    omega
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hq
    (minpoly.dvd _ _ hev) (by rw [hdeg]; exact hmin2)).symm

variable [IsCyclotomicExtension {2 ^ (e + 2)} ℚ K]

lemma adjoin_top (hz : IsPrimitiveRoot z (2 ^ (e + 2))) :
    Algebra.adjoin ℚ⟮z + z⁻¹⟯ {z} = ⊤ := by
  have hne : NeZero (2 ^ (e + 2)) := ⟨by positivity⟩
  have h := IsCyclotomicExtension.adjoin_primitive_root_eq_top (A := ℚ) hz
  rw [eq_top_iff] at h ⊢
  intro x _
  have hx : x ∈ Algebra.adjoin ℚ {z} := h Algebra.mem_top
  have hle : Algebra.adjoin ℚ {z} ≤ (Algebra.adjoin ℚ⟮z + z⁻¹⟯ {z}).restrictScalars ℚ :=
    Algebra.adjoin_le Algebra.subset_adjoin
  exact hle hx

lemma finrank_two (hz : IsPrimitiveRoot z (2 ^ (e + 2))) :
    Module.finrank ℚ⟮z + z⁻¹⟯ K = 2 := by
  have hint := isIntegral_over_adjoin_add_inv_of_isPrimitiveRoot hz
  have htop : IntermediateField.adjoin ℚ⟮z + z⁻¹⟯ {z} = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact IntermediateField.algebra_adjoin_le_adjoin _ _ (by rw [adjoin_top hz]; exact Algebra.mem_top)
  calc Module.finrank ℚ⟮z + z⁻¹⟯ K
      = Module.finrank ℚ⟮z + z⁻¹⟯ (⊤ : IntermediateField ℚ⟮z + z⁻¹⟯ K) :=
        IntermediateField.finrank_top'.symm
    _ = Module.finrank ℚ⟮z + z⁻¹⟯ (IntermediateField.adjoin ℚ⟮z + z⁻¹⟯ {z}) :=
        (IntermediateField.equivOfEq htop).toLinearEquiv.finrank_eq.symm
    _ = (minpoly ℚ⟮z + z⁻¹⟯ z).natDegree := IntermediateField.adjoin.finrank hint
    _ = 2 := by rw [minpoly_eq hz]; compute_degree!

lemma absNorm_different (hz : IsPrimitiveRoot z (2 ^ (e + 2))) :
    Ideal.absNorm (differentIdeal (𝓞 ℚ⟮z + z⁻¹⟯) (𝓞 K)) = 4 := by
  have hm : 2 ^ (e + 2) ≠ 0 := by positivity
  have hne : NeZero (2 ^ (e + 2)) := ⟨hm⟩
  have hz0 : z ≠ 0 := hz.ne_zero hm
  have hxz : algebraMap (𝓞 K) K hz.toInteger = z := rfl
  have hadjZ := IsCyclotomicExtension.Rat.adjoin_singleton_eq_top hz
  have hadj : Algebra.adjoin (𝓞 ℚ⟮z + z⁻¹⟯) {hz.toInteger} = ⊤ := by
    rw [eq_top_iff] at hadjZ ⊢
    intro y _
    have hle : Algebra.adjoin ℤ {hz.toInteger} ≤
        (Algebra.adjoin (𝓞 ℚ⟮z + z⁻¹⟯) {hz.toInteger}).restrictScalars ℤ :=
      Algebra.adjoin_le Algebra.subset_adjoin
    exact hle (hadjZ Algebra.mem_top)
  have hcond := conductor_mul_differentIdeal (𝓞 ℚ⟮z + z⁻¹⟯) ℚ⟮z + z⁻¹⟯ K hz.toInteger
    (by rw [hxz]; exact adjoin_top hz)
  rw [conductor_eq_top_of_adjoin_eq_top hadj, Ideal.top_mul] at hcond
  rw [hcond, Ideal.absNorm_span_singleton]
  have hint : IsIntegral (𝓞 ℚ⟮z + z⁻¹⟯) z := (hz.isIntegral (Nat.pos_of_ne_zero hm)).tower_top
  have hmin : minpoly ℚ⟮z + z⁻¹⟯ z = Polynomial.map (algebraMap (𝓞 ℚ⟮z + z⁻¹⟯) ℚ⟮z + z⁻¹⟯)
      (minpoly (𝓞 ℚ⟮z + z⁻¹⟯) hz.toInteger) := by
    rw [← minpoly.algebraMap_eq (IsFractionRing.injective (𝓞 K) K) hz.toInteger, hxz]
    exact minpoly.isIntegrallyClosed_eq_field_fractions' ℚ⟮z + z⁻¹⟯ hint
  have hw : algebraMap (𝓞 K) K (Polynomial.aeval hz.toInteger
      (Polynomial.derivative (minpoly (𝓞 ℚ⟮z + z⁻¹⟯) hz.toInteger))) = z - z⁻¹ := by
    rw [← Polynomial.aeval_algebraMap_apply, hxz, ← Polynomial.aeval_map_algebraMap ℚ⟮z + z⁻¹⟯,
      ← Polynomial.derivative_map, ← hmin, minpoly_eq hz]
    (try simp [th_coe]) <;> ring
  generalize Polynomial.aeval hz.toInteger
    (Polynomial.derivative (minpoly (𝓞 ℚ⟮z + z⁻¹⟯) hz.toInteger)) = w at hw ⊢
  have hN1 : Algebra.norm ℚ (z - 1) = 2 :=
    hz.norm_sub_one_two (by omega) (Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero hm))
  have hhalf : z ^ (2 ^ (e + 1)) = -1 := by
    have hsq : z ^ (2 ^ (e + 1)) * z ^ (2 ^ (e + 1)) = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ']
      exact hz.pow_eq_one
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · exact absurd h (hz.pow_ne_one_of_pos_of_lt (by positivity)
        (Nat.pow_lt_pow_right (by norm_num) (by omega)))
    · exact h
  have hcop : Nat.Coprime (2 ^ (e + 1) + 1) (2 ^ (e + 2)) :=
    Nat.Coprime.pow_right _ (Odd.coprime_two_right ⟨2 ^ e, by ring⟩)
  have hneg : IsPrimitiveRoot (-z) (2 ^ (e + 2)) := by
    have h := hz.pow_of_coprime _ hcop
    rwa [pow_succ, hhalf, neg_one_mul] at h
  have hN2 : Algebra.norm ℚ (-z - 1) = 2 :=
    hneg.norm_sub_one_two (by omega) (Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero hm))
  have hNm1 : |Algebra.norm ℚ (-1 : K)| = 1 := by
    rw [show (-1 : K) = algebraMap ℚ K (-1) by simp, Algebra.norm_algebraMap]
    simp
  have hNz : |Algebra.norm ℚ z| = 1 := by
    have h1 : (Algebra.norm ℚ z) ^ (2 ^ (e + 2)) = 1 := by
      rw [← map_pow, hz.pow_eq_one, map_one]
    have h2 : |Algebra.norm ℚ z| ^ (2 ^ (e + 2)) = 1 := by rw [← abs_pow, h1, abs_one]
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) hm).mp h2
  have hprod : z * (z - z⁻¹) = (z - 1) * ((-1) * (-z - 1)) := by
    rw [mul_sub, mul_inv_cancel₀ hz0]
    ring
  have hnorm : |Algebra.norm ℚ (z - z⁻¹)| = 4 := by
    have h := congrArg (fun t => |Algebra.norm ℚ t|) hprod
    simp only [map_mul, abs_mul, hNz, hN1, hN2, hNm1, one_mul] at h
    norm_num at h
    exact h
  have hcast : ((Algebra.norm ℤ w : ℤ) : ℚ) = Algebra.norm ℚ (z - z⁻¹) := by
    rw [← hw]
    exact Algebra.coe_norm_int w
  have habs : |((Algebra.norm ℤ w : ℤ) : ℚ)| = 4 := by rw [hcast]; exact hnorm
  have habsZ : |Algebra.norm ℤ w| = 4 := by exact_mod_cast habs
  rw [Int.abs_eq_natAbs] at habsZ
  exact_mod_cast habsZ

lemma totallyReal_F (hz : IsPrimitiveRoot z (2 ^ (e + 2))) : IsTotallyReal ℚ⟮z + z⁻¹⟯ := by
  have hm : 2 ^ (e + 2) ≠ 0 := by positivity
  refine ⟨fun v => ?_⟩
  rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
  refine RingHom.ext fun y => ?_
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
  letI : Algebra ℚ⟮z + z⁻¹⟯ ℂ := v.embedding.toAlgebra
  let Φ : K →ₐ[ℚ⟮z + z⁻¹⟯] ℂ := IsAlgClosed.lift
  have h1 := real_on_adjoin (z + z⁻¹) (Φ : K →+* ℂ) (real_theta hm hz (Φ : K →+* ℂ)) (y : K) y.2
  have h2 : (Φ : K →+* ℂ) (y : K) = v.embedding y := Φ.commutes y
  rw [h2] at h1
  exact h1

lemma discr_F (hz : IsPrimitiveRoot z (2 ^ (e + 2))) :
    discr ℚ⟮z + z⁻¹⟯ = 2 ^ (2 ^ e * (e + 1) - 1) := by
  have hK := IsCyclotomicExtension.Rat.discr_prime_pow 2 (e + 2) K
  have hexp : 2 ^ (e + 2 - 1) * ((2 - 1) * (e + 2) - 1) = 2 ^ (e + 1) * (e + 1) := by
    rw [show e + 2 - 1 = e + 1 by omega, show (2 - 1) * (e + 2) - 1 = e + 1 by omega]
  have hKabs : (discr K).natAbs = 2 ^ (2 ^ (e + 1) * (e + 1)) := by
    rw [hK, hexp]
    simp [Int.natAbs_mul, Int.natAbs_pow]
  have hF := NumberField.absNorm_differentIdeal ℚ⟮z + z⁻¹⟯ (𝓞 ℚ⟮z + z⁻¹⟯)
  have hKd := NumberField.absNorm_differentIdeal K (𝓞 K)
  have htower := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 ℚ⟮z + z⁻¹⟯) (𝓞 K)
  have hn : Module.finrank (𝓞 ℚ⟮z + z⁻¹⟯) (𝓞 K) = 2 :=
    (IsFractionRing.finrank_eq (𝓞 ℚ⟮z + z⁻¹⟯) ℚ⟮z + z⁻¹⟯ (𝓞 K) K).symm.trans (finrank_two hz)
  have hmap : Ideal.absNorm (Ideal.map (algebraMap (𝓞 ℚ⟮z + z⁻¹⟯) (𝓞 K))
      (differentIdeal ℤ (𝓞 ℚ⟮z + z⁻¹⟯))) = (discr ℚ⟮z + z⁻¹⟯).natAbs ^ 2 := by
    rw [← Ideal.absNorm_relNorm (𝓞 ℚ⟮z + z⁻¹⟯) (𝓞 K), Ideal.relNorm_algebraMap, hn, map_pow, hF]
  have heq : (discr K).natAbs = 4 * (discr ℚ⟮z + z⁻¹⟯).natAbs ^ 2 := by
    rw [← hKd, htower, map_mul, absNorm_different hz, hmap]
  have hN : 1 ≤ 2 ^ e * (e + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h4 : 4 * (discr ℚ⟮z + z⁻¹⟯).natAbs ^ 2 = 4 * (2 ^ (2 ^ e * (e + 1) - 1)) ^ 2 := by
    rw [← heq, hKabs, ← pow_mul, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]
    congr 1
    have hx : 2 ^ (e + 1) * (e + 1) = 2 * (2 ^ e * (e + 1)) := by ring
    rw [hx]
    generalize 2 ^ e * (e + 1) = N at hN ⊢
    omega
  have hd : (discr ℚ⟮z + z⁻¹⟯).natAbs = 2 ^ (2 ^ e * (e + 1) - 1) :=
    Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0)
      (Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4) h4)
  have htr := totallyReal_F hz
  have hsign := NumberField.sign_discr ℚ⟮z + z⁻¹⟯
  rw [NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, Int.sign_eq_one_iff_pos] at hsign
  rw [← Int.natAbs_of_nonneg hsign.le, hd]
  push_cast
  rfl

end Cyc

end Discr

namespace Discr

variable {L : Type} [Field L] [NumberField L]

lemma real_subfield_le_adjoin (ζ : L) : F1 ζ ≤ ℚ⟮ζ⟯ := by
  unfold F1
  exact IntermediateField.adjoin_simple_le_iff.mpr
    (add_mem (IntermediateField.mem_adjoin_simple_self ℚ ζ)
      (inv_mem (IntermediateField.mem_adjoin_simple_self ℚ ζ)))

abbrev Fz (ζ : L) : IntermediateField ℚ ℚ⟮ζ⟯ :=
  @IntermediateField.adjoin ℚ _ ℚ⟮ζ⟯ _ DivisionRing.toRatAlgebra
    {(AdjoinSimple.gen ℚ ζ) + (AdjoinSimple.gen ℚ ζ)⁻¹}

lemma mem_F_iff (ζ : L) (x : ℚ⟮ζ⟯) :
    x ∈ Fz ζ ↔ (x : L) ∈ F1 ζ := by
  have key : ∀ (f : ℚ →+* ℚ⟮ζ⟯) (q : ℚ),
      (IntermediateField.val ℚ⟮ζ⟯ : ℚ⟮ζ⟯ →+* L) (f q) = algebraMap ℚ L q := fun f q =>
    RingHom.congr_fun
      (RingHom.ext_rat ((IntermediateField.val ℚ⟮ζ⟯ : ℚ⟮ζ⟯ →+* L).comp f) (algebraMap ℚ L)) q
  constructor
  · intro hx
    refine (Subfield.closure_le
      (t := (F1 ζ).toSubfield.comap (IntermediateField.val ℚ⟮ζ⟯ : ℚ⟮ζ⟯ →+* L))).mpr ?_ hx
    rintro y (⟨q, rfl⟩ | rfl)
    · rw [SetLike.mem_coe, Subfield.mem_comap, key]
      exact (F1 ζ).algebraMap_mem q
    · show (ζ + ζ⁻¹ : L) ∈ F1 ζ
      unfold F1
      exact IntermediateField.mem_adjoin_simple_self ℚ _
  · intro hx
    have hS : (F1 ζ).toSubfield ≤
        (Fz ζ).toSubfield.map (IntermediateField.val ℚ⟮ζ⟯ : ℚ⟮ζ⟯ →+* L) := by
      unfold F1
      refine Subfield.closure_le.mpr ?_
      rintro y (⟨q, rfl⟩ | rfl)
      · exact ⟨_, (Fz ζ).algebraMap_mem q, key _ q⟩
      · exact ⟨AdjoinSimple.gen ℚ ζ + (AdjoinSimple.gen ℚ ζ)⁻¹,
          Subfield.subset_closure (Or.inr rfl), rfl⟩
    obtain ⟨y, hy, hyx⟩ := hS hx
    have hxy : y = x := Subtype.ext hyx
    subst hxy
    exact hy

def equivF (ζ : L) : Fz ζ ≃+* F1 ζ where
  toFun x := ⟨((x : ℚ⟮ζ⟯) : L), (mem_F_iff ζ x).1 x.2⟩
  invFun y := ⟨⟨y, real_subfield_le_adjoin ζ y.2⟩, (mem_F_iff ζ ⟨y, real_subfield_le_adjoin ζ y.2⟩).2 y.2⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv := fun ⟨_, _⟩ => rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

end Discr

open Discr in
theorem discriminant_real_subfield : DiscrMaximalRealCyclotomic := by
  intro e L _ _ ζ hζ
  have hne : NeZero (2 ^ (e + 2)) := ⟨by positivity⟩
  have hcyc : IsCyclotomicExtension {2 ^ (e + 2)} ℚ ℚ⟮ζ⟯ :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have hz : IsPrimitiveRoot (AdjoinSimple.gen ℚ ζ) (2 ^ (e + 2)) :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ
  rw [← NumberField.discr_eq_discr_of_ringEquiv _ (equivF ζ)]
  exact discr_F hz

end Formalism.FrobeniusOrbits
