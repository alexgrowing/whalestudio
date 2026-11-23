import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeAdjoinKthRootStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubmoduleEqSpanOfPowEqSpanPow
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize.Capit

def clMap {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] (ψ : A →+* B)
    (hψ : Function.Injective ψ) : ClassGroup A →* ClassGroup B :=
  letI := ψ.toAlgebra
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hψ
  ClassGroup.extendedHom A B

theorem clMap_mk0_eq_one_iff {A B : Type} [CommRing A] [IsDedekindDomain A] [CommRing B]
    [IsDedekindDomain B] (ψ : A →+* B) (hψ : Function.Injective ψ) (I : (Ideal A)⁰) :
    clMap ψ hψ (ClassGroup.mk0 I) = 1 ↔ (I.1.map ψ).IsPrincipal := by
  letI := ψ.toAlgebra
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hψ
  change ClassGroup.extendedHom A B (ClassGroup.mk0 I) = 1 ↔ _
  rw [ClassGroup.extendedHom_mk0]
  exact ClassGroup.mk0_eq_one_iff (ClassGroup.extendedIdeal A B I).2

theorem coeSubmodule_pow {R K : Type} [CommRing R] [CommRing K] [Algebra R K] (I : Ideal R) (k : ℕ) :
    IsLocalization.coeSubmodule K (I ^ k) = IsLocalization.coeSubmodule K I ^ k := by
  induction k with
  | zero => simp [IsLocalization.coeSubmodule_top]
  | succ k ih => rw [pow_succ, pow_succ, IsLocalization.coeSubmodule_mul, ih]

variable {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ)

def intMap (F : IntermediateField ℚ ℂ) (h : ∀ x, φ x ∈ F) : 𝓞 E →+* 𝓞 F :=
  RingOfIntegers.mapRingHom (φ.codRestrict F h)

theorem coe_intMap (F : IntermediateField ℚ ℂ) (h : ∀ x, φ x ∈ F) (a : 𝓞 E) :
    ((intMap φ F h a : F) : ℂ) = φ (a : E) := rfl

theorem intMap_injective (F : IntermediateField ℚ ℂ) (h : ∀ x, φ x ∈ F) :
    Function.Injective (intMap φ F h) := by
  intro a b hab
  have h1 : φ (a : E) = φ (b : E) := by rw [← coe_intMap φ F h, ← coe_intMap φ F h, hab]
  exact RingOfIntegers.ext (φ.injective h1)

def intIncl {F K : IntermediateField ℚ ℂ} (hFK : F ≤ K) : 𝓞 F →+* 𝓞 K :=
  RingOfIntegers.mapRingHom (IntermediateField.inclusion hFK).toRingHom

theorem map_intMap {F K : IntermediateField ℚ ℂ} (hFK : F ≤ K) (h : ∀ x, φ x ∈ F) (I : Ideal (𝓞 E)) :
    I.map (intMap φ K fun x => hFK (h x)) = (I.map (intMap φ F h)).map (intIncl hFK) := by
  rw [Ideal.map_map]; rfl

theorem isPrincipal_mono {F K : IntermediateField ℚ ℂ} (hFK : F ≤ K) (h : ∀ x, φ x ∈ F) (I : Ideal (𝓞 E))
    (hI : (I.map (intMap φ F h)).IsPrincipal) : (I.map (intMap φ K fun x => hFK (h x))).IsPrincipal := by
  obtain ⟨y, hy⟩ := hI
  rw [map_intMap φ hFK h, hy]
  exact ⟨intIncl hFK y, by simp [Ideal.map_span]⟩

theorem sz_mono' {F : IntermediateField ℚ ℂ} {a b a' b' : ℝ} (h : Sz F a b) (ha : a ≤ a') (hb : b ≤ b') :
    Sz F a' b' := by
  obtain ⟨i, h1, h2⟩ := h
  exact ⟨i, h1.trans ha, h2.trans hb⟩

theorem step (F : IntermediateField ℚ ℂ) (a b : ℝ) (hF : Sz F a b) (h : ∀ x, φ x ∈ F) (k : ℕ) (hk : 0 < k)
    (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (hp : ((I ^ k).map (intMap φ F h)).IsPrincipal) :
    ∃ (K : IntermediateField ℚ ℂ) (hFK : F ≤ K), Sz K (a + Real.log k) (b + Real.log k) ∧
      (I.map (intMap φ K fun x => hFK (h x))).IsPrincipal := by
  obtain ⟨y, hy⟩ := hp
  have hy' : (I ^ k).map (intMap φ F h) = Ideal.span {y} := hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_zero, Ideal.map_eq_bot_iff_of_injective (intMap_injective φ F h)] at hy'
    exact pow_ne_zero k hI hy'
  have hyF : (y : F) ≠ 0 := fun h0 => hy0 (RingOfIntegers.ext h0)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((y : F) : ℂ) hk
  have hS := GlobalTheory.T.field_size_adjoin_kth_root F a b k (y : F) (IsLocalization.coeSubmodule F (I.map (intMap φ F h))) z hF hk hyF
    (by rw [← coeSubmodule_pow, ← Ideal.map_pow, hy', IsLocalization.coeSubmodule_span_singleton]) hz
  have hzK : z ∈ F ⊔ ℚ⟮z⟯ := (le_sup_right : ℚ⟮z⟯ ≤ F ⊔ ℚ⟮z⟯) (IntermediateField.mem_adjoin_simple_self ℚ z)
  have hFK : F ≤ F ⊔ ℚ⟮z⟯ := le_sup_left
  generalize F ⊔ ℚ⟮z⟯ = K at hS hzK hFK
  refine ⟨K, hFK, hS, ?_⟩
  haveI := finiteDimensional_of_sz hS
  haveI : NumberField K := NumberField.mk
  rw [← IsFractionRing.coeSubmodule_isPrincipal (𝓞 K) K]
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hk.ne'] at hz
    exact hyF (by exact_mod_cast hz.symm)
  refine ⟨⟨z, hzK⟩, GlobalTheory.submodule_eq_span_of_pow_eq_span_pow K _ ⟨z, hzK⟩ k hk
    (fun h0 => hz0 (congrArg Subtype.val h0)) ?_ ?_⟩
  · exact (IsLocalization.coeSubmodule_fg K (RingOfIntegers.coe_injective) _).mpr (IsNoetherian.noetherian _)
  · rw [← coeSubmodule_pow, ← Ideal.map_pow, map_intMap φ hFK h, hy', Ideal.map_span, Set.image_singleton,
      IsLocalization.coeSubmodule_span_singleton]
    congr 2
    apply Subtype.ext
    exact hz.symm

theorem induct (n : ℕ) : ∀ (F : IntermediateField ℚ ℂ) [NumberField F] (a b : ℝ) (h : ∀ x, φ x ∈ F), Sz F a b →
    (clMap (intMap φ F h) (intMap_injective φ F h)).ker.index = n →
    ∃ (K : IntermediateField ℚ ℂ) (hFK : F ≤ K), Sz K (a + Real.log n) (b + Real.log n) ∧
      ∀ I : (Ideal (𝓞 E))⁰, (I.1.map (intMap φ K fun x => hFK (h x))).IsPrincipal := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F _ a b h hF hn
  by_cases hall : ∀ I : (Ideal (𝓞 E))⁰, (I.1.map (intMap φ F h)).IsPrincipal
  · have := Real.log_natCast_nonneg n
    exact ⟨F, le_rfl, sz_mono' hF (by linarith) (by linarith), hall⟩
  push Not at hall
  obtain ⟨I, hI⟩ := hall
  set f := clMap (intMap φ F h) (intMap_injective φ F h) with hf
  have hne : f (ClassGroup.mk0 I) ≠ 1 := fun h1 => hI ((clMap_mk0_eq_one_iff _ _ I).mp h1)
  set k := orderOf (f (ClassGroup.mk0 I)) with hk
  have hk0 : 0 < k := orderOf_pos _
  have hk1 : k ≠ 1 := fun h1 => hne (orderOf_eq_one_iff.mp h1)
  have hpow : f (ClassGroup.mk0 (I ^ k)) = 1 := by rw [map_pow, map_pow, pow_orderOf_eq_one]
  obtain ⟨K, hFK, hK, hIK⟩ := step φ F a b hF h k hk0 I.1 (nonZeroDivisors.coe_ne_zero I)
    ((clMap_mk0_eq_one_iff _ _ (I ^ k)).mp hpow)
  haveI := finiteDimensional_of_sz hK
  haveI : NumberField K := NumberField.mk
  set g := clMap (intMap φ K fun x => hFK (h x)) (intMap_injective φ K _) with hg
  have hle : f.ker ≤ g.ker := by
    intro c hc
    obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective c
    exact (clMap_mk0_eq_one_iff _ _ J).mpr (isPrincipal_mono φ hFK h _ ((clMap_mk0_eq_one_iff _ _ J).mp hc))
  have hmem : ClassGroup.mk0 I ∈ g.ker := (clMap_mk0_eq_one_iff _ _ I).mpr hIK
  have hmul := Subgroup.relIndex_mul_index hle
  rw [Subgroup.relIndex_ker, hn] at hmul
  have hkr : k ≤ Nat.card (g.ker.map f) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_map_of_mem f hmem))
  have hm0 : 0 < g.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hkm : k * g.ker.index ≤ n := hmul ▸ Nat.mul_le_mul_right _ hkr
  have hlt : g.ker.index < n := by
    have : 2 ≤ k := by omega
    nlinarith
  obtain ⟨L, hKL, hL, hall⟩ := ih _ hlt K _ _ _ hK rfl
  have hlog : Real.log k + Real.log g.ker.index ≤ Real.log n := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hkm)
  exact ⟨L, hFK.trans hKL, sz_mono' hL (by linarith) (by linarith), hall⟩

end GlobalTheory.FieldSize.Capit

namespace GlobalTheory.FieldSize

open Capit in

theorem exists_sz_capitulation : ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (F : IntermediateField ℚ ℂ) (a b : ℝ), Sz F a b → (∀ x, φ x ∈ F) → ∃ F' : IntermediateField ℚ ℂ, F ≤ F' ∧ Sz F' (a + Real.log (classNumber E)) (b + Real.log (classNumber E)) ∧ ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K], F' ≤ K → ∀ 𝔞 : Ideal (𝓞 E), ∃ β : K, Submodule.span (𝓞 K) {β} = Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = φ (a : E)} := by
  intro E _ _ φ F a b hF h
  haveI := finiteDimensional_of_sz hF
  haveI : NumberField F := NumberField.mk
  obtain ⟨L, hFL, hL, hall⟩ := induct φ _ F a b h hF rfl
  set m := (clMap (intMap φ F h) (intMap_injective φ F h)).ker.index with hm
  have hm0 : 0 < m := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hmh : m ≤ classNumber E := by
    rw [classNumber, ← Nat.card_eq_fintype_card]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
  have hlog : Real.log m ≤ Real.log (classNumber E) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hmh)
  refine ⟨L, hFL, sz_mono' hL (by linarith) (by linarith), fun K _ hLK 𝔞 => ?_⟩
  have hK : ∀ x, φ x ∈ K := fun x => hLK (hFL (h x))
  have hp : (𝔞.map (intMap φ K hK)).IsPrincipal := by
    by_cases h0 : 𝔞 = ⊥
    · rw [h0, Ideal.map_bot]; infer_instance
    · exact isPrincipal_mono φ hLK _ _ (hall ⟨𝔞, mem_nonZeroDivisors_iff_ne_zero.mpr h0⟩)
  obtain ⟨y, hy⟩ := hp
  refine ⟨(y : K), ?_⟩
  have h1 := congrArg (IsLocalization.coeSubmodule K) hy
  rw [Ideal.submodule_span_eq, IsLocalization.coeSubmodule_span_singleton, Ideal.map,
    IsLocalization.coeSubmodule_span] at h1
  refine h1.symm.trans ?_
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, hx⟩
    exact ⟨_, ⟨a, ha, rfl⟩, Subtype.ext hx.symm⟩

end GlobalTheory.FieldSize
