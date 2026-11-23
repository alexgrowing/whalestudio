import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetTypeNormPrincipal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagSingleSingle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHcParamCodeWord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer

noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace Pre

variable (B : Pre)

theorem level_split_E : ∀ p ∈ B.host.levelPrimes, (placesOver B.host.E p).ncard = Module.finrank ℚ B.host.E := fun p hp =>
  (GlobalTheory.HostSplit.split_of_one_mod B.R B.host p (B.level_cond p hp).1 (B.level_cond p hp).2).1

theorem g_split : ∀ k, (placesOver B.host.E (B.host.g k)).ncard = Module.finrank ℚ B.host.E := fun k => B.level_split_E _ (B.host.g_level k)

theorem pde_split :
    (Ideal.primesOver (Ideal.span {(B.host.pde : ℤ)}) (𝓞 B.host.E)).ncard = Module.finrank ℚ B.host.E ∧
    (Ideal.primesOver (Ideal.span {(B.host.pde' : ℤ)}) (𝓞 B.host.E)).ncard = Module.finrank ℚ B.host.E := by
  constructor
  · rw [← GlobalTheory.HostSplit.ncard_placesOver _ B.host.pde_prime]
    exact B.level_split_E _ B.host.pde_level.1
  · rw [← GlobalTheory.HostSplit.ncard_placesOver _ B.host.pde'_prime]
    exact B.level_split_E _ B.host.pde_level.2

end Pre

section Spaces

open DiagSp

variable (R : Ranks) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)

def spacesNorm : Spaces R F E :=
  { spacesStd R cm T hT pz hpz (fun _ => false) with
    z := Pi.single (⟨R.rankY R.m, by rw [N_top]; omega⟩ : Fin (R.N R.m)) pz
    z_anis := by
      refine ne_of_eq_of_ne (diag_single_single _ (fun _ => false) _ _ pz pz) ?_
      rw [if_pos rfl]
      simp only [sgn, Bool.false_eq_true, if_false, mul_one, hpz]
      exact_mod_cast hT.ne_zero
    z_orth := fun x => diag_ext_single _ _ (fun _ => false) x _ pz le_rfl }

theorem spacesNorm_T : (spacesNorm R cm T hT pz hpz).T = T := rfl

theorem spacesNorm_Y_sig (j : ℕ) (τ : E →+* ℂ) : ((spacesNorm R cm T hT pz hpz).Y j).sig τ = sigYD R j := spY_sig R j τ

theorem spacesNorm_z_norm : ((spacesNorm R cm T hT pz hpz).X R.m).hT (spacesNorm R cm T hT pz hpz).z
    (spacesNorm R cm T hT pz hpz).z = (T : E) := by
  refine (diag_single_single (R.N R.m) (fun _ => false)
    (⟨R.rankY R.m, by rw [N_top]; omega⟩ : Fin (R.N R.m)) _ pz pz).trans ?_
  rw [if_pos rfl]
  simp only [sgn, Bool.false_eq_true, if_false, mul_one, hpz]

theorem diag_pair {N n c : ℕ} (h : n + 2 * c ≤ N) (a b a' b' : E) (i j : Fin c) :
    diagForm N (cut N (n + c))
      (Pi.single (⟨n + i, by omega⟩ : Fin N) a + Pi.single (⟨n + c + i, by omega⟩ : Fin N) b)
      (Pi.single (⟨n + j, by omega⟩ : Fin N) a' + Pi.single (⟨n + c + j, by omega⟩ : Fin N) b') =
      if i = j then star a * a' - star b * b' else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [map_add, LinearMap.add_apply, diag_single_single]
  rw [if_neg (show n + (i : ℕ) ≠ n + c + j by omega), if_neg (show n + c + (i : ℕ) ≠ n + j by omega)]
  have h1 : cut N (n + c) ⟨n + i, by omega⟩ = false := by
    simp only [cut, decide_eq_false_iff_not]; omega
  have h2 : cut N (n + c) ⟨n + c + i, by omega⟩ = true := by
    simp only [cut, decide_eq_true_eq]; omega
  rw [h1, h2]
  by_cases hij : i = j
  · subst hij
    simp [sgn]
    ring
  · have hij' : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
    simp [hij', hij]

theorem auxiliary_frame_normalized_spaces (j : ℕ) (hj : j < R.m) : HasHyperbolicAuxiliaryFrame (spacesNorm R cm T hT pz hpz) j := by
  obtain ⟨a, ha⟩ := R.m_even
  have hr : R.N j + (R.m - 1 - j) = R.rankY j := by
    simp only [Ranks.N, Ranks.rankY, Ranks.r, mul_add, mul_one]; omega
  have hp : pY R j = R.N j + (R.m - 1 - j) / 2 := by
    simp only [pY]; omega
  have h2 : R.N j + 2 * ((R.m - 1 - j) / 2) ≤ R.rankY j := by omega
  have hcut : cut (R.rankY j) (pY R j) = cut (R.rankY j) (R.N j + (R.m - 1 - j) / 2) := by rw [hp]
  have pair : ∀ (a b a' b' : E) (i i' : Fin ((R.m - 1 - j) / 2)),
      diagForm (R.rankY j) (cut _ (pY R j))
        (Pi.single (⟨R.N j + i, by omega⟩ : Fin (R.rankY j)) a +
          Pi.single (⟨R.N j + (R.m - 1 - j) / 2 + i, by omega⟩ : Fin (R.rankY j)) b)
        (Pi.single (⟨R.N j + i', by omega⟩ : Fin (R.rankY j)) a' +
          Pi.single (⟨R.N j + (R.m - 1 - j) / 2 + i', by omega⟩ : Fin (R.rankY j)) b') =
      if i = i' then star a * a' - star b * b' else 0 := by
    intro a b a' b' i i'
    rw [hcut]
    exact diag_pair h2 a b a' b' i i'
  have orthX : ∀ (x : Fin (R.N j) → E) (k k' : Fin (R.rankY j)) (b b' : E), R.N j ≤ k → R.N j ≤ k' →
      diagForm (R.rankY j) (cut _ (pY R j)) (extTo (R.N j) (R.rankY j) x)
        (Pi.single k b + Pi.single k' b') = 0 := by
    intro x k k' b b' hk hk'
    rw [map_add, diag_ext_single _ _ _ x k b hk, diag_ext_single _ _ _ x k' b' hk', add_zero]
  have orthS : ∀ (k k₁ k₂ : Fin (R.rankY j)) (b b₁ b₂ : E), (k : ℕ) ≠ k₁ → (k : ℕ) ≠ k₂ →
      diagForm (R.rankY j) (cut _ (pY R j)) (Pi.single k b) (Pi.single k₁ b₁ + Pi.single k₂ b₂) = 0 := by
    intro k k₁ k₂ b b₁ b₂ h₁ h₂
    rw [map_add, diag_single_single, diag_single_single, if_neg h₁, if_neg h₂, add_zero]
  refine ⟨fun i => Pi.single (⟨R.N j + i, by omega⟩ : Fin (R.rankY j)) (1 : E) +
      Pi.single (⟨R.N j + (R.m - 1 - j) / 2 + i, by omega⟩ : Fin (R.rankY j)) (1 : E),
    fun i => Pi.single (⟨R.N j + i, by omega⟩ : Fin (R.rankY j)) (1 / 2 : E) +
      Pi.single (⟨R.N j + (R.m - 1 - j) / 2 + i, by omega⟩ : Fin (R.rankY j)) (-(1 / 2) : E),
    fun i i' => ?_, fun i i' => ?_, fun i i' => ?_, fun i x => ⟨?_, ?_⟩, fun hev => ?_⟩
  · exact (pair 1 1 1 1 i i').trans (by simp)
  · exact (pair (1 / 2) (-(1 / 2)) (1 / 2) (-(1 / 2)) i i').trans
      (by split_ifs <;> simp [star_neg, star_ofNat])
  · exact (pair 1 1 (1 / 2) (-(1 / 2)) i i').trans (by split_ifs <;> norm_num)
  · exact orthX x _ _ 1 1 (Nat.le_add_right _ _) ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  · exact orthX x _ _ (1 / 2) (-(1 / 2)) (Nat.le_add_right _ _)
      ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  · have hj2 : R.N j + 2 * ((R.m - 1 - j) / 2) < R.rankY j := by
      obtain ⟨b, hb⟩ := hev
      omega
    have hneg : cut (R.rankY j) (pY R j) ⟨R.N j + 2 * ((R.m - 1 - j) / 2), hj2⟩ = true := by
      simp only [cut, decide_eq_true_eq]; omega
    refine ⟨Pi.single (⟨R.N j + 2 * ((R.m - 1 - j) / 2), hj2⟩ : Fin (R.rankY j)) pz, ?_, fun x => ?_,
      fun i => ⟨?_, ?_⟩⟩
    · refine (diag_single_single (R.rankY j) (cut _ (pY R j))
        (⟨R.N j + 2 * ((R.m - 1 - j) / 2), hj2⟩ : Fin (R.rankY j)) _ pz pz).trans ?_
      rw [if_pos rfl, hneg, spacesNorm_T]
      simp only [sgn, if_true, mul_neg, mul_one, neg_mul, hpz]
    · exact diag_ext_single _ _ _ x _ pz (Nat.le_add_right _ _)
    · exact orthS _ (⟨R.N j + i, by omega⟩ : Fin (R.rankY j))
        (⟨R.N j + (R.m - 1 - j) / 2 + i, by omega⟩ : Fin (R.rankY j)) pz 1 1
        (show R.N j + 2 * ((R.m - 1 - j) / 2) ≠ R.N j + i by omega)
        (show R.N j + 2 * ((R.m - 1 - j) / 2) ≠ R.N j + (R.m - 1 - j) / 2 + i by omega)
    · exact orthS _ (⟨R.N j + i, by omega⟩ : Fin (R.rankY j))
        (⟨R.N j + (R.m - 1 - j) / 2 + i, by omega⟩ : Fin (R.rankY j)) pz (1 / 2) (-(1 / 2))
        (show R.N j + 2 * ((R.m - 1 - j) / 2) ≠ R.N j + i by omega)
        (show R.N j + 2 * ((R.m - 1 - j) / 2) ≠ R.N j + (R.m - 1 - j) / 2 + i by omega)

end Spaces

theorem exists_finset_capitulation (E : Type) [Field E] [NumberField E] (τ : E →+* ℂ) :
    ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K],
      (∀ z ∈ S, z ∈ K) → (∀ x, τ x ∈ K) → ∀ 𝔞 : Ideal (𝓞 E), ∃ β : K,
        Submodule.span (𝓞 K) {β} = Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} := by
  classical
  have hpos : 0 < Fintype.card (ClassGroup (𝓞 E)) := Fintype.card_pos
  choose rep γ hrep hγ hpow using exists_rep_pow_classNumber E
  choose α hα using fun c : ClassGroup (𝓞 E) =>
    IsAlgClosed.exists_pow_nat_eq (τ (γ c : E)) hpos
  have hαint : ∀ c, IsIntegral ℤ (α c) := fun c =>
    IsIntegral.of_pow hpos (by rw [hα c]; exact (RingOfIntegers.isIntegral_coe (γ c)).map τ.toIntAlgHom)
  refine ⟨Finset.univ.image α, ?_, ?_⟩
  · intro z hz
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hz
    exact ((hαint c).tower_top (A := ℚ)).isAlgebraic
  intro K _ hS hτ 𝔞
  have : NumberField K := {}
  let f : E →+* K := τ.codRestrict K hτ
  have hset : {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} = {x : K | ∃ a ∈ 𝔞, x = f (a : E)} := by
    ext x
    constructor
    · rintro ⟨a, ha, e⟩
      exact ⟨a, ha, Subtype.ext e⟩
    · rintro ⟨a, ha, e⟩
      exact ⟨a, ha, congrArg Subtype.val e⟩
  rw [hset, span_image_eq_coeSubmodule_map f 𝔞]
  by_cases h0 : 𝔞 = ⊥
  · refine ⟨0, ?_⟩
    rw [h0, Ideal.map_bot, IsLocalization.coeSubmodule_bot, Submodule.span_singleton_eq_bot.mpr rfl]
  set φ := RingOfIntegers.mapRingHom f
  set c := ClassGroup.mk0 (⟨𝔞, mem_nonZeroDivisors_of_ne_zero h0⟩ : (Ideal (𝓞 E))⁰) with hc
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp (hrep c).symm
  have haK : α c ∈ K := hS _ (Finset.mem_image_of_mem _ (Finset.mem_univ c))
  have haint : IsIntegral ℤ (⟨α c, haK⟩ : K) :=
    (isIntegral_algHom_iff (K.val : K →+* ℂ).toIntAlgHom Subtype.val_injective).mp (hαint c)
  let aO : 𝓞 K := ⟨⟨α c, haK⟩, haint⟩
  have hφγ : φ (γ c) = aO ^ Fintype.card (ClassGroup (𝓞 E)) := by
    apply RingOfIntegers.ext
    apply Subtype.ext
    simp only [φ, RingOfIntegers.mapRingHom_apply, map_pow]
    exact (hα c).symm
  have hrepmap : Ideal.map φ (rep c : Ideal (𝓞 E)) = Ideal.span {aO} := by
    apply pow_left_injective hpos.ne'
    simp only
    rw [← Ideal.map_pow, hpow c, Ideal.map_span, Set.image_singleton, hφγ, Ideal.span_singleton_pow]
  have hmap := congrArg (fun I => IsLocalization.coeSubmodule K (Ideal.map φ I)) hxy
  simp only [Ideal.map_mul, hrepmap, Ideal.map_span, Set.image_singleton,
    IsLocalization.coeSubmodule_mul, IsLocalization.coeSubmodule_span_singleton] at hmap
  have hu : algebraMap (𝓞 K) K (φ x) ≠ 0 := by
    show f (x : E) ≠ 0
    rw [map_ne_zero]
    exact fun h => hx (RingOfIntegers.ext (by simpa using h))
  refine ⟨(algebraMap (𝓞 K) K (φ x))⁻¹ * (algebraMap (𝓞 K) K (φ y) * algebraMap (𝓞 K) K aO), ?_⟩
  have hone : Submodule.span (𝓞 K) {(algebraMap (𝓞 K) K (φ x))⁻¹} *
      Submodule.span (𝓞 K) {algebraMap (𝓞 K) K (φ x)} = 1 := by
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton, inv_mul_cancel₀ hu,
      Submodule.one_eq_span]
  rw [← one_mul (IsLocalization.coeSubmodule K (Ideal.map φ 𝔞)), ← hone, mul_assoc, hmap,
    Submodule.span_mul_span, Set.singleton_mul_singleton, Submodule.span_mul_span,
    Set.singleton_mul_singleton]

end GlobalTheory.Mem

end
