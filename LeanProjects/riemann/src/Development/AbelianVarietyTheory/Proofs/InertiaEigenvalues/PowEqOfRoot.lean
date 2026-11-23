import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSumRootsOfUnity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocF

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.BKReal IsLocalRing Polynomial Formalism.BasicNotions.Examples₂.LB
open scoped Formalism.Per TensorProduct

namespace GlobalTheory.AinfK

variable {l : ℕ} [hl : Fact l.Prime] (K : FinExt l)

theorem l_res : ((l : ℕ) : ResidueField ↥(OL K)) = 0 := by
  rw [← map_natCast (residue ↥(OL K))]
  exact (residue_eq_zero_iff _).mpr (l_mem_max K)

theorem exists_card : ∃ a : ℕ, a ≠ 0 ∧ Nat.card (ResidueField ↥(OL K)) = l ^ a := by
  have := OL_resFinite K
  have := Fintype.ofFinite (ResidueField ↥(OL K))
  have : CharP (ResidueField ↥(OL K)) l := (CharP.charP_iff_prime_eq_zero hl.out).2 (l_res K)
  obtain ⟨n, -, hn⟩ := FiniteField.card (ResidueField ↥(OL K)) l
  exact ⟨n, n.ne_zero, by rw [Nat.card_eq_fintype_card, hn]⟩

variable {K} {a : ℕ} [NeZero a]

omit [NeZero a] in

theorem res_pow (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) (x : ResidueField ↥(OL K)) : x ^ l ^ a = x := by
  have := OL_resFinite K
  have := Fintype.ofFinite (ResidueField ↥(OL K))
  rw [← h, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem exists_teich (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) (x : ↥(OL K)) :
    ∃ w : ↥(OL K), w ^ l ^ a = w ∧ residue _ w = residue _ x := by
  obtain ⟨_, hc, -⟩ := GlobalTheory.FinExtIntegers.dvr_complete K
  have h1 := one_lt_pow_l l a
  have hm : (X ^ l ^ a - X : (↥(OL K))[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1)
  obtain ⟨w, hw, hx⟩ := HenselianRing.is_henselian (I := maximalIdeal ↥(OL K)) _ hm x (by
      rw [← residue_eq_zero_iff]; simp [res_pow h]) (by
      change IsUnit (residue _ _)
      have : ((l : ResidueField ↥(OL K))) ^ a = 0 := by rw [l_res, zero_pow (NeZero.ne a)]
      simp [derivative_X_pow, this])
  refine ⟨w, by simpa [sub_eq_zero] using hw, ?_⟩
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  exact hx

theorem exists_toOm (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) (x : Om l) (hx : x ^ l ^ a = x) :
    ∃ w : ↥(OL K), toOm K w = x := by
  classical
  have := OL_resFinite K
  have := Fintype.ofFinite (ResidueField ↥(OL K))
  have h1 := one_lt_pow_l l a
  choose r hr using residue_surjective (R := ↥(OL K))
  choose s hs hs' using fun y => exists_teich h (r y)
  have hinj : Function.Injective fun y => toOm K (s y) := fun y z e => by
    rw [← hr y, ← hr z, ← hs', ← hs', toOm_injective K e]
  have hm : (X ^ l ^ a - X : (Om l)[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1)
  have hmem : ∀ y : Om l, y ∈ (X ^ l ^ a - X : (Om l)[X]).roots.toFinset ↔ y ^ l ^ a = y := fun y => by
    simp [mem_roots hm.ne_zero, sub_eq_zero]
  have hsub : Finset.univ.image (fun y => toOm K (s y)) = (X ^ l ^ a - X : (Om l)[X]).roots.toFinset := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
    · obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hy
      rw [hmem, ← map_pow, hs]
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ← Nat.card_eq_fintype_card, h]
      refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
      rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ h1]
  obtain ⟨z, -, hz⟩ := Finset.mem_image.1 (hsub ▸ (hmem x).2 hx)
  exact ⟨_, hz⟩

theorem hasUnr (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) : HasUnr a K :=
  ⟨IntermediateField.adjoin_le_iff.2 fun x hx => by
    obtain ⟨w, rfl⟩ := exists_toOm h x hx
    exact (w : ↥K.1).2⟩

theorem pow_eq_of_root (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) {x : Om l} (hx : x ∈ K.1) {m : ℕ}
    (h0 : 0 < m) (hm : ¬ l ∣ m) (h1 : x ^ m = 1) : x ^ l ^ a = x := by
  have h2 : (⟨x, hx⟩ : ↥K.1) ∈ OL K := IsIntegral.of_pow h0 (by
    rw [show (⟨x, hx⟩ : ↥K.1) ^ m = 1 from Subtype.ext h1]; exact isIntegral_one)
  set y : ↥(OL K) := ⟨_, h2⟩
  have hy : y ^ m = 1 := Subtype.ext (Subtype.ext h1)
  obtain ⟨k, hk⟩ : ∃ k, l ^ a = k + 1 := ⟨l ^ a - 1, by have := one_lt_pow_l l a; omega⟩
  have hr0 : residue _ y ≠ 0 := ((IsUnit.of_pow_eq_one hy h0.ne').map _).ne_zero
  have hr : residue _ (y ^ k) = 1 := by
    have := res_pow h (residue _ y)
    rw [hk, pow_succ] at this
    rw [map_pow]
    exact mul_right_cancel₀ hr0 (by rw [this, one_mul])
  have hg := mul_geom_sum (y ^ k) m
  rw [← pow_mul, mul_comm k, pow_mul, hy, one_pow, sub_self] at hg
  have : CharP (ResidueField ↥(OL K)) l := (CharP.charP_iff_prime_eq_zero hl.out).2 (l_res K)
  have hs : ∑ i ∈ Finset.range m, (y ^ k) ^ i ≠ 0 := fun e => hm (by
    have := congrArg (residue _) e
    simp only [map_sum, map_pow (residue _) (y ^ k), hr, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, map_zero] at this
    exact (CharP.cast_eq_zero_iff _ l m).1 this)
  have h3 : y ^ k = 1 := sub_eq_zero.1 ((mul_eq_zero.1 hg).resolve_right hs)
  have h4 : x ^ k = 1 := congrArg (toOm K) h3
  rw [hk, pow_succ, h4, one_mul]

theorem Kunr_eq (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) : Kunr l a = K0 K := by
  refine le_antisymm (le_inf (hasUnr h).le (Kunr_le_Kur l a)) ?_
  have key : ∀ c ∈ K0 K, ‖c‖ ≤ 1 → c ∈ Kunr l a := fun c hc h1 => by
    obtain ⟨n, z, ω, hω, rfl⟩ := GlobalTheory.UnramSpan.exists_sum_rootsOfUnity l K c hc h1
    refine sum_mem fun i _ => mul_mem (IntermediateField.algebraMap_mem _ _) ?_
    obtain ⟨h2, m, h0, hm, h3⟩ := hω i
    exact IntermediateField.subset_adjoin _ _ (pow_eq_of_root h h2.1 h0 hm h3)
  intro c hc
  rcases le_total ‖c‖ 1 with h1 | h1
  · exact key c hc h1
  · exact inv_mem_iff.1 (key _ (inv_mem hc) (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h1))

variable (l a) in

theorem free_Wq : Module.Free ℤ_[l] (Wq l a) := by
  have := GlobalTheory.TameFrob.finite_Wq l a
  have : FaithfulSMul ℤ_[l] (Wq l a) := (faithfulSMul_iff_algebraMap_injective _ _).2 fun u v h => by
    have := congrArg (GlobalTheory.TameFrob.iotaO l a) h
    simp only [GlobalTheory.TameFrob.iotaO_algebraMap] at this
    exact Subtype.val_injective ((algebraMap ℚ_[l] (Om l)).injective this)
  infer_instance

variable (l a) in

theorem finrank_Wq : Module.finrank ℤ_[l] (Wq l a) = a := by
  have := free_Wq l a
  have h := (splitEquiv (AlgHom.id ℤ_[l] (Wq l a))).toLinearEquiv.finrank_eq
  rw [Module.finrank_baseChange] at h
  simpa using h

attribute [local instance] GlobalTheory.TameFrob.algK GlobalTheory.TameFrob.isFractionRing in
variable (l a) in

theorem finrank_Kunr : Module.finrank ℚ_[l] ↥(Kunr l a) = a := by
  have := GlobalTheory.TameFrob.finite_Wq l a
  have : IsScalarTower ℤ_[l] (Wq l a) ↥(Kunr l a) := IsScalarTower.of_algebraMap_eq fun u =>
    Subtype.ext (GlobalTheory.TameFrob.iotaO_algebraMap l a u).symm
  rw [Algebra.IsAlgebraic.finrank_of_isFractionRing ℤ_[l] ℚ_[l] (Wq l a) ↥(Kunr l a), finrank_Wq]

theorem exists_thetaW [HasUnr a K] (h : Nat.card (ResidueField ↥(OL K)) = l ^ a) (x : ↥(OL K)) :
    ∃ w : Wq l a, residue _ (thetaW a K w) = residue _ x := by
  obtain ⟨y, hy, hx⟩ := exists_teich h x
  rw [← hx]
  rcases eq_or_ne y 0 with rfl | h0
  · exact ⟨0, by rw [map_zero]⟩
  obtain ⟨z, ω, hω, hz, -⟩ := exists_gen l a
  have h1 := one_lt_pow_l l a
  have : NeZero (l ^ a - 1) := ⟨by omega⟩
  have h2 : y ^ (l ^ a - 1) = 1 :=
    mul_right_cancel₀ h0 (by rw [← pow_succ, Nat.sub_add_cancel h1.le, hy, one_mul])
  obtain ⟨k, -, hk⟩ := hω.eq_pow_of_pow_eq_one (ξ := toOm K y) (by rw [← map_pow, h2, map_one])
  refine ⟨WittVector.teichmuller l z ^ k, congrArg _ (intToOC_injective K (Subtype.ext ?_))⟩
  rw [intToOC_thetaW, map_pow, map_pow, wA_teich, WittVector.fontaineTheta_teichmuller, SubmonoidClass.coe_pow,
    GlobalTheory.MemLoc.IsTiltOf.untilt_eq hz]
  exact (map_pow (algebraMap (Om l) ℂ_[l]) ω k).symm.trans (congrArg _ hk)

variable (K)

def fK : ℕ := Module.finrank ℚ_[l] ↥(K0 K)

theorem card_res' : fK K ≠ 0 ∧ Nat.card (ResidueField ↥(OL K)) = l ^ fK K := by
  obtain ⟨a, ha, h⟩ := exists_card K
  have : NeZero a := ⟨ha⟩
  have e : fK K = a := by rw [fK, ← Kunr_eq h, finrank_Kunr]
  rw [e]
  exact ⟨ha, h⟩

instance : NeZero (fK K) := ⟨(card_res' K).1⟩

theorem card_res : Nat.card (ResidueField ↥(OL K)) = l ^ fK K := (card_res' K).2

instance : HasUnr (fK K) K := hasUnr (card_res K)

theorem Kunr_fK : Kunr l (fK K) = K0 K := Kunr_eq (card_res K)

end GlobalTheory.AinfK
