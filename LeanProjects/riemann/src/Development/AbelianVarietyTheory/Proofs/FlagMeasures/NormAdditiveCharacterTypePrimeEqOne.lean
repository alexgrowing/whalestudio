import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.FramePsi

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

def pairL (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    (Fin n → E) →ₗ[E] E where
  toFun x := hf L Hm x y
  map_add' a b := by simp [hf, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_span_right (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x : Fin n → E)
    (s : Set (Fin n → E)) (hs : ∀ y ∈ s, hf L Hm x y = 0) :
    ∀ y ∈ Submodule.span E s, hf L Hm x y = 0 := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y h => exact hs y h
  | zero => simp [hf]
  | add a b _ _ ha hb =>
    have : hf L Hm x (a + b) = hf L Hm x a + hf L Hm x b := by
      simp [hf, mul_add, Finset.sum_add_distrib]
    rw [this, ha, hb, add_zero]
  | smul c a _ ha =>
    have : hf L Hm x (c • a) = L.cj c * hf L Hm x a := by
      simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this, ha, mul_zero]

theorem coef_mul {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V)
    (gs : Fin r → S.V) (t : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then t else 0)
    (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (a : S.GLV) (ha : a ∈ S.Nof g) (b : S.GLV) (hb : b ∈ S.Nof g) (j : Fin r) :
    S.coef g gs (a * b) j = S.coef g gs a j + S.coef g gs b j := by
  simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf] at ha hb
  obtain ⟨⟨-, ha1⟩, -⟩ := ha
  obtain ⟨⟨-, hb1⟩, hb2⟩ := hb
  have hA : b (g j.succ) - g j.succ ∈ S.spanTo g (j + 1) := by
    by_cases hj : (j : ℕ) + 1 < r
    · refine (hb1 ⟨j + 1, hj⟩).2 _ (Submodule.subset_span ⟨j.succ, ?_, rfl⟩)
      simp
    · have hr : (j : ℕ) + 1 = r := by have := j.2; omega
      rw [hr]
      refine hb2.2 _ ?_
      refine hf_span_right L S.Hm _ _ ?_
      rintro _ ⟨i, hi, rfl⟩
      rw [hg, if_neg]
      rintro ⟨-, rfl⟩
      simp at hi
  have hB := (ha1 j).2 _ hA
  have hK : S.spanTo g j ≤ LinearMap.ker (pairL L S.Hm (gs j)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    change hf L S.Hm (g i) (gs j) = 0
    rw [hd, if_neg]
    rintro rfl
    simp at hi
  have h0 : pairL L S.Hm (gs j) (g j.succ) = 0 := by
    change hf L S.Hm (g j.succ) (gs j) = 0
    rw [hd, if_neg]
    intro h
    have := congrArg Fin.val h
    simp at this
  have h1 := LinearMap.mem_ker.1 (hK hB)
  change pairL L S.Hm (gs j) (a (b (g j.succ))) =
    pairL L S.Hm (gs j) (a (g j.succ)) + pairL L S.Hm (gs j) (b (g j.succ))
  simp only [map_sub] at h1
  linear_combination h1 - h0

theorem exists_nsmul_mem [IsNonarchimedeanLocalField F] (L : LocE F E) (y : E) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : E) * y ∈ L.O := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have hyF : IsAlgebraic F y := Algebra.IsAlgebraic.isAlgebraic y
  have hy : IsAlgebraic 𝒪[F] y := (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 hyF
  obtain ⟨c, hc, hcy⟩ := hy.exists_integral_multiple
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  have hp : ((Nat.card 𝓀[F] : ℕ) : 𝒪[F]) ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    have := Fintype.ofFinite 𝓀[F]
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hp
  have hdv : c ∣ ((Nat.card 𝓀[F] ^ m : ℕ) : 𝒪[F]) := by
    rw [hu, Nat.cast_pow, Units.mul_left_dvd]
    exact pow_dvd_pow_of_dvd hp m
  obtain ⟨d, hd⟩ := hdv
  refine ⟨Nat.card 𝓀[F] ^ m, pow_ne_zero _ Nat.card_pos.ne', (L.O_def _).2 ?_⟩
  have : ((Nat.card 𝓀[F] ^ m : ℕ) : E) * y = d • (c • y) := by
    rw [smul_smul, mul_comm d c, ← hd, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  rw [this]
  exact hcy.smul d

theorem norm_additiveCharacter_typePrime_eq_one [IsNonarchimedeanLocalField F] (L : LocE F E) (y : E) : ‖L.psi0 y‖ = 1 := by
  obtain ⟨n, hn, hy⟩ := exists_nsmul_mem L y
  have h1 : L.psi0 ((n : E) * y) = 1 := by
    simpa using (L.additive_character_dual_ring _).2 hy 1 L.O.one_mem
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow] at h1
  have h2 := congrArg norm h1
  rw [norm_pow, norm_one] at h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h2

theorem psi_unitary_character : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ a ∈ S.N, ∀ b ∈ S.N, S.psi (a * b) = S.psi a * S.psi b) ∧ (∀ a ∈ S.N', ∀ b ∈ S.N', S.psi' (a * b) = S.psi' a * S.psi' b) ∧ (∀ a, ‖S.psi a‖ = 1 ∧ ‖S.psi' a‖ = 1) ∧ ∀ y : E, ‖L.psi0 y‖ = 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  refine ⟨fun a ha b hb => ?_, fun a ha b hb => ?_,
    fun a => ⟨norm_additiveCharacter_typePrime_eq_one L _, norm_additiveCharacter_typePrime_eq_one L _⟩, norm_additiveCharacter_typePrime_eq_one L⟩
  · simp only [Frames.psi, Frames.psiOf]
    rw [← AddChar.map_add_eq_mul, ← mul_add, ← Finset.sum_add_distrib]
    simp only [coef_mul S S.f S.es _ S.gram S.dual a ha b hb]
  · simp only [Frames.psi', Frames.psiOf]
    rw [← AddChar.map_add_eq_mul, ← mul_add, ← Finset.sum_add_distrib]
    simp only [coef_mul S S.f' S.es' _ S.gram' S.dual' a ha b hb]

end GlobalTheory.FramePsi
