import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementAB
import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffAevalLinP
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BiHomSum
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DegLESum

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (jetPair)

section Shift

variable {K ι κ : Type} [Field K] [Fintype κ]

def shiftGen (b : κ → ι → K) (x : ι) : MvPolynomial κ (MvPolynomial ι K) :=
  MvPolynomial.C (MvPolynomial.X x) +
    ∑ k, MvPolynomial.C (MvPolynomial.C (b k x)) * MvPolynomial.X k

lemma shiftPoly_eq (b : κ → ι → K) (Q : MvPolynomial ι K) :
    shiftPoly b Q = MvPolynomial.aeval (shiftGen b) Q := rfl

lemma shiftPoly_mul (b : κ → ι → K) (f g : MvPolynomial ι K) :
    shiftPoly b (f * g) = shiftPoly b f * shiftPoly b g := by
  simp only [shiftPoly_eq, map_mul]

lemma shiftPoly_add (b : κ → ι → K) (f g : MvPolynomial ι K) :
    shiftPoly b (f + g) = shiftPoly b f + shiftPoly b g := by
  simp only [shiftPoly_eq, map_add]

lemma shiftPoly_zero (b : κ → ι → K) : shiftPoly b (0 : MvPolynomial ι K) = 0 := by
  simp only [shiftPoly_eq, map_zero]

lemma shiftPoly_one (b : κ → ι → K) : shiftPoly b (1 : MvPolynomial ι K) = 1 := by
  simp only [shiftPoly_eq, map_one]

lemma shiftPoly_X (b : κ → ι → K) (x : ι) :
    shiftPoly b (MvPolynomial.X x) = shiftGen b x := by
  simp only [shiftPoly_eq, MvPolynomial.aeval_X]

lemma shiftPoly_C (b : κ → ι → K) (a : K) :
    shiftPoly b (MvPolynomial.C a) = MvPolynomial.C (MvPolynomial.C a) := by
  simp only [shiftPoly_eq, MvPolynomial.aeval_C]
  rfl

lemma shiftPoly_sum {α : Type*} (b : κ → ι → K) (s : Finset α) (f : α → MvPolynomial ι K) :
    shiftPoly b (∑ a ∈ s, f a) = ∑ a ∈ s, shiftPoly b (f a) := by
  simp only [shiftPoly_eq, map_sum]

lemma hasseDir_zero_right (b : κ → ι → K) (β : κ →₀ ℕ) :
    hasseDir b β (0 : MvPolynomial ι K) = 0 := by
  simp only [hasseDir, shiftPoly_zero, MvPolynomial.coeff_zero]

lemma hasseDir_mul [DecidableEq κ] (b : κ → ι → K) (β : κ →₀ ℕ) (f g : MvPolynomial ι K) :
    hasseDir b β (f * g) =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal β, hasseDir b x.1 f * hasseDir b x.2 g := by
  simp only [hasseDir, shiftPoly_mul, MvPolynomial.coeff_mul]

lemma hasseDir_zero_left (b : κ → ι → K) (Q : MvPolynomial ι K) : hasseDir b 0 Q = Q := by
  unfold hasseDir
  rw [← MvPolynomial.constantCoeff_eq]
  induction Q using MvPolynomial.induction_on with
  | C a => rw [shiftPoly_C, MvPolynomial.constantCoeff_C]
  | add p q hp hq => rw [shiftPoly_add, map_add, hp, hq]
  | mul_X p x hp =>
    rw [shiftPoly_mul, map_mul, hp, shiftPoly_X]
    simp [shiftGen]

def dirD (c : ι → K) [Fintype ι] (Q : MvPolynomial ι K) : MvPolynomial ι K :=
  ∑ x, MvPolynomial.C (c x) * MvPolynomial.pderiv x Q

lemma pderiv_shiftGen (b : κ → ι → K) (x : ι) (k : κ) :
    MvPolynomial.pderiv k (shiftGen b x) = MvPolynomial.C (MvPolynomial.C (b k x)) := by
  classical
  unfold shiftGen
  rw [map_add, MvPolynomial.pderiv_C, zero_add, map_sum, Finset.sum_eq_single k]
  · rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X_self, mul_one]
  · intro k' _ hk'
    rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X_of_ne hk', mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

lemma shiftPoly_dirD [Fintype ι] (b : κ → ι → K) (k : κ) (Q : MvPolynomial ι K) :
    shiftPoly b (dirD (b k) Q) = MvPolynomial.pderiv k (shiftPoly b Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C a => simp [dirD, shiftPoly_C, shiftPoly_zero]
  | add p q hp hq =>
    have : dirD (b k) (p + q) = dirD (b k) p + dirD (b k) q := by
      simp only [dirD, map_add, mul_add, Finset.sum_add_distrib]
    rw [this, shiftPoly_add, shiftPoly_add, map_add, hp, hq]
  | mul_X p x hp =>
    have : dirD (b k) (p * MvPolynomial.X x) =
        dirD (b k) p * MvPolynomial.X x + p * MvPolynomial.C (b k x) := by
      simp only [dirD, MvPolynomial.pderiv_mul, mul_add, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      · rw [Finset.sum_eq_single x]
        · rw [MvPolynomial.pderiv_X_self]
          ring
        · intro j _ hj
          rw [MvPolynomial.pderiv_X_of_ne hj.symm]
          simp
        · intro h
          exact absurd (Finset.mem_univ x) h
    rw [this, shiftPoly_add, shiftPoly_mul, shiftPoly_mul, shiftPoly_mul, hp, shiftPoly_X,
      shiftPoly_C, MvPolynomial.pderiv_mul, pderiv_shiftGen]

lemma hasseDir_dirD [Fintype ι] (b : κ → ι → K) (k : κ) (β : κ →₀ ℕ) (Q : MvPolynomial ι K) :
    hasseDir b β (dirD (b k) Q) =
      MvPolynomial.C ((β k + 1 : ℕ) : K) * hasseDir b (β + Finsupp.single k 1) Q := by
  unfold hasseDir
  rw [shiftPoly_dirD, MvPolynomial.coeff_pderiv]
  simp [mul_comm]

end Shift

section Jet

variable {K ι : Type} [Field K]

lemma jetPair_monomial_left (κ : ι →₀ ℕ) (a : K) (F : MvPowerSeries ι K) :
    jetPair (MvPolynomial.monomial κ a) F =
      a * ((Formalism.DworkPowerSeriesWeights.mfact κ : ℕ) : K) * MvPowerSeries.coeff κ F := by
  classical
  rw [Formalism.DworkPowerSeriesWeights.jetPair_eq_sum _ _ {κ} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]

lemma jetPair_X_mul (Q : MvPolynomial ι K) (x : ι) (G : MvPowerSeries ι K) :
    jetPair Q (MvPowerSeries.X x * G) = jetPair (MvPolynomial.pderiv x Q) G := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, Formalism.DworkPowerSeriesWeights.jetPair_add_left, Formalism.DworkPowerSeriesWeights.jetPair_add_left, hp, hq]
  | monomial κ a =>
    rw [MvPolynomial.pderiv_monomial, jetPair_monomial_left, jetPair_monomial_left]
    by_cases h : κ x = 0
    · rw [h]
      have : MvPowerSeries.coeff κ (MvPowerSeries.X x * G) = 0 := by
        rw [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul, if_neg]
        intro hle
        have := hle x
        simp [h] at this
      rw [this]
      simp
    · obtain ⟨μ, rfl⟩ : ∃ μ, κ = μ + Finsupp.single x 1 := by
        refine ⟨κ - Finsupp.single x 1, ?_⟩
        rw [tsub_add_cancel_of_le]
        rw [Finsupp.single_le_iff]
        omega
      rw [add_tsub_cancel_right, Formalism.DworkPowerSeriesWeights.mfact_add_single, add_comm μ, MvPowerSeries.X,
        MvPowerSeries.coeff_add_monomial_mul]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one, one_mul]
      ring

lemma jetPair_linS_mul [Fintype ι] (c : ι → K) (Q : MvPolynomial ι K) (G : MvPowerSeries ι K) :
    jetPair Q (linS c * G) = jetPair (dirD c Q) G := by
  unfold linS dirD
  rw [Finset.sum_mul, Formalism.DworkPowerSeriesWeights.jetPair_sum_right, Formalism.DworkPowerSeriesWeights.jetPair_sum_left]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_assoc, Formalism.DworkPowerSeriesWeights.jetPair_C_mul_right, Formalism.DworkPowerSeriesWeights.jetPair_C_mul_left, jetPair_X_mul]

end Jet

lemma finsupp_step_induction {κ : Type} (P : (κ →₀ ℕ) → Prop) (h0 : P 0)
    (hs : ∀ β k, P β → P (β + Finsupp.single k 1)) : ∀ β, P β := by
  classical
  intro β
  induction β using Finsupp.induction with
  | zero => exact h0
  | single_add a n f _ _ ih =>
    clear * - ih hs
    induction n with
    | zero => simpa using ih
    | succ n ihn =>
      have : Finsupp.single a (n + 1) + f = (Finsupp.single a n + f) + Finsupp.single a 1 := by
        rw [Finsupp.single_add]
        abel
      rw [this]
      exact hs _ _ ihn

theorem e_one_identity_of : JetPairingHasseIdentity := by
  classical
  intro K ι κ _ _ _ b β
  induction β using finsupp_step_induction with
  | h0 =>
    intro Q G
    simp [hasseDir_zero_left]
  | hs β k ih =>
    intro Q G
    have h1 : (∏ k', linS (b k') ^ (β + Finsupp.single k 1 : κ →₀ ℕ) k') =
        linS (b k) * ∏ k', linS (b k') ^ β k' := by
      simp only [Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]
      rw [mul_comm]
      congr 1
      rw [Finset.prod_eq_single k]
      · simp
      · intro k' _ hk'
        simp [hk'.symm]
      · intro h
        exact absurd (Finset.mem_univ k) h
    have h2 : (∏ k', ((β + Finsupp.single k 1 : κ →₀ ℕ) k').factorial) =
        (β k + 1) * ∏ k', (β k').factorial := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
        ← Finset.mul_prod_erase _ (fun k' => (β k').factorial) (Finset.mem_univ k)]
      have : ∏ k' ∈ Finset.univ.erase k, ((β + Finsupp.single k 1 : κ →₀ ℕ) k').factorial =
          ∏ k' ∈ Finset.univ.erase k, (β k').factorial :=
        Finset.prod_congr rfl fun j hj => by
          simp [(Finset.ne_of_mem_erase hj).symm]
      rw [this]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
      ring
    rw [h1, mul_assoc, jetPair_linS_mul, ih, hasseDir_dirD, Formalism.DworkPowerSeriesWeights.jetPair_C_mul_left, h2]
    push_cast
    ring

lemma weight_one_eq {ι : Type} (n : ι →₀ ℕ) : Finsupp.weight (1 : ι → ℕ) n = n.degree :=
  (DFunLike.congr_fun Finsupp.degree_eq_weight_one n).symm

theorem e_one_vanish_of : HasseDerivProdVanish := by
  classical
  intro K ι κ _ _ b C
  induction C with
  | zero =>
    intro f m S _ β hβ
    have hne : (0 : κ →₀ ℕ) ≠ β := by
      rintro rfl
      simp at hβ
    simp only [Finset.univ_eq_empty, Finset.prod_empty, hasseDir, shiftPoly_one,
      MvPolynomial.coeff_one, if_neg hne]
  | succ C ih =>
    intro f m S h β hβ
    rw [Fin.prod_univ_succ, hasseDir_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases h0 : m 0 < ∑ k ∈ S, x.1 k
    · rw [h 0 x.1 h0, zero_mul]
    · rw [ih (fun c => f c.succ) (fun c => m c.succ) S (fun c => h c.succ) x.2, mul_zero]
      rw [Fin.sum_univ_succ, ← hx] at hβ
      simp only [Finsupp.add_apply, Finset.sum_add_distrib] at hβ
      omega

section Expand

variable {K ι κ : Type} [Field K] [Fintype κ]

lemma shiftPoly_expand (b : κ → ι → K) (Q : MvPolynomial ι K) :
    shiftPoly b Q = ∑ d ∈ Q.support, MvPolynomial.C (MvPolynomial.C (MvPolynomial.coeff d Q)) *
      ∏ i ∈ d.support, shiftGen b i ^ d i := by
  rw [shiftPoly_eq, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  rfl

def biHom (d : ℕ) (F : MvPolynomial κ (MvPolynomial ι K)) : Prop :=
  ∀ β n, MvPolynomial.coeff n (MvPolynomial.coeff β F) ≠ 0 → n.degree + β.degree = d

lemma biHom_add {d : ℕ} {F G : MvPolynomial κ (MvPolynomial ι K)} (hF : biHom d F)
    (hG : biHom d G) : biHom d (F + G) := by
  intro β n h
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add] at h
  by_cases h1 : MvPolynomial.coeff n (MvPolynomial.coeff β F) = 0
  · rw [h1, zero_add] at h
    exact hG β n h
  · exact hF β n h1

lemma biHom_sum {α : Type*} {d : ℕ} (s : Finset α) (F : α → MvPolynomial κ (MvPolynomial ι K))
    (h : ∀ a ∈ s, biHom d (F a)) : biHom d (∑ a ∈ s, F a) := by
  first | exact UpperTheory.Reformulated.B.Qf22.biHom_sum .. | (apply UpperTheory.Reformulated.B.Qf22.biHom_sum <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qf22.biHom_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.Qf22.biHom_sum <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qf22.biHom_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.Qf22.biHom_sum <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qf22.biHom_sum K ι κ ‹_› ‹_› α d s F h | exact @UpperTheory.Reformulated.B.Qf22.biHom_sum K ι κ ‹_› ‹_› α d s F | exact @UpperTheory.Reformulated.B.Qf22.biHom_sum K ι κ ‹_› ‹_› α d s | exact @UpperTheory.Reformulated.B.Qf22.biHom_sum K ι κ ‹_› ‹_› α d | exact @UpperTheory.Reformulated.B.Qf22.biHom_sum K ι κ ‹_› ‹_› α | exact @UpperTheory.Reformulated.B.Qf22.biHom_sum K ι κ ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qf22.biHom_sum K ι κ ‹_› | exact @UpperTheory.Reformulated.B.Qf22.biHom_sum K ι κ | exact @UpperTheory.Reformulated.B.Qf22.biHom_sum K ι | exact @UpperTheory.Reformulated.B.Qf22.biHom_sum K

lemma biHom_mul {d e : ℕ} {F G : MvPolynomial κ (MvPolynomial ι K)} (hF : biHom d F)
    (hG : biHom e G) : biHom (d + e) (F * G) := by
  classical
  intro β n h
  rw [MvPolynomial.coeff_mul, MvPolynomial.coeff_sum] at h
  obtain ⟨x, hx, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [MvPolynomial.coeff_mul] at h
  obtain ⟨y, hy, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
  have h1 := hF x.1 y.1 (left_ne_zero_of_mul h)
  have h2 := hG x.2 y.2 (right_ne_zero_of_mul h)
  rw [← hx, ← hy, map_add, map_add]
  omega

lemma biHom_one : biHom 0 (1 : MvPolynomial κ (MvPolynomial ι K)) := by
  classical
  intro β n h
  rw [MvPolynomial.coeff_one] at h
  split_ifs at h with h1
  · rw [MvPolynomial.coeff_one] at h
    split_ifs at h with h2
    · rw [← h1, ← h2]
      simp
    · exact absurd rfl h
  · simp at h

lemma biHom_pow {d : ℕ} {F : MvPolynomial κ (MvPolynomial ι K)} (hF : biHom d F) (m : ℕ) :
    biHom (m * d) (F ^ m) := by
  induction m with
  | zero => simpa using biHom_one
  | succ m ih =>
    rw [pow_succ, Nat.succ_mul]
    exact biHom_mul ih hF

lemma biHom_prod {α : Type*} (s : Finset α) (d : α → ℕ)
    (F : α → MvPolynomial κ (MvPolynomial ι K)) (h : ∀ a ∈ s, biHom (d a) (F a)) :
    biHom (∑ a ∈ s, d a) (∏ a ∈ s, F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using biHom_one
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact biHom_mul (h a (Finset.mem_insert_self _ _))
      (ih fun a' ha' => h a' (Finset.mem_insert_of_mem ha'))

lemma biHom_C {d : ℕ} {p : MvPolynomial ι K} (hp : p.IsHomogeneous d) :
    biHom d (MvPolynomial.C p : MvPolynomial κ (MvPolynomial ι K)) := by
  classical
  intro β n h
  rw [MvPolynomial.coeff_C] at h
  split_ifs at h with h1
  · have := hp h
    rw [weight_one_eq] at this
    rw [← h1, this]
    simp
  · simp at h

lemma biHom_X (k : κ) : biHom 1 (MvPolynomial.X k : MvPolynomial κ (MvPolynomial ι K)) := by
  classical
  intro β n h
  rw [MvPolynomial.coeff_X] at h
  split_ifs at h with h1
  · rw [MvPolynomial.coeff_one] at h
    split_ifs at h with h2
    · rw [← h1, ← h2]
      simp
    · exact absurd rfl h
  · simp at h

lemma biHom_shiftGen (b : κ → ι → K) (x : ι) : biHom 1 (shiftGen b x) := by
  unfold shiftGen
  refine biHom_add (biHom_C (MvPolynomial.isHomogeneous_X K x)) (biHom_sum _ _ fun k _ => ?_)
  have := biHom_mul (biHom_C (κ := κ) (MvPolynomial.isHomogeneous_C ι (b k x)))
    (biHom_X (ι := ι) (K := K) k)
  simpa using this

lemma biHom_shiftPoly (b : κ → ι → K) {d : ℕ} {Q : MvPolynomial ι K} (hQ : Q.IsHomogeneous d) :
    biHom d (shiftPoly b Q) := by
  rw [shiftPoly_expand]
  refine biHom_sum _ _ fun n hn => ?_
  have h1 : n.degree = d := by
    rw [← weight_one_eq]
    exact hQ (MvPolynomial.mem_support_iff.mp hn)
  have h2 := biHom_mul (biHom_C (κ := κ) (MvPolynomial.isHomogeneous_C ι (MvPolynomial.coeff n Q)))
    (biHom_prod n.support (fun i => n i * 1) (fun i => shiftGen b i ^ n i)
      fun i _ => biHom_pow (biHom_shiftGen b i) (n i))
  simp only [mul_one, zero_add] at h2
  rw [← h1, Finsupp.degree_apply]
  exact h2

end Expand

section Integral

variable (K ι κ : Type) [NormedField K] [IsUltrametricDist K]

def biInt : Subring (MvPolynomial κ (MvPolynomial ι K)) where
  carrier := {F | ∀ β, MvPolynomial.coeff β F ∈ Formalism.DworkPowerSeriesWeights.opInt K ι}
  mul_mem' := by
    intro P Q hP hQ β
    classical
    rw [MvPolynomial.coeff_mul]
    exact Subring.sum_mem _ fun x _ => Subring.mul_mem _ (hP _) (hQ _)
  one_mem' := by
    intro β
    classical
    rw [MvPolynomial.coeff_one]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  add_mem' := by
    intro P Q hP hQ β
    rw [MvPolynomial.coeff_add]
    exact Subring.add_mem _ (hP _) (hQ _)
  zero_mem' := by
    intro β
    rw [MvPolynomial.coeff_zero]
    exact Subring.zero_mem _
  neg_mem' := by
    intro P hP β
    rw [MvPolynomial.coeff_neg]
    exact Subring.neg_mem _ (hP β)

variable {K ι κ}

lemma C_mem_biInt {p : MvPolynomial ι K} (hp : p ∈ Formalism.DworkPowerSeriesWeights.opInt K ι) :
    (MvPolynomial.C p : MvPolynomial κ (MvPolynomial ι K)) ∈ biInt K ι κ := by
  classical
  intro β
  rw [MvPolynomial.coeff_C]
  split_ifs
  · exact hp
  · exact Subring.zero_mem _

lemma X_mem_biInt (k : κ) :
    (MvPolynomial.X k : MvPolynomial κ (MvPolynomial ι K)) ∈ biInt K ι κ := by
  classical
  intro β
  rw [MvPolynomial.coeff_X]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

lemma C_mem_opInt {c : K} (hc : ‖c‖ ≤ 1) :
    (MvPolynomial.C c : MvPolynomial ι K) ∈ Formalism.DworkPowerSeriesWeights.opInt K ι := by
  classical
  intro n
  rw [MvPolynomial.coeff_C]
  split_ifs
  · exact hc
  · simp

lemma X_mem_opInt (x : ι) : (MvPolynomial.X x : MvPolynomial ι K) ∈ Formalism.DworkPowerSeriesWeights.opInt K ι := by
  classical
  intro n
  rw [MvPolynomial.coeff_X]
  split_ifs <;> simp

lemma shiftPoly_mem_biInt [Fintype κ] (b : κ → ι → K) (Q : MvPolynomial ι K)
    (hQ : ∀ n, ‖MvPolynomial.coeff n Q‖ ≤ 1) (hb : ∀ k x, ‖b k x‖ ≤ 1) :
    shiftPoly b Q ∈ biInt K ι κ := by
  rw [shiftPoly_expand]
  refine Subring.sum_mem _ fun n _ => Subring.mul_mem _ (C_mem_biInt (C_mem_opInt (hQ n)))
    (Subring.prod_mem _ fun x _ => Subring.pow_mem _ ?_ _)
  unfold shiftGen
  exact Subring.add_mem _ (C_mem_biInt (X_mem_opInt x)) (Subring.sum_mem _ fun k _ =>
    Subring.mul_mem _ (C_mem_biInt (C_mem_opInt (hb k x))) (X_mem_biInt k))

end Integral

theorem e_one_integral_of : HasseDerivIntegralHomogeneous := by
  intro K ι κ _ _ _ b β Q
  refine ⟨fun hQ hb n => shiftPoly_mem_biInt b Q hQ hb β n, fun d hQ => ?_, fun d hQ hd => ?_⟩
  · intro n hn
    have := biHom_shiftPoly b hQ β n hn
    rw [Finsupp.degree_eq_sum β] at this
    rw [weight_one_eq]
    omega
  · ext n
    by_contra hn
    have := biHom_shiftPoly b hQ β n hn
    rw [Finsupp.degree_eq_sum β] at this
    omega

section DegLE

variable {κ R : Type} [CommRing R]

def degLE (W : Finset κ) (n : ℕ) (F : MvPolynomial κ R) : Prop :=
  ∀ β, MvPolynomial.coeff β F ≠ 0 → ∑ k ∈ W, β k ≤ n

lemma degLE_zero (W : Finset κ) (n : ℕ) : degLE W n (0 : MvPolynomial κ R) := by
  intro β h
  simp at h

lemma degLE_mono {W : Finset κ} {n m : ℕ} {F : MvPolynomial κ R} (h : degLE W n F)
    (hnm : n ≤ m) : degLE W m F := fun β hβ => (h β hβ).trans hnm

lemma degLE_add {W : Finset κ} {n : ℕ} {F G : MvPolynomial κ R} (hF : degLE W n F)
    (hG : degLE W n G) : degLE W n (F + G) := by
  intro β h
  rw [MvPolynomial.coeff_add] at h
  by_cases h1 : MvPolynomial.coeff β F = 0
  · rw [h1, zero_add] at h
    exact hG β h
  · exact hF β h1

lemma degLE_sum {α : Type*} {W : Finset κ} {n : ℕ} (s : Finset α) (F : α → MvPolynomial κ R)
    (h : ∀ a ∈ s, degLE W n (F a)) : degLE W n (∑ a ∈ s, F a) := by
  first | exact UpperTheory.Reformulated.B.Qf21.degLE_sum .. | (apply UpperTheory.Reformulated.B.Qf21.degLE_sum <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qf21.degLE_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.Qf21.degLE_sum <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qf21.degLE_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.Qf21.degLE_sum <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qf21.degLE_sum κ R ‹_› α W n s F h | exact @UpperTheory.Reformulated.B.Qf21.degLE_sum κ R ‹_› α W n s F | exact @UpperTheory.Reformulated.B.Qf21.degLE_sum κ R ‹_› α W n s | exact @UpperTheory.Reformulated.B.Qf21.degLE_sum κ R ‹_› α W n | exact @UpperTheory.Reformulated.B.Qf21.degLE_sum κ R ‹_› α W | exact @UpperTheory.Reformulated.B.Qf21.degLE_sum κ R ‹_› α | exact @UpperTheory.Reformulated.B.Qf21.degLE_sum κ R ‹_› | exact @UpperTheory.Reformulated.B.Qf21.degLE_sum κ R | exact @UpperTheory.Reformulated.B.Qf21.degLE_sum κ

lemma degLE_mul {W : Finset κ} {n m : ℕ} {F G : MvPolynomial κ R} (hF : degLE W n F)
    (hG : degLE W m G) : degLE W (n + m) (F * G) := by
  classical
  intro β h
  rw [MvPolynomial.coeff_mul] at h
  obtain ⟨x, hx, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have h1 := hF x.1 (left_ne_zero_of_mul h)
  have h2 := hG x.2 (right_ne_zero_of_mul h)
  rw [← hx]
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  omega

lemma degLE_C (W : Finset κ) (r : R) : degLE W 0 (MvPolynomial.C r : MvPolynomial κ R) := by
  classical
  intro β h
  rw [MvPolynomial.coeff_C] at h
  split_ifs at h with h1
  · rw [← h1]
    simp
  · exact absurd rfl h

lemma degLE_one (W : Finset κ) : degLE W 0 (1 : MvPolynomial κ R) := by
  simpa using degLE_C W (1 : R)

lemma degLE_X (W : Finset κ) (k : κ) : degLE W 1 (MvPolynomial.X k : MvPolynomial κ R) := by
  classical
  intro β h
  rw [MvPolynomial.coeff_X] at h
  split_ifs at h with h1
  · rw [← h1]
    simp only [Finsupp.single_apply, Finset.sum_ite_eq]
    split_ifs <;> omega
  · exact absurd rfl h

lemma degLE_X_of_notMem {W : Finset κ} {k : κ} (hk : k ∉ W) :
    degLE W 0 (MvPolynomial.X k : MvPolynomial κ R) := by
  classical
  intro β h
  rw [MvPolynomial.coeff_X] at h
  split_ifs at h with h1
  · rw [← h1]
    simp only [Finsupp.single_apply, Finset.sum_ite_eq, if_neg hk, le_refl]
  · exact absurd rfl h

lemma degLE_prod {α : Type*} {W : Finset κ} (s : Finset α) (n : α → ℕ)
    (F : α → MvPolynomial κ R) (h : ∀ a ∈ s, degLE W (n a) (F a)) :
    degLE W (∑ a ∈ s, n a) (∏ a ∈ s, F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using degLE_one W
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact degLE_mul (h a (Finset.mem_insert_self _ _))
      (ih fun a' ha' => h a' (Finset.mem_insert_of_mem ha'))

lemma degLE_det_col {l : ℕ} {W : Finset κ} (N : Matrix (Fin l) (Fin l) (MvPolynomial κ R))
    (n : Fin l → ℕ) (h : ∀ i c, degLE W (n c) (N i c)) : degLE W (∑ c, n c) N.det := by
  rw [Matrix.det_apply']
  refine degLE_sum _ _ fun σ _ => ?_
  have h1 : degLE W 0 (((Equiv.Perm.sign σ : ℤ) : MvPolynomial κ R)) := by
    rw [← map_intCast (MvPolynomial.C : R →+* MvPolynomial κ R)]
    exact degLE_C W _
  have := degLE_mul h1 (degLE_prod Finset.univ n (fun c => N (σ c) c) fun c _ => h (σ c) c)
  rwa [zero_add] at this

lemma degLE_det_row {l : ℕ} {W : Finset κ} (N : Matrix (Fin l) (Fin l) (MvPolynomial κ R))
    (n : Fin l → ℕ) (h : ∀ i c, degLE W (n i) (N i c)) : degLE W (∑ c, n c) N.det := by
  rw [← Matrix.det_transpose]
  exact degLE_det_col N.transpose n fun i c => h c i

lemma degLE_det_rankOne {K : Type} [Field K] {l : ℕ} {W : Finset κ} (φ : K →+* MvPolynomial κ R)
    (hφ : ∀ a, degLE W 0 (φ a)) (M' : Matrix (Fin l) (Fin l) (MvPolynomial κ R)) (v : Fin l → K)
    (η : Fin l → MvPolynomial κ R) (hM : ∀ i c, degLE W 0 (M' i c)) (hη : ∀ c, degLE W 1 (η c)) :
    degLE W 1 (Matrix.of fun i c => M' i c + φ (v i) * η c).det := by
  classical
  by_cases hv : ∀ i, v i = 0
  · have : (Matrix.of fun i c => M' i c + φ (v i) * η c) = M' := by
      ext i c
      simp [hv i]
    rw [this]
    have := degLE_det_col M' (fun _ => 0) hM
    exact degLE_mono this (by simp)
  · push Not at hv
    obtain ⟨i0, hi0⟩ := hv
    set N : Matrix (Fin l) (Fin l) (MvPolynomial κ R) :=
      Matrix.of fun i c => M' i c + φ (v i) * η c with hN
    set A : Matrix (Fin l) (Fin l) (MvPolynomial κ R) :=
      Matrix.of fun i c => if i = i0 then N i0 c else M' i c + φ (-(v i / v i0)) * M' i0 c with hA
    have hdet : A.det = N.det := by
      refine Matrix.det_eq_of_forall_row_eq_smul_add_const
        (fun i => if i = i0 then 0 else φ (-(v i / v i0))) i0 (by simp) fun i c => ?_
      by_cases hi : i = i0
      · subst hi
        simp [hA]
      · simp only [hA, hN, Matrix.of_apply, if_neg hi]
        have : φ (v i) = φ (v i / v i0) * φ (v i0) := by
          rw [← map_mul, div_mul_cancel₀ _ hi0]
        rw [this, map_neg]
        ring
    rw [← hdet]
    have := degLE_det_row (W := W) A (fun i => if i = i0 then 1 else 0) fun i c => by
      by_cases hi : i = i0
      · simp only [hA, hN, Matrix.of_apply, if_pos hi]
        refine degLE_add (degLE_mono (hM _ _) (Nat.zero_le _)) ?_
        simpa using degLE_mul (hφ (v i0)) (hη c)
      · simp only [hA, Matrix.of_apply, if_neg hi]
        refine degLE_add (hM _ _) ?_
        simpa using degLE_mul (hφ (-(v i / v i0))) (hM i0 c)
    simpa using this

end DegLE

section Minor

variable {K σ κ : Type} [Field K] [DecidableEq σ] [Fintype κ]

lemma degLE_CC (W : Finset κ) {ι : Type} (a : K) :
    degLE W 0 (MvPolynomial.C (MvPolynomial.C a) : MvPolynomial κ (MvPolynomial ι K)) :=
  degLE_C W _

lemma degLE_shiftGen {ι : Type} (W : Finset κ) (b : κ → ι → K) (x : ι) :
    degLE W 1 (shiftGen b x) := by
  unfold shiftGen
  refine degLE_add (degLE_mono (degLE_C W _) (Nat.zero_le _)) (degLE_sum _ _ fun k _ => ?_)
  simpa using degLE_mul (degLE_CC W (b k x)) (degLE_X W k)

lemma degLE_shiftGen_zero {ι : Type} (W : Finset κ) (b : κ → ι → K) (x : ι)
    (h : ∀ k ∈ W, b k x = 0) : degLE W 0 (shiftGen b x) := by
  unfold shiftGen
  refine degLE_add (degLE_C W _) (degLE_sum _ _ fun k _ => ?_)
  by_cases hk : k ∈ W
  · rw [h k hk]
    simpa using degLE_zero W 0
  · simpa using degLE_mul (degLE_CC W (b k x)) (degLE_X_of_notMem hk)

lemma shiftPoly_minorAt {r0 r1 l : ℕ} (b : κ → σ × Fin r0 × Fin r1 → K) (s : σ)
    (T : Fin l → Fin r0 → K) (I : Fin l → Fin r1) :
    shiftPoly b (minorAt s T I) = (Matrix.of fun (i c : Fin l) =>
      ∑ a, MvPolynomial.C (MvPolynomial.C (T i a)) * shiftGen b (s, a, I c)).det := by
  rw [shiftPoly_eq, minorAt, AlgHom.map_det]
  congr 1
  refine Matrix.ext fun i c => ?_
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  rw [← shiftPoly_eq, shiftPoly_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [shiftPoly_mul, shiftPoly_C, shiftPoly_X]

variable {r0 r1 l : ℕ} (s : σ) (T : Fin l → Fin r0 → K) (I : Fin l → Fin r1) (pos : κ → σ)
  (ξ : κ → Fin r0 → K) (col : κ → Fin r1)

lemma degLE_minor_col (hI : Function.Injective I) (S : Finset κ) (J : Finset (Fin r1))
    (hS : ∀ k ∈ S, pos k = s → col k ∈ J) :
    degLE S ((univ.image I) ∩ J).card
      (shiftPoly (fun k => colDir (pos k) (ξ k) (col k)) (minorAt s T I)) := by
  classical
  rw [shiftPoly_minorAt]
  have hcard : ((univ.image I) ∩ J).card = ∑ c : Fin l, if I c ∈ J then 1 else 0 := by
    rw [← Finset.card_filter, ← Finset.card_image_of_injective _ hI]
    congr 1
    ext y
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨⟨c, rfl⟩, hc⟩
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, rfl⟩, hc⟩
  rw [hcard]
  refine degLE_det_col _ _ fun i c => ?_
  simp only [Matrix.of_apply]
  refine degLE_sum _ _ fun a _ => ?_
  by_cases hc : I c ∈ J
  · rw [if_pos hc]
    simpa using degLE_mul (degLE_CC S (T i a)) (degLE_shiftGen S _ (s, a, I c))
  · rw [if_neg hc]
    have := degLE_mul (degLE_CC S (T i a)) (degLE_shiftGen_zero S
      (fun k => colDir (pos k) (ξ k) (col k)) (s, a, I c) fun k hk => by
        unfold colDir
        rw [if_neg]
        rintro ⟨h1, h2⟩
        simp only at h1 h2
        exact hc (h2 ▸ hS k hk h1.symm))
    simpa using this

lemma hits_col (S : Finset κ) (J : Finset (Fin r1)) (hS : ∀ k ∈ S, pos k = s → col k ∈ J)
    (β : κ →₀ ℕ) (hβ : ((univ.image I) ∩ J).card < ∑ k ∈ S, β k) :
    hasseDir (fun k => colDir (pos k) (ξ k) (col k)) β (minorAt s T I) = 0 := by
  classical
  by_cases hI : Function.Injective I
  · by_contra h
    exact absurd (degLE_minor_col s T I pos ξ col hI S J hS β h) (not_le.mpr hβ)
  · have : minorAt s T I = 0 := by
      unfold Function.Injective at hI
      push Not at hI
      obtain ⟨c, c', hcc, hne⟩ := hI
      unfold minorAt
      refine Matrix.det_zero_of_column_eq hne fun i => ?_
      simp only [Matrix.of_apply, hcc]
    rw [this, hasseDir_zero_right]

lemma degLE_minor_row (W : Finset κ) (ξ0 : Fin r0 → K) (hW : ∀ k ∈ W, ξ k = ξ0) :
    degLE W 1 (shiftPoly (fun k => colDir (pos k) (ξ k) (col k)) (minorAt s T I)) := by
  classical
  rw [shiftPoly_minorAt]
  set φ : K →+* MvPolynomial κ (MvPolynomial (σ × Fin r0 × Fin r1) K) :=
    (MvPolynomial.C).comp MvPolynomial.C with hφ
  have key := degLE_det_rankOne (W := W) φ (fun a => degLE_CC W a)
    (Matrix.of fun (i c : Fin l) => ∑ a, MvPolynomial.C (MvPolynomial.C (T i a)) *
      (MvPolynomial.C (MvPolynomial.X (s, a, I c)) + ∑ k ∈ Wᶜ,
        MvPolynomial.C (MvPolynomial.C (colDir (pos k) (ξ k) (col k) (s, a, I c))) *
          MvPolynomial.X k))
    (fun i => ∑ a, T i a * ξ0 a)
    (fun c => ∑ k ∈ W, MvPolynomial.C (MvPolynomial.C (if s = pos k ∧ I c = col k then 1 else 0)) *
      MvPolynomial.X k)
    (fun i c => by
      simp only [Matrix.of_apply]
      refine degLE_sum _ _ fun a _ => ?_
      have := degLE_mul (degLE_CC W (ι := σ × Fin r0 × Fin r1) (T i a))
        (degLE_add (degLE_C W (MvPolynomial.X (s, a, I c))) (degLE_sum Wᶜ (fun k =>
          MvPolynomial.C (MvPolynomial.C (colDir (pos k) (ξ k) (col k) (s, a, I c))) *
          MvPolynomial.X k) fun k hk => by
            simpa using degLE_mul (degLE_CC W (K := K) (ι := σ × Fin r0 × Fin r1) _)
              (degLE_X_of_notMem (Finset.mem_compl.mp hk))))
      simpa using this)
    (fun c => degLE_sum _ _ fun k _ => by
      have := degLE_mul (degLE_CC W (K := K) (ι := σ × Fin r0 × Fin r1)
        (if s = pos k ∧ I c = col k then 1 else 0)) (degLE_X W k)
      rwa [zero_add] at this)
  convert key using 2
  refine Matrix.ext fun i c => ?_
  simp only [Matrix.of_apply, shiftGen]
  rw [hφ, RingHom.comp_apply, map_sum, map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_sum_compl W, Finset.mul_sum, mul_add, mul_add, mul_add, Finset.mul_sum,
    Finset.mul_sum]
  have : ∀ k ∈ W, MvPolynomial.C (MvPolynomial.C (T i a)) *
      (MvPolynomial.C (MvPolynomial.C (colDir (pos k) (ξ k) (col k) (s, a, I c))) *
        MvPolynomial.X k) =
      (MvPolynomial.C (MvPolynomial.C (T i a * ξ0 a)) *
        (MvPolynomial.C (MvPolynomial.C (if s = pos k ∧ I c = col k then 1 else 0)) *
          MvPolynomial.X k) : MvPolynomial κ (MvPolynomial (σ × Fin r0 × Fin r1) K)) := by
    intro k hk
    unfold colDir
    simp only [hW k hk]
    split_ifs
    · simp only [map_mul, map_one]
      ring
    · simp
  rw [Finset.sum_congr rfl this]
  ring

lemma hits_row (W : Finset κ) (ξ0 : Fin r0 → K) (hW : ∀ k ∈ W, ξ k = ξ0) (β : κ →₀ ℕ)
    (hβ : 1 < ∑ k ∈ W, β k) :
    hasseDir (fun k => colDir (pos k) (ξ k) (col k)) β (minorAt s T I) = 0 := by
  by_contra h
  exact absurd (degLE_minor_row s T I pos ξ col W ξ0 hW β h) (not_le.mpr hβ)

end Minor

theorem minor_hits : MinorHits := by
  classical
  intro K σ κ _ _ _ r0 r1 l s T I pos ξ col β h
  rcases h with ⟨k, hk⟩ | ⟨k, k', hne, hk, hk', -, h | h⟩ | ⟨k, hk, h | h⟩
  · refine hits_row s T I pos ξ col {k} (ξ k) (fun k' hk' => by rw [Finset.mem_singleton.mp hk']) β ?_
    rw [Finset.sum_singleton]
    omega
  · refine hits_row s T I pos ξ col {k, k'} (ξ k) (fun j hj => ?_) β ?_
    · rcases Finset.mem_insert.mp hj with rfl | hj
      · rfl
      · rw [Finset.mem_singleton.mp hj, h]
    · rw [Finset.sum_pair hne]
      omega
  · refine hits_col s T I pos ξ col {k, k'} {col k} (fun j hj _ => ?_) β ?_
    · rcases Finset.mem_insert.mp hj with rfl | hj
      · exact Finset.mem_singleton_self _
      · rw [Finset.mem_singleton.mp hj, h]
        exact Finset.mem_singleton_self _
    · rw [Finset.sum_pair hne]
      have : ((univ.image I) ∩ {col k}).card ≤ 1 :=
        (Finset.card_le_card Finset.inter_subset_right).trans (by simp)
      omega
  · refine hits_col s T I pos ξ col {k} ∅ (fun j hj hp => ?_) β ?_
    · rw [Finset.mem_singleton.mp hj] at hp
      exact absurd hp h
    · rw [Finset.sum_singleton, Finset.inter_empty, Finset.card_empty]
      omega
  · refine hits_col s T I pos ξ col {k} {col k} (fun j hj _ => ?_) β ?_
    · rw [Finset.mem_singleton.mp hj]
      exact Finset.mem_singleton_self _
    · have : (univ.image I) ∩ {col k} = ∅ := by
        ext y
        simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and,
          Finset.mem_singleton, Finset.notMem_empty, iff_false]
        rintro ⟨⟨c, rfl⟩, hc⟩
        exact h ⟨c, hc⟩
      rw [Finset.sum_singleton, this, Finset.card_empty]
      omega

end Formalism.InvariantFactorPaths.G7
