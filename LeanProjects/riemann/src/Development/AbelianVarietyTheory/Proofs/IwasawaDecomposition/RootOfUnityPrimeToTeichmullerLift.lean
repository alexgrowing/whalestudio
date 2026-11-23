import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariantStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem exists_isTiltOf (c : Om l) (m : ℕ) (hm : 0 < m) (hl : ¬ l ∣ m) (hc : c ^ m = 1) :
    ∃ xb : Per.Fl l, IsTiltOf c m xb := by
  have hcC : (c : ℂ_[l]) ^ m = 1 := by
    have := congrArg (algebraMap (Om l) ℂ_[l]) hc
    rw [map_pow, map_one] at this
    exact this
  have hn : ‖(c : ℂ_[l])‖ = 1 := by
    have := congrArg norm hcC
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 this
  let C : Per.OC l := ⟨(c : ℂ_[l]), (GlobalTheory.RingBasics.mem_OC _).2 hn.le⟩
  have hC : C ^ m = 1 := Subtype.ext (by simpa using hcC)
  have hcop : Nat.Coprime l m := ((Fact.out : l.Prime).coprime_iff_not_dvd).2 hl
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a * l ≡ 1 [MOD m] := by
    refine ⟨l ^ (Nat.totient m - 1), ?_⟩
    rw [← pow_succ, Nat.sub_add_cancel (Nat.totient_pos.2 hm)]
    exact Nat.ModEq.pow_totient hcop
  let y : ℕ → Per.OC l := fun k => C ^ (a ^ k)
  have hy : ∀ k, y (k + 1) ^ l = y k := by
    intro k
    simp only [y]
    rw [← pow_mul]
    refine pow_eq_pow_of_modEq ?_ hC
    rw [pow_succ, mul_assoc]
    simpa using ha.mul_left (a ^ k)
  have hy0 : ∀ k, y k ^ (l ^ k) = C := by
    intro k
    induction k with
    | zero => simp [y]
    | succ k ih => rw [pow_succ', pow_mul, hy, ih]
  refine ⟨(⟨fun k => Ideal.Quotient.mk _ (y k), fun k => ?_⟩ : Perfection (ModP (Per.OC l) l) l), fun k => ⟨y k, ?_, ?_, rfl⟩⟩
  · rw [← map_pow, hy]
  · have := congrArg Subtype.val (hy0 k)
    simpa using this
  · simp only [y]
    rw [← pow_mul, mul_comm, pow_mul, hC, one_pow]

theorem IsTiltOf.pow_eq_one {c : Om l} {m : ℕ} {xb : Per.Fl l} (h : IsTiltOf c m xb) : xb ^ m = 1 := by
  refine Perfection.ext fun k => ?_
  obtain ⟨y, -, h2, h3⟩ := h k
  change PreTilt.coeff k (xb ^ m) = PreTilt.coeff k (1 : Per.Fl l)
  rw [map_pow, map_one, h3, ← map_pow, h2, map_one]

theorem IsTiltOf.untilt_eq {c : Om l} {m : ℕ} {xb : Per.Fl l} (h : IsTiltOf c m xb) :
    ((xb.untilt : Per.OC l) : ℂ_[l]) = (c : ℂ_[l]) := by
  obtain ⟨y0, h0, -, -⟩ := h 0
  rw [pow_zero, pow_one] at h0
  have : xb.untilt = y0 := by
    refine Perfection.teichmuller_spec (I := Ideal.span {((l : ℕ) : Per.OC l)}) fun n => ?_
    obtain ⟨y, h1, -, h3⟩ := h n
    refine ⟨y, h3.symm, ?_⟩
    have : y ^ l ^ n = y0 := Subtype.ext (by simpa [h0] using h1)
    rw [this]
  rw [this, h0]

theorem rootOfUnity_teichmuller : ∀ (l : ℕ) [Fact l.Prime], ∀ o : Om l →+* Per.BdRp l, IsSec o → ∀ (c : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → (∃ xb : Per.Fl l, IsTiltOf c m xb) ∧ ∀ xb : Per.Fl l, IsTiltOf c m xb → xb ^ m = 1 ∧ ((xb.untilt : Per.OC l) : ℂ_[l]) = (c : ℂ_[l]) ∧ aDp l (Per.tm xb) = o c := by
  intro l _ o ho c m hm hl hc
  refine ⟨exists_isTiltOf c m hm hl hc, fun xb h => ⟨IsTiltOf.pow_eq_one h, IsTiltOf.untilt_eq h, ?_⟩⟩
  obtain ⟨-, -, hu, hθ, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  have h1 : aDp l (Per.tm xb) ^ m = 1 := by
    rw [← map_pow, ← map_pow, IsTiltOf.pow_eq_one h, map_one, map_one]
  have h2 : o c ^ m = 1 := by rw [← map_pow, hc, map_one]
  have t1 : Per.θD l (aDp l (Per.tm xb)) = (c : ℂ_[l]) := by
    rw [hθ, WittVector.fontaineTheta_teichmuller, IsTiltOf.untilt_eq h]
  have t2 : Per.θD l (o c) = (c : ℂ_[l]) := ho.th c
  generalize aDp l (Per.tm xb) = y at h1 t1 ⊢
  have hc0 : (c : ℂ_[l]) ≠ 0 := by
    intro h0
    have := congrArg (Per.θD l) h2
    rw [map_pow, map_one, t2, h0, zero_pow hm.ne'] at this
    exact zero_ne_one this
  have hg := (Commute.all y (o c)).geom_sum₂_mul m
  rw [h1, h2, sub_self] at hg
  have hS : IsUnit (∑ i ∈ Finset.range m, y ^ i * o c ^ (m - 1 - i)) := by
    apply hu
    rw [map_sum]
    simp only [map_mul, map_pow, t1, t2]
    rw [geom_sum₂_self]
    exact mul_ne_zero (by exact_mod_cast hm.ne') (pow_ne_zero _ hc0)
  exact sub_eq_zero.1 (hS.mul_right_eq_zero.1 hg)

end GlobalTheory.MemLoc
