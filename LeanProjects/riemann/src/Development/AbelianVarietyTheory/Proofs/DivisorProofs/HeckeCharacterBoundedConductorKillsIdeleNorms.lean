import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDeterminantKernelOpenAndFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TildeCharacterOnUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

open GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.SplitChar GlobalTheory.NormSum.UnramHecke Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.NormKill

variable {D : D7}

theorem vl_le_of_dvd {p N : ℕ} (h : p ∣ N) (v : HeightOneSpectrum (𝓞 D.host.E)) :
    vl D v (N : AE D) ≤ vl D v (p : AE D) := by
  obtain ⟨c, rfl⟩ := h
  rw [Nat.cast_mul, map_mul]
  exact mul_le_of_le_one_right' (vl_le (natCast_mem _ _) v)

theorem exists_global_congN {N : ℕ} (hN : 1 < N) (x : (AE D)ˣ) :
    ∃ a : D.host.Eˣ, ∃ s ∈ OhE D, ((incU D a * x⁻¹ : (AE D)ˣ) : AE D) - 1 = (N : AE D) * s := by
  obtain ⟨n, hn, hx⟩ := GlobalTheory.HeckeVal.exists_denom D ((x⁻¹ : (AE D)ˣ) : AE D)
  obtain ⟨a, r, hr, e⟩ := exists_approx (x : AE D) (Nat.mul_pos (by omega : 0 < N) hn)
  have h1 : inc D a * ((x⁻¹ : (AE D)ˣ) : AE D) - 1 = (N : AE D) * (-(r * ((n : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D)))) := by
    rw [Nat.cast_mul] at e
    linear_combination x.mul_inv - ((x⁻¹ : (AE D)ˣ) : AE D) * e
  have ha : a ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.E (Nat.minFac_prime (by omega : N ≠ 1))
    have h2 := congrArg (vl D v) h1
    rw [map_zero, zero_mul, zero_sub, Valuation.map_neg, map_one, map_mul] at h2
    have h3 : vl D v (N : AE D) < 1 := (vl_le_of_dvd (Nat.minFac_dvd N) v).trans_lt (val_nat_lt hv)
    have h4 := (mul_le_of_le_one_right' (vl_le (neg_mem (mul_mem hr hx)) v)).trans_lt h3
    rw [← h2] at h4
    exact lt_irrefl _ h4
  exact ⟨Units.mk0 a ha, _, neg_mem (mul_mem hr hx), h1⟩

theorem vl_norm_sub_one {N : ℕ} {z : (AE D)ˣ} {s : AE D} (hs : s ∈ OhE D) (e : (z : AE D) - 1 = (N : AE D) * s)
    (v : HeightOneSpectrum (𝓞 D.host.E)) :
    vl D v (((z * sgU D z : (AE D)ˣ) : AE D) - 1) ≤ vl D v (N : AE D) := by
  obtain ⟨v', hv', -⟩ := existsUnique_conjPl D.host.conj.toRingEquiv v
  have hN1 : ∀ w, vl D w (N : AE D) ≤ 1 := fun w => vl_le (natCast_mem _ _) w
  have h1 : ∀ w, vl D w ((z : AE D) - 1) ≤ vl D w (N : AE D) := fun w => by
    rw [e, map_mul]
    exact mul_le_of_le_one_right' (vl_le hs w)
  have h2 : vl D v (sgA D z - 1) ≤ vl D v (N : AE D) := by
    rw [← map_one (sgA D), ← map_sub, vl_sgA (conjPl_symm hv')]
    refine (h1 v').trans (le_of_eq ?_)
    rw [← vl_sgA (conjPl_symm hv'), map_natCast]
  have e2 : ((z * sgU D z : (AE D)ˣ) : AE D) - 1 =
      ((z : AE D) - 1) * (sgA D z - 1) + (((z : AE D) - 1) + (sgA D z - 1)) := by
    change (z : AE D) * sgA D z - 1 = _
    ring
  rw [e2]
  refine Valuation.map_add_le _ ?_ (Valuation.map_add_le _ (h1 v) h2)
  rw [map_mul]
  exact (mul_le_of_le_one_right' (h2.trans (hN1 v))).trans (h1 v)

theorem vl_pow_le {p m : ℕ} (hp : p ∣ m) {v : HeightOneSpectrum (𝓞 D.host.E)} (hv : OverP D.host p v) (k : ℕ) :
    vl D v ((m ^ (k + 1) : ℕ) : AE D) ≤ WithZero.exp (-((k : ℤ) + 1)) := by
  have h1 : vl D v (m : AE D) ≤ WithZero.exp (-1) := by
    have := GlobalTheory.Mem.KerDet.le_exp_neg_one ((vl_le_of_dvd hp v).trans_lt (val_nat_lt hv))
    simpa using this
  rw [Nat.cast_pow, map_pow]
  calc vl D v (m : AE D) ^ (k + 1) ≤ WithZero.exp (-1) ^ (k + 1) := pow_le_pow_left₀ zero_le h1 _
    _ = WithZero.exp (-((k : ℤ) + 1)) := by
      rw [← WithZero.exp_nsmul]
      congr 1
      simp

theorem chi_norm_global (χ : HChar D.host.E) {n : D.what₂.Tau → ℤ} (hi : χ.HasInf (embT D) n) (a : D.host.Eˣ) :
    χ.1 (finIdl D (incU D a * sgU D (incU D a))) = 1 := by
  obtain ⟨k', hk⟩ := exists_real_norm a
  have hu : ((upF D.host.F k' : D.host.Eˣ) : D.host.E) = (a : D.host.E) * D.host.conj a := by
    haveI : Nontrivial (AE D) := by
      obtain ⟨v, -⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.E Nat.prime_two
      refine ⟨⟨0, 1, fun h => ?_⟩⟩
      have := congrArg (vl D v) h
      rw [map_zero, map_one] at this
      exact zero_ne_one this
    apply (inc D).injective
    have := congrArg Units.val hk
    change inc D a * sgA D (inc D a) = inc D _ at this
    rw [← this, sgA_inc, map_mul]
  have hinf : χ.inf (upF D.host.F k') = 1 := by
    apply Units.ext
    rw [hi, Units.val_one]
    refine Finset.prod_eq_one fun τ _ => ?_
    have h0 : embT D τ (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
    have h1 : embT D τ ((upF D.host.F k' : D.host.Eˣ) : D.host.E) = ((Complex.normSq (embT D τ (a : D.host.E)) : ℝ) : ℂ) := by
      rw [hu, map_mul, emb_conj, Complex.mul_conj]
    have h2 : (0 : ℝ) < Complex.normSq (embT D τ (a : D.host.E)) := Complex.normSq_pos.2 h0
    rw [h1, Complex.norm_real, Real.norm_of_nonneg h2.le, div_self (by exact_mod_cast h2.ne'), one_zpow]
  rw [hk, finIdl_incU]
  have h1 := χ.2.2 (upF D.host.F k')
  rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul] at h1
  have h2 : χ.1 (infDiag (upF D.host.F k')) = 1 := hinf
  rw [h2, one_mul] at h1
  exact h1

theorem chi_norm_cong (χ : HChar D.host.E) (S : Finset ℕ) (k : ℕ) (ht : χ.TrivOn D.host.F)
    (hl : ∀ v, χ.UnrAt v ∨ ∃ q ∈ S, Formalism.L2.Host.OverP D.host q v ∧ χ.LevelLe v k) (z : (AE D)ˣ)
    (hz : ∀ q ∈ S, ∀ v, Formalism.L2.Host.OverP D.host q v →
      vl D v (((z * sgU D z : (AE D)ˣ) : AE D) - 1) ≤ WithZero.exp (-((k : ℤ) + 1))) :
    χ.1 (finIdl D (z * sgU D z)) = 1 := by
  obtain ⟨c, -, -, hu, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  have hG : ∀ v k', locF (L := D.host.E) D.host.F v k' ∈ (χ.1.comp (finPartI D.host.E)).ker := fun v k' => by
    rw [MonoidHom.mem_ker]
    exact GlobalTheory.Mem.KerDet.map_finPartI_locF ht v k'
  obtain ⟨b, hb, hun, hc⟩ := exists_of_balanced hu _ hG _ (norm_balanced z)
  rw [MonoidHom.mem_ker] at hb
  rw [← finPartI_finIdl, ← mul_inv_cancel_left b (finIdl D (z * sgU D z)), map_mul, map_mul]
  rw [show χ.1 (finPartI D.host.E b) = 1 from hb, one_mul]
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E χ.1 χ.2.1 _ (finPartI_mem_unitIdl.2 hun) (fun _ => rfl) fun v y hy => ?_
  have hy' : (y : v.adicCompletion D.host.E) = ((b⁻¹ * finIdl D (z * sgU D z) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 v := hy
  have hyu : IsUnitAt v y := by
    unfold IsUnitAt
    rw [hy']
    exact hun v
  change χ.loc v y = 1
  rcases hl v with hU | ⟨q, hq, hov, hL⟩
  · exact hU y hyu
  · have hlt : WithZero.exp (-((k : ℤ) + 1)) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have h0 : Valued.v ((finIdl D (z * sgU D z) : AdeleRing (𝓞 D.host.E) D.host.E).2 v - 1) < 1 := by
      rw [vl_sub_one]
      exact (hz q hq v hov).trans_lt hlt
    have hv1 : IdlFact.valAt v (finIdl D (z * sgU D z)) = 1 := by
      rw [IdlFact.valAt_apply, ← sub_add_cancel ((finIdl D (z * sgU D z) : AdeleRing (𝓞 D.host.E) D.host.E).2 v) 1, add_comm]
      exact Valuation.map_one_add_of_lt _ h0
    have h3 : Units.map (GlobalTheory.Mem.LocTriv.ev v) (b⁻¹ * finIdl D (z * sgU D z)) = Units.map (GlobalTheory.Mem.LocTriv.ev v) (finIdl D (z * sgU D z)) := by
      rw [map_mul, map_inv, hc v hv1, inv_one, one_mul]
    have h4 := congrArg Units.val h3
    refine hL y hyu ?_
    rw [hy']
    change Valued.v (((b⁻¹ * finIdl D (z * sgU D z) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 v - 1) ≤ _
    have h4' : ((b⁻¹ * finIdl D (z * sgU D z) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 v =
        (finIdl D (z * sgU D z) : AdeleRing (𝓞 D.host.E) D.host.E).2 v := h4
    rw [h4', vl_sub_one]
    refine (hz q hq v hov).trans ?_
    rw [WithZero.exp_le_exp]
    omega

theorem mul_eq_mul_mul_inv {G : Type} [CommGroup G] (x y u v : G) : x * y = (u * v) * ((u * x⁻¹) * (v * y⁻¹))⁻¹ := by
  simp [mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]

theorem chi_finIdl_norm_eq_one : ∀ (D : D7) (χ : HChar D.host.E) (n : D.what₂.Tau → ℤ) (S : Finset ℕ) (k : ℕ), χ.TrivOn D.host.F → χ.HasInf (embT D) n → (∀ q ∈ S, q.Prime) → (∀ v, χ.UnrAt v ∨ ∃ q ∈ S, Formalism.L2.Host.OverP D.host q v ∧ χ.LevelLe v k) → ∀ x : (AE D)ˣ, χ.1 (finIdl D (x * sgU D x)) = 1 := by
  intro D χ n S k ht hi hS hl x
  have hP : 0 < ∏ q ∈ S, q := Finset.prod_pos fun q hq => (hS q hq).pos
  have hm : 1 < (2 * ∏ q ∈ S, q) ^ (k + 1) := Nat.one_lt_pow (by omega) (by omega)
  obtain ⟨a, s, hs, e⟩ := exists_global_congN (D := D) hm x
  have hz : ∀ q ∈ S, ∀ v, Formalism.L2.Host.OverP D.host q v →
      vl D v ((((incU D a * x⁻¹) * sgU D (incU D a * x⁻¹) : (AE D)ˣ) : AE D) - 1) ≤ WithZero.exp (-((k : ℤ) + 1)) :=
    fun q hq v hov => (vl_norm_sub_one hs e v).trans
      (vl_pow_le (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hq) 2) hov k)
  have h1 := chi_norm_cong χ S k ht hl _ hz
  have h2 := chi_norm_global χ hi a
  have e2 : x * sgU D x = (incU D a * sgU D (incU D a)) * ((incU D a * x⁻¹) * sgU D (incU D a * x⁻¹))⁻¹ := by
    rw [map_mul, map_inv]
    exact mul_eq_mul_mul_inv _ _ _ _
  rw [e2, map_mul, map_mul, map_inv, map_inv, h2, h1, inv_one, one_mul]

end GlobalTheory.NormKill
