import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolTSt

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct

namespace VolTU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def OS : Submodule (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
  Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)

theorem mem_OEv (x : Fv F v ⊗[F] E) : x ∈ OEv (E := E) v ↔ x ∈ OS (E := E) v := Iff.rfl

theorem sc_mul (a b : Fv F v) : sc (E := E) v (a * b) = sc (E := E) v a * sc (E := E) v b := by
  simp [sc, Algebra.TensorProduct.tmul_mul_tmul]

theorem sc_one : sc (E := E) v (1 : Fv F v) = 1 := rfl

theorem sc_mul_eq_smul (c : Fv F v) (x : Fv F v ⊗[F] E) : sc (E := E) v c * x = c • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sc, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul']
  | add x y hx hy => rw [mul_add, hx, hy, smul_add]

theorem sc_mul_mem {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) {x : Fv F v ⊗[F] E}
    (hx : x ∈ OEv (E := E) v) : sc (E := E) v c * x ∈ OEv (E := E) v := by
  rw [mem_OEv] at hx ⊢
  rw [sc_mul_eq_smul]
  have := (OS (E := E) v).smul_mem (⟨c, hc⟩ : v.adicCompletionIntegers F) hx
  exact this

theorem val_le_one_mem {c : Fv F v} (hc : Valued.v c ≤ 1) : c ∈ v.adicCompletionIntegers F :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) (K := F) (v := v)).mpr hc

theorem unit_mul_mem_iff {c : Fv F v} (hc : Valued.v c = 1) (x : Fv F v ⊗[F] E) :
    sc (E := E) v c * x ∈ OEv (E := E) v ↔ x ∈ OEv (E := E) v := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hc; exact zero_ne_one hc
  constructor
  · intro h
    have hi : Valued.v c⁻¹ ≤ 1 := by rw [map_inv₀, hc, inv_one]
    have := sc_mul_mem (E := E) v (val_le_one_mem v hi) h
    rwa [← mul_assoc, ← sc_mul, inv_mul_cancel₀ hc0, sc_one, one_mul] at this
  · intro h
    exact sc_mul_mem (E := E) v (val_le_one_mem v hc.le) h

theorem val_alp (hd : Valued.v (dV v) = 1) (r : ℕ) (a : Fin (r + 1)) : Valued.v (alp v r a) = 1 := by
  unfold alp
  split_ifs
  · rw [map_pow, map_inv₀, hd, inv_one, one_pow]
  · exact map_one _

theorem natCast_ne_zero {g : ℕ} (hg : g ≠ 0) : (g : Fv F v) ≠ 0 := Nat.cast_ne_zero.mpr hg

theorem natCast_memO (g : ℕ) : (g : Fv F v) ∈ v.adicCompletionIntegers F :=
  _root_.natCast_mem (v.adicCompletionIntegers F) g

theorem one_lt_absNorm : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

theorem val_eq_one_of_absV {x : Fv F v} (h : absV v x = 1) : Valued.v x = 1 := by
  unfold absV at h
  split_ifs at h with h0
  · exact absurd h zero_ne_one
  · have hN : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast one_lt_absNorm v
    have hk : Multiplicative.toAdd (WithZero.unzero h0) = 0 :=
      (zpow_eq_one_iff_right₀ (by positivity) hN.ne').mp h
    have hu : WithZero.unzero h0 = 1 := by
      rw [← ofAdd_toAdd (WithZero.unzero h0), hk, ofAdd_zero]
    rw [← WithZero.coe_unzero h0, hu, WithZero.coe_one]

end VolTU

open VolTU in

theorem volTUOEq_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (hd : Valued.v (dV v) = 1) {g : ℕ} (hg : g ≠ 0) (r : ℕ) :
    VolTUOEq (E := E) v g r := by
  have key : ∀ (q : UIdx r) (y : Fv F v ⊗[F] E),
      sc (E := E) v ((alp v r q.1.1)⁻¹ * alp v r q.1.2) * y ∈ OEv (E := E) v ↔ y ∈ OEv (E := E) v := by
    intro q y
    apply unit_mul_mem_iff
    rw [map_mul, map_inv₀, val_alp v hd, val_alp v hd, inv_one, one_mul]
  have e : ∀ (a b : Fv F v) (y : Fv F v ⊗[F] E),
      sc (E := E) v (a * b * (g : Fv F v)⁻¹) * y = sc (E := E) v (a * b) * (sc (E := E) v (g : Fv F v)⁻¹ * y) := by
    intro a b y
    rw [sc_mul, mul_assoc]
  have hg0 := natCast_ne_zero v hg
  have hgO := natCast_memO v g
  have sw : ∀ y : Fv F v ⊗[F] E,
      y * sc (E := E) v (g : Fv F v)⁻¹ ∈ OS (E := E) v ↔ sc (E := E) v (g : Fv F v)⁻¹ * (-y) ∈ OS (E := E) v := by
    intro y
    rw [mul_neg, Submodule.neg_mem_iff, mul_comm]
  ext p
  simp only [deepCongruenceVolume, VolTUSet, UO, Set.mem_setOf_eq, e, key]
  simp only [mem_OEv]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun q => ?_⟩
    rw [sw, neg_sub]
    exact h3 q
  · rintro ⟨h1, h3⟩
    have h3' : ∀ q, sc (E := E) v (g : Fv F v)⁻¹ * (p.1 q - p.2 q) ∈ OS (E := E) v := fun q => by
      rw [← neg_sub, ← sw]
      exact h3 q
    refine ⟨h1, fun q => ?_, h3'⟩
    have h4 := (OS (E := E) v).smul_mem (⟨(g : Fv F v), hgO⟩ : v.adicCompletionIntegers F) (h3' q)
    have h5 : p.1 q - p.2 q ∈ OS (E := E) v := by
      have h6 : (g : Fv F v) • (sc (E := E) v (g : Fv F v)⁻¹ * (p.1 q - p.2 q)) ∈ OS (E := E) v := h4
      rwa [← sc_mul_eq_smul, ← mul_assoc, ← sc_mul, mul_inv_cancel₀ hg0, sc_one, one_mul] at h6
    have h7 : p.2 q = p.1 q - (p.1 q - p.2 q) := by abel
    rw [h7]
    exact (OS (E := E) v).sub_mem (h1 q) h5

end Formalism.L2.SG.Pf.NcVal
