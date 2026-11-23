import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.JetExpShape
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.DegreeLeOfMemAntidiagonal

noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.C

namespace JetSubstitutionLemmas

section Field

variable {K : Type} [Field K]

theorem hs1 {a : PowerSeries K} (h : PowerSeries.constantCoeff a = 0) : PowerSeries.HasSubst a := by
  exact PowerSeries.HasSubst.of_constantCoeff_zero h

theorem cc_subst {σ : Type} {a : MvPowerSeries σ K} (ha : MvPowerSeries.constantCoeff a = 0)
    (g : PowerSeries K) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a g) = PowerSeries.constantCoeff g := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  simp only [map_pow, ha]
  rw [finsum_eq_single _ 0 (fun d hd => by simp [zero_pow hd])]
  simp

theorem cc_subst1 {a : PowerSeries K} (ha : PowerSeries.constantCoeff a = 0) (g : PowerSeries K) :
    PowerSeries.constantCoeff (PowerSeries.subst a g) = PowerSeries.constantCoeff g := by
  exact cc_subst (σ := Unit) ha g

theorem cc_derivative_log {l linv : PowerSeries K} (h : IsLogPair l linv) :
    PowerSeries.constantCoeff (PowerSeries.derivative K l) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
  simp [h.2.1]

private theorem powerSeries_subst_mul {τ : Type} {a : MvPowerSeries τ K} (ha : PowerSeries.HasSubst a)
    (f g : PowerSeries K) :
    PowerSeries.subst a (f * g) = PowerSeries.subst a f * PowerSeries.subst a g := by
  rw [← PowerSeries.coe_substAlgHom ha, map_mul]

theorem subst_Dinv {l linv : PowerSeries K} (h : IsLogPair l linv) (g : PowerSeries K) :
    PowerSeries.subst linv (Dinv l g) =
      PowerSeries.derivative K (PowerSeries.subst linv g) := by
  obtain ⟨_, _, hi0, _, hil⟩ := h
  have hsl : PowerSeries.HasSubst linv := hs1 hi0
  have hd : PowerSeries.subst linv (PowerSeries.derivative K l) * PowerSeries.derivative K linv = 1 := by
    rw [← PowerSeries.derivative_subst hsl, hil, PowerSeries.derivative_X]
  have hc : PowerSeries.constantCoeff (PowerSeries.derivative K l) = 1 :=
    cc_derivative_log ⟨by assumption, by assumption, hi0, by assumption, hil⟩
  have hinv : (PowerSeries.derivative K l)⁻¹ * PowerSeries.derivative K l = 1 :=
    PowerSeries.inv_mul_cancel _ (by rw [hc]; exact one_ne_zero)
  have hsubinv : PowerSeries.subst linv ((PowerSeries.derivative K l)⁻¹) *
      PowerSeries.subst linv (PowerSeries.derivative K l) = 1 := by
    rw [← powerSeries_subst_mul hsl, hinv, ← PowerSeries.coe_substAlgHom hsl, map_one]
  have key : PowerSeries.subst linv ((PowerSeries.derivative K l)⁻¹) = PowerSeries.derivative K linv := by
    calc PowerSeries.subst linv ((PowerSeries.derivative K l)⁻¹)
        = PowerSeries.subst linv ((PowerSeries.derivative K l)⁻¹) *
          (PowerSeries.subst linv (PowerSeries.derivative K l) * PowerSeries.derivative K linv) := by
          rw [hd, mul_one]
      _ = (PowerSeries.subst linv ((PowerSeries.derivative K l)⁻¹) *
          PowerSeries.subst linv (PowerSeries.derivative K l)) * PowerSeries.derivative K linv := by ring
      _ = PowerSeries.derivative K linv := by rw [hsubinv, one_mul]
  unfold Dinv
  rw [powerSeries_subst_mul hsl, key, PowerSeries.derivative_subst hsl, mul_comm]

theorem subst_Dinv_iterate {l linv : PowerSeries K} (h : IsLogPair l linv) (g : PowerSeries K)
    (i : ℕ) : PowerSeries.subst linv ((Dinv l)^[i] g) =
      (PowerSeries.derivative K)^[i] (PowerSeries.subst linv g) := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', subst_Dinv h, ih]

theorem jet_eq_cc {l linv : PowerSeries K} (h : IsLogPair l linv) (g : PowerSeries K) (i : ℕ) :
    jet l g i =
      PowerSeries.constantCoeff ((PowerSeries.derivative K)^[i] (PowerSeries.subst linv g)) := by
  unfold jet
  rw [← subst_Dinv_iterate h g i, cc_subst1 h.2.2.1]

theorem jet_eq {l linv : PowerSeries K} (h : IsLogPair l linv) (g : PowerSeries K) (i : ℕ) :
    jet l g i = (i.factorial : K) * PowerSeries.coeff i (PowerSeries.subst linv g) := by
  rw [jet_eq_cc h, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_iterate_derivative]
  simp [Nat.one_ascFactorial]

variable {R : Subring K}

theorem intMv_of_intPS {f : PowerSeries K} (h : IntPS R f) : IntMv R (f : MvPowerSeries Unit K) := by
  intro n
  have hn : n = Finsupp.single () (n ()) := by
    ext ⟨⟩
    simp
  have := h (n ())
  rw [hn]
  exact this

theorem intPS_of_intMv {f : PowerSeries K} (h : IntMv R (f : MvPowerSeries Unit K)) : IntPS R f := by
  intro n
  exact h (Finsupp.single () n)

theorem intPS_mul {f g : PowerSeries K} (hf : IntPS R f) (hg : IntPS R g) : IntPS R (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  exact sum_mem fun p _ => mul_mem (hf _) (hg _)

theorem intPS_derivative {f : PowerSeries K} (hf : IntPS R f) :
    IntPS R (PowerSeries.derivative K f) := by
  intro n
  rw [PowerSeries.coeff_derivative]
  exact mul_mem (hf _) (add_mem (natCast_mem R n) (one_mem R))

theorem intPS_of_mul_eq_one {U V : PowerSeries K} (hU : IntPS R U)
    (hU0 : PowerSeries.constantCoeff U = 1) (hUV : U * V = 1) : IntPS R V := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h1 := congrArg (PowerSeries.coeff n) hUV
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ'] at h1
    simp only [Nat.sub_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, hU0, one_mul] at h1
    have hrest : ∑ k ∈ Finset.range n, PowerSeries.coeff (k + 1) U * PowerSeries.coeff (n - (k + 1)) V ∈ R :=
      sum_mem fun k hk => mul_mem (hU _) (ih _ (by have := Finset.mem_range.mp hk; omega))
    have h1' : PowerSeries.coeff n V = PowerSeries.coeff n (1 : PowerSeries K) -
        ∑ k ∈ Finset.range n, PowerSeries.coeff (k + 1) U * PowerSeries.coeff (n - (k + 1)) V := by
      rw [← h1]
      ring
    rw [h1']
    refine sub_mem ?_ hrest
    rw [PowerSeries.coeff_one]
    split_ifs
    · exact one_mem R
    · exact zero_mem R

theorem intPS_Dinv {l f : PowerSeries K} (hl : IsOneUnit R (PowerSeries.derivative K l))
    (hf : IntPS R (PowerSeries.derivative K f)) : IntPS R (Dinv l f) := by
  unfold Dinv
  exact intPS_mul (intPS_of_mul_eq_one hl.2 hl.1
    (PowerSeries.mul_inv_cancel _ (by rw [hl.1]; exact one_ne_zero))) hf

end Field

section CharZero

variable {K : Type} [Field K] [CharZero K] {R : Subring K}

theorem intPS_derivative_of_LG {f : PowerSeries K} (hf : LG R f) :
    IntPS R (PowerSeries.derivative K f) := by
  obtain ⟨hf0, hE⟩ := hf
  have hEi : IntPS R (mvExp f : PowerSeries K) := intPS_of_intMv hE
  have hE0 : PowerSeries.constantCoeff (mvExp f : PowerSeries K) = 1 := IntegralMvPolynomialLemmas.constantCoeff_mvExp hf0
  have hd := derivative_mvExp (K := K) (f := f) hf0
  have hinv := PowerSeries.mul_inv_cancel (mvExp f : PowerSeries K) (by rw [hE0]; exact one_ne_zero)
  have e : PowerSeries.derivative K f =
      PowerSeries.derivative K (mvExp f : PowerSeries K) * (mvExp f : PowerSeries K)⁻¹ := by
    rw [hd, mul_assoc, hinv, mul_one]
  rw [e]
  exact intPS_mul (intPS_derivative hEi) (intPS_of_mul_eq_one hEi hE0 hinv)

end CharZero

end JetSubstitutionLemmas

open JetSubstitutionLemmas

theorem jetAdditivity : JetAdditive := by
  intro K _ _ l linv f h i
  exact jet_eq h f i

theorem jetExpIntegral' : JetLG := by
  intro K _ _ R l f hl hf i hi
  have h1 : IntPS R (Dinv l f) := intPS_Dinv hl (intPS_derivative_of_LG hf)
  have h2 : ∀ n : ℕ, IntPS R ((Dinv l)^[n] (Dinv l f)) := by
    intro n
    induction n with
    | zero => exact h1
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact intPS_Dinv hl (intPS_derivative ih)
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  unfold jet
  rw [Function.iterate_succ_apply]
  have := h2 n 0
  rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply] at this

namespace JetSubstitutionLemmas

section Norm

variable {K : Type} [Field K]

theorem cc_mulBy {l linv : PowerSeries K} (h : IsLogPair l linv) (a : K) :
    PowerSeries.constantCoeff (mulBy l linv a) = 0 := by
  unfold mulBy
  rw [cc_subst1 (by simp [h.1]) linv]
  exact h.2.2.1

theorem subst_linv_mulBy {l linv : PowerSeries K} (h : IsLogPair l linv) (a : K)
    (ph : PowerSeries K) :
    PowerSeries.subst linv (PowerSeries.subst (mulBy l linv a) ph) =
      PowerSeries.rescale a (PowerSeries.subst linv ph) := by
  have hi := hs1 h.2.2.1
  have hm : PowerSeries.HasSubst (mulBy l linv a) := hs1 (cc_mulBy h a)
  have haX : PowerSeries.HasSubst (a • PowerSeries.X : PowerSeries K) := hs1 (by simp)
  have hCl : PowerSeries.HasSubst (PowerSeries.C a * l) := hs1 (by simp [h.1])
  rw [PowerSeries.subst_comp_subst_apply hm hi, PowerSeries.rescale_eq_subst]
  have e1 : PowerSeries.subst linv (mulBy l linv a) = PowerSeries.subst (a • PowerSeries.X : PowerSeries K) linv := by
    unfold mulBy
    rw [PowerSeries.subst_comp_subst_apply hCl hi]
    congr 1
    rw [← PowerSeries.smul_eq_C_mul, PowerSeries.subst_smul hi, h.2.2.2.2]
  rw [e1]
  exact (PowerSeries.subst_comp_subst_apply hi haX ph).symm

theorem jet_mulBy {l linv : PowerSeries K} (h : IsLogPair l linv) (a : K) (ph : PowerSeries K)
    (i : ℕ) : jet l (PowerSeries.subst (mulBy l linv a) ph) i = a ^ i * jet l ph i := by
  rw [jet_eq h, jet_eq h, subst_linv_mulBy h, PowerSeries.coeff_rescale]
  ring

theorem jet_sub {l linv : PowerSeries K} (h : IsLogPair l linv) (f g : PowerSeries K) (i : ℕ) :
    jet l (f - g) i = jet l f i - jet l g i := by
  have hi := hs1 h.2.2.1
  rw [jet_eq h, jet_eq h, jet_eq h, ← PowerSeries.coe_substAlgHom hi, map_sub, map_sub]
  ring

theorem jet_smul {l linv : PowerSeries K} (h : IsLogPair l linv) (c : K) (f : PowerSeries K)
    (i : ℕ) : jet l (c • f) i = c * jet l f i := by
  have hi := hs1 h.2.2.1
  rw [jet_eq h, jet_eq h, PowerSeries.subst_smul hi, map_smul, smul_eq_mul]
  ring

end Norm

end JetSubstitutionLemmas

theorem jetNorm' : JetNorm := by
  intro K _ _ R l linv ph a b h hl _ hN i hi
  have := jetExpIntegral' K R l (PowerSeries.subst (mulBy l linv a) ph - (a * b) • ph) hl hN i hi
  rw [jet_sub h, jet_mulBy h, jet_smul h] at this
  convert this using 1
  ring

theorem jetOne' : JetOne := by
  intro K _ _ R l linv ph h hl hph hN h2
  have := jetNorm' K R l linv ph (-1) (-1) h hl hph hN 1 le_rfl
  have e : jet l ph 1 = (((-1 : K) ^ 1 - (-1) * (-1)) * jet l ph 1) * (-(2 : K)⁻¹) := by
    rw [show ((-1 : K) ^ 1 - (-1) * (-1)) = -2 by norm_num]
    rw [show (-2 : K) * jet l ph 1 * -(2 : K)⁻¹ = (2 * (2 : K)⁻¹) * jet l ph 1 by ring,
      mul_inv_cancel₀ two_ne_zero, one_mul]
  rw [e]
  exact mul_mem this (neg_mem h2)

namespace JetSubstitutionLemmas

section Adj

variable {K : Type} [Field K] {σ : Type}

theorem hsM {a : MvPowerSeries σ K} (h : MvPowerSeries.constantCoeff a = 0) :
    PowerSeries.HasSubst a := by
  exact PowerSeries.HasSubst.of_constantCoeff_zero h

theorem cc_subst_zero {a : MvPowerSeries σ K} (ha : MvPowerSeries.constantCoeff a = 0)
    {g : PowerSeries K} (hg : PowerSeries.constantCoeff g = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a g) = 0 := by
  rw [cc_subst ha g, hg]

theorem subst_subst_linv {l linv : PowerSeries K} (h : IsLogPair l linv) {g : MvPowerSeries σ K}
    (hg : MvPowerSeries.constantCoeff g = 0) :
    PowerSeries.subst (PowerSeries.subst g linv) l = g := by
  rw [← PowerSeries.subst_comp_subst_apply (hs1 h.2.2.1) (hsM hg), h.2.2.2.2, PowerSeries.subst_X (hsM hg)]

theorem subst_subst_l {l linv : PowerSeries K} (h : IsLogPair l linv) {w : MvPowerSeries σ K}
    (hw : MvPowerSeries.constantCoeff w = 0) :
    PowerSeries.subst (PowerSeries.subst w l) linv = w := by
  rw [← PowerSeries.subst_comp_subst_apply (hs1 h.1) (hsM hw), h.2.2.2.1, PowerSeries.subst_X (hsM hw)]

theorem subst_ph_linv {l linv : PowerSeries K} (h : IsLogPair l linv) (ph : PowerSeries K)
    {g : MvPowerSeries σ K} (hg : MvPowerSeries.constantCoeff g = 0) :
    PowerSeries.subst (PowerSeries.subst g linv) ph =
      PowerSeries.subst g (PowerSeries.subst linv ph) := by
  exact (PowerSeries.subst_comp_subst_apply (hs1 h.2.2.1) (hsM hg) ph).symm

theorem subst_ph {l linv : PowerSeries K} (h : IsLogPair l linv) (ph : PowerSeries K)
    {w : MvPowerSeries σ K} (hw : MvPowerSeries.constantCoeff w = 0) :
    PowerSeries.subst w ph =
      PowerSeries.subst (PowerSeries.subst w l) (PowerSeries.subst linv ph) := by
  rw [PowerSeries.subst_comp_subst_apply (hs1 h.2.2.1) (hsM (cc_subst_zero hw h.1)), subst_subst_l h hw]

def Q (l ψ : PowerSeries K) (α β : K) : MvPowerSeries (Fin 2) K :=
  PowerSeries.subst (MvPowerSeries.C α * PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) l +
    MvPowerSeries.C β * PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) l) ψ

theorem cc_pderiv_Q {l : PowerSeries K} (hl0 : PowerSeries.constantCoeff l = 0)
    (hl1 : PowerSeries.constantCoeff (PowerSeries.derivative K l) = 1) (ψ : PowerSeries K)
    (α β : K) :
    MvPowerSeries.constantCoeff (MvPowerSeries.pderiv K 0 (MvPowerSeries.pderiv K 1 (Q l ψ α β))) =
      α * β * PowerSeries.constantCoeff (PowerSeries.derivative K (PowerSeries.derivative K ψ)) := by
  have hX : ∀ j : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) = 0 :=
    fun j => MvPowerSeries.constantCoeff_X j
  have hdv : ∀ (i j : Fin 2) (g : PowerSeries K),
      MvPowerSeries.pderiv K i (PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) g) =
        PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) (PowerSeries.derivative K g) *
          (Pi.single i (1 : MvPowerSeries (Fin 2) K) : Fin 2 → MvPowerSeries (Fin 2) K) j := by
    intro i j g
    rw [IntegralMvPolynomialLemmas.pderiv_subst g (hX j) i, MvPowerSeries.pderiv_X]
  have hv : ∀ j : Fin 2,
      MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) l) = 0 :=
    fun j => cc_subst_zero (hX j) hl0
  unfold Q
  have hu : MvPowerSeries.constantCoeff (MvPowerSeries.C α * PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) l +
      MvPowerSeries.C β * PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) l : MvPowerSeries (Fin 2) K) = 0 := by
    rw [map_add, map_mul, map_mul, hv 0, hv 1]
    simp
  generalize hU : (MvPowerSeries.C α * PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) l +
      MvPowerSeries.C β * PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) l : MvPowerSeries (Fin 2) K) = u at hu ⊢
  have hd1 : MvPowerSeries.pderiv K 1 u =
      MvPowerSeries.C β * PowerSeries.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K)
        (PowerSeries.derivative K l) := by
    rw [← hU, map_add, Derivation.leibniz, Derivation.leibniz, MvPowerSeries.pderiv_C,
      MvPowerSeries.pderiv_C, hdv, hdv]
    simp
  have hd0 : MvPowerSeries.pderiv K 0 u =
      MvPowerSeries.C α * PowerSeries.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K)
        (PowerSeries.derivative K l) := by
    rw [← hU, map_add, Derivation.leibniz, Derivation.leibniz, MvPowerSeries.pderiv_C,
      MvPowerSeries.pderiv_C, hdv, hdv]
    simp
  have hd01 : MvPowerSeries.pderiv K 0 (MvPowerSeries.pderiv K 1 u) = 0 := by
    rw [hd1, Derivation.leibniz, MvPowerSeries.pderiv_C, hdv]
    simp
  rw [IntegralMvPolynomialLemmas.pderiv_subst ψ hu 1, Derivation.leibniz, hd01, IntegralMvPolynomialLemmas.pderiv_subst _ hu 0, hd0, hd1]
  simp only [smul_zero, smul_eq_mul, mul_zero, zero_add, map_mul]
  rw [cc_subst hu, MvPowerSeries.constantCoeff_C, MvPowerSeries.constantCoeff_C, cc_subst (hX 0),
    cc_subst (hX 1), hl1]
  ring

theorem addDefect_eq {l linv : PowerSeries K} (h : IsLogPair l linv) (ph : PowerSeries K) (a b : K) :
    be0 l linv ph (fmul l linv a (MvPowerSeries.X (0 : Fin 2)))
        (fmul l linv b (MvPowerSeries.X (1 : Fin 2))) =
      Q l (PowerSeries.subst linv ph) a b - Q l (PowerSeries.subst linv ph) a 0 -
        Q l (PowerSeries.subst linv ph) 0 b := by
  have hX : ∀ j : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) = 0 :=
    fun j => MvPowerSeries.constantCoeff_X j
  have hv : ∀ (j : Fin 2) (c : K), MvPowerSeries.constantCoeff
      (MvPowerSeries.C c * PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) l) = 0 := by
    intro j c
    rw [map_mul, cc_subst_zero (hX j) h.1, mul_zero]
  have hsum : MvPowerSeries.constantCoeff
      (MvPowerSeries.C a * PowerSeries.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) l +
        MvPowerSeries.C b * PowerSeries.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) l) = 0 := by
    rw [map_add, hv, hv, add_zero]
  unfold be0 fadd fmul Q
  rw [subst_subst_linv h (hv 0 a), subst_subst_linv h (hv 1 b), subst_ph_linv h ph hsum,
    subst_ph_linv h ph (hv 0 a), subst_ph_linv h ph (hv 1 b)]
  simp only [map_zero, zero_mul, add_zero, zero_add]

theorem fmul_one {l linv : PowerSeries K} (h : IsLogPair l linv) {w : MvPowerSeries σ K}
    (hw : MvPowerSeries.constantCoeff w = 0) : fmul l linv 1 w = w := by
  unfold fmul
  rw [map_one, one_mul, subst_subst_l h hw]

end Adj

end JetSubstitutionLemmas

theorem jetAdjoint' : JetAdj := by
  intro K _ _ R l linv ph a b h hph hA
  have hX : ∀ j : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) = 0 :=
    fun j => MvPowerSeries.constantCoeff_X j
  have hXpt : ∀ j : Fin 2, IsPt R (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) := by
    intro j
    refine ⟨hX j, fun n => ?_⟩
    rw [MvPowerSeries.coeff_X]
    split_ifs
    · exact one_mem R
    · exact zero_mem R
  have hC := hA (Fin 2) (MvPowerSeries.X 0) (MvPowerSeries.X 1) (hXpt 0) (hXpt 1)
  have hI := IntegralMvPolynomialLemmas.intMv_pderiv (expIntegralDeriv' K R (Fin 2) _ hC 1) 0 0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at hI
  have e1 := addDefect_eq h ph a 1
  rw [fmul_one h (hX 1)] at e1
  have e2 := addDefect_eq h ph 1 b
  rw [fmul_one h (hX 0)] at e2
  have hl1 := cc_derivative_log h
  rw [e1, e2] at hI
  simp only [map_sub, cc_pderiv_Q h.1 hl1] at hI
  have hj : jet l ph 2 = PowerSeries.constantCoeff
      (PowerSeries.derivative K (PowerSeries.derivative K (PowerSeries.subst linv ph))) := by
    rw [jet_eq_cc h]
    rfl
  rw [hj]
  convert hI using 1
  ring

namespace JetSubstitutionLemmas

section Hurwitz

variable {K : Type} [Field K] {R : Subring K}

theorem hurwitz_mul {A B : PowerSeries K} (n : ℕ)
    (hA : ∀ j ≤ n, (j.factorial : K) * PowerSeries.coeff j A ∈ R)
    (hB : ∀ k ≤ n, (k.factorial : K) * PowerSeries.coeff k B ∈ R) :
    (n.factorial : K) * PowerSeries.coeff n (A * B) ∈ R := by
  rw [PowerSeries.coeff_mul, Finset.mul_sum]
  refine sum_mem fun p hp => ?_
  have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have e : (n.factorial : K) * (PowerSeries.coeff p.1 A * PowerSeries.coeff p.2 B) =
      ((n.choose p.1 : ℕ) : K) * ((p.1.factorial : K) * PowerSeries.coeff p.1 A) *
        ((p.2.factorial : K) * PowerSeries.coeff p.2 B) := by
    rw [← hp', ← Nat.add_choose_mul_factorial_mul_factorial p.1 p.2]
    push_cast
    rw [Nat.choose_symm_add]
    ring
  rw [e]
  exact mul_mem (mul_mem (natCast_mem R _) (hA _ (by omega))) (hB _ (by omega))

theorem factorial_succ_coeff (g : PowerSeries K) (n : ℕ) :
    ((n + 1).factorial : K) * PowerSeries.coeff (n + 1) g =
      (n.factorial : K) * PowerSeries.coeff n (PowerSeries.derivative K g) := by
  rw [PowerSeries.coeff_derivative, Nat.factorial_succ]
  push_cast
  ring

variable [CharZero K]

theorem hurwitz_exp {F : PowerSeries K} (hF0 : PowerSeries.constantCoeff F = 0)
    (hF : ∀ i : ℕ, 1 ≤ i → (i.factorial : K) * PowerSeries.coeff i F ∈ R) (n : ℕ) :
    (n.factorial : K) * PowerSeries.coeff n (mvExp F : PowerSeries K) ∈ R := by
  have hE' := derivative_mvExp (K := K) hF0
  have hE0 : PowerSeries.constantCoeff (mvExp F : PowerSeries K) = 1 := IntegralMvPolynomialLemmas.constantCoeff_mvExp hF0
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hE0, one_mem]
    | succ n =>
      rw [factorial_succ_coeff, hE']
      refine hurwitz_mul n (fun j hj => ?_) (fun k hk => ih k (by omega))
      rw [← factorial_succ_coeff]
      exact hF (j + 1) (by omega)

theorem jet_exp {l linv F : PowerSeries K} (h : IsLogPair l linv)
    (hF0 : PowerSeries.constantCoeff F = 0) (hF : ∀ i : ℕ, 1 ≤ i → jet l F i ∈ R) (i : ℕ) :
    jet l (mvExp F : PowerSeries K) i ∈ R := by
  have hi := hs1 h.2.2.1
  have hF0' : PowerSeries.constantCoeff (PowerSeries.subst linv F : PowerSeries K) = 0 := by
    rw [cc_subst1 h.2.2.1]
    exact hF0
  have e : PowerSeries.subst linv (mvExp F : PowerSeries K) =
      (mvExp (PowerSeries.subst linv F : PowerSeries K) : PowerSeries K) := by
    unfold mvExp
    exact PowerSeries.subst_comp_subst_apply (hs1 hF0) hi _
  rw [jet_eq h, e]
  exact hurwitz_exp hF0' (fun j hj => by rw [← jet_eq h]; exact hF j hj) i

theorem jet_neg {l linv : PowerSeries K} (h : IsLogPair l linv) (f : PowerSeries K) (i : ℕ) :
    jet l (-f) i = -jet l f i := by
  have hi := hs1 h.2.2.1
  rw [jet_eq h, jet_eq h, ← PowerSeries.coe_substAlgHom hi, map_neg, map_neg]
  ring

theorem jet_sq {l linv : PowerSeries K} (h : IsLogPair l linv) (c : K) (i : ℕ) :
    jet l (PowerSeries.C c * l ^ 2) i = if i = 2 then 2 * c else 0 := by
  have hi := hs1 h.2.2.1
  rw [jet_eq h]
  have e : PowerSeries.subst linv (PowerSeries.C c * l ^ 2) = PowerSeries.C c * PowerSeries.X ^ 2 := by
    rw [← PowerSeries.smul_eq_C_mul, PowerSeries.subst_smul hi, ← PowerSeries.coe_substAlgHom hi, map_pow,
      PowerSeries.coe_substAlgHom hi, h.2.2.2.2, PowerSeries.smul_eq_C_mul]
  rw [e, PowerSeries.coeff_C_mul_X_pow]
  split_ifs with h2
  · subst h2
    norm_num [Nat.factorial]
  · simp

end Hurwitz

end JetSubstitutionLemmas

theorem jetExp' : JetExp := by
  intro K _ _ R l linv ph h hph hj i
  exact jet_exp h (by rw [map_neg, hph, neg_zero])
    (fun i hi => by rw [jet_neg h]; exact neg_mem (hj i hi)) i

theorem jetExpShape' : JetExpShape := by
  intro K _ _ R l linv ph h hph hj
  have hq0 : PowerSeries.constantCoeff (PowerSeries.C (jet l ph 2 / 2) * l ^ 2) = 0 := by simp [h.1]
  have h0 : PowerSeries.constantCoeff (ph - PowerSeries.C (jet l ph 2 / 2) * l ^ 2) = 0 := by
    rw [map_sub, hph, hq0, sub_zero]
  refine ⟨mvExp (-(ph - PowerSeries.C (jet l ph 2 / 2) * l ^ 2)), fun i => ?_, ?_⟩
  · refine jet_exp h (by rw [map_neg, h0, neg_zero]) (fun j hj1 => ?_) i
    rw [jet_neg h, jet_sub h, jet_sq h]
    by_cases h2 : j = 2
    · subst h2
      have e : (2 : K) * (jet l ph 2 / 2) = jet l ph 2 := by
        field_simp
      rw [if_pos rfl, e, sub_self, neg_zero]
      exact zero_mem R
    · rw [if_neg h2, sub_zero]
      exact neg_mem (hj j hj1 h2)
  · have e : -ph = -(PowerSeries.C (jet l ph 2 / 2) * l ^ 2) + -(ph - PowerSeries.C (jet l ph 2 / 2) * l ^ 2) := by
      ring
    have hadd := (formalExpLaws' K Unit).2.2.1 (-(PowerSeries.C (jet l ph 2 / 2) * l ^ 2))
      (-(ph - PowerSeries.C (jet l ph 2 / 2) * l ^ 2)) (by rw [map_neg, neg_eq_zero]; exact hq0)
      (by rw [map_neg, neg_eq_zero]; exact h0)
    exact (congrArg mvExp e).trans hadd

end Formalism.L2.Th1.C
