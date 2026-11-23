import Mathlib
import Formalism.SatakeDualWeyl.StatementF
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AevalRootEqZeroIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOneAddPiOMul
import GroundTheory.LocalFields.FilteredSurj
open Polynomial Matrix Formalism.UG

noncomputable section

open Filter Topology

namespace GlobalTheory.NormEq.Cmpl

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem exists_pow_lt {w γ : WithZero (Multiplicative ℤ)}
    (hw : w = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) (hγ : γ ≠ 0) :
    ∃ N : ℕ, w ^ N < γ := by
  subst hw
  obtain ⟨g, rfl⟩ := WithZero.ne_zero_iff_exists.mp hγ
  refine ⟨(-Multiplicative.toAdd g).toNat + 1, ?_⟩
  rw [← WithZero.coe_pow, WithZero.coe_lt_coe, ← ofAdd_toAdd g, ← ofAdd_nsmul, Multiplicative.ofAdd_lt]
  simp only [toAdd_ofAdd, smul_neg, nsmul_eq_mul, mul_one]
  omega

theorem ball_mem_nhds_of_ne {x c : L} (hc : c ≠ 0) : {y | Valued.v (y - x) < Valued.v c} ∈ 𝓝 x := by
  rw [Valued.mem_nhds]
  have h' : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).restrict c ≠ 0 := by simp [hc]
  exact ⟨Units.mk0 _ h', fun y hy => (Valuation.restrict_lt_iff _).1 hy⟩

theorem exists_lim_of_cauchy [CompleteSpace L] {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (s : ℕ → L) (hsO : ∀ n, Valued.v (s n) ≤ 1)
    (hs : ∀ N : ℕ, ∃ M, ∀ m ≥ M, ∀ n ≥ M, Valued.v (s n - s m) ≤ Valued.v ϖ ^ N) :
    ∃ ℓ, Valued.v ℓ ≤ 1 ∧ ∀ N : ℕ, ∀ᶠ n in atTop, Valued.v (s n - ℓ) ≤ Valued.v ϖ ^ N := by
  have hϖ0 : ϖ ≠ 0 := fun h0 => by rw [h0, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  have hcs : CauchySeq s := by
    rw [(Valued.hasBasis_uniformity L (WithZero (Multiplicative ℤ))).cauchySeq_iff]
    intro γ _
    obtain ⟨c, hc⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
      (.ofClass (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))) γ.1
    have hc' : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).restrict c = γ.1 := hc
    have hc0 : Valued.v c ≠ 0 := by
      intro h0
      rw [(Valued.v).zero_iff.mp h0, map_zero] at hc'
      exact γ.ne_zero hc'.symm
    obtain ⟨N, hN⟩ := exists_pow_lt hϖ hc0
    obtain ⟨M, hM⟩ := hs N
    refine ⟨M, fun m hm n hn => ?_⟩
    change (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).restrict (s n - s m) < γ.1
    rw [← hc', Valuation.restrict_lt_iff]
    exact lt_of_le_of_lt (hM m hm n hn) hN
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hcs
  have hev : ∀ N : ℕ, ∀ᶠ n in atTop, Valued.v (s n - ℓ) < Valued.v ϖ ^ N := fun N => by
    have := hℓ (ball_mem_nhds_of_ne (x := ℓ) (pow_ne_zero N hϖ0))
    simpa [map_pow] using this
  refine ⟨ℓ, ?_, fun N => (hev N).mono fun n hn => hn.le⟩
  obtain ⟨n, hn⟩ := (hev 0).exists
  rw [pow_zero] at hn
  have e : ℓ = s n - (s n - ℓ) := by ring
  rw [e]
  exact (Valued.v.map_sub _ _).trans (max_le (hsO n) hn.le)

variable {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (sigO σ h.2.1))

theorem mem_piPow_iff {N : ℕ} {a : GlobalTheory.UTr.Alg P} :
    a ∈ piPow h P N ↔ ∀ i, Valued.v (((GlobalTheory.UTr.powBasis P).repr a i : intL L) : L) ≤ Valued.v ϖ ^ N := by
  have hϖ0 : ϖ ≠ 0 := fun h0 => by
    have := h.2.2.2.1; rw [h0, map_zero] at this; exact WithZero.zero_ne_coe this
  constructor
  · intro ha i
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [← map_pow, mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, Subring.coe_mul,
      SubmonoidClass.coe_pow, coe_piO, map_mul, map_pow]
    calc _ ≤ Valued.v ϖ ^ N * 1 := mul_le_mul' le_rfl (((GlobalTheory.UTr.powBasis P).repr c i).2)
      _ = _ := mul_one _
  · intro ha
    have hϖN : ϖ ^ N ≠ 0 := pow_ne_zero _ hϖ0
    let d : Fin P.1.natDegree → intL L := fun i => ⟨((GlobalTheory.UTr.powBasis P).repr a i : L) / ϖ ^ N, by
      change Valued.v (((GlobalTheory.UTr.powBasis P).repr a i : L) / ϖ ^ N) ≤ 1
      rw [map_div₀, map_pow]
      exact (div_le_one₀ (zero_lt_iff.mpr (pow_ne_zero _ ((Valued.v).ne_zero_iff.mpr hϖ0)))).mpr (ha i)⟩
    refine Ideal.mem_span_singleton'.mpr ⟨(GlobalTheory.UTr.powBasis P).equivFun.symm d, ?_⟩
    refine (GlobalTheory.UTr.powBasis P).ext_elem fun i => ?_
    have hd : (GlobalTheory.UTr.powBasis P).repr ((GlobalTheory.UTr.powBasis P).equivFun.symm d) i = d i := by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [← map_pow, mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, hd]
    apply Subtype.ext
    rw [Subring.coe_mul, SubmonoidClass.coe_pow, coe_piO]
    exact mul_div_cancel₀ _ hϖN

theorem eq_zero_of_forall_mem_piPow {z : GlobalTheory.UTr.Alg P} (hz : ∀ N, z ∈ piPow h P N) : z = 0 := by
  refine (GlobalTheory.UTr.powBasis P).ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  by_contra hne
  have hne' : (((GlobalTheory.UTr.powBasis P).repr z i : intL L) : L) ≠ 0 := fun h0 => hne (Subtype.ext h0)
  obtain ⟨N, hN⟩ := exists_pow_lt h.2.2.2.1 ((Valued.v).ne_zero_iff.mpr hne')
  exact absurd ((mem_piPow_iff h P).mp (hz N) i) (not_le.mpr hN)

theorem exists_lim_alg [CompleteSpace L] (a : ℕ → GlobalTheory.UTr.Alg P)
    (ha : ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, a n - a m ∈ piPow h P N) :
    ∃ y, ∀ N, ∀ᶠ n in atTop, a n - y ∈ piPow h P N := by
  have hco : ∀ i, ∃ ℓ : L, Valued.v ℓ ≤ 1 ∧ ∀ N : ℕ, ∀ᶠ n in atTop,
      Valued.v ((((GlobalTheory.UTr.powBasis P).repr (a n) i : intL L) : L) - ℓ) ≤ Valued.v ϖ ^ N := by
    intro i
    refine exists_lim_of_cauchy h.2.2.2.1 _ (fun n => ((GlobalTheory.UTr.powBasis P).repr (a n) i).2) fun N => ?_
    obtain ⟨M, hM⟩ := ha N
    refine ⟨M, fun m hm n hn => ?_⟩
    have := (mem_piPow_iff h P).mp (hM m hm n hn) i
    rwa [map_sub, Finsupp.sub_apply, AddSubgroupClass.coe_sub] at this
  choose ℓ hℓO hℓ using hco
  refine ⟨(GlobalTheory.UTr.powBasis P).equivFun.symm (fun i => ⟨ℓ i, hℓO i⟩), fun N => ?_⟩
  filter_upwards [Filter.eventually_all.mpr (fun i => hℓ i N)] with n hn
  rw [mem_piPow_iff]
  intro i
  have hd : (GlobalTheory.UTr.powBasis P).repr ((GlobalTheory.UTr.powBasis P).equivFun.symm (fun i => ⟨ℓ i, hℓO i⟩)) i =
      ⟨ℓ i, hℓO i⟩ := by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [map_sub, Finsupp.sub_apply, hd, AddSubgroupClass.coe_sub]
  exact hn i

end GlobalTheory.NormEq.Cmpl

namespace GlobalTheory.NormEq

open Cmpl in

theorem filtrationComplete_filt : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)),
    GroundTheory.LocalField.FiltrationComplete (GlobalTheory.NormEq.filt h P) := by
  intro L _ _ _ σ ϖ q h P x hx
  have ha : ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, ((x n : GlobalTheory.UTr.Alg P) - x m) ∈ piPow h P N := by
    intro N
    obtain ⟨M, hM⟩ := hx N
    refine ⟨M, fun m hm n hn => ?_⟩
    have h1 : ((x n / x m : (GlobalTheory.UTr.Alg P)ˣ) : GlobalTheory.UTr.Alg P) - 1 ∈ piPow h P N := hM m hm n hn
    have e : (x n : GlobalTheory.UTr.Alg P) - x m = (x m : GlobalTheory.UTr.Alg P) * (((x n / x m : (GlobalTheory.UTr.Alg P)ˣ) : GlobalTheory.UTr.Alg P) - 1) := by
      rw [div_eq_mul_inv, Units.val_mul]
      linear_combination (-(x n : GlobalTheory.UTr.Alg P)) * (x m).mul_inv
    rw [e]; exact Ideal.mul_mem_left _ _ h1
  have hb : ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M,
      (((x n)⁻¹ : (GlobalTheory.UTr.Alg P)ˣ) : GlobalTheory.UTr.Alg P) - ((x m)⁻¹ : (GlobalTheory.UTr.Alg P)ˣ) ∈ piPow h P N := by
    intro N
    obtain ⟨M, hM⟩ := hx N
    refine ⟨M, fun m hm n hn => ?_⟩
    have h1 : ((x n / x m : (GlobalTheory.UTr.Alg P)ˣ) : GlobalTheory.UTr.Alg P) - 1 ∈ piPow h P N := hM m hm n hn
    have e : (((x n)⁻¹ : (GlobalTheory.UTr.Alg P)ˣ) : GlobalTheory.UTr.Alg P) - ((x m)⁻¹ : (GlobalTheory.UTr.Alg P)ˣ) =
        -(((x n)⁻¹ : (GlobalTheory.UTr.Alg P)ˣ) : GlobalTheory.UTr.Alg P) * (((x n / x m : (GlobalTheory.UTr.Alg P)ˣ) : GlobalTheory.UTr.Alg P) - 1) := by
      rw [div_eq_mul_inv, Units.val_mul]
      linear_combination (((x m)⁻¹ : (GlobalTheory.UTr.Alg P)ˣ) : GlobalTheory.UTr.Alg P) * (x n).inv_mul
    rw [e]; exact Ideal.mul_mem_left _ _ h1
  obtain ⟨y, hy⟩ := exists_lim_alg h P _ ha
  obtain ⟨y', hy'⟩ := exists_lim_alg h P _ hb
  have hyy : y * y' = 1 := by
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_mem_piPow h P fun N => ?_
    obtain ⟨n, hn1, hn2⟩ := ((hy N).and (hy' N)).exists
    have e : y * y' - 1 = -((x n : GlobalTheory.UTr.Alg P) - y) * y' -
        (x n : GlobalTheory.UTr.Alg P) * ((((x n)⁻¹ : (GlobalTheory.UTr.Alg P)ˣ) : GlobalTheory.UTr.Alg P) - y') := by
      linear_combination (x n).mul_inv
    rw [e]
    exact (piPow h P N).sub_mem ((piPow h P N).mul_mem_right _ ((piPow h P N).neg_mem hn1))
      ((piPow h P N).mul_mem_left _ hn2)
  refine ⟨⟨y, y', hyy, by rw [mul_comm]; exact hyy⟩, fun N => ?_⟩
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hy N)
  refine ⟨M, fun n hn => ?_⟩
  rw [mem_filt, div_eq_mul_inv, Units.val_mul, Units.inv_mk, Units.val_mk]
  have e : (x n : GlobalTheory.UTr.Alg P) * y' - 1 = ((x n : GlobalTheory.UTr.Alg P) - y) * y' := by
    linear_combination hyy
  rw [e]
  exact (piPow h P N).mul_mem_right _ (hM n hn)

end GlobalTheory.NormEq
