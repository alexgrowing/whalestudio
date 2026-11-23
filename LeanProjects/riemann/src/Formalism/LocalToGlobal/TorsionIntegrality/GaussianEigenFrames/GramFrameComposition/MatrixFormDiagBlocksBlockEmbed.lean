import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementB
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.NeZeroOfNorm
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.QuadraticSemicharactersOfProductThetaMem
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstUniqueOf

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom slice)
open Formalism.L2.Th1.CM (omegaK)
open Formalism.L2.Th1.D.GaussNormEstimates (normZ_le normZ_one)

namespace GramFrameLatticeLemmas

lemma sqrt_sq_c (d : ℕ) : (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) ^ 2 = -(d : ℂ) := by
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  push_cast
  ring

lemma conj_omega (d : ℕ) : conj (omegaK d) = 1 - omegaK d := by
  rw [omegaK, map_div₀, map_add, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring

def emb {n : Type} (b : Fin 4) (v : n → ℂ) : Fin 4 × n → ℂ := fun w => if w.1 = b then v w.2 else 0

lemma matH_apply' {n : Type} [Fintype n] (h : Matrix n n ℂ) (z w : n → ℂ) :
    matH h z w = ∑ i, ∑ j, z i * h i j * conj (w j) := rfl

lemma stdH_apply' (L : PeriodPair) {n : Type} [Fintype n] [DecidableEq n] (z w : n → ℂ) :
    stdH L n z w = ((Formalism.L2.Th1.F.area L : ℝ) : ℂ)⁻¹ * ∑ i, z i * conj (w i) := by
  rw [stdH, matH_apply', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp [Matrix.smul_apply, Matrix.one_apply] <;> ring
  · intro j _ hj
    simp [Matrix.smul_apply, Matrix.one_apply, Ne.symm hj]
  · simp

lemma matrixForm_diagBlocks_blockEmbed {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (a b : Fin 4) (v v' : n → ℂ) :
    matH (blk4 h) (emb a v) (emb b v') = if a = b then matH h v v' else 0 := by
  rw [matH_apply']
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, matH_apply', Fintype.sum_prod_type, Finset.sum_eq_single a]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
      · simp [emb, blk4]
      · intro c _ hc
        apply Finset.sum_eq_zero
        intro j _
        simp [emb, hc]
      · simp
    · intro c _ hc
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro w _
      simp [emb, hc]
    · simp
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro x _
    apply Finset.sum_eq_zero
    intro y _
    simp only [emb, blk4]
    split_ifs <;> simp_all

lemma smul_emb_mem {L : PeriodPair} {n : Type} {Λ : AddSubgroup (n → ℂ)} {v : n → ℂ} (hv : InMul L Λ v) (b : Fin 4)
    {ω : ℂ} (hω : ω ∈ L.lattice) : ω • emb b v ∈ pow4 Λ := by
  show ∀ a, slice a (ω • emb b v) ∈ Λ
  intro a
  by_cases hab : a = b
  · subst hab
    have h1 : slice a (ω • emb a v) = ω • v := by
      ext i
      simp [slice, emb]
    rw [h1]
    exact hv ω hω
  · have h1 : slice a (ω • emb b v) = 0 := by
      ext i
      simp [slice, emb, hab]
    rw [h1]
    exact Λ.zero_mem

lemma eq_sum_single {W : Type} [Fintype W] [DecidableEq W] (y : W → ℂ) :
    y = ∑ w, y w • (Pi.single w 1 : W → ℂ) := by
  ext x
  simp [Pi.single_apply]

end GramFrameLatticeLemmas

open GramFrameLatticeLemmas

theorem IotaOK_proof : IotaOK := by
  intro d hd p _ ι
  set s : ℂ := Complex.I * ((Real.sqrt d : ℝ) : ℂ) with hs
  have hs2 : s ^ 2 = -(d : ℂ) := sqrt_sq_c d
  have hω : omegaK d = (1 + s) / 2 := rfl
  have hns : ‖ι s‖ ^ 2 = ‖(d : ℂ_[p])‖ := by
    rw [← norm_pow, ← map_pow, hs2, map_neg, map_natCast, norm_neg]
  have hnat : ∀ k : ℕ, ‖(k : ℂ_[p])‖ ≤ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))
  have hint : ∀ k : ℤ, ‖(k : ℂ_[p])‖ ≤ 1 := by
    intro k
    obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · simpa using hnat j
    · simpa using hnat j
  have hk : (d : ℂ) + 1 = 4 * (((d + 1) / 4 : ℕ) : ℂ) := by
    have h4 : d + 1 = 4 * ((d + 1) / 4) := by omega
    exact_mod_cast h4
  have hω2 : omegaK d ^ 2 = omegaK d - (((d + 1) / 4 : ℕ) : ℂ) := by
    rw [hω]
    linear_combination (1 / 4 : ℂ) * hs2 - (1 / 4 : ℂ) * hk
  have hx2 : ι (omegaK d) ^ 2 = ι (omegaK d) - (((d + 1) / 4 : ℕ) : ℂ_[p]) := by
    rw [← map_pow, hω2, map_sub, map_natCast]
  have hx : ‖ι (omegaK d)‖ ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    have h1 : ‖ι (omegaK d)‖ ^ 2 ≤ ‖ι (omegaK d)‖ := by
      rw [← norm_pow, hx2, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le le_rfl ?_)
      rw [norm_neg]
      exact (hnat _).trans hlt.le
    nlinarith
  refine ⟨?_, ?_⟩
  · rw [← hns, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
  · intro m n
    refine ⟨?_, ?_⟩
    · rw [map_add, map_mul, map_intCast, map_intCast]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hint m) ?_)
      rw [norm_mul]
      exact mul_le_one₀ (hint n) (norm_nonneg _) hx
    · rw [← map_sub]
      have h1 : ((m : ℂ) + (n : ℂ) * omegaK d) - conj ((m : ℂ) + (n : ℂ) * omegaK d) = s * (n : ℂ) := by
        rw [map_add, map_mul, conj_omega, map_intCast, map_intCast, hω]
        ring
      rw [h1, map_mul, map_intCast]

theorem GramTransfer_of (hM : MulRing) (hI : IotaOK) : GramTransfer := by
  intro a b c d ha hd lam hlam hcm n _ _ h Λ g hiso p _ ι hp J _ v hv
  set L := cmL a b d ha hd lam hlam with hL
  set N := relIdx (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))
    with hNdef
  have hd3 : d % 4 = 3 := by
    have := hcm.2.2.1
    omega
  have hNn1 : ‖(N : ℂ_[p])‖ = 1 := Formalism.L2.Th1.E.Tor.norm_natCast p hp
  have hN0 : (N : ℂ_[p]) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hNn1
    exact zero_ne_one hNn1
  have hnat : ∀ k : ℕ, ‖(k : ℂ_[p])‖ ≤ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))
  have hint : ∀ k : ℤ, ‖(k : ℂ_[p])‖ ≤ 1 := by
    intro k
    obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · simpa using hnat j
    · simpa using hnat j
  obtain ⟨Y, hY⟩ : ∃ Y : Fin 4 × J → Fin 4 × n → ℂ, ∀ x, Y x = g (emb x.1 (v x.2)) :=
    ⟨_, fun _ => rfl⟩
  have hkey : ∀ y ∈ imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ),
      N • y ∈ stdLat L (Fin 4 × n) := by
    intro y hy
    have h1 := AddSubgroup.nsmul_index_mem
      ((stdLat L (Fin 4 × n)).addSubgroupOf
        (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))) ⟨y, hy⟩
    rw [AddSubgroup.mem_addSubgroupOf] at h1
    simpa [hNdef, relIdx, AddSubgroup.relIndex] using h1
  have hmemimg : ∀ (x : Fin 4 × J) (ω : ℂ), ω ∈ L.lattice →
      ω • Y x ∈ imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ) := by
    intro x ω hω
    refine AddSubgroup.mem_map.mpr ⟨ω • emb x.1 (v x.2), smul_emb_mem (hv x.2) x.1 hω, ?_⟩
    rw [hY]
    simp [map_smul]
  have hrep : ∀ x w, ∃ m n' : ℤ, (N : ℂ) * Y x w = m + n' * omegaK d := by
    intro x w
    apply hM a b c d ha hd lam hlam hcm
    intro ω hω
    have h1 := hkey _ (hmemimg x ω hω)
    rw [stdLat, AddSubgroup.mem_pi] at h1
    have h2 := h1 w (Set.mem_univ w)
    have h3 : (N • (ω • Y x)) w = (N : ℂ) * Y x w * ω := by
      simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
      ring
    rw [h3] at h2
    exact h2
  choose M Nn hMN using hrep
  have hI := IotaOK_proof d hd3 p ι
  have hD : ∀ w x, ‖ι (Y x w)‖ ≤ 1 := by
    intro w x
    have h1 : ι (Y x w) * (N : ℂ_[p]) = ι ((M x w : ℂ) + (Nn x w : ℂ) * omegaK d) := by
      rw [← hMN, map_mul, map_natCast, mul_comm]
    have h2 := congrArg norm h1
    rw [norm_mul, hNn1, mul_one] at h2
    rw [h2]
    exact (hI.2 (M x w) (Nn x w)).1
  have hconj : ∀ y w, ι (Y y w) = ι (conj (Y y w)) +
      ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) * (Nn y w : ℂ_[p]) / (N : ℂ_[p]) := by
    intro y w
    have h3 := (hI.2 (M y w) (Nn y w)).2
    rw [← hMN y w, map_mul ι, map_mul (starRingEnd ℂ), map_mul ι, map_natCast (starRingEnd ℂ),
      map_natCast ι] at h3
    have h4 : ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) * (Nn y w : ℂ_[p]) / (N : ℂ_[p]) =
        ι (Y y w) - ι (conj (Y y w)) := by
      rw [div_eq_iff hN0]
      linear_combination -h3
    rw [h4]
    ring
  have harea : ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Formalism.L2.Th1.F.PeriodAreaSignLemmas.area_pos L).ne'
  have hgram : ∀ x y : Fin 4 × J, ∑ w, Y x w * conj (Y y w) =
      if x.1 = y.1 then hOK L h (v x.2) (v y.2) else 0 := by
    intro x y
    have h1 := hiso (emb x.1 (v x.2)) (emb y.1 (v y.2))
    rw [stdH_apply', matrixForm_diagBlocks_blockEmbed] at h1
    simp only [LinearEquiv.coe_coe] at h1
    rw [← hY x, ← hY y] at h1
    calc ∑ w, Y x w * conj (Y y w)
        = ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) *
          (((Formalism.L2.Th1.F.area L : ℝ) : ℂ)⁻¹ * ∑ w, Y x w * conj (Y y w)) := by
          rw [← mul_assoc, mul_inv_cancel₀ harea, one_mul]
      _ = _ := by
          rw [h1]
          by_cases hxy : x.1 = y.1 <;> simp [hxy, hOK]
  have hsum : ∀ (z : Fin 4 × n → ℂ) (q : Fin 4 × n),
      ∑ w, g.symm (Pi.single w 1) q * z w = g.symm z q := by
    intro z q
    conv_rhs => rw [eq_sum_single z]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  refine ⟨fun w x => ι (Y x w),
    fun x y => ∑ w, ι (Y x w) * (Nn y w : ℂ_[p]) / (N : ℂ_[p]), ?_, ?_, ?_, ?_⟩
  · exact hD
  · intro x y
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro w _
    rw [norm_div, norm_mul, hNn1, div_one]
    exact mul_le_one₀ (hD w x) (norm_nonneg _) (hint _)
  · intro a' i b' j
    show ∑ w, ι (g.symm (Pi.single w 1) (a', i)) * ι (Y (b', j) w) = _
    simp_rw [← map_mul]
    rw [← map_sum, hsum, hY, LinearEquiv.symm_apply_apply]
    by_cases hab : a' = b' <;> simp [emb, hab]
  · intro x y
    show ∑ w, ι (Y x w) * ι (Y y w) = _
    have e1 : ∑ w, ι (Y x w) * ι (Y y w) = ∑ w, ι (Y x w * conj (Y y w)) +
        ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) * ∑ w, ι (Y x w) * (Nn y w : ℂ_[p]) / (N : ℂ_[p]) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [hconj y w, map_mul ι (Y x w)]
      ring
    rw [e1, ← map_sum, hgram x y]
    by_cases hxy : x.1 = y.1 <;> simp [hxy]

end Formalism.L2.Th1.GD
