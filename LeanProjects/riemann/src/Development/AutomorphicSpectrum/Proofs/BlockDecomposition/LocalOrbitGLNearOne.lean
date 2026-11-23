import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClopenCoset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZpowMulVec
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZCore

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ}

theorem latZ_subset_of_mem_nhds (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) {A : Set (Fin d → k)} (hA : A ∈ 𝓝 (0 : Fin d → k)) :
    ∃ r : ℕ, ∀ y, y ∈ (latZ z (r : ℤ)).sub → y ∈ A := by
  have hall : ∀ᶠ t : k in 𝓝 0, ∀ w ∈ ((lat0 : COSub k d).sub : Set (Fin d → k)), t • w ∈ A := by
    refine (lat0 : COSub k d).isCompact.eventually_forall_of_forall_eventually fun w _ => ?_
    have hc : Continuous fun p : k × (Fin d → k) => p.1 • p.2 := continuous_fst.smul continuous_snd
    have h0 : A ∈ 𝓝 (((0 : k), w).1 • ((0 : k), w).2) := by simpa using hA
    exact hc.continuousAt.eventually h0
  have ht : Filter.Tendsto (fun n : ℕ => ϖ ^ n) Filter.atTop (𝓝 0) := by
    rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
    intro γ hγ
    have : MulArchimedean (ValuativeRel.ValueGroupWithZero k) :=
      ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ (Units.mk0 γ hγ)
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    rw [map_pow]
    exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hϖ.le hm) hn
  obtain ⟨r, hr⟩ := (ht.eventually hall).exists
  refine ⟨r, fun y hy => ?_⟩
  have h1 : ϖ ^ r • ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y) ∈ A := hr _ hy
  have h2 : ϖ ^ r • ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y) = y := by
    have := zpow_mulVec z ϖ hz hϖ0 (r : ℤ) ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y)
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, zpow_natCast] at this
    exact this.symm
  rwa [h2] at h1

theorem vecMulVec_single_mul_self (i : Fin d) (u : Fin d → k) :
    vecMulVec u (Pi.single i (1 : k)) * vecMulVec u (Pi.single i (1 : k)) =
      u i • vecMulVec u (Pi.single i (1 : k)) := by
  ext a b
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, Pi.single_apply]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul]
  simp
  split_ifs <;> simp [mul_comm]

theorem exists_mem_nhds_one_mulVec_eq (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (U : Set (GL (Fin d) k))
    (hU : U ∈ 𝓝 (1 : GL (Fin d) k)) (x : Fin d → k) (hx : x ≠ 0) :
    ∃ s : ℕ, ∀ y : Fin d → k, y - x ∈ (latZ z (s : ℤ)).sub →
      ∃ g ∈ U, (g : Matrix (Fin d) (Fin d) k).mulVec x = y := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  let P : (Fin d → k) → Matrix (Fin d) (Fin d) k := fun y => vecMulVec (y - x) (Pi.single i (1 : k))
  let M : (Fin d → k) → Matrix (Fin d) (Fin d) k := fun y => 1 + (x i)⁻¹ • P y
  let N : (Fin d → k) → Matrix (Fin d) (Fin d) k := fun y => 1 - (y i)⁻¹ • P y
  have hPc : Continuous P := (continuous_id.sub continuous_const).matrix_vecMulVec continuous_const
  have hPx : P x = 0 := by
    ext a b
    simp [P, vecMulVec_apply]
  have hMc : ContinuousAt M x := by
    have h : Continuous fun y => (1 : Matrix (Fin d) (Fin d) k) + (x i)⁻¹ • P y := by fun_prop
    exact h.continuousAt
  have hNc : ContinuousAt N x := by
    have h1 : ContinuousAt (fun y : Fin d → k => (y i)⁻¹) x := (continuous_apply i).continuousAt.inv₀ hi
    have h2 : ContinuousAt (fun y => (y i)⁻¹ • P y) x := h1.fun_smul hPc.continuousAt
    have h3 : ContinuousAt (fun y => (1 : Matrix (Fin d) (Fin d) k) - (y i)⁻¹ • P y) x := continuousAt_const.fun_sub h2
    exact h3
  have hMx : M x = 1 := by simp [M, hPx]
  have hNx : N x = 1 := by simp [N, hPx]
  have hMN : ∀ y, y i ≠ 0 → M y * N y = 1 := by
    intro y hy
    have hsq : P y * P y = (y i - x i) • P y := by
      simpa [P] using vecMulVec_single_mul_self i (y - x)
    simp only [M, N, mul_sub, add_mul, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, hsq, smul_smul]
    have h3 : (y i)⁻¹ + ((y i)⁻¹ * ((x i)⁻¹ * y i) - (y i)⁻¹ * ((x i)⁻¹ * x i)) = (x i)⁻¹ := by
      field_simp
      ring
    rw [← add_smul, h3, add_sub_cancel_right]
  have hNM : ∀ y, y i ≠ 0 → N y * M y = 1 := fun y hy => mul_eq_one_comm.1 (hMN y hy)
  have hMv : ∀ y, (M y).mulVec x = y := by
    intro y
    have h1 : (P y).mulVec x = x i • (y - x) := by
      ext a
      simp [P, vecMulVec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
    simp only [M, Matrix.add_mulVec, one_mulVec, Matrix.smul_mulVec, h1, smul_smul, inv_mul_cancel₀ hi, one_smul]
    abel
  have hT : Filter.Tendsto (fun y => (M y, MulOpposite.op (N y))) (𝓝 x)
      (𝓝 (Units.embedProduct (Matrix (Fin d) (Fin d) k) 1)) := by
    have e : Units.embedProduct (Matrix (Fin d) (Fin d) k) 1 = (M x, MulOpposite.op (N x)) := by
      rw [hMx, hNx, map_one]
      rfl
    rw [e]
    exact hMc.tendsto.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hNc.tendsto)
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨W, hW, hWU⟩ := hU
  have hgood : ∀ᶠ y in 𝓝 x, y i ≠ 0 ∧ (M y, MulOpposite.op (N y)) ∈ W :=
    ((continuous_apply i).continuousAt.eventually_ne hi).and (hT.eventually hW)
  have hA : {l : Fin d → k | (x + l) i ≠ 0 ∧ (M (x + l), MulOpposite.op (N (x + l))) ∈ W} ∈ 𝓝 (0 : Fin d → k) := by
    have hc : Filter.Tendsto (fun l : Fin d → k => x + l) (𝓝 0) (𝓝 x) := by
      have h : Continuous fun l : Fin d → k => x + l := by fun_prop
      simpa using h.tendsto 0
    exact hc.eventually hgood
  obtain ⟨s, hs⟩ := latZ_subset_of_mem_nhds z ϖ hz hϖ hϖ0 hA
  refine ⟨s, fun y hy => ?_⟩
  have hy' := hs _ hy
  rw [Set.mem_setOf_eq, add_sub_cancel] at hy'
  refine ⟨⟨M y, N y, hMN y hy'.1, hNM y hy'.1⟩, hWU ?_, hMv y⟩
  exact hy'.2

end GlobalTheory.CompanionTheory.BZCore

end
