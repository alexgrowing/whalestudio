import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSelfStar

noncomputable section

namespace PIW.AdelClassFin

open MeasureTheory Matrix Module
open scoped MatrixOrder

theorem hmk_factor {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef) :
    ∃ B : Matrix (Fin N) (Fin N) ℝ, G = Bᵀ * B := by
  refine ⟨CFC.sqrt G, ?_⟩
  have h0 : (0 : Matrix (Fin N) (Fin N) ℝ) ≤ G := hG.posSemidef.nonneg
  have hsa : IsSelfAdjoint (CFC.sqrt G) := (CFC.sqrt_nonneg G).isSelfAdjoint
  have ht : (CFC.sqrt G)ᵀ = CFC.sqrt G := by
    have := hsa.star_eq
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  rw [ht, CFC.sqrt_mul_sqrt_self G h0]

theorem hmk_int {N : ℕ} (x : Fin N → ℝ)
    (hx : x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin N)))) :
    ∃ c : Fin N → ℤ, (fun i => (c i : ℝ)) = x := by
  rw [(Pi.basisFun ℝ (Fin N)).mem_span_iff_repr_mem (R := ℤ) x] at hx
  choose c hc using hx
  refine ⟨c, funext fun i => ?_⟩
  have := hc i
  simp only [Pi.basisFun_repr, algebraMap_int_eq, Int.coe_castRingHom] at this
  exact this

theorem hmk_box {N : ℕ} (hN : 1 ≤ N) (B : Matrix (Fin N) (Fin N) ℝ) (hB : B.det ≠ 0) :
    ∃ c : Fin N → ℤ, c ≠ 0 ∧
      ∀ i, |(B *ᵥ fun j => (c j : ℝ)) i| ≤ 2 * |B.det| ^ ((1 : ℝ) / N) := by
  set d := |B.det| with hd
  have hd0 : 0 < d := abs_pos.mpr hB
  set t := 2 * d ^ ((1 : ℝ) / N) with ht
  have ht0 : 0 < t := by positivity
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (0:ℝ) < N := by exact_mod_cast hN
    exact this.ne'
  have htN : t ^ N = 2 ^ N * d := by
    rw [ht, mul_pow, ← Real.rpow_natCast (d ^ _), ← Real.rpow_mul hd0.le]
    rw [one_div_mul_cancel hN0, Real.rpow_one]
  let f : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) := Matrix.toLin' B
  have hf : LinearMap.det f ≠ 0 := by rw [LinearMap.det_toLin']; exact hB
  let box : Set (Fin N → ℝ) := Set.pi Set.univ fun _ => Set.Icc (-t) t
  let s : Set (Fin N → ℝ) := f ⁻¹' box
  let b := Pi.basisFun ℝ (Fin N)
  have fund := ZSpan.isAddFundamentalDomain' b (volume : Measure (Fin N → ℝ))
  have hvolF : volume (ZSpan.fundamentalDomain b) = 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, volume_pi, Measure.pi_pi]
    simp
  have hvolbox : volume box = ENNReal.ofReal (2 * t) ^ N := by
    simp only [box]
    rw [volume_pi, Measure.pi_pi]
    simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 2
    ring
  have hvols : volume s = ENNReal.ofReal (4 ^ N) := by
    simp only [s]
    rw [MeasureTheory.Measure.addHaar_preimage_linearMap _ hf, hvolbox,
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    rw [LinearMap.det_toLin', abs_inv, ← hd, mul_pow, htN]
    rw [show (4 : ℝ) ^ N = 2 ^ N * 2 ^ N by rw [← mul_pow]; norm_num]
    field_simp
  have h_symm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    simp only [s, box, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc,
      map_neg, Pi.neg_apply] at hx ⊢
    intro i
    obtain ⟨h1, h2⟩ := hx i
    constructor <;> linarith
  have h_conv : Convex ℝ s :=
    (convex_pi fun i _ => convex_Icc (-t) t).linear_preimage f
  have h : volume (ZSpan.fundamentalDomain b) * 2 ^ finrank ℝ (Fin N → ℝ) < volume s := by
    rw [hvolF, one_mul, hvols, Module.finrank_fin_fun]
    rw [show (2 : ENNReal) ^ N = ENNReal.ofReal (2 ^ N) by
      rw [ENNReal.ofReal_pow (by norm_num)]; simp]
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    exact pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  haveI : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  obtain ⟨x, hx0, hxs⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure fund h_symm h_conv h
  obtain ⟨c, hc⟩ := hmk_int (x : Fin N → ℝ) x.2
  refine ⟨c, ?_, ?_⟩
  · rintro rfl
    apply hx0
    ext i
    have := congrFun hc i
    simp at this
    simp [← this]
  · intro i
    have := hxs
    simp only [s, box, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Icc] at this
    rw [hc]
    exact abs_le.mpr (this i)

theorem partMink : PartMink := by
  intro N hN
  refine ⟨4 * N, fun G hG => ?_⟩
  obtain ⟨B, rfl⟩ := hmk_factor G hG
  have hdet : (Bᵀ * B).det = B.det ^ 2 := by rw [det_mul, det_transpose, sq]
  have hpos := hG.det_pos
  have hB : B.det ≠ 0 := by
    intro h0; rw [hdet, h0] at hpos; simp at hpos
  obtain ⟨c, hc0, hc⟩ := hmk_box hN B hB
  refine ⟨c, hc0, ?_⟩
  set v : Fin N → ℝ := fun i => (c i : ℝ)
  set d := |B.det|
  have hd0 : 0 < d := abs_pos.mpr hB
  have hq : v ⬝ᵥ ((Bᵀ * B) *ᵥ v) = ∑ i, (B *ᵥ v) i ^ 2 := by
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    simp [dotProduct, sq]
  have hdetG : (Bᵀ * B).det = d ^ 2 := by rw [hdet, sq_abs]
  have hpow : (d ^ ((1 : ℝ) / N)) ^ 2 = (d ^ 2) ^ ((1 : ℝ) / N) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast d, ← Real.rpow_mul hd0.le, ← Real.rpow_mul hd0.le,
      mul_comm]
  rw [hq, hdetG, ← hpow]
  calc ∑ i, (B *ᵥ v) i ^ 2 ≤ ∑ _i : Fin N, (2 * d ^ ((1 : ℝ) / N)) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact sq_le_sq' (abs_le.mp (hc i)).1 (abs_le.mp (hc i)).2
    _ = 4 * N * (d ^ ((1 : ℝ) / N)) ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ]; ring

end PIW.AdelClassFin
