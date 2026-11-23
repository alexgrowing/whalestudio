import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SiegelCover
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelSetEntryBoundOfLatticeMin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReducedBasisIntegralConjEntriesBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelReducedIntegralFormBoundedEntriesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspIntegralBasisCovolumeConstant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulMatTranspose
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TraceFormRealCoordinatesIntegralGramStatement

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

noncomputable section

namespace GlobalTheory.CuspGeo.RedBasisPf

variable (I : AutInst)

theorem vec_add (y : I.Ginf) (u w : Fin I.n → I.E) : vec I y (u + w) = vec I y u + vec I y w := by
  funext v
  simp only [vec, Pi.add_apply]
  rw [← Matrix.mulVec_add, ← Matrix.mulVec_add]
  congr 2
  funext i
  simp

def vecHom (y : I.Ginf) : (Fin I.n → I.E) →+ (InfinitePlace I.F → Fin I.n → ℂ) :=
  AddMonoidHom.mk' (vec I y) (vec_add I y)

theorem vec_sum_zsmul (y : I.Ginf) {N : ℕ} (z : Fin N → ℤ) (e : Fin N → Fin I.n → I.E) :
    vec I y (∑ j, z j • e j) = ∑ j, z j • vec I y (e j) := by
  exact MulCoord.vec_sum_zsmul I y e z

theorem gm_mulVec {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (y : I.Ginf)
    (e : Fin N → Fin I.n → I.E) (z : Fin N → ℤ) :
    gm I ρ y e *ᵥ (fun j => (z j : ℝ)) = ρ (vec I y (∑ j, z j • e j)) := by
  rw [vec_sum_zsmul, map_sum]
  funext i
  simp only [map_zsmul]
  simp only [gm, mulVec, dotProduct, of_apply, Finset.sum_apply, Pi.smul_apply, zsmul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem gm_change {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (y : I.Ginf)
    (e : Fin N → Fin I.n → I.E) (M : Matrix (Fin N) (Fin N) ℤ) :
    gm I ρ y (fun j => ∑ i, M i j • e i) = gm I ρ y e * M.map (Int.cast : ℤ → ℝ) := by
  ext i j
  simp only [gm, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply]
  rw [vec_sum_zsmul I y (fun k => M k j) e, map_sum]
  simp only [map_zsmul]
  simp only [Finset.sum_apply, Pi.smul_apply, zsmul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem sum_change {N : ℕ} (M : Matrix (Fin N) (Fin N) ℤ) (e : Fin N → Fin I.n → I.E) (w : Fin N → ℤ) :
    ∑ j, w j • (∑ i, M i j • e i) = ∑ i, (M *ᵥ w) i • e i := by
  simp only [Finset.smul_sum, smul_smul, mulVec, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem isZBasis_change {N : ℕ} (e : Fin N → Fin I.n → I.E) (he : IsZBasis I e)
    (M : Matrix (Fin N) (Fin N) ℤ) (hM : IsUnit M.det) : IsZBasis I (fun j => ∑ i, M i j • e i) := by
  obtain ⟨hli, hspan⟩ := he
  have hinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have hinv' : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hM
  refine ⟨?_, fun u => ?_⟩
  · rw [Fintype.linearIndependent_iff] at hli ⊢
    intro g hg i
    rw [sum_change] at hg
    have hMg : M *ᵥ g = 0 := funext (hli _ hg)
    have hg' : g = M⁻¹ *ᵥ (M *ᵥ g) := by rw [Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
    rw [hg', hMg, Matrix.mulVec_zero]
    rfl
  · rw [hspan u]
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨M⁻¹ *ᵥ z, ?_⟩
      rw [sum_change, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    · rintro ⟨w, rfl⟩
      exact ⟨M *ᵥ w, sum_change I M e w⟩

theorem norm_le_sqrt {N : ℕ} {ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)}
    (hρ : IsRealCoord I ρ) (x : InfinitePlace I.F → Fin I.n → ℂ) : ‖x‖ ≤ Real.sqrt N * ‖ρ x‖ := by
  have hre : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := by
    intro z
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hsq : ∀ v i, ‖x v i‖ ^ 2 ≤ N * ‖ρ x‖ ^ 2 := by
    intro v i
    have h1 : ‖x v i‖ ^ 2 ≤ ∑ w, ∑ k, (star (x w k) * x w k).re := by
      simp only [hre]
      calc ‖x v i‖ ^ 2 ≤ ∑ k, ‖x v k‖ ^ 2 :=
            Finset.single_le_sum (f := fun k => ‖x v k‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
        _ ≤ ∑ w, ∑ k, ‖x w k‖ ^ 2 :=
            Finset.single_le_sum (f := fun w => ∑ k, ‖x w k‖ ^ 2)
              (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ v)
    rw [← hρ x x] at h1
    refine h1.trans ?_
    unfold dotProduct
    calc ∑ k, ρ x k * ρ x k ≤ ∑ _k : Fin N, ‖ρ x‖ ^ 2 := Finset.sum_le_sum fun k _ => by
            have hk := norm_le_pi_norm (ρ x) k
            rw [Real.norm_eq_abs] at hk
            have h := mul_self_le_mul_self (abs_nonneg _) hk
            rw [abs_mul_abs_self] at h
            nlinarith [h]
      _ = N * ‖ρ x‖ ^ 2 := by simp
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun v => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have h := Real.sqrt_le_sqrt (hsq v i)
  rwa [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

def entSum {N : ℕ} (X : Matrix (Fin N) (Fin N) ℝ) : ℝ := ∑ i, ∑ j, |X i j|

theorem abs_le_entSum {N : ℕ} (X : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) : |X i j| ≤ entSum X := by
  unfold entSum
  calc |X i j| ≤ ∑ j', |X i j'| :=
        Finset.single_le_sum (f := fun j' => |X i j'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', |X i' j'| :=
        Finset.single_le_sum (f := fun i' => ∑ j', |X i' j'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

end GlobalTheory.CuspGeo.RedBasisPf

end

noncomputable section

namespace GlobalTheory.CuspGeo.RedBasisPf

theorem smul_conj {N : ℕ} (l c : ℝ) (A X : Matrix (Fin N) (Fin N) ℝ) :
    (l • A)ᵀ * (c • X) * (l • A) = (l * c * l) • (Aᵀ * X * A) := by
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  ring_nf

theorem smul_conj' {N : ℕ} (l : ℝ) (A B : Matrix (Fin N) (Fin N) ℝ) :
    (l • A) * B * (l • A)ᵀ = (l * l) • (A * B * Aᵀ) := by
  simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

end GlobalTheory.CuspGeo.RedBasisPf

open GlobalTheory.CuspGeo.RedBasisPf in

theorem GlobalTheory.CuspGeo.redBasis_holds : ∀ I : AutInst, RedBasis I := by
  intro I
  obtain ⟨N, e0, ρ, d, hd, he0, hρ, hdet⟩ := covolume_const I
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact ⟨0, 0, 0, fun y => ⟨e0, he0, ⟨fun k j => j.elim0, fun i => i.elim0⟩, fun t _ _ _ j => j.elim0⟩⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨lam, hlam0, hlamN⟩ : ∃ lam : ℝ, 0 < lam ∧ lam ^ N * d = 1 := by
    refine ⟨(d⁻¹) ^ ((N : ℝ)⁻¹), Real.rpow_pos_of_pos (inv_pos.2 hd) _, ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_pos.2 hd).le, inv_mul_cancel₀ hNr.ne', Real.rpow_one,
      inv_mul_cancel₀ hd.ne']
  obtain ⟨c', hc'0, hc'1, hc'2⟩ : ∃ c' : ℝ, 0 < c' ∧ c' ≤ 1 ∧ c' ≤ lam / Real.sqrt N :=
    ⟨min 1 (lam / Real.sqrt N), lt_min one_pos (div_pos hlam0 (Real.sqrt_pos.2 hNr)), min_le_left _ _,
      min_le_right _ _⟩
  obtain ⟨C0, hC0⟩ := siegel_cover (Fin N)
  obtain ⟨C1, hC1⟩ := siegel_entry_bound N C0
  have hint : ∀ k, IsIntegral ℤ (integralBasis I.E k) := by
    intro k
    rw [integralBasis_apply]
    exact RingOfIntegers.isIntegral_coe _
  choose X hX using fun k => MulCoord.mul_conj_coord I N ρ hρ _ (hint k)
  choose C2 hC2 using fun k => GlobalTheory.T.reducedBasis_integral_conj_entries_bounded N C0 (entSum (X k))
  obtain ⟨Xt, μ, c, hμ, hc, hXt⟩ := GlobalTheory.T.traceForm_real_coordinates_integral_gram I N ρ hρ
  obtain ⟨s, hs⟩ : ∃ s : ℝ, lam * s * lam = 1 := ⟨lam⁻¹ * lam⁻¹, by field_simp⟩
  obtain ⟨μ', hμ'0, hμ'⟩ : ∃ μ' : ℝ, μ' ≠ 0 ∧ lam * lam * μ = μ' * s := by
    refine ⟨lam * lam * μ * lam * lam, by positivity, ?_⟩
    have hs' : s = lam⁻¹ * lam⁻¹ := by
      field_simp
      linarith
    rw [hs']
    field_simp
  obtain ⟨C3, hC3⟩ := GlobalTheory.T.siegelReduced_integral_form_bounded_entries N C0 (max |μ'| (entSum (s • Xt)))
  refine ⟨N, max (∑ k, |C2 k|) C3, Real.sqrt N * (lam⁻¹ * C1 / c' ^ N), fun y => ?_⟩
  have hdy := hdet y
  obtain ⟨S, hSu, hSd⟩ : ∃ S : Matrix (Fin N) (Fin N) ℤ, IsUnit S.det ∧
      (gm I ρ y e0 * S.map (Int.cast : ℤ → ℝ)).det = d := by
    rcases le_or_gt 0 (gm I ρ y e0).det with hpos | hneg
    · refine ⟨1, by simp, ?_⟩
      rw [Matrix.det_mul]
      simp only [Matrix.map_one Int.cast Int.cast_zero Int.cast_one, Matrix.det_one, mul_one]
      rw [← hdy, abs_of_nonneg hpos]
    · let f : Fin N → ℤ := fun i => if i = ⟨0, hN⟩ then -1 else 1
      have hf : ∏ i, f i = -1 := by
        simp [f, Finset.prod_ite_eq']
      refine ⟨Matrix.diagonal f, by rw [Matrix.det_diagonal, hf]; exact isUnit_one.neg, ?_⟩
      rw [Matrix.det_mul, Matrix.diagonal_map Int.cast_zero, Matrix.det_diagonal]
      have hf' : ∏ i, ((f i : ℤ) : ℝ) = -1 := by
        rw [← Int.cast_prod, hf]
        simp
      rw [hf', ← hdy, abs_of_neg hneg]
      ring
  let e1 : Fin N → Fin I.n → I.E := fun j => ∑ i, S i j • e0 i
  have he1 : IsZBasis I e1 := isZBasis_change I e0 he0 S hSu
  have hg1 : gm I ρ y e1 = gm I ρ y e0 * S.map Int.cast := gm_change I ρ y e0 S
  have hdet1 : (lam • gm I ρ y e1).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, hg1, hSd, hlamN]
  obtain ⟨γ, hγ, k, a, n, hsieg, hfac⟩ := hC0 _ hdet1
  let e : Fin N → Fin I.n → I.E := fun j => ∑ i, γ i j • e1 i
  have he : IsZBasis I e := isZBasis_change I e1 he1 γ (by rw [hγ]; exact isUnit_one)
  have hK : k * Matrix.diagonal a * n = lam • gm I ρ y e := by
    rw [← hfac, gm_change I ρ y e1 γ, Matrix.smul_mul]
  refine ⟨e, he, ⟨fun kk j => ?_, fun i j => ?_⟩, fun t ht0 ht1 hns j => ?_⟩
  · obtain ⟨M, M', h1, h2, h3⟩ := hX kk y e he
    refine ⟨fun i => M i j, h3 j, fun i => ?_⟩
    have hb := hC2 kk k a n hsieg (X kk) M M' (fun i j => abs_le_entSum (X kk) i j)
      (by rw [hK, Matrix.smul_mul, h1, Matrix.mul_smul])
      (by rw [hK, Matrix.smul_mul, h2, Matrix.mul_smul]) i j
    calc |((M i j : ℤ) : ℝ)| ≤ C2 kk := hb
      _ ≤ |C2 kk| := le_abs_self _
      _ ≤ ∑ k, |C2 k| := Finset.single_le_sum (f := fun k => |C2 k|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ kk)
      _ ≤ _ := le_max_left _ _
  · obtain ⟨B, B', hB1, hB2, hB3⟩ := hXt y e he
    have hb := hC3 k a n hsieg (s • Xt) B B' μ' hμ'0 (le_max_left _ _)
      (fun i j => (abs_le_entSum (s • Xt) i j).trans (le_max_right _ _))
      (by rw [hK, smul_conj, hs, one_smul, hB1])
      (by rw [hK, smul_conj', hB2, smul_smul, smul_smul, hμ']) i j
    have hcast : ((B i j : ℤ) : ℝ) = (c : ℝ) * ((trForm I (e i) (e j) : ℚ) : ℝ) := by
      exact_mod_cast hB3 i j
    have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
    have htr : |((trForm I (e i) (e j) : ℚ) : ℝ)| ≤ |((B i j : ℤ) : ℝ)| := by
      rw [hcast, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ c)]
      nlinarith [abs_nonneg ((trForm I (e i) (e j) : ℚ) : ℝ)]
    exact htr.trans (hb.trans (le_max_right _ _))
  · have hz : ∀ z : Fin N → ℤ, z ≠ 0 → c' * t ≤ ‖(k * Matrix.diagonal a * n) *ᵥ fun i => (z i : ℝ)‖ := by
      intro z hz
      rw [hK, Matrix.smul_mulVec, gm_mulVec, norm_smul, Real.norm_eq_abs, abs_of_pos hlam0]
      have hu : (∑ j, z j • e j) ≠ 0 := by
        intro h
        apply hz
        exact funext (Fintype.linearIndependent_iff.1 he.1 z h)
      have hiv : IntVec I (∑ j, z j • e j) := (he.2 _).2 ⟨z, rfl⟩
      have h1 : t ≤ ‖vec I y (∑ j, z j • e j)‖ := hns _ hiv hu
      have h2 := norm_le_sqrt I hρ (vec I y (∑ j, z j • e j))
      have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
      calc c' * t ≤ lam / Real.sqrt N * t := mul_le_mul_of_nonneg_right hc'2 ht0.le
        _ ≤ lam / Real.sqrt N * (Real.sqrt N * ‖ρ (vec I y (∑ j, z j • e j))‖) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
        _ = lam * ‖ρ (vec I y (∑ j, z j • e j))‖ := by field_simp
    have hbound := hC1 k a n hsieg (c' * t) (mul_pos hc'0 ht0) (by nlinarith) hz
    have hcol : ∀ i, |ρ (vec I y (e j)) i| * t ^ N ≤ lam⁻¹ * C1 / c' ^ N := by
      intro i
      have hij := hbound i j
      have hKij : (k * Matrix.diagonal a * n) i j = lam * ρ (vec I y (e j)) i := by
        rw [hK]
        simp [gm]
      rw [hKij, abs_mul, abs_of_pos hlam0, mul_pow] at hij
      rw [le_div_iff₀ (pow_pos hc'0 N)]
      calc |ρ (vec I y (e j)) i| * t ^ N * c' ^ N
          = lam⁻¹ * (lam * |ρ (vec I y (e j)) i| * (c' ^ N * t ^ N)) := by field_simp
        _ ≤ lam⁻¹ * C1 := by gcongr
    have hD : 0 ≤ lam⁻¹ * C1 / c' ^ N := (by positivity : (0 : ℝ) ≤ |ρ (vec I y (e j)) j| * t ^ N).trans (hcol j)
    have hρn : ‖ρ (vec I y (e j))‖ ≤ lam⁻¹ * C1 / c' ^ N / t ^ N := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      rw [Real.norm_eq_abs, le_div_iff₀ (pow_pos ht0 N)]
      exact hcol i
    calc ‖vec I y (e j)‖ * t ^ N ≤ Real.sqrt N * ‖ρ (vec I y (e j))‖ * t ^ N :=
          mul_le_mul_of_nonneg_right (norm_le_sqrt I hρ _) (by positivity)
      _ ≤ Real.sqrt N * (lam⁻¹ * C1 / c' ^ N / t ^ N) * t ^ N := by gcongr
      _ = Real.sqrt N * (lam⁻¹ * C1 / c' ^ N) := by field_simp

end
