import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ContinuousOnIteratedFDerivTranslate

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem rising_product_ne_zero (a : ℤ) (m : ℕ) (h : ∀ i : ℕ, i < m → (i : ℤ) + a ≠ 0) :
    ∏ i ∈ Finset.range m, ((a : ℂ) + (i : ℂ)) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i hi h0
  apply h i (Finset.mem_range.1 hi)
  have : (((i : ℤ) + a : ℤ) : ℂ) = 0 := by push_cast; linear_combination h0
  exact_mod_cast this

theorem herm_isHermitian (x : Fin n → Fin n → ℝ) : (herm x)ᴴ = herm x := by
  ext i j
  simp only [herm, Matrix.conjTranspose_apply]
  apply Complex.ext <;> simp <;> ring

theorem inG_nU_herm (x : Fin n → Fin n → ℝ) : InG (nU (herm x)) := by
  have hH := herm_isHermitian x
  unfold InG nU JJ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hH]

theorem fubini_step (p q : ℤ) (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
    (hK : ∀ g, InK g ↔ ∃ k, ι k = g) (a b : M2 n) (ha : InG a) (hb : InG b) (ψ : (Fin n → Fin n → ℝ) → ℂ)
    (hψ : IsSingTest ψ) :
    ∫ k, (∫ x, f0 p q (ι k * a * nU (herm x) * b) * ψ x) * (f0 p q (ι k))⁻¹ ∂μ =
      ∫ x, (∫ k, f0 p q (ι k * (a * nU (herm x) * b)) * (f0 p q (ι k))⁻¹ ∂μ) * ψ x := by
  have hιG : ∀ k, InG (ι k) := fun k => ((hK (ι k)).2 ⟨k, rfl⟩).1
  have hU0 : ∀ g : M2 n, InG g → g ∈ {x : M2 n | (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0} := fun g hg =>
    ⟨(gset_sub_dom hg).2.1, (gset_sub_dom hg).2.2.1⟩
  have hf0c : ContinuousOn (f0 (n := n) p q) {x : M2 n | (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0} :=
    (contDiffOn_scalar_section p q).continuousOn
  have hf0ne : ∀ k, f0 p q (ι k) ≠ 0 := fun k h => by
    have := scalar_section_mul_conjugate_section ((hK (ι k)).2 ⟨k, rfl⟩) p q; rw [h, zero_mul] at this; exact zero_ne_one this
  have hc : Continuous fun k => (f0 p q (ι k))⁻¹ :=
    (hf0c.comp_continuous hι (fun k => hU0 _ (hιG k))).inv₀ hf0ne
  have hherm : Continuous (herm (n := n)) := by
    unfold herm; fun_prop
  have hnU : Continuous fun x : Fin n → Fin n → ℝ => nU (herm x) := by
    unfold nU; exact Continuous.matrix_fromBlocks continuous_const hherm continuous_const continuous_const
  have hmap : Continuous fun z : Kg × (Fin n → Fin n → ℝ) => ι z.1 * a * nU (herm z.2) * b :=
    (((hι.comp continuous_fst).mul continuous_const).mul (hnU.comp continuous_snd)).mul continuous_const
  set F : Kg × (Fin n → Fin n → ℝ) → ℂ := fun z => f0 p q (ι z.1 * a * nU (herm z.2) * b) * ψ z.2 *
    (f0 p q (ι z.1))⁻¹ with hFdef
  have hFc : Continuous F :=
    ((hf0c.comp_continuous hmap (fun z => hU0 _ (inG_mul (inG_mul (inG_mul (hιG z.1) ha) (inG_nU_herm z.2)) hb))).mul
      (hψ.1.comp continuous_snd)).mul (hc.comp continuous_fst)
  have hFs : HasCompactSupport F := by
    refine IsCompact.of_isClosed_subset (isCompact_univ.prod hψ.2.1) (isClosed_tsupport F) ?_
    refine closure_minimal (fun z hz => ⟨Set.mem_univ _, subset_tsupport ψ ?_⟩)
      (isClosed_univ.prod (isClosed_tsupport ψ))
    intro h0; apply hz; simp [hFdef, h0]
  have hFi : Integrable F (μ.prod volume) := hFc.integrable_of_hasCompactSupport hFs
  have e1 : ∀ k, (∫ x, f0 p q (ι k * a * nU (herm x) * b) * ψ x) * (f0 p q (ι k))⁻¹ = ∫ x, F (k, x) := by
    intro k; rw [← integral_mul_const]
  have e2 : ∀ x, (∫ k, f0 p q (ι k * (a * nU (herm x) * b)) * (f0 p q (ι k))⁻¹ ∂μ) * ψ x = ∫ k, F (k, x) ∂μ := by
    intro x; rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hFdef, mul_assoc]; ring
  simp_rw [e1, e2]
  exact integral_integral_swap (f := fun k x => F (k, x)) hFi

theorem embOn_add (s : Finset (Fin n)) (T T' : Matrix s s ℂ) : embOn s (T + T') = embOn s T + embOn s T' := by
  ext a b; simp only [embOn, Matrix.add_apply]; split_ifs <;> simp

theorem embOn_smul (s : Finset (Fin n)) (c : ℂ) (T : Matrix s s ℂ) : embOn s (c • T) = c • embOn s T := by
  ext a b; simp only [embOn, Matrix.smul_apply]; split_ifs <;> simp

theorem WD_add (Q Q' R R' : Matrix (Fin n) (Fin n) ℂ) : WD (Q + Q') (R + R') = WD Q R + WD Q' R' := by
  have : fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (Q + Q') (R + R') 0 = fromBlocks 0 Q R 0 + fromBlocks 0 Q' R' 0 := by
    rw [Matrix.fromBlocks_add, add_zero]
  simp only [WD, this, Matrix.mul_add, Matrix.add_mul]

theorem WD_smul (c : ℂ) (Q R : Matrix (Fin n) (Fin n) ℂ) : WD (c • Q) (c • R) = c • WD Q R := by
  have : fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (c • Q) (c • R) 0 = c • fromBlocks 0 Q R 0 := by
    rw [Matrix.fromBlocks_smul, smul_zero]
  simp only [WD, this, Matrix.mul_smul, Matrix.smul_mul]

theorem WD_split (Q R : Matrix (Fin n) (Fin n) ℂ) : WD Q R = WD Q 0 + WD 0 R := by
  rw [← WD_add]; simp

def LQ (s : Finset (Fin n)) (x : M2 n) : Matrix s s ℂ →L[ℂ] M2 n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => x * WD (embOn s T) 0
      map_add' := fun T T' => by
        have h := WD_add (embOn s T) (embOn s T') (0 : Matrix (Fin n) (Fin n) ℂ) 0
        rw [add_zero] at h
        rw [embOn_add, h, Matrix.mul_add]
      map_smul' := fun c T => by
        have h := WD_smul c (embOn s T) (0 : Matrix (Fin n) (Fin n) ℂ)
        rw [smul_zero] at h
        simp only [RingHom.id_apply]
        rw [embOn_smul, h, Matrix.mul_smul] }

def LR (s : Finset (Fin n)) (x : M2 n) : Matrix s s ℂ →L[ℂ] M2 n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => x * WD 0 (embOn s T)
      map_add' := fun T T' => by
        have h := WD_add (0 : Matrix (Fin n) (Fin n) ℂ) 0 (embOn s T) (embOn s T')
        rw [add_zero] at h
        rw [embOn_add, h, Matrix.mul_add]
      map_smul' := fun c T => by
        have h := WD_smul c (0 : Matrix (Fin n) (Fin n) ℂ) (embOn s T)
        rw [smul_zero] at h
        simp only [RingHom.id_apply]
        rw [embOn_smul, h, Matrix.mul_smul] }

theorem LQ_apply (s : Finset (Fin n)) (x : M2 n) (T : Matrix s s ℂ) : LQ s x T = x * WD (embOn s T) 0 := rfl

theorem LR_apply (s : Finset (Fin n)) (x : M2 n) (T : Matrix s s ℂ) : LR s x T = x * WD 0 (embOn s T) := rfl

theorem mul_mX (x : M2 n) (Q R : Matrix (Fin n) (Fin n) ℂ) : x * mX 1 Q R 1 = x + x * WD Q 0 + x * WD 0 R := by
  rw [mX_eq, Matrix.mul_add, Matrix.mul_one, WD_split, Matrix.mul_add, add_assoc]

theorem fin_append_mul {a b : ℕ} (M : M2 n) (u : Fin a → M2 n) (v : Fin b → M2 n) :
    (fun i => M * Fin.append u v i) = Fin.append (fun i => M * u i) (fun i => M * v i) := by
  funext i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

theorem contDiff_mulLeft (M : M2 n) : ContDiff ℂ ∞ (fun x : M2 n => M * x) :=
  (LinearMap.mulLeft ℂ M).toContinuousLinearMap.contDiff

theorem contDiff_nU_sandwich (a b : M2 n) : ContDiff ℂ ∞ (fun H : Matrix (Fin n) (Fin n) ℂ => a * nU H * b) := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n :=
    { toFun := fun H => a * fromBlocks 0 H 0 0 * b
      map_add' := fun H H' => by
        have : (fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (H + H') 0 0 : M2 n) = fromBlocks 0 H 0 0 + fromBlocks 0 H' 0 0 := by
          rw [Matrix.fromBlocks_add]; simp
        rw [this, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c H => by
        have : (fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (c • H) 0 0 : M2 n) = c • fromBlocks 0 H 0 0 := by
          rw [Matrix.fromBlocks_smul]; simp
        simp only [RingHom.id_apply]
        rw [this, Matrix.mul_smul, Matrix.smul_mul] }
  have h : (fun H : Matrix (Fin n) (Fin n) ℂ => a * nU H * b) = fun H => a * b + L.toContinuousLinearMap H := by
    funext H
    have : nU H = 1 + (fromBlocks 0 H 0 0 : M2 n) := by
      rw [nU, ← Matrix.fromBlocks_one, Matrix.fromBlocks_add]; simp
    simp only [L, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
    rw [this, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
  rw [h]
  exact contDiff_const.add L.toContinuousLinearMap.contDiff

theorem iteratedFDeriv_mul_const_of (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (c : ℂ)
    (x : M2 n) (hx : x ∈ U) (N : ℕ) (v : Fin N → M2 n) :
    iteratedFDeriv ℂ N (fun y => F y * c) x v = iteratedFDeriv ℂ N F x v * c := by
  have hFx : ContDiffAt ℂ ∞ F x := hF.contDiffAt (hU.mem_nhds hx)
  have h := ContinuousLinearMap.iteratedFDeriv_comp_left ((ContinuousLinearMap.mul ℂ ℂ).flip c) hFx
    (i := N) (by exact_mod_cast le_top)
  have e : (fun y => F y * c) = (ContinuousLinearMap.mul ℂ ℂ).flip c ∘ F := by funext y; rfl
  rw [e, h]; rfl

theorem integrable_of_continuous_K {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [IsFiniteMeasureOnCompacts μ] {f : Kg → ℂ} (hf : Continuous f) :
    Integrable f μ :=
  hf.integrable_of_hasCompactSupport (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport f) (Set.subset_univ _))

theorem detD_detD_mul_const {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (x₀ : M2 n) (hx : x₀ ∈ U)
    (LA : Matrix ιA ιA ℂ →L[ℂ] M2 n) (LB : Matrix ιB ιB ℂ →L[ℂ] M2 n) (c : ℂ) :
    detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S) * c)) =
      detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S))) * c := by
  rw [detD_detD_comp (fun y => F y * c) U hU (hF.mul contDiffOn_const) x₀ hx LA LB,
    detD_detD_comp F U hU hF x₀ hx LA LB, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [iteratedFDeriv_mul_const_of F U hU hF c x₀ hx]; ring

end PositivityTheory.Rg.Sw.LVs
