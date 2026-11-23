import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFrameDatumZetaIntegralEqSmaller

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.StdPairMatch
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_KO_iff_isGLO {n : ℕ} (g : GL (Fin n) k) : g ∈ KO k (Fin n) ↔ IsGLO g.val := by
  constructor
  · intro hg
    exact ⟨((mem_KO_iff g).1 hg).1, valuation_gdet_of_mem_KO hg⟩
  · rintro ⟨hM, hd⟩
    let A : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨g.val i j, hM i j⟩
    have e : (algebraMap 𝒪[k] k).mapMatrix A = g.val := rfl
    have hu : IsUnit A.det := by
      refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 ?_
      rw [RingHom.map_det, e, hd]
    obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det A).2 hu
    refine ⟨u, Units.ext ?_⟩
    change (algebraMap 𝒪[k] k).mapMatrix u.val = g.val
    rw [hu', e]

theorem mul_mem_cball {m p r : Type} [Fintype p] {s : kˣ} {A : Matrix m p k} {B : Matrix p r k}
    (hA : ∀ i j, A i j ∈ 𝒪[k]) (hB : ∀ i j, B i j ∈ cball s) (i : m) (j : r) : (A * B) i j ∈ cball s := by
  rw [Matrix.mul_apply]
  refine Finset.sum_induction _ (· ∈ cball s) (fun x y hx hy => add_mem_cball hx hy) ?_ fun l _ => ?_
  · simp only [cball, Set.mem_setOf_eq]
    simp
  · simp only [cball, Set.mem_setOf_eq]
    rw [map_mul]
    exact (mul_le_of_le_one_left' (hA i l)).trans (hB l j)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem blk₁_mul {m m' a a' : ℕ} (M : Matrix (Fin m') (Fin m) k) (X : Matrix (Fin m) (Fin (a + a')) k) :
    blk₁ (M * X) = M * blk₁ X := by
  ext i j; simp [blk₁, Matrix.mul_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem blk₂_mul {m m' a a' : ℕ} (M : Matrix (Fin m') (Fin m) k) (X : Matrix (Fin m) (Fin (a + a')) k) :
    blk₂ (M * X) = M * blk₂ X := by
  ext i j; simp [blk₂, Matrix.mul_apply]

end GlobalTheory.StdPairMatch

namespace GlobalTheory.StdPairMatch
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil Matrix MeasureTheory

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open Classical in

theorem stdA_mul {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c a a' : ℕ} {X : Matrix (Fin a) (Fin (a + a')) k} {g₀ : GL (Fin a) k}
    (hg₀ : g₀.val = blk₁ X) (g : GL (Fin a) k) :
    stdA ν ϖ c a a' (g.val * X) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2) =
      ((fun g : GL (Fin a) k => g * g₀⁻¹⁻¹) ⁻¹' (KO k (Fin a) : Set (GL (Fin a) k))).indicator
        (fun _ => (((ν (gdet g₀))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₀) (-(Fintype.card (Fin (a + a')) : ℂ) / 2) *
          (if ∀ i j, ((g₀⁻¹).val * blk₂ X) i j ∈ cball (ϖ ^ c) then 1 else 0)) g := by
  have hb1 : blk₁ (g.val * X) = (g * g₀).val := by rw [blk₁_mul, Units.val_mul, hg₀]
  have hb2 : blk₂ (g.val * X) = (g * g₀).val * ((g₀⁻¹).val * blk₂ X) := by
    rw [blk₂_mul, ← Matrix.mul_assoc, ← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]
  by_cases hS : g * g₀ ∈ KO k (Fin a)
  · rw [Set.indicator_of_mem (by simpa using hS)]
    have hG : IsGLO (blk₁ (g.val * X)) := hb1 ▸ (mem_KO_iff_isGLO _).1 hS
    have hdet : (blk₁ (g.val * X)).det ≠ 0 := hb1 ▸ (g * g₀).det_ne_zero
    have hcond : (∀ i j, blk₂ (g.val * X) i j ∈ cball (ϖ ^ c)) ↔
        ∀ i j, ((g₀⁻¹).val * blk₂ X) i j ∈ cball (ϖ ^ c) := by
      constructor
      · intro H
        have e : (g₀⁻¹).val * blk₂ X = ((g * g₀)⁻¹).val * blk₂ (g.val * X) := by
          rw [hb2, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
        rw [e]
        exact mul_mem_cball ((mem_KO_iff _).1 hS).2 H
      · intro H
        rw [hb2]
        exact mul_mem_cball ((mem_KO_iff _).1 hS).1 H
    have hu : Units.mk0 _ hdet = gdet g * gdet g₀ := by
      ext; simp [hb1, Matrix.GeneralLinearGroup.val_det_apply]
    have hv : valuation k ((gdet (g * g₀) : kˣ) : k) = 1 := valuation_gdet_of_mem_KO hS
    have hap : apow (gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2) =
        apow (gdet g₀) (-(Fintype.card (Fin (a + a')) : ℂ) / 2) := by
      have : gdet g = gdet (g * g₀) * (gdet g₀)⁻¹ := by rw [gdet_mul]; group
      rw [this, apow_mul, apow_of_valuation_eq_one hv, one_mul, apow_inv, neg_div]
    by_cases hc : ∀ i j, ((g₀⁻¹).val * blk₂ X) i j ∈ cball (ϖ ^ c)
    · rw [if_pos hc, stdA, dif_pos ⟨hdet, hG, hcond.2 hc⟩, hu, hap, map_mul]
      simp only [_root_.mul_inv_rev, Units.val_mul, mul_one]
      have h1 : ((ν (gdet g) : ℂˣ) : ℂ) * (((ν (gdet g))⁻¹ : ℂˣ) : ℂ) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      linear_combination ((((ν (gdet g₀))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₀) (-(Fintype.card (Fin (a + a')) : ℂ) / 2)) * h1
    · rw [if_neg hc, stdA, dif_neg (fun H => hc (hcond.1 H.2.2))]
      simp
  · rw [Set.indicator_of_notMem (by simpa using hS), stdA, dif_neg (fun H => hS ((mem_KO_iff_isGLO _).2 (hb1 ▸ H.2.1)))]
    simp

end GlobalTheory.StdPairMatch

namespace GlobalTheory.StdPairMatch
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil Matrix MeasureTheory

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open Classical in

theorem stdB_mul {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c a a' : ℕ} {Y : Matrix (Fin a') (Fin (a + a')) k} {g₀ : GL (Fin a') k}
    (hg₀ : g₀.val = blk₂ Y) (g : GL (Fin a') k) :
    stdB ν ϖ c a a' (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2) =
      ((fun g : GL (Fin a') k => g * g₀⁻¹⁻¹) ⁻¹' (KO k (Fin a') : Set (GL (Fin a') k))).indicator
        (fun _ => (((ν (gdet g₀))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₀) (-(Fintype.card (Fin (a + a')) : ℂ) / 2) *
          (if ∀ i j, ((g₀⁻¹).val * blk₁ Y) i j ∈ cball (ϖ ^ c) then 1 else 0)) g := by
  have hb1 : blk₂ (g.val * Y) = (g * g₀).val := by rw [blk₂_mul, Units.val_mul, hg₀]
  have hb2 : blk₁ (g.val * Y) = (g * g₀).val * ((g₀⁻¹).val * blk₁ Y) := by
    rw [blk₁_mul, ← Matrix.mul_assoc, ← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]
  by_cases hS : g * g₀ ∈ KO k (Fin a')
  · rw [Set.indicator_of_mem (by simpa using hS)]
    have hG : IsGLO (blk₂ (g.val * Y)) := hb1 ▸ (mem_KO_iff_isGLO _).1 hS
    have hdet : (blk₂ (g.val * Y)).det ≠ 0 := hb1 ▸ (g * g₀).det_ne_zero
    have hcond : (∀ i j, blk₁ (g.val * Y) i j ∈ cball (ϖ ^ c)) ↔
        ∀ i j, ((g₀⁻¹).val * blk₁ Y) i j ∈ cball (ϖ ^ c) := by
      constructor
      · intro H
        have e : (g₀⁻¹).val * blk₁ Y = ((g * g₀)⁻¹).val * blk₁ (g.val * Y) := by
          rw [hb2, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
        rw [e]
        exact mul_mem_cball ((mem_KO_iff _).1 hS).2 H
      · intro H
        rw [hb2]
        exact mul_mem_cball ((mem_KO_iff _).1 hS).1 H
    have hu : Units.mk0 _ hdet = gdet g * gdet g₀ := by
      ext; simp [hb1, Matrix.GeneralLinearGroup.val_det_apply]
    have hv : valuation k ((gdet (g * g₀) : kˣ) : k) = 1 := valuation_gdet_of_mem_KO hS
    have hap : apow (gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2) =
        apow (gdet g₀) (-(Fintype.card (Fin (a + a')) : ℂ) / 2) := by
      have : gdet g = gdet (g * g₀) * (gdet g₀)⁻¹ := by rw [gdet_mul]; group
      rw [this, apow_mul, apow_of_valuation_eq_one hv, one_mul, apow_inv, neg_div]
    by_cases hc : ∀ i j, ((g₀⁻¹).val * blk₁ Y) i j ∈ cball (ϖ ^ c)
    · rw [if_pos hc, stdB, dif_pos ⟨hdet, hG, hcond.2 hc⟩, hu, hap, map_mul]
      simp only [_root_.mul_inv_rev, Units.val_mul, mul_one]
      have h1 : ((ν (gdet g) : ℂˣ) : ℂ) * (((ν (gdet g))⁻¹ : ℂˣ) : ℂ) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      linear_combination ((((ν (gdet g₀))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₀) (-(Fintype.card (Fin (a + a')) : ℂ) / 2)) * h1
    · rw [if_neg hc, stdB, dif_neg (fun H => hc (hcond.1 H.2.2))]
      simp
  · rw [Set.indicator_of_notMem (by simpa using hS), stdB, dif_neg (fun H => hS ((mem_KO_iff_isGLO _).2 (hb1 ▸ H.2.1)))]
    simp

end GlobalTheory.StdPairMatch

namespace GlobalTheory.StdPairMatch
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil Matrix MeasureTheory

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]

open Classical in

theorem bigF_stdA {ν : kˣ →* ℂˣ} {ϖ : kˣ} (hϖ : IsUnif ϖ) (c : ℕ) {a a' : ℕ} {X : Matrix (Fin a) (Fin (a + a')) k}
    {g₀ : GL (Fin a) k} (hg₀ : g₀.val = blk₁ X) :
    bigF (haarVol (KO k (Fin a))) ϖ ν (stdA ν ϖ c a a') X =
      (((ν (gdet g₀))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₀) (-(Fintype.card (Fin (a + a')) : ℂ) / 2) *
          (if ∀ i j, ((g₀⁻¹).val * blk₂ X) i j ∈ cball (ϖ ^ c) then 1 else 0) := by
  set V : ℂ := (((ν (gdet g₀))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₀) (-(Fintype.card (Fin (a + a')) : ℂ) / 2) *
          (if ∀ i j, ((g₀⁻¹).val * blk₂ X) i j ∈ cball (ϖ ^ c) then 1 else 0) with hV
  set S : Set (GL (Fin a) k) := (fun g => g * g₀⁻¹⁻¹) ⁻¹' (KO k (Fin a) : Set (GL (Fin a) k)) with hSdef
  obtain ⟨⟨m₀, hm₀⟩, hmem, huniq⟩ := GlobalTheory.OneSquareZeta.exists_unique_shell hϖ g₀⁻¹
  have hSm : @MeasurableSet (GL (Fin a) k) Units.instMeasurableSpace S := by
    letI : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
    haveI : BorelSpace (GL (Fin a) k) := borel_GL
    exact (isOpen_KO.preimage (continuous_mul_right _)).measurableSet
  have hS1 : (haarVol (KO k (Fin a))).real S = 1 := by
    simp [hSdef, Measure.real, measure_preimage_mul_right, haarVol_self isOpen_KO le_rfl]
  have hint : ∀ g : GL (Fin a) k, stdA ν ϖ c a a' (g.val * X) * (ν (gdet g) : ℂ) *
      apow (gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2) = S.indicator (fun _ => V) g := stdA_mul hg₀
  have hshell : ∀ m : {m : Fin a → ℤ // Antitone m}, shell (haarVol (KO k (Fin a))) ϖ ν
      ((Fintype.card (Fin (a + a')) : ℂ) / 2) (fun M => stdA ν ϖ c a a' (M * X)) m.1 =
      (haarVol (KO k (Fin a))).real (shellSet ϖ m.1 ∩ S) • V := by
    intro m
    rw [shell]
    simp_rw [hint]
    have e1 := setIntegral_indicator (μ := haarVol (KO k (Fin a))) (s := shellSet ϖ m.1)
      (f := fun _ => V) hSm
    rw [e1, setIntegral_const]
  have hsub : S ⊆ shellSet ϖ m₀ := by
    intro g hg
    obtain ⟨x, hx, y, hy, e⟩ := mem_shellSet.1 hmem
    refine mem_shellSet.2 ⟨g * g₀⁻¹⁻¹ * x, mul_mem hg hx, y, hy, ?_⟩
    calc g = g * g₀⁻¹⁻¹ * g₀⁻¹ := by group
      _ = _ := by rw [e]; simp only [mul_assoc]; try rfl
  rw [bigF, shellSum, finsum_eq_single _ ⟨m₀, hm₀⟩]
  · rw [hshell, Set.inter_eq_right.2 hsub, hS1, one_smul]
  · intro m hm
    rw [hshell]
    have : shellSet ϖ m.1 ∩ S = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun g ⟨hg1, hg2⟩ => hm (huniq m ?_)
      obtain ⟨x, hx, y, hy, e⟩ := mem_shellSet.1 hg1
      refine mem_shellSet.2 ⟨(g * g₀⁻¹⁻¹)⁻¹ * x, mul_mem (inv_mem hg2) hx, y, hy, ?_⟩
      calc g₀⁻¹ = (g * g₀⁻¹⁻¹)⁻¹ * g := by group
        _ = _ := by rw [e]; simp only [mul_assoc]; try rfl
    simp [this]

theorem bigF_stdA_of_det_eq_zero (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) {a a' : ℕ} {X : Matrix (Fin a) (Fin (a + a')) k}
    (hX : (blk₁ X).det = 0) : bigF (haarVol (KO k (Fin a))) ϖ ν (stdA ν ϖ c a a') X = 0 := by
  have h0 : ∀ g : Matrix (Fin a) (Fin a) k, stdA ν ϖ c a a' (g * X) = 0 := fun g => by
    rw [stdA, dif_neg]
    rintro ⟨hd, -⟩
    exact hd (by rw [blk₁_mul, det_mul, hX, mul_zero])
  simp [bigF, shellSum, shell, h0]

open Classical in

theorem smallF_stdB {ν : kˣ →* ℂˣ} {ϖ : kˣ} (c : ℕ) {a a' : ℕ} {Y : Matrix (Fin a') (Fin (a + a')) k}
    {g₀ : GL (Fin a') k} (hg₀ : g₀.val = blk₂ Y) :
    smallF (haarVol (KO k (Fin a'))) ν (stdB ν ϖ c a a') Y =
      (((ν (gdet g₀))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₀) (-(Fintype.card (Fin (a + a')) : ℂ) / 2) *
          (if ∀ i j, ((g₀⁻¹).val * blk₁ Y) i j ∈ cball (ϖ ^ c) then 1 else 0) := by
  set S : Set (GL (Fin a') k) := (fun g => g * g₀⁻¹⁻¹) ⁻¹' (KO k (Fin a') : Set (GL (Fin a') k)) with hSdef
  have hSm : @MeasurableSet (GL (Fin a') k) Units.instMeasurableSpace S := by
    letI : MeasurableSpace (GL (Fin a') k) := Units.instMeasurableSpace
    haveI : BorelSpace (GL (Fin a') k) := borel_GL
    exact (isOpen_KO.preimage (continuous_mul_right _)).measurableSet
  have hS1 : (haarVol (KO k (Fin a'))).real S = 1 := by
    simp [hSdef, Measure.real, measure_preimage_mul_right, haarVol_self isOpen_KO le_rfl]
  unfold smallF
  simp_rw [stdB_mul hg₀]
  rw [← hSdef]
  refine (integral_indicator hSm).trans ((setIntegral_const _).trans ?_)
  erw [hS1, one_smul]

theorem smallF_stdB_of_det_eq_zero (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) {a a' : ℕ} {Y : Matrix (Fin a') (Fin (a + a')) k}
    (hY : (blk₂ Y).det = 0) : smallF (haarVol (KO k (Fin a'))) ν (stdB ν ϖ c a a') Y = 0 := by
  have h0 : ∀ g : Matrix (Fin a') (Fin a') k, stdB ν ϖ c a a' (g * Y) = 0 := fun g => by
    rw [stdB, dif_neg]
    rintro ⟨hd, -⟩
    exact hd (by rw [blk₂_mul, det_mul, hY, mul_zero])
  simp [smallF, h0]

end GlobalTheory.StdPairMatch

namespace GlobalTheory.StdPairMatch
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil Matrix

variable {k : Type} [Field k]

theorem det_mul_det_blk {a a' : ℕ} (h : GL (Fin (a + a')) k) :
    (gdet h : k) * (blk₁ (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ _) * (invT h).val)).det =
      (blk₂ (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ _) * h.val)).det := by
  set e : Fin a ⊕ Fin a' ≃ Fin (a + a') := finSumFinEquiv with he
  set H := h.val.submatrix e e with hH
  set Hi := (h⁻¹).val.submatrix e e with hHi
  have hHH : H * Hi = 1 := by
    rw [hH, hHi, Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]
  have hb : fromBlocks (H.toBlocks₁₁ * Hi.toBlocks₁₁ + H.toBlocks₁₂ * Hi.toBlocks₂₁)
      (H.toBlocks₁₁ * Hi.toBlocks₁₂ + H.toBlocks₁₂ * Hi.toBlocks₂₂)
      (H.toBlocks₂₁ * Hi.toBlocks₁₁ + H.toBlocks₂₂ * Hi.toBlocks₂₁)
      (H.toBlocks₂₁ * Hi.toBlocks₁₂ + H.toBlocks₂₂ * Hi.toBlocks₂₂) = fromBlocks 1 0 0 1 := by
    rw [← fromBlocks_multiply, fromBlocks_toBlocks, fromBlocks_toBlocks, hHH, fromBlocks_one]
  obtain ⟨h11, -, h21, -⟩ := fromBlocks_inj.1 hb
  have key : H * fromBlocks Hi.toBlocks₁₁ 0 Hi.toBlocks₂₁ 1 = fromBlocks 1 H.toBlocks₁₂ 0 H.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks H]
    rw [fromBlocks_multiply, h11, h21]
    simp
  have hd := congrArg Matrix.det key
  rw [det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁, det_one, det_one, mul_one, one_mul] at hd
  have e1 : (gdet h : k) = H.det := by
    rw [hH, det_submatrix_equiv_self]; rfl
  have e2 : blk₁ (X0 k e * (invT h).val) = (Hi.toBlocks₁₁)ᵀ := by
    ext i j; simp [blk₁, frameMatrixFirstColumnBlock_mul_apply, invT_val, hHi, toBlocks₁₁, he]
  have e3 : blk₂ (Y0 k e * h.val) = H.toBlocks₂₂ := by
    ext i j; simp [blk₂, frameMatrixSecondColumnBlock_mul_apply, hH, toBlocks₂₂, he]
  rw [e1, e2, e3, det_transpose, hd]

theorem blk_orth {a a' : ℕ} (h : GL (Fin (a + a')) k) :
    blk₁ (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ _) * h.val) *
        (blk₁ (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ _) * (invT h).val))ᵀ +
      blk₂ (Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ _) * h.val) *
        (blk₂ (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ _) * (invT h).val))ᵀ = 0 := by
  have h0 := frameSecondBlock_mul_frameFirstBlock_transpose_eq_zero (k := k) (finSumFinEquiv : Fin a ⊕ Fin a' ≃ _) h
  ext i j
  have h1 := congrFun (congrFun h0 i) j
  rw [Matrix.mul_apply, Fin.sum_univ_add] at h1
  simpa [Matrix.mul_apply, blk₁, blk₂] using h1

theorem inv_mul_blk {a a' : ℕ} {X : Matrix (Fin a) (Fin (a + a')) k} {Y : Matrix (Fin a') (Fin (a + a')) k}
    (hXY : blk₁ Y * (blk₁ X)ᵀ + blk₂ Y * (blk₂ X)ᵀ = 0) {g₀ : GL (Fin a) k} {g₁ : GL (Fin a') k}
    (hg₀ : g₀.val = blk₁ X) (hg₁ : g₁.val = blk₂ Y) :
    (g₁⁻¹).val * blk₁ Y = -((g₀⁻¹).val * blk₂ X)ᵀ := by
  have hC : blk₁ Y * (blk₁ X)ᵀ = -(blk₂ Y * (blk₂ X)ᵀ) := eq_neg_of_add_eq_zero_left hXY
  calc (g₁⁻¹).val * blk₁ Y = (g₁⁻¹).val * blk₁ Y * ((blk₁ X)ᵀ * ((g₀⁻¹).val)ᵀ) := by
        rw [← transpose_mul, ← hg₀, Units.inv_mul, transpose_one, Matrix.mul_one]
    _ = (g₁⁻¹).val * (blk₁ Y * (blk₁ X)ᵀ) * ((g₀⁻¹).val)ᵀ := by simp only [Matrix.mul_assoc]
    _ = -(((g₁⁻¹).val * blk₂ Y) * (blk₂ X)ᵀ * ((g₀⁻¹).val)ᵀ) := by
        rw [hC]; simp [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
    _ = -((g₀⁻¹).val * blk₂ X)ᵀ := by
        rw [← hg₁, Units.inv_mul, Matrix.one_mul, transpose_mul]

theorem matrixFirstColumnBlock_standardFrame_eq_one {a a' : ℕ} : blk₁ (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ _)) = 1 := by
  ext i j; simp [blk₁, X0, Matrix.one_apply, eq_comm]

theorem matrixLastColumnBlock_standardFrame_eq_zero {a a' : ℕ} : blk₂ (X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ _)) = 0 := by
  ext i j
  simp only [blk₂, X0, Matrix.of_apply, Matrix.zero_apply]
  split_ifs with h
  · exfalso
    simp [Fin.ext_iff] at h
    omega
  · rfl

end GlobalTheory.StdPairMatch

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdPairMatch in
open Classical in

theorem GlobalTheory.StdPairMatch.bigZetaIntegral_stdA_eq_smallZetaIntegral_stdB : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (α β ν : kˣ →* ℂˣ) (ϖ : kˣ) (c m a a' : ℕ), GlobalTheory.SplitFlip.IsUnif ϖ → ν = α / β → 1 ≤ c → GlobalTheory.SplitFlip.CondLE ϖ c ν →
    GlobalTheory.SplitFlip.CondLE ϖ m α → GlobalTheory.SplitFlip.CondLE ϖ m β → (∀ x, ‖(α x : ℂ)‖ = 1) → (∀ x, ‖(β x : ℂ)‖ = 1) →
      GlobalTheory.SplitFlip.bigP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ finSumFinEquiv ν β (stdA ν ϖ c a a') =
        GlobalTheory.SplitFlip.smallP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a'))) finSumFinEquiv ν α (stdB ν ϖ c a a') ∧
      GlobalTheory.SplitFlip.bigP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ finSumFinEquiv ν β (stdA ν ϖ c a a') ≠ 0 := by
  intro k _ _ _ _ _ _ α β ν ϖ c m a a' hϖ hν _ _ _ _ _ _
  have key : ∀ h : GL (Fin (a + a')) k,
      bigP (haarVol (KO k (Fin a))) ϖ finSumFinEquiv ν β (stdA ν ϖ c a a') h =
        smallP (haarVol (KO k (Fin a'))) finSumFinEquiv ν α (stdB ν ϖ c a a') h := by
    intro h
    rw [bigZetaIntegral_eq, smallP]
    have hJ := det_mul_det_blk (k := k) (a := a) (a' := a') h
    have hO := blk_orth (k := k) (a := a) (a' := a') h
    set X := X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ _) * (invT h).val with hX
    set Y := Y0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ _) * h.val with hY
    by_cases hD : (blk₂ Y).det = 0
    · have hP : (blk₁ X).det = 0 := by
        rw [hD] at hJ; exact (mul_eq_zero.1 hJ).resolve_left (Units.ne_zero _)
      rw [bigF_stdA_of_det_eq_zero _ _ _ hP, smallF_stdB_of_det_eq_zero _ _ _ hD]
      simp
    · have hP : (blk₁ X).det ≠ 0 := fun h0 => hD (by rw [← hJ, h0, mul_zero])
      set g₀ := Matrix.GeneralLinearGroup.mkOfDetNeZero (blk₁ X) hP with hg₀
      set g₁ := Matrix.GeneralLinearGroup.mkOfDetNeZero (blk₂ Y) hD with hg₁
      rw [bigF_stdA hϖ c (g₀ := g₀) rfl, smallF_stdB c (g₀ := g₁) rfl]
      have hrel := inv_mul_blk hO (g₀ := g₀) (g₁ := g₁) rfl rfl
      have hcond : (∀ i j, ((g₀⁻¹).val * blk₂ X) i j ∈ cball (ϖ ^ c)) ↔
          (∀ i j, ((g₁⁻¹).val * blk₁ Y) i j ∈ cball (ϖ ^ c)) := by
        rw [hrel]
        constructor
        · intro H i j
          rw [Matrix.neg_apply, Matrix.transpose_apply]
          exact neg_mem_cball (H j i)
        · intro H i j
          have := neg_mem_cball (H j i)
          rwa [Matrix.neg_apply, Matrix.transpose_apply, neg_neg] at this
      rw [if_congr hcond rfl rfl]
      have hdet : gdet g₁ = gdet h * gdet g₀ := Units.ext (by
        simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, hg₀, hg₁,
          Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
        exact hJ.symm)
      rw [hdet, map_mul, apow_mul]
      set I : ℂ := if ∀ (i : Fin a') (j : Fin a), ((g₁⁻¹).val * blk₁ Y) i j ∈ cball (ϖ ^ c) then 1 else 0 with hI
      have eA : apow (gdet h) ((Fintype.card (Fin a') : ℂ) / 2) *
          apow (gdet h) (-(Fintype.card (Fin (a + a')) : ℂ) / 2) = apow (gdet h) (-(a : ℂ) / 2) := by
        rw [← apow_add]; congr 1; simp only [Fintype.card_fin]; push_cast; ring
      have eN : (α (gdet h) : ℂ) = (ν (gdet h) : ℂ) * (β (gdet h) : ℂ) := by
        rw [hν, ← Units.val_mul, MonoidHom.div_apply, div_mul_cancel]
      have hx : (ν (gdet h) : ℂ) * (((ν (gdet h))⁻¹ : ℂˣ) : ℂ) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [eN]
      simp only [_root_.mul_inv_rev, Units.val_mul]
      linear_combination (-(β (gdet h) : ℂ) * (((ν (gdet g₀))⁻¹ : ℂˣ) : ℂ) *
          apow (gdet g₀) (-(Fintype.card (Fin (a + a')) : ℂ) / 2) * I * (ν (gdet h) : ℂ) *
          (((ν (gdet h))⁻¹ : ℂˣ) : ℂ)) * eA +
        (-(β (gdet h) : ℂ) * (((ν (gdet g₀))⁻¹ : ℂˣ) : ℂ) *
          apow (gdet g₀) (-(Fintype.card (Fin (a + a')) : ℂ) / 2) * I * apow (gdet h) (-(a : ℂ) / 2)) * hx
  refine ⟨funext key, fun H => ?_⟩
  have h1 := congrFun H 1
  rw [bigZetaIntegral_eq, map_one, Units.val_one, Matrix.mul_one,
    bigF_stdA hϖ c (g₀ := 1) (by rw [Units.val_one, matrixFirstColumnBlock_standardFrame_eq_one]), matrixLastColumnBlock_standardFrame_eq_zero] at h1
  have h0 : (0 : k) ∈ cball (ϖ ^ c) := by simp [cball]
  simp [h0] at h1
