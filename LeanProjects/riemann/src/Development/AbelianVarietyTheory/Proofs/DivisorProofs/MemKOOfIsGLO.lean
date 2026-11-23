import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFrameDatumZetaIntegralEqSmaller

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable local instance measFvZetaA {F : Type} [Field F] [NumberField F] (v : Pl F) : MeasurableSpace (Fv F v) := borel _

local instance borelFvZetaA {F : Type} [Field F] [NumberField F] (v : Pl F) : BorelSpace (Fv F v) := ⟨rfl⟩

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.StdPairZeta
open GlobalTheory.OneSquareZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem blk₁_mul {m a a' : ℕ} (M : Matrix (Fin m) (Fin a) k) (X : Matrix (Fin a) (Fin (a + a')) k) :
    blk₁ (M * X) = M * blk₁ X := by
  ext i j; simp [blk₁, Matrix.mul_apply]

theorem blk₂_mul {m a a' : ℕ} (M : Matrix (Fin m) (Fin a) k) (X : Matrix (Fin a) (Fin (a + a')) k) :
    blk₂ (M * X) = M * blk₂ X := by
  ext i j; simp [blk₂, Matrix.mul_apply]

theorem val_gdet {a : ℕ} (g : GL (Fin a) k) : ((gdet g : kˣ) : k) = g.val.det := by
  first | rfl | exact Matrix.GeneralLinearGroup.val_det_apply g

theorem isGLO_of_mem_KO {a : ℕ} {g : GL (Fin a) k} (hg : g ∈ KO k (Fin a)) : g.val.det ≠ 0 ∧ IsGLO g.val := by
  have hv : valuation k g.val.det = 1 := by rw [← val_gdet]; exact GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO hg
  exact ⟨fun h => by simp [h] at hv, ((GlobalTheory.SplitFlip.mem_KO_iff g).1 hg).1, hv⟩

theorem mem_KO_of_isGLO {a : ℕ} (g : GL (Fin a) k) (h : IsGLO g.val) : g ∈ KO k (Fin a) := by
  obtain ⟨hM, hd⟩ := h
  let A : Matrix (Fin a) (Fin a) 𝒪[k] := fun i j => ⟨g.val i j, hM i j⟩
  have e : (algebraMap 𝒪[k] k).mapMatrix A = g.val := rfl
  have hu : IsUnit A.det := by
    refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 ?_
    rw [RingHom.map_det, e, hd]
  obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det A).2 hu
  refine ⟨u, Units.ext ?_⟩
  change (algebraMap 𝒪[k] k).mapMatrix u.val = g.val
  rw [hu', e]

theorem mul_mem_cball {n m p : ℕ} {s : kˣ} {M : Matrix (Fin n) (Fin m) k} {Y : Matrix (Fin m) (Fin p) k}
    (hM : ∀ i j, M i j ∈ 𝒪[k]) (hY : ∀ i j, Y i j ∈ GlobalTheory.SplitWeil.cball s) :
    ∀ i j, (M * Y) i j ∈ GlobalTheory.SplitWeil.cball s := by
  intro i j
  simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, Matrix.mul_apply] at hY ⊢
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact (mul_le_mul' ((Valuation.mem_integer_iff _ _).1 (hM i l)) (hY l j)).trans_eq (one_mul _)

variable [MeasurableSpace k] [BorelSpace k]

theorem bigF_stdA_zero (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (X : Matrix (Fin a) (Fin (a + a')) k)
    (hX : (blk₁ X).det = 0) : bigF (haarVol (KO k (Fin a))) ϖ ν (stdA ν ϖ c a a') X = 0 := by
  have h0 : ∀ g : Matrix (Fin a) (Fin a) k, stdA ν ϖ c a a' (g * X) = 0 := by
    intro g
    unfold stdA
    rw [dif_neg]
    rintro ⟨h, -⟩
    exact h (by rw [blk₁_mul, Matrix.det_mul, hX, mul_zero])
  simp [bigF, shellSum, shell, h0]

theorem bigF_stdA_eq (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (hϖ : IsUnif ϖ) (X : Matrix (Fin a) (Fin (a + a')) k)
    (g₁ : GL (Fin a) k) (hg₁ : g₁.val = blk₁ X) :
    bigF (haarVol (KO k (Fin a))) ϖ ν (stdA ν ϖ c a a') X =
      (((ν (gdet g₁))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₁) (-((Fintype.card (Fin (a + a')) : ℂ) / 2)) *
        Set.indicator {M : Matrix (Fin a) (Fin a') k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1 ((g₁⁻¹).val * blk₂ X) := by
  set N : ℂ := (Fintype.card (Fin (a + a')) : ℂ) / 2 with hN
  set Y := (g₁⁻¹).val * blk₂ X with hY
  set C : ℂ := (((ν (gdet g₁))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₁) (-N) *
      Set.indicator {M : Matrix (Fin a) (Fin a') k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1 Y with hC
  set S : Set (GL (Fin a) k) := (fun g => g * g₁) ⁻¹' (KO k (Fin a) : Set (GL (Fin a) k)) with hSdef
  have hSm : @MeasurableSet (GL (Fin a) k) Units.instMeasurableSpace S := by
    letI : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
    haveI : BorelSpace (GL (Fin a) k) := borel_GL
    exact (isOpen_KO.preimage (continuous_mul_right _)).measurableSet
  have hS1 : (haarVol (KO k (Fin a))).real S = 1 := by
    simp [hSdef, Measure.real, measure_preimage_mul_right, haarVol_self isOpen_KO le_rfl]
  have hint : ∀ g : GL (Fin a) k, stdA ν ϖ c a a' (g.val * X) * (ν (gdet g) : ℂ) * apow (gdet g) N =
      S.indicator (fun _ => C) g := by
    intro g
    have h1 : blk₁ (g.val * X) = (g * g₁).val := by rw [blk₁_mul, Units.val_mul, hg₁]
    have h2 : blk₂ (g.val * X) = (g * g₁).val * Y := by
      rw [blk₂_mul, hY, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel_right]
    by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem hg]
      have hκ : g * g₁ ∈ KO k (Fin a) := hg
      obtain ⟨hdet, hglo⟩ := isGLO_of_mem_KO hκ
      have hv : valuation k ((gdet (g * g₁) : kˣ) : k) = 1 := GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO hκ
      have hinv : (g * g₁)⁻¹ ∈ KO k (Fin a) := inv_mem hκ
      have hYiff : (∀ i j, ((g * g₁).val * Y) i j ∈ cball (ϖ ^ c)) ↔ ∀ i j, Y i j ∈ cball (ϖ ^ c) := by
        constructor
        · intro h
          have e : Y = ((g * g₁)⁻¹).val * ((g * g₁).val * Y) := by
            rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
          rw [e]; exact mul_mem_cball ((GlobalTheory.SplitFlip.mem_KO_iff _).1 hinv).1 h
        · exact mul_mem_cball ((GlobalTheory.SplitFlip.mem_KO_iff _).1 hκ).1
      have hap : apow (gdet g) N = apow (gdet g₁) (-N) := by
        have : gdet g = gdet (g * g₁) * (gdet g₁)⁻¹ := by rw [gdet_mul]; group
        rw [this, apow_mul, apow_of_valuation_eq_one hv, one_mul, apow_inv]
      unfold stdA
      by_cases hc : ∀ i j, Y i j ∈ cball (ϖ ^ c)
      · have hcond : (blk₁ (g.val * X)).det ≠ 0 ∧ IsGLO (blk₁ (g.val * X)) ∧
            ∀ i j, blk₂ (g.val * X) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
          rw [h1, h2]; exact ⟨hdet, hglo, hYiff.2 hc⟩
        have hmk : Units.mk0 _ hcond.1 = gdet g * gdet g₁ := by
          rw [← gdet_mul]; exact Units.ext (by rw [Units.val_mk0, val_gdet, h1])
        rw [dif_pos hcond, hC, Set.indicator_of_mem (show Y ∈ {M : Matrix (Fin a) (Fin a') k |
          ∀ i j, M i j ∈ cball (ϖ ^ c)} from hc), Pi.one_apply, mul_one, hmk, hap, map_mul, mul_inv]
        simp only [Units.val_mul, Units.val_inv_eq_inv_val]
        have h3 := (ν (gdet g)).ne_zero
        linear_combination ((ν (gdet g₁) : ℂ))⁻¹ * apow (gdet g₁) (-N) * inv_mul_cancel₀ h3
      · have hneg : ¬ ((blk₁ (g.val * X)).det ≠ 0 ∧ IsGLO (blk₁ (g.val * X)) ∧
            ∀ i j, blk₂ (g.val * X) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) := by
          rintro ⟨-, -, h⟩
          rw [h2] at h
          exact hc (hYiff.1 h)
        rw [dif_neg hneg, hC, Set.indicator_of_notMem (show Y ∉ {M : Matrix (Fin a) (Fin a') k |
          ∀ i j, M i j ∈ cball (ϖ ^ c)} from hc)]
        simp
    · rw [Set.indicator_of_notMem hg]
      have hneg : ¬ ((blk₁ (g.val * X)).det ≠ 0 ∧ IsGLO (blk₁ (g.val * X)) ∧
          ∀ i j, blk₂ (g.val * X) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) := by
        rintro ⟨-, hglo, -⟩
        rw [h1] at hglo
        exact hg (mem_KO_of_isGLO _ hglo)
      unfold stdA
      rw [dif_neg hneg, zero_mul, zero_mul]
  have hshell : ∀ m : {m : Fin a → ℤ // Antitone m}, shell (haarVol (KO k (Fin a))) ϖ ν N
      (fun M => stdA ν ϖ c a a' (M * X)) m.1 = (haarVol (KO k (Fin a))).real (shellSet ϖ m.1 ∩ S) • C := by
    intro m
    rw [shell]
    simp_rw [hint]
    have e1 := setIntegral_indicator (μ := haarVol (KO k (Fin a))) (s := shellSet ϖ m.1)
      (f := fun _ => C) hSm
    rw [e1, setIntegral_const]
  obtain ⟨⟨m₀, hm₀⟩, hmem, huniq⟩ := exists_unique_shell hϖ g₁⁻¹
  have hsub : S ⊆ shellSet ϖ m₀ := by
    intro g hg
    obtain ⟨x, hx, y, hy, e⟩ := mem_shellSet.1 hmem
    refine mem_shellSet.2 ⟨g * g₁ * x, mul_mem hg hx, y, hy, ?_⟩
    calc g = g * g₁ * g₁⁻¹ := by group
      _ = _ := by rw [e]; simp only [mul_assoc]; try rfl
  rw [bigF, shellSum, finsum_eq_single _ ⟨m₀, hm₀⟩]
  · rw [hshell, Set.inter_eq_right.2 hsub, hS1, one_smul]
  · intro m hm
    rw [hshell]
    have : shellSet ϖ m.1 ∩ S = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun g ⟨hg1, hg2⟩ => hm (huniq m ?_)
      obtain ⟨x, hx, y, hy, e⟩ := mem_shellSet.1 hg1
      refine mem_shellSet.2 ⟨(g * g₁)⁻¹ * x, mul_mem (inv_mem hg2) hx, y, hy, ?_⟩
      calc g₁⁻¹ = (g * g₁)⁻¹ * g := by group
        _ = _ := by rw [e]; simp only [mul_assoc]; try rfl
    simp [this]

end GlobalTheory.StdPairZeta

open GlobalTheory.StdPairZeta in

theorem GlobalTheory.StdPairZeta.bigF_stdA : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ), IsUnif ϖ →
    (∀ X : Matrix (Fin a) (Fin (a + a')) k, (blk₁ X).det = 0 →
      bigF (haarVol (KO k (Fin a))) ϖ ν (stdA ν ϖ c a a') X = 0) ∧
    ∀ (X : Matrix (Fin a) (Fin (a + a')) k) (g₁ : GL (Fin a) k), g₁.val = blk₁ X →
      bigF (haarVol (KO k (Fin a))) ϖ ν (stdA ν ϖ c a a') X =
        (((ν (gdet g₁))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₁) (-((Fintype.card (Fin (a + a')) : ℂ) / 2)) *
          Set.indicator {M : Matrix (Fin a) (Fin a') k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1 ((g₁⁻¹).val * blk₂ X) := by
  intro k _ _ _ _ _ _ ν ϖ c a a' hϖ
  exact ⟨fun X hX => bigF_stdA_zero ν ϖ c a a' X hX, fun X g₁ hg₁ => bigF_stdA_eq ν ϖ c a a' hϖ X g₁ hg₁⟩
