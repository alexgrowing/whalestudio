import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchAt
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.WeilDirBound

open GlobalTheory.AdelicU

theorem norm_entry_le_opNorm {m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) (i k : m) :
    ‖A i k‖ ≤ (opNorm A : ℝ) := by
  have h1 : Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A (EuclideanSpace.single k 1) =
      WithLp.toLp 2 (A *ᵥ Pi.single k 1) := Matrix.toEuclideanCLM_toLp A _
  have h2 : (A *ᵥ Pi.single k (1 : ℂ)) i = A i k := by simp
  calc ‖A i k‖ = ‖(Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A (EuclideanSpace.single k 1)).ofLp i‖ := by
        rw [h1, ← h2]
    _ ≤ ‖Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A (EuclideanSpace.single k 1)‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A‖ * ‖EuclideanSpace.single k (1 : ℂ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = (opNorm A : ℝ) := by rw [EuclideanSpace.norm_single, norm_one, mul_one]; rfl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem norm_piInf_entry_le_heightGL {m : Type} [Fintype m] [DecidableEq m] (g : GL m (AF F ⊗[F] E))
    (w : InfinitePlace F) (τ : EmbOver E w) (i k : m) :
    ‖piInf τ ((g : Matrix m m (AF F ⊗[F] E)) i k)‖ ≤ (heightGL F g : ℝ) := by
  have e : piInf τ ((g : Matrix m m (AF F ⊗[F] E)) i k) =
      (((Formalism.UG.bc (compInf F E w) g : GL m (w.Completion ⊗[F] E)) : Matrix m m _).map (infEmb τ)) i k := rfl
  rw [e]
  refine (norm_entry_le_opNorm _ i k).trans ?_
  have h1 : opNorm (((Formalism.UG.bc (compInf F E w) g : GL m (w.Completion ⊗[F] E)) : Matrix m m _).map (infEmb τ))
      ≤ heightGL F g := by
    refine ((normInf_le_iff F w).1 le_rfl τ).trans ((le_htOf _ _).trans ?_)
    refine le_trans ?_ (le_mul_of_one_le_right' (one_le_finprod' fun _ => one_le_htOf _ _))
    exact Finset.single_le_prod' (f := fun w => htInf F w (Formalism.UG.bc (compInf F E w) g))
      (fun _ _ => one_le_htOf _ _) (Finset.mem_univ w)
  exact_mod_cast h1

end GlobalTheory.WeilDirBound

end

namespace GlobalTheory.WeilDirBound

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem norm_piInf_actAB_le (σ : E →ₐ[F] E) (n d : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E) (p : UA σ J × UA σ J')
    (x : Matrix (Fin n) (Fin d) (AE F E)) (B : ℝ) (hB : 0 ≤ B)
    (hx : ∀ (w : InfinitePlace F) (τ : EmbOver E w) k l, ‖piInf τ (x k l)‖ ≤ B) :
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) i j,
      ‖piInf τ (actAB (cA σ) p x i j)‖ ≤ n * d * ((ht p.1 : ℝ) * ht p.2) * B := by
  intro w τ i j
  set g : GL (Fin n) (AF F ⊗[F] E) := (p.1 : GL (Fin n) (AF F ⊗[F] E)) with hg
  set h : GL (Fin d) (AF F ⊗[F] E) := (p.2 : GL (Fin d) (AF F ⊗[F] E)) with hh
  have hg1 : (ht p.1 : ℝ) = heightGL F g := rfl
  have hh1 : (ht p.2 : ℝ) = heightGL F h := rfl
  have e : actAB (cA σ) p x i j = ∑ l, ∑ k,
      (g : Matrix (Fin n) (Fin n) _) i k * x k l * (h : Matrix (Fin d) (Fin d) _) j l := by
    simp only [actAB, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rfl
  have hG := fun k => norm_piInf_entry_le_heightGL g w τ i k
  have hH := fun l => norm_piInf_entry_le_heightGL h w τ j l
  have hG0 : (0 : ℝ) ≤ heightGL F g := NNReal.coe_nonneg _
  have hH0 : (0 : ℝ) ≤ heightGL F h := NNReal.coe_nonneg _
  rw [e, hg1, hh1]
  calc ‖piInf τ (∑ l, ∑ k, (g : Matrix (Fin n) (Fin n) _) i k * x k l * (h : Matrix (Fin d) (Fin d) _) j l)‖
      ≤ ∑ l : Fin d, ∑ k : Fin n, ((heightGL F g : ℝ) * heightGL F h * B) := by
        rw [map_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [map_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [map_mul, map_mul, norm_mul, norm_mul]
        calc ‖piInf τ ((g : Matrix (Fin n) (Fin n) _) i k)‖ * ‖piInf τ (x k l)‖ *
              ‖piInf τ ((h : Matrix (Fin d) (Fin d) _) j l)‖
            ≤ (heightGL F g : ℝ) * B * heightGL F h :=
              mul_le_mul (mul_le_mul (hG k) (hx w τ k l) (norm_nonneg _) hG0) (hH l) (norm_nonneg _)
                (mul_nonneg hG0 hB)
          _ = (heightGL F g : ℝ) * heightGL F h * B := by ring
    _ = n * d * ((heightGL F g : ℝ) * heightGL F h) * B := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end GlobalTheory.WeilDirBound

theorem GlobalTheory.WeilDirBound.norm_piInf_actAB_le_target : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E) (p : UA σ J × UA σ J')
    (x : Matrix (Fin n) (Fin d) (AE F E)) (B : ℝ), 0 ≤ B →
    (∀ (w : InfinitePlace F) (τ : EmbOver E w) k l, ‖piInf τ (x k l)‖ ≤ B) →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) i j,
      ‖piInf τ (actAB (cA σ) p x i j)‖ ≤ n * d * ((ht p.1 : ℝ) * ht p.2) * B :=
  fun F E _ _ _ _ _ σ n d J J' p x B hB hx => GlobalTheory.WeilDirBound.norm_piInf_actAB_le σ n d J J' p x B hB hx
