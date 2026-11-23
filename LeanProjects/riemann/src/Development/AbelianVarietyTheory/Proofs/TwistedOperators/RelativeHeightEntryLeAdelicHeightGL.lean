import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneLeHtE

open NumberField

noncomputable section
namespace GlobalTheory.RatCount
open GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain Formalism.UG
open scoped TensorProduct NNReal

theorem nnnorm_entry_le_opNorm {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (i j : n) :
    ‖A i j‖₊ ≤ opNorm A := by
  unfold opNorm
  have h1 : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A (EuclideanSpace.single j 1)) i = A i j := by
    change ∑ d, A i d * (EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ n) d = A i j
    simp [EuclideanSpace.single_apply]
  have h2 := ContinuousLinearMap.le_opNNNorm (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) (EuclideanSpace.single j 1)
  rw [PiLp.nnnorm_single, nnnorm_one, mul_one] at h2
  rw [← h1]
  exact (PiLp.nnnorm_apply_le _ i).trans h2

theorem htE_entry_le_heightGL (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (N : ℕ) (γ : GL (Fin N) E) (i j : Fin N) :
    GlobalTheory.RatCount.htE F ((γ : Matrix (Fin N) (Fin N) E) i j) ≤
      GlobalTheory.AdelicU.heightGL F (Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ) := by
  classical
  set x : E := (γ : Matrix (Fin N) (Fin N) E) i j with hx
  set g := Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ with hg
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F),
      max 1 (absFin F v ((1 : Fv F v) ⊗ₜ[F] x)) ≤ htFin F v (bc (compFin F E v) g) := by
    intro v
    refine max_le (one_le_htOf _ _) (le_trans ?_ (le_htOf _ _))
    have he : ((bc (compFin F E v) g : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) i j = (1 : Fv F v) ⊗ₜ[F] x := by
      change compFin F E v ((1 : AF F) ⊗ₜ[F] x) = _
      simp [compFin, Algebra.TensorProduct.map_tmul]
    rw [← he]
    exact absFin_le_normFin F v _ i j
  have hinf : ∀ w : InfinitePlace F,
      max 1 (Finset.univ.sup fun τ : EmbOver E w => ‖τ.1 x‖₊) ≤ htInf F w (bc (compInf F E w) g) := by
    intro w
    refine max_le (one_le_htOf _ _) (le_trans ?_ (le_htOf _ _))
    refine Finset.sup_le fun τ _ => ?_
    have he : (((bc (compInf F E w) g : GL (Fin N) _) : Matrix (Fin N) (Fin N) _).map (infEmb τ)) i j = τ.1 x := by
      change infEmb τ (compInf F E w ((1 : AF F) ⊗ₜ[F] x)) = _
      simp [compInf, Algebra.TensorProduct.map_tmul, infEmb_tmul]
    rw [← he]
    exact (nnnorm_entry_le_opNorm _ i j).trans ((normInf_le_iff F w).1 le_rfl τ)
  unfold htE heightGL
  refine mul_le_mul' (Finset.prod_le_prod' fun w _ => hinf w) ?_
  have hg' := finite_mulSupport_htFin F g
  refine finprod_le_finprod' (hg'.subset fun v hv hv' => hv ?_) hg' hfin
  exact le_antisymm ((hfin v).trans (le_of_eq hv')) (le_max_left _ _)

end GlobalTheory.RatCount
