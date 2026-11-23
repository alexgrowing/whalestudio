import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingDarbouxPairSetting
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.DblBox
open GlobalTheory.ThK.DblKer GlobalTheory.DblWeilCoord

noncomputable section

namespace GlobalTheory.DblHerm

theorem exists_isHerm_dbl : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ (n r s' : ℕ) (X : Spc F E n), X.IsHerm σ B r s' →
    ∀ X₂ : Spc F E (n + n), X₂.J = dblGram finSumFinEquiv X.J → X₂.L = sumLat finSumFinEquiv X.L X.L →
    (∀ w, X₂.θ w = blkMat finSumFinEquiv (X.θ w) (-X.θ w)) →
    ∃ bas, (Spc.mk X₂.J X₂.L X₂.θ bas).IsHerm σ B (r + s') (s' + r) := by
  intro F E _ _ _ _ _ σ B hB n r s W hW X₂ hJ hL hθ
  classical
  have hθ' : X₂.θ = fun w => blkMat finSumFinEquiv (W.θ w) (-W.θ w) := funext hθ
  rw [hJ, hL, hθ']
  haveI : Submodule.IsLattice E W.L := hW.lat
  have hex : ∀ v : B.P, ∃ β, IsSplitBasis (B.τ v) (sumLat finSumFinEquiv W.L W.L) β :=
    fun v => exists_isSplitBasis (B.τ v) _ hB.cm
  refine ⟨fun v => if h : v ∈ B.P then (hex ⟨v, h⟩).choose else 1, ⟨?_, ?_, inferInstance, ?_, ?_, ?_⟩⟩
  · intro i j
    show σ (dblGram finSumFinEquiv W.J j i) = dblGram finSumFinEquiv W.J i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [dblGram, blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
        Matrix.neg_apply, map_zero, map_neg, hW.herm]
  · intro w
    show HasSig ((dblGram finSumFinEquiv W.J).map (B.emb w).1) (r + s) (s + r)
    rw [dblGram, blkMat_map _ _ (map_zero _), Matrix.map_neg _ (map_neg _)]
    exact hasSig_dbl _ (hW.sig w)
  · intro y
    show y ∈ sumLat finSumFinEquiv W.L W.L ↔ ∀ x ∈ sumLat finSumFinEquiv W.L W.L,
      IsIntegral ℤ (form σ (dblGram finSumFinEquiv W.J) y x)
    refine ⟨fun hy x hx => ?_, fun H => ?_⟩
    · rw [← pairVec_eta finSumFinEquiv y] at hy ⊢
      rw [← pairVec_eta finSumFinEquiv x] at hx ⊢
      rw [pairVec_mem_sumLat] at hy hx
      rw [form_dblGram]
      exact ((hW.dual _).1 hy.1 _ hx.1).sub ((hW.dual _).1 hy.2 _ hx.2)
    · rw [← pairVec_eta finSumFinEquiv y, pairVec_mem_sumLat]
      constructor
      · refine (hW.dual _).2 fun x hx => ?_
        have h1 := H (pairVec finSumFinEquiv x 0) ((pairVec_mem_sumLat _).2 ⟨hx, zero_mem _⟩)
        rw [← pairVec_eta finSumFinEquiv y, form_dblGram, form_zero_right, sub_zero] at h1
        exact h1
      · refine (hW.dual _).2 fun x hx => ?_
        have h1 := H (pairVec finSumFinEquiv 0 x) ((pairVec_mem_sumLat _).2 ⟨zero_mem _, hx⟩)
        rw [← pairVec_eta finSumFinEquiv y, form_dblGram, form_zero_right, zero_sub] at h1
        simpa using h1.neg
  · intro w
    show IsCartan ((dblGram finSumFinEquiv W.J).map (B.emb w).1) (blkMat finSumFinEquiv (W.θ w) (-W.θ w))
    rw [dblGram, blkMat_map _ _ (map_zero _), Matrix.map_neg _ (map_neg _)]
    exact GlobalTheory.DblUnfoldCont.isCartan_dbl _ _ (hW.cartan w)
  · intro v
    show IsSplitBasis (B.τ v) (sumLat finSumFinEquiv W.L W.L) (if h : (v : Pl F) ∈ B.P then (hex ⟨v, h⟩).choose else 1)
    rw [dif_pos v.2]
    exact (hex v).choose_spec

end GlobalTheory.DblHerm
