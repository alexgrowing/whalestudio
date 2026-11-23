import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbBar
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH.StdInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compFin_finOne_smul' (v : HeightOneSpectrum (𝓞 F)) (z : AE F E) :
    compFin F E v (finOne F • z) = compFin F E v z := by
  have h1 : GlobalTheory.AdelicU.evFin F v (GlobalTheory.ThK.Dbl.finOne F) = 1 := by
    simp only [GlobalTheory.AdelicU.evFin, GlobalTheory.ThK.Dbl.finOne, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA, LinearMap.inr_apply]
    change (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = 1
    exact map_one _
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    rw [TensorProduct.smul_tmul']
    simp [GlobalTheory.AdelicU.compFin, h1]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy]

theorem absFin_compFin_le_one {z : AE F E} (hz : z ∈ intHat F E) (v : HeightOneSpectrum (𝓞 F)) :
    absFin F v (compFin F E v z) ≤ 1 := by
  let S : AddSubgroup (AE F E) :=
    { carrier := {z | GlobalTheory.AdelicU.absFin F v (GlobalTheory.AdelicU.compFin F E v z) ≤ 1}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [show GlobalTheory.AdelicU.compFin F E v (x + y) = GlobalTheory.AdelicU.compFin F E v x + GlobalTheory.AdelicU.compFin F E v y from map_add _ _ _]
        exact (GlobalTheory.AdelicU.absFin_add_le F v _ _).trans (max_le hx hy)
      zero_mem' := by
        simp only [Set.mem_ofPred_eq]
        rw [show GlobalTheory.AdelicU.compFin F E v 0 = 0 from map_zero _, GlobalTheory.AdelicU.absFin_zero]
        exact zero_le_one
      neg_mem' := fun {x} hx => by
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [show GlobalTheory.AdelicU.compFin F E v (-x) = -GlobalTheory.AdelicU.compFin F E v x from map_neg _ _, GlobalTheory.AdelicU.absFin_neg]
        exact hx }
  have hle : intHat F E ≤ S := by
    rw [GlobalTheory.ThK.Dbl.intHat, AddSubgroup.closure_le]
    rintro z ⟨a, -, ha, o, rfl⟩
    show GlobalTheory.AdelicU.absFin F v (GlobalTheory.AdelicU.compFin F E v _) ≤ 1
    have h2 : GlobalTheory.AdelicU.compFin F E v (a • (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) (o : E)) =
        (GlobalTheory.AdelicU.evFin F v a) ⊗ₜ[F] (o : E) := by
      simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, GlobalTheory.AdelicU.compFin, TensorProduct.smul_tmul']
    rw [h2]
    refine (GlobalTheory.AdelicU.absFin_tmul_le F v _ o).trans ?_
    exact nnnorm_le_one_iff_mem.mpr (ha v)
  exact hle hz

theorem absFin_inFrame_le_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n) (B : Base F E) (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)),
    IsStdK (σ := σ) (Y := Y) B b K → ∀ k ∈ K, ∀ (v : Pl F) (i j : Fin n ⊕ Fin n), absFin F v (compFin F E v (inFrame b k i j)) ≤ 1 := by
  intro F E _ _ _ _ _ σ n Y B b K hK k hk v i j
  have h : GlobalTheory.ThK.Dbl.finOne F • GlobalTheory.ThK.Dbl.inFrame b k i j ∈ GlobalTheory.ThK.Dbl.intHat F E :=
    ((hK k).1 hk).2 k (by simp) i j
  have h' := absFin_compFin_le_one h v
  rwa [compFin_finOne_smul'] at h'

end GlobalTheory.CompanionTheory.GodementH.StdInt

end
