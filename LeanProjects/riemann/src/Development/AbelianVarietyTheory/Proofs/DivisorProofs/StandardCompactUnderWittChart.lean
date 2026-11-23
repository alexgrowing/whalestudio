import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

noncomputable section

namespace GlobalTheory.SWLink

open GlobalTheory.AdelicU in

theorem mem_stabArch_one_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hc : IsCMExt F E σ) {k : ℕ} (J : Matrix (Fin k) (Fin k) E) (w : InfinitePlace F)
    (τ : EmbOver E w) (x : GArch σ J w) :
    x ∈ stabArch σ J w (Formalism.UG.bc (compInf F E w) 1) ↔
      (matHom _ σ J x).1.map (infEmb τ) ∈ Matrix.unitaryGroup (Fin k) ℂ := by
  rw [mem_stabArch, map_one, inv_one, one_mul, mul_one, Matrix.mem_unitaryGroup_iff']
  generalize matHom _ σ J x = y
  change Formalism.UG.cT _ y.1 * 1 * y.1 = 1 ↔ _
  rw [← (Matrix.map_injective (infEmb_bijective hc τ).1).eq_iff]
  beta_reduce
  rw [mul_one, Matrix.map_mul, Frames.map_cT_sigR hc, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.star_eq_conjTranspose]

open GlobalTheory.AdelicU in

theorem mem_levelAll_std_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hc : IsCMExt F E σ) {k : ℕ} (J : Matrix (Fin k) (Fin k) E) (x : GAd σ J) :
    x ∈ levelAll σ J (stdLattice E k) 1 ↔
      (∀ v i j, compFin F E v ((matHom _ σ J x).1 i j) ∈ intLoc F E v ∧
        compFin F E v ((matHom _ σ J x⁻¹).1 i j) ∈ intLoc F E v) ∧
      ∀ (w : InfinitePlace F) (τ : EmbOver E w),
        (matHom _ σ J x).1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf τ) ∈ Matrix.unitaryGroup (Fin k) ℂ := by
  rw [mem_levelAll]
  refine and_congr (forall_congr' fun v => ?_) (forall_congr' fun w => ?_)
  · rw [mem_stabLoc_stdLattice_iff, ← map_inv (proj σ J v)]
    simp only [forall_and]
    exact Iff.rfl
  · have hm : ∀ τ : EmbOver E w, (matHom _ σ J x).1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf τ) =
        (matHom _ σ J (projArch σ J w x)).1.map (infEmb τ) := fun τ => Matrix.ext fun _ _ => rfl
    simp only [hm, ← mem_stabArch_one_iff hc J w, forall_const]

theorem stdK_iff : ∀ (D : D7) (n : ℕ) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E) (κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n), IsChartW T κ → ∀ K : Subgroup (UD D J₂), IsStdK D.sp.cm.sig T K → ∀ g : UD D J₂, g ∈ K ↔ κ g ∈ GlobalTheory.StdUnn.K D n := by
  intro D n J₂ T κ hκ K hK g
  rw [hK g, ← hκ g, ← hκ g⁻¹, map_inv]
  exact (mem_levelAll_std_iff (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.StdUnn.Jst D n) (κ g)).symm

end GlobalTheory.SWLink

end
