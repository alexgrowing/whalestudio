import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviNormalizesUnipotentVariant
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanIwasawaMinimalParabolic
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RationalUnipotentLeParabolic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstTermEqZeroOfFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstAlongCocompactUniqueStages
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientMeasureProductGroups
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice

def IsSliceFrame {D : D7} (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V) {m m' : ℕ}
    (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m)) (e : Fin m' → Fin m)
    (X' Y' : Matrix (Fin V'.rank) (Fin m') D.host.E) : Prop :=
  StrictMono e ∧ (∀ i, i ∉ upTo T ↔ i ∈ Set.range e) ∧
    frameMat V V' ι * X' = X.submatrix id e ∧ frameMat V V' ι * Y' = Y.submatrix id e

variable {D : D7} {V V' : HSp D} {ι : V'.V →ₗ[D.host.E] V.V}

abbrev prM (V V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V) : Matrix (Fin V'.rank) (Fin V.rank) D.host.E :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projMat D.sp.cm V' V ι

theorem repr_symm (V : HSp D) (a : Fin V.rank → D.host.E) (i : Fin V.rank) :
    V.frame.repr (V.frame.equivFun.symm a) i = a i := by
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

theorem hT_frame (V : HSp D) (a b : Fin V.rank → D.host.E) :
    V.hT (V.frame.equivFun.symm a) (V.frame.equivFun.symm b) = ∑ i, ∑ j, star (a i) * V.gram i j * b j := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]
  simp only [repr_symm]

theorem prM_mul_frameMat (hι : HSpace.IsIsomEmb V' V ι) : prM V V' ι * frameMat V V' ι = 1 :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projMat_embMat D.sp.cm V' V ι hι

theorem cT_frameMat_mul_gram :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram = V'.gram * prM V V' ι :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_projMat D.sp.cm V' V ι

theorem mat_eq (hι : HSpace.IsIsomEmb V' V ι) {s : GA D V' →* GA D V} (hs : ∀ h, EmbRel V V' ι (s h) h) (b : GA D V') :
    (matHom V (s b)).1 = 1 + HMul.hMul (HMul.hMul (adMat D.host.F (frameMat V V' ι)) ((matHom V' b).1 - 1)) (adMat D.host.F (prM V V' ι)) := by
  rw [(GlobalTheory.AutFunCompare.embRel_iff V V' ι hι (s b) b).1 (hs b)]
  rfl

theorem prM_mulVec_eq_zero {x : Fin V.rank → D.host.E}
    (h : ∀ v' : V'.V, V.hT (V.frame.equivFun.symm x) (ι v') = 0) : prM V V' ι *ᵥ x = 0 := by
  have hJ : IsUnit V'.gram.det := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V'
  have h1 : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V V' ι) * V.gram) *ᵥ x = 0 := by
    funext j
    have h2 : V.hT (ι (V'.frame j)) (V.frame.equivFun.symm x) = 0 :=
      (V.herm.eq (V.frame.equivFun.symm x) (ι (V'.frame j))).symm.trans (by rw [h]; simp)
    rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord] at h2
    simp only [repr_symm] at h2
    simp only [Pi.zero_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_) h2
    simp only [Formalism.UG.cT, frameMat, LinearMap.toMatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
    rfl
  rw [cT_frameMat_mul_gram, ← Matrix.mulVec_mulVec] at h1
  exact Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hJ) (h1.trans (Matrix.mulVec_zero _).symm)

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice
end
