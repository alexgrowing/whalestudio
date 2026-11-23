import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFHypS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFApxDom
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDJDJComm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbGermRateLowBOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jf_mem_ffkb {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hF : ∀ (A : ℝ) (m : ℕ), B.InCC A m F) :
    B.JF p.T.base F ∈ FFKB p := by
  set Bs := p.T.base
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW'
  have hN := bessel_unipotent_equiv_holds Wp Wq P.k P.r Bs.z Bs.z' cStd Bs.π Bs.π' Bs.μW Bs.μN Bs.μW' F Bs.z_mem Bs.z'_mem
    Bs.haarN.conc (fun n₀ h => Bs.haarN.left n₀ h)
  refine ⟨fun g₀ hg₀ => Formalism.FourierDecayAlt.P5.Rad.jf_smoothLev Bs F hF g₀ ⟨hg₀.1, (CutMP.jdc_om_of _ _ hg₀.1.1 hg₀.2).2⟩, ?_, ?_, ?_⟩
  · intro g _ n hn
    have e := hN g n hn.1 1 WeylGroupFacts.mem_n_one
    rw [Matrix.mul_one, BesselCapelliCommutation.psi_one Bs.z'_mem, mul_one] at e
    exact e
  · intro g _ n hn
    have e := hN g 1 WeylGroupFacts.mem_n_one n hn.1
    rw [Matrix.one_mul, BesselCapelliCommutation.psi_one Bs.z_mem, one_mul] at e
    exact e
  · intro g _ h hh h' hh'
    exact Formalism.FourierDecayAlt.P5.jf_uEquiv Bs F g hh hh'

theorem normal_form_jacobi_cutoff : NFJCutFF := by
  intro Wp Wq _ _ _ _ _ _ P p f hf n
  apply jf_mem_ffkb
  have hcomp : IsCompact {g : B.Mat P.k P.r | B.gN g ≤ 2 * ((n : ℝ) + 1)} := by
    have hcont : Continuous (fun g : B.Mat P.k P.r => B.gN g) := by
      unfold B.gN
      exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
        continuous_finsetSum _ fun j _ =>
          Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))
    have hsub : {g : B.Mat P.k P.r | B.gN g ≤ 2 * ((n : ℝ) + 1)}
        ⊆ Metric.closedBall (0 : B.Mat P.k P.r) (2 * ((n : ℝ) + 1)) := by
      intro g hg
      rw [Metric.mem_closedBall, dist_zero_right]
      refine (Matrix.norm_le_iff (by positivity)).mpr fun i j => le_trans ?_ hg
      unfold B.gN
      rw [← Real.sqrt_sq (norm_nonneg (g i j))]
      apply Real.sqrt_le_sqrt
      rw [← Complex.normSq_eq_norm_sq]
      calc Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j') :=
            Finset.single_le_sum (f := fun j' => Complex.normSq (g i j'))
              (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
        _ ≤ ∑ i', ∑ j', Complex.normSq (g i' j') :=
            Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
              (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    exact (isCompact_closedBall _ _).of_isClosed_subset (isClosed_le hcont continuous_const) hsub
  intro A m
  refine Formalism.FourierDecayAlt.P.JFxG.cptInCC_G (Formalism.FourierDecayAlt.P.CutBP.cutN_ckOn hf n) hcomp ?_ A m
  intro g hg hgC
  by_contra hne
  exact hgC (Formalism.FourierDecayAlt.P.FormNormSumIdentities.cutN_supp f n g hg hne)

end Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
