import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedPartsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslateStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinUA

theorem hermA_neg_transpose {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (c : E ≃ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → GlobalTheory.AdLat.RA F E) :
    GlobalTheory.AdLat.hermA c (-Jᵀ) x y =
      -((fun b => GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (y b)) ⬝ᵥ
        ((J.map fun t => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] t : GlobalTheory.AdLat.RA F E)) *ᵥ x)) := by
  unfold GlobalTheory.AdLat.hermA
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply,
    TensorProduct.tmul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem hermA_mulVec {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (c : E ≃ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E))
    (h : (g.map (GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c))ᵀ *
      (J.map fun t => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] t : GlobalTheory.AdLat.RA F E)) * g =
      J.map fun t => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] t : GlobalTheory.AdLat.RA F E))
    (x y : Fin n → GlobalTheory.AdLat.RA F E) :
    GlobalTheory.AdLat.hermA c (-Jᵀ) (g *ᵥ x) (g *ᵥ y) = GlobalTheory.AdLat.hermA c (-Jᵀ) x y := by
  rw [hermA_neg_transpose, hermA_neg_transpose]
  congr 1
  have e : (fun b => GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c ((g *ᵥ y) b)) =
      (g.map (GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c)) *ᵥ
        (fun b => GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (y b)) := by
    funext b
    simp [Matrix.mulVec, dotProduct, map_sum]
  rw [e]
  conv_rhs => rw [← h]
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ (Matrix.transpose _),
    Matrix.vecMul_transpose]

theorem isUA_finHom : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (g : GA D V),
    GlobalTheory.UCls.IsUA (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ)
      ((finHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) := by
  intro D V g
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).1 (finHom V g).isUnit, fun x y => hermA_mulVec _ _ _ ?_ x y⟩
  have h : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) g.1.1 * JR (AF D.host.F) V.gram * g.1.1
      = JR (AF D.host.F) V.gram := g.2
  let φ := (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hc : ∀ t, D.sp.cm.sig t = IsCMField.complexConj D.host.E t :=
    (GlobalTheory.Member.latHat_eq_hat_and_gram D V).2.2.2.2.2.1
  have hφ : ∀ z, φ (sigR (AF D.host.F) D.sp.cm.sig z) =
      GlobalTheory.AdLat.sg (Af D.host.F) (IsCMField.complexConj D.host.E) (φ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a t => simp [φ, sigR, GlobalTheory.AdLat.sg, hc]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hJ : (JR (AF D.host.F) V.gram).map φ =
      V.gram.map fun t => ((1 : Af D.host.F) ⊗ₜ[D.host.F] t : Af D.host.F ⊗[D.host.F] D.host.E) := by
    ext a b
    simp [φ, JR, inclR]
  have h2 := congrArg (fun M => Matrix.map M φ) h
  simp only [Matrix.map_mul] at h2
  rw [hJ] at h2
  have hg : (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) g.1.1).map φ =
      ((g.1.1.map φ).map (GlobalTheory.AdLat.sg (Af D.host.F) (IsCMField.complexConj D.host.E)))ᵀ := by
    ext a b
    exact hφ _
  rw [hg] at h2
  exact h2

end GlobalTheory.FinUA
