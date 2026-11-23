import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralTensorOfIntegrable
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
noncomputable section

namespace GlobalTheory.TrConv

variable {D : D7}

theorem finFn_eq_tensorFin (V : HSp D) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) (y : GfC V) :
    finFn V ff y = tensorFin D.sp.cm.sig V.gram ff ((finPtsEquiv D.sp.cm.sig V.gram).symm y) := by
  unfold finFn tensorFin
  refine finprod_congr fun v => congrArg (ff v) ?_
  have := proj_ofFin D.sp.cm.sig V.gram v ((finPtsEquiv D.sp.cm.sig V.gram).symm y)
  rw [← this]
  congr 1
  exact (congrArg Subtype.val ((finPtsEquiv D.sp.cm.sig V.gram).apply_symm_apply y)).symm

theorem conv_finFn : ∀ (D : D7) (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∀ a b, IsFinFamily D.sp.cm.sig V.gram (frameLat V) a → IsFinFamily D.sp.cm.sig V.gram (frameLat V) b → IsFinFamily D.sp.cm.sig V.gram (frameLat V) (fun v => conv (μf v) (a v) (b v)) ∧ finFn V (fun v => conv (μf v) (a v) (b v)) = conv ν (finFn V a) (finFn V b) ∧ finFn V a ∈ GlobalTheory.SplitWeil.SB (GfC V) := by
  intro D V μf _ h1 ν hν a b ha hb
  refine ⟨GlobalTheory.Orb.IsFinFamily.conv ha hb h1, funext fun y => ?_, ?_⟩
  · have hfam := GlobalTheory.Orb.IsFinFamily.mul_translate ha hb (y : GA D V)
    have hint : (fun x : GfC V => finFn V a x * finFn V b (x⁻¹ * y)) =
        finFn V (fun v x => a v x * b v (x⁻¹ * proj D.sp.cm.sig V.gram v (y : GA D V))) := by
      funext x
      have e1 := ha.finite_mulSupport ((finPtsEquiv D.sp.cm.sig V.gram).symm x)
      have e2 := hb.finite_mulSupport ((finPtsEquiv D.sp.cm.sig V.gram).symm (x⁻¹ * y))
      rw [finFn_eq_tensorFin, finFn_eq_tensorFin]
      unfold finFn
      unfold tensorFin
      rw [← finprod_mul_distrib e1 e2]
      refine finprod_congr fun v => ?_
      have p1 := proj_ofFin D.sp.cm.sig V.gram v ((finPtsEquiv D.sp.cm.sig V.gram).symm x)
      have p2 := proj_ofFin D.sp.cm.sig V.gram v ((finPtsEquiv D.sp.cm.sig V.gram).symm (x⁻¹ * y))
      have q1 : ofFin D.sp.cm.sig V.gram ((finPtsEquiv D.sp.cm.sig V.gram).symm x) = (x : GA D V) :=
        congrArg Subtype.val ((finPtsEquiv D.sp.cm.sig V.gram).apply_symm_apply x)
      have q2 : ofFin D.sp.cm.sig V.gram ((finPtsEquiv D.sp.cm.sig V.gram).symm (x⁻¹ * y)) = ((x⁻¹ * y : GfC V) : GA D V) :=
        congrArg Subtype.val ((finPtsEquiv D.sp.cm.sig V.gram).apply_symm_apply _)
      rw [q1] at p1
      rw [q2] at p2
      rw [← p1, ← p2]
      simp [map_mul, map_inv]
    symm
    show ∫ x, finFn V a x * finFn V b (x⁻¹ * y) ∂ν = _
    rw [hint, hν.2 _ hfam]
    rfl
  · have hm := ha.tensorFin_mem
    rw [show finFn V a = tensorFin D.sp.cm.sig V.gram a ∘ (finPtsEquiv D.sp.cm.sig V.gram).symm from
      funext fun y => finFn_eq_tensorFin V a y]
    exact ⟨hm.1.comp_continuous (finPtsEquiv D.sp.cm.sig V.gram).symm.continuous,
      hm.2.comp_homeomorph (finPtsEquiv D.sp.cm.sig V.gram).symm.toHomeomorph⟩

end GlobalTheory.TrConv
