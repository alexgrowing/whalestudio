import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructureStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteAdelicLatticeTransportLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRationalRealTrivialAtCongruentFactorStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevelStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionTranslatesThetaByUnitScalar
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelDatumVectorEqThetaOfTestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilPairLevelTrivialMapsLevelVectorStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionFixesLevelVectorUpToUnit
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeakWeilRepCarriesDerivativesVacuaFockVectorsStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.Red

variable {D : D7}

theorem mt_one' (V : HSp D) : mt V 1 = 1 := by rw [Formalism.L2.Theta.mt, map_one]; rfl

theorem fmt_one (V : HSp D) : fmt V 1 = 1 := by rw [fmt, mt_one']; exact Matrix.map_one _ (map_zero _) (map_one _)

theorem fmtC_one (V : HSp D) : fmtC V 1 = 1 := by rw [fmtC, mt_one', cM, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]

theorem trivAt_one (V : HSp D) (I : Ideal (𝓞 D.host.F)) : TrivAt V I 1 := by
  intro v _ ε _ i j
  simp [mt_one']

theorem isMov_one {k : ℕ} (L : Lt D.host.E k) : IsMov 1 L L := by
  intro u
  exact ⟨fun h => ⟨u, h, (Matrix.one_mulVec u).symm⟩, by rintro ⟨u₀, h, rfl⟩; rwa [Matrix.one_mulVec]⟩

theorem stdL_fg (n : ℕ) : (stdL D.host.E n).FG := by
  unfold stdL
  exact Submodule.fg_span (Set.finite_range _)

theorem compAt_of_fin (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (h : GA D V) (hh : h ∈ GfC V) :
    compAt θ τ (mt V h) = 1 := by
  unfold GfC infHom at hh
  unfold compAt
  rw [MonoidHom.mem_ker] at hh
  have h1 : (Formalism.L2.Theta.mt V h).map (infPart D) = 1 := by
    have := congrArg Units.val hh
    exact this
  have h2 : ((Formalism.L2.Theta.mt V h).map fun a => θ τ (infPart D a)) =
      ((Formalism.L2.Theta.mt V h).map (infPart D)).map (θ τ) := by
    rw [Matrix.map_map]; rfl
  rw [h2, h1, Matrix.map_one _ (map_zero _) (map_one _)]

variable {S T : HSp D}

theorem om_fvec (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (hW : IsWeak C.ψ S T om)
    (h : GA D S) (hh : h ∈ GfC S) (g : GA D T) (f : WO S T → ℂ) (hf : C.IsTh f) (B : C.Bas) (hB : C.IsB B)
    (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    om (h, g) (C.fvec B f Q) = C.fvec (C.mvB g B) (om (h, g) f) Q := by
  have hc : (fun τ => compAt C.θ τ (Formalism.L2.Theta.mt S h)) = fun _ => (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) :=
    funext fun τ => compAt_of_fin C.θ τ S h hh
  rw [((GlobalTheory.T.weakWeilRep_carries_derivatives_vacua_fockVectors D S T C om hW h g f hf).2 B hB).2 Q, hc]
  rfl

theorem levK_one (C : Ctx S T) (Lv : SW.Level C.X) (k : GA D T) (hk : k ∈ GfC T)
    (hm : IsMov (fmt T k) C.X.Λ C.X.Λ)
    (hc : ∀ u ∈ hatV C.X.Λ, fmt T k *ᵥ u - u ∈ hatV (Lv.𝔪 • C.X.Λ)) : C.LevK Lv k 1 := by
  refine ⟨hk, hm, 1, by simp, fun i => ?_⟩
  have hβ : toAf (Lv.β i) ∈ hatV C.X.Λ :=
    ((GlobalTheory.T.finiteAdelicLatticeTransport_laws D T.rank C.X.Λ ⟨C.X.Λ_fg, C.X.Λ_span⟩).1 (Lv.β i)).2 (Lv.β_mem i)
  have hsum : (∑ j, (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) j i • Lv.β j) = Lv.β i := by
    simp [Matrix.one_apply]
  rw [hsum]
  exact hc _ hβ

end GlobalTheory.Ker.Red
