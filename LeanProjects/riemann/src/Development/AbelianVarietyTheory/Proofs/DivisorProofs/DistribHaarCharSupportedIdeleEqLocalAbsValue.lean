import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFormBox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ModuLocal

theorem infComp_eq_one {F : Type} [Field F] [NumberField F] {v : Pl F} {u : (AF F)ˣ}
    (hu : At (evFin F v) ((u : AF F) - 1)) (w : NumberField.InfinitePlace F) : (u : AF F).1 w = 1 := by
  have h := hu (pairA F 1 0) (by change evalV F v 0 = 0; exact map_zero _)
  have h' : (1 : Ainf F) * ((u : AF F).1 - 1) = 0 := congrArg Prod.fst h
  rw [one_mul, sub_eq_zero] at h'
  rw [h']
  rfl

theorem finComp_eq_one {F : Type} [Field F] [NumberField F] {v : Pl F} {u : (AF F)ˣ}
    (hu : At (evFin F v) ((u : AF F) - 1)) {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    (u : AF F).2 w = 1 := by
  have h := hu (pairA F 0 (GlobalTheory.AdelicU.singleFin w 1))
    (by change evalV F v (GlobalTheory.AdelicU.singleFin w 1) = 0; exact GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hw) 1)
  have h2 : GlobalTheory.AdelicU.singleFin w 1 * ((u : AF F).2 - 1) = 0 := congrArg Prod.snd h
  have h' := congrArg (evalV F w) h2
  rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul, map_sub, map_zero, sub_eq_zero] at h'
  rw [← (map_one (evalV F w) : evalV F w 1 = 1)]
  exact h'

end GlobalTheory.ModuLocal

theorem GlobalTheory.ModuLocal.distribHaarChar_eq_nabs_of_at : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (u : (AF F)ˣ), At (evFin F v) ((u : AF F) - 1) →
    ((MeasureTheory.distribHaarChar (AF F) u : NNReal) : ℝ) = GlobalTheory.SplitWeil.nabs (Fv F v) (Units.map (evFin F v : AF F →* Fv F v) u) := by
  intro F _ _ v u hu
  rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing F u, GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have hinf : (∏ w : NumberField.InfinitePlace F, ‖(u : AF F).1 w‖ ^ w.mult) = 1 :=
    Finset.prod_eq_one fun w _ => by rw [GlobalTheory.ModuLocal.infComp_eq_one hu w, norm_one, one_pow]
  have hfin : (∏ᶠ w : HeightOneSpectrum (𝓞 F), ‖(u : AF F).2 w‖) = ‖(u : AF F).2 v‖ :=
    finprod_eq_single _ v fun w hw => by rw [GlobalTheory.ModuLocal.finComp_eq_one hu hw, norm_one]
  have hloc := ((GlobalTheory.CompletionNorm.norm_nabs_valuation F v).1 (Units.map (evFin F v : AF F →* Fv F v) u)).1
  refine (congrArg₂ (· * ·) hinf hfin).trans ?_
  rw [one_mul]
  exact hloc
