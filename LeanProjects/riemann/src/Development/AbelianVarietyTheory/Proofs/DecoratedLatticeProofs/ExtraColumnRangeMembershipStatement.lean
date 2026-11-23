import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtraColumnRangeMembership
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extra_column_range_membership : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (g : GlobalTheory.Fam.Geo D) t j (h : j + 2 * 0 + 2 = D.R.m) (F : CXP (pk W) (lvP W) t), ∃ h' : F.1 ∈ LinearMap.range ((pk W).cX.toMap (pk W).prX ∘ₗ ((pk W).HX t).e), (GlobalTheory.Published.CuspRapidDecay → (ioXT (pk W) t j h ⟨F.1, h'⟩).1 ∈ CP (pk W) (lvP W) t (j + 1)) ∧ ∀ v, IsStepVecOf (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) ((pk W).ΛY (j + 1)) (pk W).ΛX ((pk W).βY (j + 1)) (pk W).βX ((pk W).datYt t (j + 1) (lvP W)) ((pk W).chi D.R.m) ((pk W).Q t) ((pk W).xiR t) (vacT (pk W) j h) v → ∀ Q x, liftS (omT (pk W) t j h) ((pk W).νX t) ((pk W).fdX t) (F.1 x) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) v Q) = (Nat.card (lvP W).H : ℂ) • (ioXT (pk W) t j h ⟨F.1, h'⟩).1 ((commOf (pk W) u g).ItT j h Q x) := by
  first | exact @GlobalTheory.TopStep.ioXT_levelP | exact GlobalTheory.TopStep.ioXT_levelP | (intros; apply GlobalTheory.TopStep.ioXT_levelP <;> assumption)
