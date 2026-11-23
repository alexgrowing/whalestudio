import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepDatumEqMulHalves
import Mathlib
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
theorem _root_.GlobalTheory.T.stepDatum_eq_mul_halves : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ S.rank) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (χj ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (eG eQ : AE D), IsIdemSum eG Pg → IsIdemSum eQ Q → eG * eQ = 0 → ∀ x : WO S T, (if IsHalf (eG + eQ) x ∧ IsIntM (frMapO S T βS βT x) then omegaG (datY S.rank r t j hr Pg Q P χ ξ Frm.B) χj (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ Q (datY S.rank r t j hr Pg Q P χ ξ Frm.B).r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) = (if IsHalf eG (eG • x) ∧ IsIntM (frMapO S T βS βT (eG • x)) then omegaG (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B) χj (fun PP => redM PP (frMapO S T βS βT (eG • x))) * omegaQ ∅ (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B).r (fun _ => 1) 1 (fun PP => redM PP (frMapO S T βS βT (eG • x))) else 0) * (if IsHalf eQ (eQ • x) ∧ IsIntM (frMapO S T βS βT (eQ • x)) then omegaG (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B) χj (fun PP => redM PP (frMapO S T βS βT (eQ • x))) * omegaQ Q (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B).r ξ 1 (fun PP => redM PP (frMapO S T βS βT (eQ • x))) else 0) * (if IsHalf (eG + eQ) x then 1 else 0) := by
  first | exact @GlobalTheory.DatumHalves.stepDatum_eq_mul | exact GlobalTheory.DatumHalves.stepDatum_eq_mul | (intros; apply GlobalTheory.DatumHalves.stepDatum_eq_mul <;> assumption)
