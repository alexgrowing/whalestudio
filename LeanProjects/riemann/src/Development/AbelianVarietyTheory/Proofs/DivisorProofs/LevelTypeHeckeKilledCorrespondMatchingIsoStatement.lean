import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelTypeHeckeKilledCorrespondMatchingIso
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelTypeHecke_killed_correspond_matching_iso : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (hr' : r ≤ V'.rank) (Pg : Finset (Pl D.host.E)) (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Φ : GfC V ≃ₜ* GfC V') {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 Pg r) (c : G → ℂ) (P : LevelP Pg r ℂ) {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GfC V') X), V.rank = V'.rank → (∀ κ : GfC V, finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ↔ finE V' (Φ κ : GA D V') ∈ parLev D.sp.cm V'.gram β' (princDat V'.rank r t hr' Pg χ')) → (∀ κ : GfC V, finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) → (rTup β' (princDat V'.rank r t hr' Pg χ') (finE V' (Φ κ : GA D V')) : G0 Pg r) = (rTup β (princDat V.rank r t hr Pg χ) (finE V (κ : GA D V)) : G0 Pg r)) → (∀ P0 ∈ ok, ∀ k (α : GfC V), IsHeckeAt V (pl P0) k α ↔ IsHeckeAt V' (pl P0) k (Φ α)) → killed (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ (GfC V) X) (eqSet V β (princDat V.rank r t hr Pg χ) eG c P ok pl q Sg) = killed ρ (eqSet V' β' (princDat V'.rank r t hr' Pg χ') eG c P ok pl q Sg) := by
  first | exact @GlobalTheory.CuspMult.EqTrans.killed_eqSet_comp | exact GlobalTheory.CuspMult.EqTrans.killed_eqSet_comp | (intros; apply GlobalTheory.CuspMult.EqTrans.killed_eqSet_comp <;> assumption)
