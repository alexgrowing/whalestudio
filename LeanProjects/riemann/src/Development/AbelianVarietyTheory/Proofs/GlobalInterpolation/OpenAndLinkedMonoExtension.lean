import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DepthZeroSupport
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoreSlotConstructionMonoFewerCoresBothPasses
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory.Glob

theorem open_and_linked_of_stronger_extension : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N N' : NExt hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N' K B f T w Z Wt p0 t nch n xd c → Nonempty (N K B f T w Z Wt p0 t nch n xd c)) → (∀ H : ∀ 𝒜 : FamClass, RawSel Bundle 𝒜 → Prop, RL.At (prmR N S Γ) (fun Q L => Row Q L H) → RL.At (prmR N' S Γ) (fun Q L => Row Q L H)) ∧ (S0.Open0 (prmR N S Γ) → S0.Open0 (prmR N' S Γ)) := by
  intro hL N N' S Γ hN
  obtain ⟨hB, hG, hLk, -⟩ := GlobalTheory.HeightCounting.Up.rows_of_stronger_nExt hL N N' S Γ hN
  have m : ∀ H : ∀ 𝒜 : FamClass, RawSel Bundle 𝒜 → Prop, RL.At (prmR N S Γ) (fun Q L => Row Q L H) → RL.At (prmR N' S Γ) (fun Q L => Row Q L H) :=
    fun H h => GlobalTheory.HeightCounting.Up.eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => GlobalTheory.HeightCounting.Up.row_mono_id hS hLk h) h
  exact ⟨m, fun o => ⟨m _ o.hPA, m _ o.hLamP, m _ o.hDivG, m _ o.hDcPtG, m _ o.selJ, m _ o.tie, m _ o.lab, m _ o.good, m _ o.geo, m _ o.mi, m _ o.kap, m _ o.df⟩⟩

end GlobalTheory.Glob
