import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyIrreducibleComponentsWeberValuesStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesMemOfContainsRayFieldStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistField

theorem coverField_of_containsRayField : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), LawsJ T → R.toLevCh.Is A.μ0 → QGuard R → (∀ t, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK D) (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel R t)) → GlobalTheory.TwistField.CoverField T R := by
  intro D G _ _ Pl0 T0 A T _ R hT hL hQ hray
  unfold GlobalTheory.TwistField.CoverField
  intro i t l₂ hdvd hM hA Xo₂ c₂ hc
  obtain ⟨hHost, hLev, -, -⟩ := hT.pins
  unfold Par.PinHost at hHost
  unfold Par.PinLevel at hLev

  have hn : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel R t = l₂.M := by
    rw [hM, hLev.1]
    rfl

  have hsq : ∃ a : D.host.K, a ^ 2 = -(T.Q.H.d : D.host.K) := by
    refine ⟨⟨D.host.sqrtMinusD, Formalism.L2.Pj.LPb.sqrtMinusD_mem_K D⟩, ?_⟩
    rw [hHost.1]
    apply Subtype.ext
    push_cast
    exact Formalism.BasicNotions.Host.sqrtMinusD_sq D.host
  have h3 : 3 ≤ GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel R t := hn ▸ l₂.three_le

  have hW := (GlobalTheory.T.weberValues_mem_of_containsRayField D.host.E T.Q.H D.host.K D.what₂.LL (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK D) D.what₂.embLL
    (Formalism.L2.Pj.LPb.finrank_K D) hsq _ h3 (hray t)).1
  refine GlobalTheory.T.geometricallyIrreducible_components_weberValues D T.Q hT.pins ((i : ℕ) + 1) ⟨by omega, by omega⟩ l₂ Xo₂ c₂
    (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel R t) (by omega) ?_ (Or.inl (hc ▸ hW))
  show Nat.lcm l₂.M l₂.A ∣ _
  rw [hA, Nat.lcm_one_right, hn]

end GlobalTheory.TwistField
