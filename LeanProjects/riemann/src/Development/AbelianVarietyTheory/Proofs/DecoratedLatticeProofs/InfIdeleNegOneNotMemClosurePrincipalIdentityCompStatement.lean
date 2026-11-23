import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InfIdeleNegOneNotMemClosurePrincipalIdentityComp
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infIdele_neg_one_not_mem_closure_principal_identityComponent : ∀ (E : Type) [Field E] [NumberField E] (w : InfinitePlace E), w.IsReal → ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E w (-1) ∉ ((diagUnits E).range ⊔ infConn E).topologicalClosure := by
  first | exact @GlobalTheory.RealSignIdele.infIdele_neg_one_not_mem | exact GlobalTheory.RealSignIdele.infIdele_neg_one_not_mem | (intros; apply GlobalTheory.RealSignIdele.infIdele_neg_one_not_mem <;> assumption)
