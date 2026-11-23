import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdelicLatticeMembershipIff
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adelic_lattice_membership_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (d M : ℕ) (b : Module.Basis (Fin d) F E) (a : ℕ) (X : Fin 1 → Fin M → Af F ⊗[F] E), (∀ v, (fun p i => (a : Fv F v ⊗[F] E) * projV v X p i) ∈ latV b v) ↔ ∀ i v, ((a : Af F) * cv (Af F) b (X 0) i) v ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.Lat.natCast_mul_mem_latV_iff | exact GlobalTheory.CompanionTheory.SW.BB.Lat.natCast_mul_mem_latV_iff | (intros; apply GlobalTheory.CompanionTheory.SW.BB.Lat.natCast_mul_mem_latV_iff <;> assumption)
