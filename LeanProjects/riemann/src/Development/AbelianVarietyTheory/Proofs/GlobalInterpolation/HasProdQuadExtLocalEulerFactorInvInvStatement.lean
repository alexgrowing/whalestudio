import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasProdQuadExtLocalEulerFactorInvInv
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDualIndex
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProd_quadExtLocalEulerFactorInv_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ M : ℕ, 2 ≤ M → 0 < Formalism.HermitianLatticesTheory.lValEta E M ∧ HasProd (fun v => (eulerInv F E M v)⁻¹) (Formalism.HermitianLatticesTheory.lValEta E M) := by
  first | exact @GlobalTheory.EtaEulerProduct.hasProd_eulerInv_inv | exact GlobalTheory.EtaEulerProduct.hasProd_eulerInv_inv | (intros; apply GlobalTheory.EtaEulerProduct.hasProd_eulerInv_inv <;> assumption)
