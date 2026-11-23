import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepPureTensorLocal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPt

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_rep_pure_tensor_local : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F)
    (w : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) w →
    ∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ),
      (∀ᶠ u in cofinite, φ u = GlobalTheory.FinComm.indO u) →
      M.co.rho ψ w (pure f φ) =
        pure f (Function.update φ v (GlobalTheory.FinComm.locOp ψ v (GlobalTheory.FinComm.locPt v (M.co.e w)) (φ v))) := by
  first | exact @GlobalTheory.FinComm.RhoPure.rho_pure | exact GlobalTheory.FinComm.RhoPure.rho_pure | (intros; apply GlobalTheory.FinComm.RhoPure.rho_pure <;> assumption)
