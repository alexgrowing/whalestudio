import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxSchroedingerArchimedeanActs
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darboux_schroedinger_archimedean_acts : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {V : Type} [AddCommGroup V] [Module (AF F) V]
    {B : V → V → AF F} (d : Darboux B κ) (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ z : V, At (evI F) z →
    ∀ f g : SInf F κ, ⇑g = sch (trP F κ) (arch F (d.e z).1) (arch F (d.e z).2) ⇑f → Acts (evI F) (d.rho ψ z) ⇑f ⇑g := by
  first | exact @GlobalTheory.ArchSch.darboux_rho_acts_sch | exact GlobalTheory.ArchSch.darboux_rho_acts_sch | (intros; apply GlobalTheory.ArchSch.darboux_rho_acts_sch <;> assumption)
