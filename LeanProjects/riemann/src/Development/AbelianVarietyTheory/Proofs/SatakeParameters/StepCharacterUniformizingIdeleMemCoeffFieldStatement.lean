import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterUniformizingIdeleMemCoeffField
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepCharacter_uniformizingIdele_mem_coeffField : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => KIn t → ∀ v π, IsUnifAt J v π → ∀ j < D.R.m, ∃ r : D.what₂.LL, D.what₂.embLL r = S.muT (j + 1) π) := by
  first | exact @GlobalTheory.TwV.Xc.MuLL.mu_mem_LL | exact GlobalTheory.TwV.Xc.MuLL.mu_mem_LL | (intros; apply GlobalTheory.TwV.Xc.MuLL.mu_mem_LL <;> assumption)
