import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivativeExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesInsertZero
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_derivative_extension : ∀ (F : Type) [Field F] [NumberField F] (n d d₁ : ℕ) (hd : d = d₁ + 2) (a b : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F)
    (f g : SInf F (Fin n × Fin d)), ⇑g = dH (ins0 hd a) (ins0 hd b) ⇑f → ⇑(ei F hd g) = dH a b ⇑(ei F hd f) := by
  first | exact @GlobalTheory.ThK.PlaneEv.ei_dH | exact GlobalTheory.ThK.PlaneEv.ei_dH | (intros; apply GlobalTheory.ThK.PlaneEv.ei_dH <;> assumption)
