import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLatBack
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatBackSeamLat
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwU

theorem latBack_seam_lat {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    latBack s (s.lat N) = N := by
  first
  | exact @_root_.GlobalTheory.LatticeBackSeam.latBack_seam_lat
  | exact _root_.GlobalTheory.LatticeBackSeam.latBack_seam_lat
  | (apply _root_.GlobalTheory.LatticeBackSeam.latBack_seam_lat <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticeBackSeam.latBack_seam_lat <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticeBackSeam.latBack_seam_lat <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticeBackSeam.latBack_seam_lat ..)

end GlobalTheory.TwU
