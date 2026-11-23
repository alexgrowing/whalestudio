import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIntegralAdelicElementExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIInfEigenspaceEqTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWIffGoodFormsOrthSum
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BadPlacesGoodCoefficients
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_integral_adelic_element_exists : ∀ (D : D7) (n : ℕ) (J : Matrix (Fin n) (Fin n) D.host.E) (β : GL (Fin n) (EAf D)) (G : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)), (intGL D.host.F D.host.E n G).val = Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) β.val * J.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * β.val → ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∃ y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E), ∀ x ∈ UA D.sp.cm J, x ∈ St β → ∀ (w' : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)), w'.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal → (v ∉ S → redFn (β * intGL D.host.F D.host.E n y) w' x = redFn β w' x) ∧ (v ∈ S → ∀ w : Pl D.host.E, IsConjPl w w' → ∀ (p : ℕ) (e : kP w ≃+* ZMod p) (e' : ZMod p ≃+* kP w') (i j : Fin n), (redFn (β * intGL D.host.F D.host.E n y) w' x).val i j = e' (e (((redFn β w x)⁻¹).val j.rev i.rev))) := by
  first | exact @GlobalTheory.FrameMove.exists_frame_move | exact GlobalTheory.FrameMove.exists_frame_move | (intros; apply GlobalTheory.FrameMove.exists_frame_move <;> assumption)
