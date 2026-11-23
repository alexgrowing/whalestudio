import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PlanePairingEquivariantTwistCartierDual
import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DvdOfMemIk
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

theorem _root_.GlobalTheory.T.planePairing_equivariant_twist_cartierDual : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hdet : dt W ^ 2 = 1) (S : Finset Pl) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ), μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∀ (s : G ℚ Ω) (y : Mn c n), GlobalTheory.Ord2.SelPerp.Phi c n (matQ c n (dual1 W) (CupCob.dual_representation_integral c W hdet hint) s *ᵥ y) = twDual μ (rhoS c n W hint S hN) (toGS Ω (S : Set Pl) s) (GlobalTheory.Ord2.SelPerp.Phi c n y) := by
  first | exact @GlobalTheory.Ord2.SelPerp.Phi_equivariant | exact GlobalTheory.Ord2.SelPerp.Phi_equivariant | (intros; apply GlobalTheory.Ord2.SelPerp.Phi_equivariant <;> assumption) | exact @GlobalTheory.Ord2.SelPerp.matQ_det_sq | exact GlobalTheory.Ord2.SelPerp.matQ_det_sq | (intros; apply GlobalTheory.Ord2.SelPerp.matQ_det_sq <;> assumption) | exact @GlobalTheory.Ord2.SelPerp.matQ_dual1_apply | exact GlobalTheory.Ord2.SelPerp.matQ_dual1_apply | (intros; apply GlobalTheory.Ord2.SelPerp.matQ_dual1_apply <;> assumption)
