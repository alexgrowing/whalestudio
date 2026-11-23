import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UJClassFin
import Formalism.PeriodIntegrals.UJClassMassAlt
import Formalism.PeriodIntegrals.MassRankOne
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteDimensionalOfOrtho
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassZero
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassSteps

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_sig_ne (D : D7) : ∃ θ : D.host.E, D.sp.cm.sig θ ≠ θ := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (NumberField.RingOfIntegers D.host.E)
  obtain ⟨θ, t, e, h⟩ := D.sp.cm.cmUnram.2.2 P hP
  refine ⟨algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E θ, fun h' => h ?_⟩
  have h'' : star (algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E θ) =
      algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E θ := h'
  rw [h''] at e
  have : t = θ := NumberField.RingOfIntegers.coe_injective e
  rw [this, sub_self]
  exact P.zero_mem

theorem classFin_of_UJ (hF : PI.UJClassFin.UJClassFin) (D : D7) : ClassFin D := by
  intro W hW hsig
  exact hF D.host.F D.host.E D.sp.cm.sig W.rank W.gram (L0c D W) (fun _ => rfl)
    (fun τ => D.sp.cm.cmUnram.2.1 τ) (fun τ => by have h1 := hW τ; rw [hsig τ] at h1; exact h1)
    (StabFin.crd_up (F := D.host.F) W) (StabFin.crd_low (F := D.host.F) W)

theorem class_number_finite (D : D7) : ClassFin D := classFin_of_UJ unitary_class_set_finite D

theorem class_number_finite_rank (D : D7) (n : ℕ) : ClassFinAt D n := classFinAt_of D (class_number_finite D) n

theorem class_mass_of_genus_classes (hM : PI.UJClassMass2.UJClassMass) (D : D7) : ClassMass D := by
  intro W hW hsig n g hcov hdisj
  exact hM D.host.F D.host.E D.sp.cm.sig W.V W.hT W.rank W.frame W.L0 (fun _ => rfl) (exists_sig_ne D)
    (fun τ => D.sp.cm.cmUnram.2.1 τ) W.herm W.nondeg W.standardTuple_isLattice
    (fun τ => by have h1 := hW τ; rw [hsig τ] at h1; exact h1) n g hcov hdisj

theorem classMass_of_steps (hG : ClassSteps.LatGenus) (hS : PI.UnitaryGroupMassFormula.UJClassMass.SurjStep) (D : D7) : ClassMass D :=
  class_mass_of_genus_classes (ClassSteps.uJClassMass_of_genus hG hS) D

theorem defClassDecomp_of_UJ (hM : PI.UJClassMass2.UJClassMass) (D : D7) : DefClassDecomp D :=
  defClassDecomp_of_rest D (defClassRest_of D (class_number_finite D) (class_mass_of_genus_classes hM D))

theorem volume_mass_of_genus_classes (D : D7) (hT : VolTie D) (hG : GenusMassStd D) (hM : PI.UJClassMass2.UJClassMass) :
    DefiniteVolumeEqMass D :=
  volume_mass_of_class_items D hT hG (class_number_finite D) (class_mass_of_genus_classes hM D)

theorem Link2_of_UJ (hM : PI.UJClassMass2.UJClassMass) : Link2 :=
  Link2_of_items (fun _ _ _ _ => class_number_finite _) (fun _ _ _ _ => class_mass_of_genus_classes hM _)

theorem isIntegralLat_of_unimod {E : Type} [Field E] [NumberField E] [StarRing E] (W : HSpace E) :
    Formalism.HermitianLatticesTheory.IsIntegralLat W.hT W.L0 := by
  intro x hx y hy
  have hd : y ∈ Formalism.HermitianLatticesTheory.dual W.hT W.L0 := by rw [W.baseLattice_isUnimodular]; exact hy
  have h1 := (Submodule.mem_iInf _).1 hd x
  exact (Submodule.mem_iInf _).1 h1 hx

theorem isPosDef_of_sig (D : D7) (W : HSpace D.host.E) (hW : W.SigOK) (hsig : ∀ τ, W.sig τ = (W.rank, 0)) :
    PI.MassRankOne.IsPosDef W.hT := by
  intro τ x hx
  obtain ⟨c, hc, e⟩ := W.form_pos hW τ (D.sp.cm.cmUnram.2.1 τ) (hsig τ) x hx
  rw [e, Complex.ofReal_re]
  exact hc

theorem genusMassAt_one_of (hR : PI.MassRankOne.MassRankOne) (D : D7) : GenusMassAt D 1 := by
  intro W hW hsig hrk
  unfold massI
  exact hR D.host.E D.sp.cm.cmUnram W.V (Fin 1 → D.host.E) W.hT (stdForm D.host.E 1) W.L0
    (stdLat D.host.E 1) W.herm (isPosDef_of_sig D W hW hsig) (W.rank_eq.trans hrk) W.standardTuple_isLattice
    (isIntegralLat_of_unimod W) (Formalism.HermitianLattices.Ext.L3.stdForm_isSymm D.host.E 1)
    (Formalism.HermitianLattices.Ext.L3.stdLat_isOrtho D.host.E 1)

theorem classItemsAt_of_UJ (hM : PI.UJClassMass2.UJClassMass) (D : D7) (n : ℕ) (hG : GenusMassAt D n) :
    ClassItemsAt D n :=
  ⟨hG, class_number_finite_rank D n, classMassAt_of D (class_mass_of_genus_classes hM D) n⟩

theorem classItemsAt_one_of_UJ (hR : PI.MassRankOne.MassRankOne) (hM : PI.UJClassMass2.UJClassMass) (D : D7) :
    ClassItemsAt D 1 :=
  classItemsAt_of_UJ hM D 1 (genusMassAt_one_of hR D)

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem volume_eq_mass_of_genus (D : D7) (hT : VolTie D) (hV : VolRatioTrue D) (hG2 : GenusMassAt D 2)
    (hM : PI.UJClassMass2.UJClassMass) : BaseVolumeEqualsMass D :=
  volume_eq_mass_of_ratio D hT hV (classItemsAt_of_UJ hM D 2 hG2)

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem volume_mass_indefinite_genus (D : D7) (hT : VolTie D) (hV : VolRatioTrue D) (hG2 : GenusMassAt D 2)
    (hR : PI.MassRankOne.MassRankOne) (hM : PI.UJClassMass2.UJClassMass) : VolumeEqMass₂ D :=
  volume_mass_of_low_ranks D hT hV (classItemsAt_one_of_UJ hR hM D) (classItemsAt_of_UJ hM D 2 hG2)

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

end
