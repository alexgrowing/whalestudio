import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinPartMulIncAMem
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.TypeCharUnits

open Formalism.L2.JoinChr GlobalTheory.ConjTwist Formalism.IndefR.Datum

theorem isLocUnit_locU {D : D7} {PP : Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP) (a : 𝓞 D.host.E)
    (ha0 : (a : D.host.E) ≠ 0) (u : (kP PP)ˣ) (ha : (u : kP PP) = Ideal.Quotient.mk PP.asIdeal a) :
    IsLocUnit PP u (locU h.1.1 (Units.mk0 (a : D.host.E) ha0)) := by
  have haP : a ∉ PP.asIdeal := fun h0 => u.ne_zero (ha ▸ Ideal.Quotient.eq_zero_iff_mem.2 h0)
  have ha1 : a ≠ 0 := fun h0 => haP (h0 ▸ zero_mem _)
  have hinf : infPart D (idemAt PP) = 0 :=
    GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨idemAt, by simpa using h, by simp⟩, h.1.2.1⟩
  have hai : finPart D (idemAt PP * incA D ((a : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra k
    exact haP ((h.2 a ha1).2 k)
  obtain ⟨hi, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ PP h
  have he : idemAt PP * idemAt PP = idemAt PP := h.1.1
  have hb : toEAf D (incA D (a : D.host.E)) = ((oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := rfl
  have hxv : ((locU h.1.1 (Units.mk0 (a : D.host.E) ha0) : (AE D)ˣ) : AE D) =
      1 + idemAt PP * (incA D (a : D.host.E) - 1) := locU_val _ _
  have hxi : (((locU h.1.1 (Units.mk0 (a : D.host.E) ha0))⁻¹ : (AE D)ˣ) : AE D) =
      1 + idemAt PP * (incA D ((a : D.host.E)⁻¹) - 1) := by
    rw [GlobalTheory.HeckeDetChar.locU_inv, Units.val_inv_eq_inv_val, Units.val_mk0]
    rfl
  generalize locU h.1.1 (Units.mk0 (a : D.host.E) ha0) = x at hxv hxi
  generalize incA D (a : D.host.E) = b at hb hxv
  generalize incA D ((a : D.host.E)⁻¹) = b' at hai hxi
  have hv : toEAf D (x : AE D) =
      ((1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E a - 1) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
    rw [hxv, map_loc, hb]
    rfl
  have hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [hv]
    exact Subtype.property _
  refine ⟨?_, ?_, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf hx, ?_, hx, ?_⟩
  · rw [hxv]
    linear_combination (1 - b) * he
  · rw [hxv, map_loc, hinf, zero_mul, add_zero]
  · rw [hxi]
    have e1 : finPart D (1 + idemAt PP * (b' - 1)) = finPart D (1 - idemAt PP) + finPart D (idemAt PP * b') := by
      rw [← RingHom.map_add]
      congr 1
      ring
    rw [e1]
    refine add_mem (GlobalTheory.AdIdem.idempotent_mem_intAE D _ ?_) hai
    rw [← RingHom.map_mul]
    congr 1
    linear_combination he
  · have e2 : (⟨_, hx⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 1 + ⟨_, hi⟩ * (oToS D.host.F D.host.E a - 1) :=
      Subtype.ext hv
    refine (congrArg (resS D.host.F PP) e2).trans ?_
    rw [map_loc, h1, resS_oToS, ha]
    ring

theorem muC_eq_locK : ∀ (D : D7) (S T : HSp D) (B : GlobalTheory.ExportSeries.Base S T), B.Good → ∀ χ : HChar D.host.E, ChrEq B.mu0 χ → ∀ PP ∈ B.G.Pg, ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0) (z : (kP PP)ˣ), (z : kP PP) = Ideal.Quotient.mk PP.asIdeal u → ((B.G.muC PP z : ℂˣ) : ℂ) = ((χ.locK PP (Units.mk0 (u : D.host.E) hu) : ℂˣ) : ℂ) := by
  intro D S T B hB χ hχ PP hg u hu z hz
  obtain ⟨P, h1, h2, hP⟩ := hB.places.split
  have hI := hP.isIdemAt (h1 hg)
  have hx := isLocUnit_locU hI u hu z hz
  have e1 := hx.eq (hB.tame PP hg)
  have e2 := hx.eq_one hB.de.unram hP h2 (h1 hg) (Finset.disjoint_left.1 hB.places.disj hg)
  have e3 := hχ.2 PP _ (GlobalTheory.HeckeDetChar.isPlIdem hI) _ _ (locU_val hI.1.1 (Units.mk0 (u : D.host.E) hu))
  rw [Base.mu, MonoidHom.mul_apply, e2, mul_one] at e1
  rw [← e3, e1]
  rfl

end GlobalTheory.TypeCharUnits

end
