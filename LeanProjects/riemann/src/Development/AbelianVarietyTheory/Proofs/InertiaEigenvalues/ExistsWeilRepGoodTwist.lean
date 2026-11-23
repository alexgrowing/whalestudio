import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsClassSystem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilTwistExists

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isHeckeChar_mul' {χ χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) (h' : IsHeckeChar D χ') :
    IsHeckeChar D (χ * χ') :=
  ⟨h.1.mul h'.1, fun x => by rw [MonoidHom.mul_apply, h.2 x, h'.2 x, mul_one]⟩

theorem isHeckeChar_inv' {χ : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) : IsHeckeChar D χ⁻¹ :=
  ⟨h.1.inv, fun x => by rw [MonoidHom.inv_apply, h.2 x, inv_one]⟩

theorem resEta_zero_of_real {χ ξ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D ξ n) (hr : ∀ a, χ (idF D a) = 1) :
    ResEta D χ 0 :=
  ⟨h.1, fun η _ a => by rw [hr, pow_zero]⟩

theorem exists_isWeil : ∀ (D : D7) (S T : HSp D) (B : Base S T), GlobalTheory.Published.WeilRepresentationUnitaryPair → B.Good →
    IsStdChar D B.F.ψ (-1) → ∀ t : Twist D Circle, t.Good → ∃ ω, B.IsWeil t.chi ω := by
  intro D S T B hW hB hψ t ht
  have hEta : ResEta D B.eta 1 := hB.eta.2.2.1
  have h0 : ResEta D (B.mu * t.chi) 0 := by
    refine resEta_zero_of_real hEta fun a => ?_
    rw [MonoidHom.mul_apply, Base.mu, MonoidHom.mul_apply, hB.real, ht.real, hB.de.real, one_mul, one_mul]
  have hH : IsHeckeChar D (B.mu * t.chi) :=
    isHeckeChar_mul' (isHeckeChar_mul' hB.hecke hB.de.isHeckeChar) ht.isHeckeChar
  have hS : ResEta D (B.mu * t.chi) S.rank :=
    Formalism.L2.Theta.resEta_parity h0 (by rw [Nat.even_iff.1 hB.even])
  have hT : ResEta D (B.mu * t.chi * B.eta⁻¹) T.rank := by
    have h1 := Formalism.L2.Theta.resEta_mul h0 (Formalism.L2.Theta.resEta_inv hEta)
    exact Formalism.L2.Theta.resEta_parity h1 (by rw [Nat.odd_iff.1 hB.odd])
  exact hW D B.F.ψ S T _ _ hψ hH (isHeckeChar_mul' hH (isHeckeChar_inv' hB.eta.1)) hS hT

end GlobalTheory.WeilTwistExists

end
