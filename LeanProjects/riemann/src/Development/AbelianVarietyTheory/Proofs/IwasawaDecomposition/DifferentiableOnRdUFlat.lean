import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentVecC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniversalTripleFibreAtFramedPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalTripleFibresBaseChangeKeyData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKeyRuleTriangularFrameChangeFourthPower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerExponentSectionOfChartRegular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingSectionsFiniteType
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsEvenSecEvRNeZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TrueCx.FlatConst

section Hol

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT
open GlobalTheory.Reg GlobalTheory.KeyFourth GlobalTheory.AllWt GlobalTheory.FlatLine

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_generic_units (hpq : 1 ≤ Dw.p + Dw.q) (h : GenFrEx Xo c) :
    ∃ v : ∀ Z : Comp Xo c, (Om Z)ˣ, ∀ C : FChart h,
      ∃ u : (C.R)ˣ, ((u : C.R) : Om C.Z) = ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) := by
  obtain ⟨κ, h₁, h₂, -, -, -, h₃, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (Dw.mult τ))).symm
  have hc : ∀ Z : Comp Xo c, CharZero (Om Z) := fun Z =>
    charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
  choose Ψ hΨ using fun Z : Comp Xo c => exists_tied E H Dw l Xo c _ e (Om Z) (genFr h Z) hpq
  refine ⟨fun Z => κ (Om Z) (Ψ Z).key, fun C => ?_⟩
  haveI := C.sm
  haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
  haveI : IsNoetherianRing C.R := Algebra.FiniteType.isNoetherianRing c.F C.R
  haveI : CharZero C.R := charZero_of_injective_algebraMap (algebraMap c.F C.R).injective
  obtain ⟨Φ, hΦ⟩ := exists_tied E H Dw l Xo c _ e C.R C.y hpq
  obtain ⟨Φ', hΦ'⟩ := exists_tied E H Dw l Xo c _ e (Om C.Z) C.yg hpq
  obtain ⟨u, hu⟩ := h₃ C.R Φ.key
  refine ⟨u, ?_⟩
  rw [← rule_frBor κ h₁ h₂ E H Dw l Xo c _ e (Om C.Z) C.t _ _ (Ψ C.Z) Φ' C.bor (hΨ _) hΦ']
  exact (hu (Om C.Z) _ _ (tied_keyPB E H Dw l Xo c _ e _ _ C.R.val C.y C.yg Φ Φ' C.gen hΦ hΦ')).symm

theorem exists_key_four (hpq : 1 ≤ Dw.p + Dw.q) (σ : c.F →+* ℂ) :
    ∃ ρ ∈ secZ Xo c (fun i => keyEx Dw i * 4), ∀ y : FrPt Xo c (CAt σ), toC (evR Xo c ρ y) ≠ 0 := by
  obtain ⟨-, -, h, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨v, hv⟩ := exists_generic_units hpq h
  have hk : ∀ C : FChart h, (∏ i, C.t i ^ (keyEx Dw i * 4) : (Om C.Z)ˣ) = kch C.t ^ 4 := fun C => by
    rw [kch, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => by rw [zpow_mul]; rfl
  obtain ⟨ρ, hρ, hρv⟩ := GlobalTheory.SecGlueInt.exists_secZ_of_regular E H Dw l Xo c h (fun i => keyEx Dw i * 4)
    (fun Z => v Z) fun C => by
      obtain ⟨u, hu⟩ := hv C
      rw [hk, ← Units.val_mul, ← hu]
      exact u.1.2
  refine ⟨ρ, hρ, fun y => ?_⟩
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  obtain ⟨C, ψ, z, t, hz, hb⟩ := hA h (CAt σ) y
  obtain ⟨u, hu⟩ := hv C
  obtain ⟨b, hb₁, hb₂⟩ := GlobalTheory.DegCmp.fChart_exists_val C hρ
  have hbu : b = u := Subtype.ext (by
    rw [hb₁, hu, hk, GlobalTheory.CompHt.genVal_apply h, hρv, Units.val_mul])
  show evR Xo c ρ y ≠ 0
  rw [GlobalTheory.FlagTan.evR_frBor hρ hb, hb₂ _ ψ z hz, hbu]
  exact mul_ne_zero (Units.ne_zero _) (u.isUnit.map ψ).ne_zero

theorem exists_sec_four (hpq : 1 ≤ Dw.p + Dw.q) {σ : c.F →+* ℂ} (y : FrPt Xo c (CAt σ)) :
    ∃ n, Even n ∧ ∃ g ∈ sec Xo c (fun _ => 4) n, toC (evR Xo c g y) ≠ 0 := by
  obtain ⟨ρ, hρ, h0⟩ := exists_key_four (Xo := Xo) hpq σ
  obtain ⟨n, hn, ⟨m, rfl⟩, η, hη, hη0⟩ := exists_even_sec_evR_ne_zero E H Dw l Xo c σ y
  rw [← secZ_nat] at hη
  have h2 := mul_mem_secZ hη hη
  have h3 := mul_mem_secZ (mul_mem_secZ h2 h2) hρ
  refine ⟨2 * (4 * m - 4), even_two_mul _, η * η * (η * η) * ρ, ?_, ?_⟩
  · rw [← secZ_nat]
    convert h3 using 2
    funext i
    cases i with
    | none => simp only [ex, keyEx, Pi.add_apply]; omega
    | some i => simp [ex, keyEx]
  · have h1 : toC (evR Xo c η y) ≠ 0 := hη0
    simp only [CompSplitPfB.cspB_evR_mul]
    exact mul_ne_zero (M₀ := ℂ) (mul_ne_zero (M₀ := ℂ) (mul_ne_zero (M₀ := ℂ) h1 h1) (mul_ne_zero (M₀ := ℂ) h1 h1)) (h0 y)

open Classical in

def flatFour (τ : Psi H) : (E →+* ℂ) × ℕ → ℕ :=
  fun x => if x.1 = τ.1 then 3 else if x.1 = conjEmb τ.1 then 5 else 4

variable {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r}

end Hol

section Main

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts GlobalTheory.TrueCx
open GlobalTheory.AllWt (Psi)
attribute [local instance] Over.cartesianMonoidalCategory

end Main

end GlobalTheory.TrueCx.FlatConst
