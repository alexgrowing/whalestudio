import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumOnGoodPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeySectionUnif
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine
open GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects GlobalTheory.Reg

namespace GlobalTheory.KeyFourth

theorem prod_zpow_four_smul_keyEx {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {S : Type} [CommRing S] (t : Ix Dw → Sˣ) :
    (∏ i, t i ^ ((4 : ℤ) • keyEx Dw) i) = kch t ^ 4 := by
  rw [kch, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_comm, zpow_mul]
  norm_cast

set_option maxHeartbeats 1000000 in

theorem exists_unit_secZ_keyRule : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.FamUnit κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), 1 ≤ Dw.p + Dw.q → ∃ K : (Rul Xo c)ˣ, (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw) ∧ (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) := by
  intro κ h₁ h₂ h₃ E _ _ _ H Dw l Xo c g e hpq
  obtain ⟨hL, -, h, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨v, hv⟩ := exists_chart_units h₁ h₂ h₃ e hpq h
  obtain ⟨f, hf, hfb⟩ := GlobalTheory.T.exists_integer_exponent_section_of_chart_regular E H Dw l Xo c h ((4 : ℤ) • keyEx Dw) (fun Z => (v Z : Om Z)) fun C => by
    obtain ⟨-, u, -, -, huv⟩ := hv C
    rw [prod_zpow_four_smul_keyEx, ← Units.val_mul, ← huv]
    exact (u : C.R).2
  obtain ⟨f', hf', hfb'⟩ := GlobalTheory.T.exists_integer_exponent_section_of_chart_regular E H Dw l Xo c h (-((4 : ℤ) • keyEx Dw))
      (fun Z => (((v Z)⁻¹ : (Om Z)ˣ) : Om Z)) fun C => by
    obtain ⟨-, u, -, -, huv⟩ := hv C
    have hm : Units.map (C.R.val : C.R →* Om C.Z) u = kch C.t ^ 4 * v C.Z := Units.ext huv
    have hp : (∏ i, C.t i ^ (-((4 : ℤ) • keyEx Dw)) i) = (kch C.t ^ 4)⁻¹ := by
      rw [← prod_zpow_four_smul_keyEx, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Pi.neg_apply, zpow_neg]
    have hq : (kch C.t ^ 4)⁻¹ * (v C.Z)⁻¹ = Units.map (C.R.val : C.R →* Om C.Z) u⁻¹ := by
      rw [map_inv, hm, mul_inv_rev, mul_comm]
    rw [hp, ← Units.val_mul, hq]
    exact ((u⁻¹ : (C.R)ˣ) : C.R).2
  have h0 : GlobalTheory.AllWt.secZ Xo c 0 = sec Xo c 0 0 := by
    rw [← GlobalTheory.AllWt.secZ_nat]
    congr 1
    funext i
    cases i <;> rfl
  have hm := GlobalTheory.AllWt.mul_mem_secZ hf hf'
  rw [add_neg_cancel, h0] at hm
  have h1 := GlobalTheory.AllWt.one_mem_secZ (Xo := Xo) (c := c)
  rw [h0] at h1
  have hff : f * f' = 1 := by
    refine sub_eq_zero.1 (sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) 0 0 _ (sub_mem hm h1) fun Z => ?_)
    have e₁ : evC h Z (f * f') = evC h Z f * evC h Z f' := by simp only [evC, evR, evalAt_mul]
    have e₂ : evC h Z (1 : Rul Xo c) = 1 := evalAt_one _ _ _ (hL.test _ _)
    have e₃ := (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (genFr h Z)).map_sub
      (f * f') 1
    refine e₃.trans ?_
    change evC h Z (f * f') - evC h Z 1 = 0
    rw [e₁, e₂, hfb, hfb', Units.mul_inv, sub_self]
  refine ⟨⟨f, f', hff, (mul_comm _ _).trans hff⟩, hf, ?_⟩
  intro F _ _ _ y Φ hΦ
  change evR Xo c f y = _
  obtain ⟨C, ψ, z, t', hz, hb⟩ := hA h F y
  obtain ⟨ΦC, u, hΦC, hu, huv⟩ := hv C
  obtain ⟨p, a, u₀, hu₀⟩ := hL.test C.R C.y
  have k₁ : evR Xo c f C.yg = C.R.val (evR Xo c f C.y) := by
    rw [GlobalTheory.FlagTan.evR_eq hf.1 hu₀, GlobalTheory.FlagTan.evR_eq hf.1 (GlobalTheory.FlagTan.frMap_comp (χ := C.R.val.comp a) hu₀ C.gen fun _ => rfl)]
    rfl
  have k₂ : evR Xo c f C.yg = ((u : C.R) : Om C.Z) := by
    rw [GlobalTheory.FlagTan.evR_frBor hf C.bor, prod_zpow_four_smul_keyEx, huv]
    have := hfb C.Z
    simp only [evC] at this
    rw [this, Units.val_mul]
  have k₃ : evR Xo c f C.y = (u : C.R) := Subtype.val_injective (k₁.symm.trans k₂)
  have k₄ : evR Xo c f z = ψ (u : C.R) := by
    rw [GlobalTheory.FlagTan.evR_eq hf.1 (GlobalTheory.FlagTan.frMap_comp (χ := ψ.comp a) hu₀ hz fun _ => rfl), ← k₃, GlobalTheory.FlagTan.evR_eq hf.1 hu₀]
    rfl
  obtain ⟨Ψ, hΨ⟩ := GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e F z hpq
  have k₅ := GlobalTheory.T.theta_key_rule_triangular_frame_change_fourth_power κ h₁ h₂ E H Dw l Xo c g e F t' z y Ψ Φ hb hΨ hΦ
  have k₆ : (κ F Ψ.key : F) = ψ (u : C.R) :=
    hu F ψ.toRingHom Ψ.key (GlobalTheory.T.universal_triple_fibres_base_change_key_data E H Dw l Xo c g e C.R F ψ C.y z ΦC Ψ hz hΦC hΨ)
  rw [GlobalTheory.FlagTan.evR_frBor hf hb, prod_zpow_four_smul_keyEx, k₄, k₅, Units.val_mul, k₆]

end GlobalTheory.KeyFourth
