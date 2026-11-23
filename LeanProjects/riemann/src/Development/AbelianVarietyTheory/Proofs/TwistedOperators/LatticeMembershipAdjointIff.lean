import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAdjYZeroMemLatOIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentPowCompletionTrivialAtSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodIdealZpowCompletionAdeleConjIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JZeroMulMemLatticeIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StaircaseLatticeIsotropicLineIdealIffStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselCoreLatticeMeetsLineOfZIdealStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModulusIdealOffS0TrivialStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StaircaseIdealsCompletionEqOfModulusUnitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.LastGen

open GlobalTheory.SeeSaw GlobalTheory.SeeSaw.LastPrim

theorem incAdj_yZero_mulVec_gen {D : D7} {S A L T T₀ : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) {ρ : ℕ}
    (d : HypDec T T₀ ρ) (hρ : 0 < ρ) (a : AE D) (y : Fin S.rank → AE D) :
    Matrix.mulVec (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from d.incAdj S (a • yZero S ρ (vecB o ζ))) y =
      GlobalTheory.FinPl.colMul d.jY ⟨ρ - 1, by omega⟩ (incA D D.host.xi0⁻¹ * cA D a * (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l)) := by
  funext k
  have hell : ∀ i : Fin ρ, cA D (ell D ρ i) = if i = ⟨ρ - 1, by omega⟩ then 1 else 0 := by
    intro i
    simp only [ell, Fin.ext_iff]
    split_ifs with h1 h2 h2 <;> first | omega | simp
  simp only [HypDec.incAdj_apply, HypDec.incY_apply, yZero, zEll, adj_smul, adj_neg, GlobalTheory.FinPl.colMul, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, Matrix.smul_apply, Matrix.neg_apply, adj, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, map_mul, map_neg, hell]
  rw [Finset.sum_congr rfl fun l _ => by
    rw [Finset.sum_eq_single (⟨ρ - 1, by omega⟩ : Fin ρ) (fun i _ hi => by simp [hi]) (fun h => absurd (Finset.mem_univ _) h)]]
  simp only [if_true, mul_one, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  ring

set_option maxHeartbeats 1000000 in

theorem incAdj_yZero_mem_latO_iff_gen : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A L T T₀ : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (ρ : ℕ) (d : HypDec T T₀ ρ) (M : Lat S) (LW : Lat T) (LW₀ : Lat T₀) (𝔟 : ℕ → GlobalTheory.SeeSaw.FI D) (𝔠 : GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D), IsSelfDualC S M → IsSelfDualC T LW → GlobalTheory.SeeSaw.MonoId d LW LW₀ 𝔟 v → GlobalTheory.SeeSaw.LineId o ζ M 𝔠 v → 𝔠 ≠ 0 → 𝔟 (ρ - 1) ≠ 0 → (∀ s, s ∈ GlobalTheory.SeeSaw.idV ((D.host.AAbar : GlobalTheory.SeeSaw.FI D) * (𝔟 (ρ - 1))⁻¹) v ↔ s ∈ GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton _ D.host.xi0⁻¹ * 𝔠⁻¹) v) → 0 < ρ → ∀ a ∈ idAt D (· = v), d.incAdj S (a • yZero S ρ (vecB o ζ)) ∈ latO S T (M : Set _) (LW : Set _) (· = v) ↔ a ∈ intAt D (· = v) := by
  intro D ψ hψ S A L T T₀ o ζ ρ d M LW LW₀ 𝔟 𝔠 v hM hLW hmono hline hc hb0 hid hρ a ha
  obtain ⟨h1, h2, h3, h4, -, h6, -⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.LocFrame.cmHost_imaginaryGenerator_ne_zero
  have hci : 𝔠⁻¹ ≠ 0 := inv_ne_zero hc
  have hb : 𝔟 ((⟨ρ - 1, by omega⟩ : Fin ρ) : ℕ) ≠ 0 := hb0
  have hL0 := colMul_jY_mem_latA_iff D ψ hψ T T₀ ρ d LW (𝔟 (ρ - 1)) v ⟨ρ - 1, by omega⟩ hb
    (GlobalTheory.T.dualIsotropicLine_mem_completion_iff D ψ hψ T T₀ ρ d LW LW₀ 𝔟 v hLW hmono ⟨ρ - 1, by omega⟩ hb)
  have hL : ∀ t ∈ idAt D (· = v), GlobalTheory.FinPl.colMul d.jY ⟨ρ - 1, by omega⟩ t ∈ latA T LW (· = v) ↔
      cA D t ∈ idV (FractionalIdeal.spanSingleton _ D.host.xi0⁻¹ * 𝔠⁻¹) v :=
    fun t ht => (hL0 t ht).trans (hid _)
  have e3 : incA D (D.host.xi0⁻¹)⁻¹ * incA D (star D.host.xi0⁻¹) = -1 := by
    rw [← map_mul, inv_inv, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg, mul_neg, mul_inv_cancel₀ hξ, map_neg, map_one]
  have key : ∀ y ∈ latV S M (· = v),
      (Matrix.mulVec (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from
        d.incAdj S (a • yZero S ρ (vecB o ζ))) y ∈ latA T LW (· = v) ↔
        a * cA D (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l) ∈ idV 𝔠⁻¹ v) := by
    intro y hy
    have hzi : (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l) ∈ idAt D (· = v) :=
      sum_mem fun l _ => Ideal.mul_mem_left _ _ (latV_entry_mem' hy l)
    rw [incAdj_yZero_mulVec_gen o ζ d hρ a y, hL _ (Ideal.mul_mem_left _ _ hzi), map_mul, map_mul, GlobalTheory.SeeSaw.cA_cA, GlobalTheory.DualPairCheck.cA_incA,
      h3 _ _ (inv_ne_zero hξ)]
    have e4 : incA D (D.host.xi0⁻¹)⁻¹ * (incA D (star D.host.xi0⁻¹) * a * cA D (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l)) =
        -(a * cA D (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l)) := by
      rw [← mul_assoc, ← mul_assoc, e3]; ring
    rw [e4, neg_mem_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ha)⟩⟩
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T M LW hM hLW]
  constructor
  · rintro ⟨-, hu⟩
    obtain ⟨g, hg, g', -, hgg, hiff⟩ := h6 𝔠⁻¹ hci
    obtain ⟨y, hy, hyg⟩ := GlobalTheory.T.hermitianPairing_onto_inverseIdeal_at_place D ψ hψ S A L o ζ M 𝔠 v hM hline hc g hg
    have h7 := ((hiff _).1 ((key y hy).1 (hu y hy))).2
    rw [hyg] at h7
    rw [← hgg a ha]
    have e6 : g' * g * a = g' * (a * g) := by rw [mul_assoc, mul_comm g a]
    rw [e6]; exact h7
  · intro haI
    have hcA : cA D a ∈ idAt D (· = v) := by
      have := (h4 0 a).1 (by rw [zpow_zero]; exact (h1 a).2 haI)
      rw [zpow_zero] at this
      exact ((h1 _).1 this).1
    refine ⟨fun k l => ?_, fun y hy => (key y hy).2 ?_⟩
    · have e5 := congrFun (incAdj_yZero_mulVec_gen o ζ d hρ a (Pi.single l 1)) k
      rw [Matrix.mulVec_single_one] at e5
      refine (congrArg (· ∈ idAt D (· = v)) e5).mpr ?_
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hcA))
    · have hmul := (h2 𝔠⁻¹ 𝔠⁻¹ hci hci a ha).2 (by rw [mul_inv_cancel₀ hci]; exact (h1 a).2 haI)
      exact hmul _ (GlobalTheory.T.lineVector_pairing_mem_inverseIdealCompletion D ψ hψ S A L o ζ M 𝔠 v hM hline hc y hy)

end GlobalTheory.LastGen

namespace GlobalTheory.AscFin

theorem incAdj_yBF_mem_latO_iff : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, 0 < ρ → ∀ a ∈ idAt D (· = v), (F.dJ ρ h).incAdj (F.V₀ ρ) (a • yBF F ρ h) ∈ latO (F.V₀ ρ) _ (lat0 F ρ h : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (· = v) ↔ a ∈ intAt D (· = v) := by
  intro D hoff T L μ0 hL sc G W M hM F hF ρ h v hv hρ a ha
  have I := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hoff T L μ0 hL sc G W M hM F hF
  have hψ : IsStdChar D W.ψ (-1) := W.ψ_std
  have hsdJ := (G.isV (X := .grid (2 * ρ + 1) 0) (by simp [Node.InRange]; omega) (by simp)).sd
  obtain ⟨hb0, hc0, hid⟩ := GlobalTheory.T.staircase_ideals_completion_eq_of_modulus_unit G.pl sc ρ v hρ (GlobalTheory.T.modulus_ideal_off_S0_trivial G.pl sc v hv)
  exact GlobalTheory.LastGen.incAdj_yZero_mem_latO_iff_gen D W.ψ hψ _ _ _ _ _ (F.oB ρ h) (F.ζ (ρ + 1)) ρ (F.dJ ρ h) (lat0 F ρ h) (G.Λ (.grid (2 * ρ + 1) 0))
    (G.Λ (.core (2 * ρ + 1)))
    (fun i => FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (i + 1))⁻¹ * (G.pl.stA sc ^ (2 * ρ - i) * (G.pl.stAbar sc ^ (i + 1))⁻¹))
    _ v (I.2.1 ρ h).1 hsdJ ⟨((I.2.1 ρ h).2.1 v).2, fun i b hb => GlobalTheory.T.staircase_lattice_isotropic_line_ideal_iff D hoff T L μ0 hL sc G W M hM F hF ρ h v i b hb⟩
    (GlobalTheory.T.lineId_oB_lat0_of_pl D hoff T L μ0 hL sc G W M hM F hF ρ h v) hc0 hb0 hid hρ a ha

end GlobalTheory.AscFin
