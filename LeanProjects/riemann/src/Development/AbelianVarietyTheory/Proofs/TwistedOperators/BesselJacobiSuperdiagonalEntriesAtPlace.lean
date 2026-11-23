import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletedHomLatticeModulusDepthMemShiftStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnMemLatticeIffIdealStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmHostFractionalIdealPartitionOfUnity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiPrimitiveStandardFramesBesselLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdVLeOfLoc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiUnipotentTrivialOnLevel
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotLineLatAtZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

open GlobalTheory.SeeSaw (idV FI dI) in

theorem GlobalTheory.AscFin.coef_superdiag : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m)
    (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))) (𝔠 : GlobalTheory.SeeSaw.FI D), 𝔠 ≠ 0 →
    ∀ v : GlobalTheory.FinPl.Pl D, (∀ y ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV 𝔠 v,
      s • (M *ᵥ y) ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v)) → ∀ i j : Fin ρ, j.1 = i.1 + 1 →
    GlobalTheory.FinPlLoc.idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j ∈
      GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton _ D.host.xi0 * G.pl.stAbar sc * 𝔠⁻¹) v := by
  intro D hD T L μ0 hL sc G W M0 hM0 F hF ρ h M 𝔠 h𝔠 v hM i j hij
  obtain ⟨-, f2, -, -, -, -, -⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D W.ψ W.ψ_std v
  have hmono : MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v :=
    ((GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hD T L μ0 hL sc G W M0 hM0 F hF).2.1 ρ h).2.1 v |>.2
  obtain ⟨hcB, heB, -⟩ := hF.hB ρ h
  obtain ⟨hcJ, heJ, -⟩ := hF.hJ ρ h
  have hlatB := G.sp.colLat (2 * ρ + 2) (by omega) h
  have hlatJ := G.sp.colLat (2 * ρ + 1) (by omega) (by omega)
  have hx : ∀ n : ℕ, (-D.host.xi0) ^ n ≠ 0 := fun n => pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)
  let 𝔟B : Fin ρ → FI D := fun p => FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (p.1 + 1))⁻¹) *
    stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) (Fin.castLE (by omega) p)
  let 𝔟J : Fin ρ → FI D := fun p => FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (p.1 + 1))⁻¹) *
    stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) p)
  have lineB : ∀ (p : Fin ρ) (a : AE D), GlobalTheory.FinPl.colMul (F.dB ρ h).jX p a ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v) ↔
      a ∈ idV (𝔟B p) v := by
    intro p a
    have e1 : GlobalTheory.FinPl.colMul (F.dB ρ h).jX p a = fun k => a * incA D ((-D.host.xi0) ^ (p.1 + 1) *
        (G.colDec (2 * ρ + 2) (by omega) h).a k (Fin.castLE (by omega) p)) := by
      funext k
      simp only [GlobalTheory.FinPl.colMul, HypDec.jX, rat, Matrix.map_apply, heB, colsOf]
    rw [e1]
    have e2 : G.Λ (.grid (2 * ρ + 2) 0) = _ := hlatB
    rw [e2]
    exact GlobalTheory.StairLine.line_mem_iff _ _ _ _ (by simp only [Fin.coe_castLE]; omega) (hx _) v a
  have lineJ : ∀ (p : Fin ρ) (a : AE D), GlobalTheory.FinPl.colMul (F.dJ ρ h).jX p a ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) ↔
      a ∈ idV (𝔟J p) v := by
    intro p a
    have e1 : GlobalTheory.FinPl.colMul (F.dJ ρ h).jX p a = fun k => a * incA D ((-D.host.xi0) ^ (p.1 + 1) *
        (G.colDec (2 * ρ + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p)) := by
      funext k
      simp only [GlobalTheory.FinPl.colMul, HypDec.jX, rat, Matrix.map_apply, heJ, colsOf]
    rw [e1]
    have e2 : G.Λ (.grid (2 * ρ + 1) 0) = _ := hlatJ
    rw [e2]
    exact GlobalTheory.StairLine.line_mem_iff _ _ _ _ (by simp only [Fin.coe_castLE]; omega) (hx _) v a
  have hN : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hN' : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (GlobalTheory.AscFin.PrimStd.modulBar_ne_bot G.pl sc)
  have hA : G.pl.stA sc ≠ 0 := mul_ne_zero (GlobalTheory.CuspCharLattice.host_AA_ne_zero _) (inv_ne_zero hN')
  have hAb : G.pl.stAbar sc ≠ 0 := mul_ne_zero (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D) (inv_ne_zero hN)
  have hsp : ∀ n : ℕ, FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((-D.host.xi0) ^ n)⁻¹) ≠ 0 := fun n => by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact inv_ne_zero (hx _)
  have hb0B : ∀ p, 𝔟B p ≠ 0 := fun p => mul_ne_zero (hsp _) (by
    unfold stairId; exact mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hAb)))
  have hb0J : ∀ p, 𝔟J p ≠ 0 := fun p => mul_ne_zero (hsp _) (by
    unfold stairId; exact mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hAb)))
  have hrat : 𝔟J i * (𝔟B j)⁻¹ = FractionalIdeal.spanSingleton _ D.host.xi0 * G.pl.stAbar sc := by
    rw [mul_inv_eq_iff_eq_mul₀ (hb0B j)]
    have hneg : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (-D.host.xi0) = FractionalIdeal.spanSingleton _ D.host.xi0 :=
      FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, by simp⟩
    have e2 : ((-D.host.xi0) ^ (i.1 + 1))⁻¹ = -D.host.xi0 * ((-D.host.xi0) ^ (j.1 + 1))⁻¹ := by
      have hξ : -D.host.xi0 ≠ 0 := neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero
      rw [hij]
      field_simp
      ring
    show FractionalIdeal.spanSingleton _ _ * stairId _ _ _ _ = _ * (FractionalIdeal.spanSingleton _ _ * stairId _ _ _ _)
    rw [e2, ← FractionalIdeal.spanSingleton_mul_spanSingleton, hneg]
    unfold stairId
    simp only [Fin.coe_castLE]
    have e3 : 2 * ρ + 1 - 1 - i.1 = 2 * ρ + 2 - 1 - j.1 := by omega
    rw [e3, hij, pow_succ (G.pl.stAbar sc) (i.1 + 1), mul_inv]
    conv_lhs => rw [show (G.pl.stAbar sc ^ (i.1 + 1))⁻¹ = G.pl.stAbar sc * ((G.pl.stAbar sc ^ (i.1 + 1))⁻¹ * (G.pl.stAbar sc)⁻¹) by
      rw [mul_comm ((G.pl.stAbar sc ^ (i.1 + 1))⁻¹), ← mul_assoc, mul_inv_cancel₀ hAb, one_mul]]
    ring
  have hxA : GlobalTheory.FinPlLoc.idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j ∈ idAt D (· = v) :=
    Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)
  rw [← hrat]
  refine (f2 𝔠 _ h𝔠 (mul_ne_zero (hb0J i) (inv_ne_zero (hb0B j))) _ hxA).1 ?_
  intro s hs
  have hsA : s ∈ idAt D (· = v) := GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ s hs
  refine (f2 (𝔟B j) (𝔟J i) (hb0B j) (hb0J i) _ (Ideal.mul_mem_right _ _ hxA)).1 ?_
  intro c hc
  have hcA : c ∈ idAt D (· = v) := GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ c hc
  have h1 := hM _ ((lineB j c).2 hc) s hs
  have h3 := ((hmono _).1 h1).1 i
  rw [Matrix.mulVec_smul, GlobalTheory.FinPl.PsiUnit.mulVec_colMul, GlobalTheory.FinPl.PsiUnit.mulVec_colMul] at h3
  have h4 := (lineJ i _).1 h3
  have e4 : ((s • GlobalTheory.FinPl.colMul ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) j c) i) =
      GlobalTheory.FinPlLoc.idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j * s * c := by
    rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.FinPl.colMul]
    have hc' := (GlobalTheory.FinPlLoc.mem_idAt_iff _ c).1 hcA
    calc s * (c * _) = s * ((GlobalTheory.FinPlLoc.idem D (· = v) * c) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j) := by rw [hc']
      _ = _ := by ring
  rwa [e4] at h4
