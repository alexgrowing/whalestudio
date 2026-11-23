import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAdjYZeroMemLatOIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentPowCompletionTrivialAtSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodIdealZpowCompletionAdeleConjIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JZeroMulMemLatticeIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotLineLatAtZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.ZLineIdeal

open GlobalTheory.SeeSaw

theorem idLat_span_singleton {D : D7} (L : HSp D) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (ζ : Fin L.rank → D.host.E) :
    idLat I (Submodule.span (𝓞 D.host.E) {ζ}) = LiftModel.lineLat L ζ I := by
  apply le_antisymm
  · rw [idLat, Submodule.span_le]
    rintro _ ⟨s, hs, y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    refine ⟨c • s, (I : Submodule (𝓞 D.host.E) D.host.E).smul_mem c hs, ?_⟩
    simp only [LinearMap.coe_restrictScalars, LinearMap.toSpanSingleton_apply]
    rw [smul_assoc, smul_comm]
  · rintro _ ⟨s, hs, rfl⟩
    apply Submodule.subset_span
    exact ⟨s, hs, ζ, Submodule.mem_span_singleton_self ζ, by simp⟩

theorem lineLat_smul {D : D7} (L : HSp D) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (ζ : Fin L.rank → D.host.E) {c : D.host.E} (hc : c ≠ 0) :
    LiftModel.lineLat L (c • ζ) (FractionalIdeal.spanSingleton _ c⁻¹ * I) = LiftModel.lineLat L ζ I := by
  ext y
  simp only [LiftModel.lineLat, Submodule.mem_map, LinearMap.coe_restrictScalars,
    LinearMap.toSpanSingleton_apply, FractionalIdeal.mem_coe]
  have e : ∀ x : D.host.E, c⁻¹ * x * c = x := fun x => by field_simp
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨x', hx', rfl⟩ := (FractionalIdeal.mem_singleton_mul).1 hx
    refine ⟨x', hx', ?_⟩
    rw [smul_smul, e]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨c⁻¹ * x, (FractionalIdeal.mem_singleton_mul).2 ⟨x, hx, rfl⟩, ?_⟩
    rw [smul_smul, e]

end GlobalTheory.ZLineIdeal

open GlobalTheory.SeeSaw in

theorem GlobalTheory.ZLineIdeal.bessel_core_lattice_meets_line_of_z_ideal : OnStd fun {D} _ _ {sc} {G} _ F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D), GlobalTheory.SeeSaw.LineId (F.oB ρ h) (F.ζ (ρ + 1)) (lat0 F ρ h) (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ + 1))⁻¹ * (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹)) v := by
  have H0 := @GlobalTheory.T.grid_lattices_compact_selfDual_splitting
  unfold OnStd All at H0 ⊢
  intro D hoff T L μ0 hL sc G W M hM F hF ρ h v
  have H := (H0 D hoff T L μ0 hL sc G W M hM F hF).2.1 ρ h
  have hx : ((-D.host.xi0) ^ (ρ + 1)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)
  have hζ : F.ζ (ρ + 1) ≠ 0 := by
    intro e
    have := (F.line (ρ + 1)).2
    rw [e] at this
    simp at this
  have eL : LiftModel.lineLat (negSp F.Lz) (F.ζ (ρ + 1))
      (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ + 1))⁻¹ * (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹)) =
      idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) := by
    rw [GlobalTheory.ZLineIdeal.idLat_span_singleton (negSp F.Lz), hF.ζ (ρ + 1), GlobalTheory.ZLineIdeal.lineLat_smul _ _ _ hx]
  refine LiftModel.lineId_of_split (F.oB ρ h) (F.ζ (ρ + 1)) (lat0 F ρ h) (G.Λ (.core (2 * ρ + 2))) _ _ v
    (LiftModel.lineLatAt_lineLat _ hζ _ v) ?_
  rw [eL]
  exact H.2.2.2 v
