import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletedHomLatticeModulusDepthMemShiftStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLocalEqCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarisationTwistLatticeSelfDualSameStabilisers
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.RowBig

open scoped Pointwise

variable {D : D7}

theorem idLat_one {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    idLat (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) Λ = Λ := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨s, hs, y, hy, rfl⟩
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hs
    rw [algebraMap_smul]
    exact Λ.smul_mem r hy
  · intro y hy
    exact Submodule.subset_span ⟨1, FractionalIdeal.one_mem_one _, y, hy, (one_smul _ _).symm⟩

theorem conjFI_coe (I : Ideal (𝓞 D.host.E)) :
    GlobalTheory.SeeSaw.conjFI D (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      ((D.host.conj • I : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  ext x
  rw [GlobalTheory.SeeSaw.mem_conjFI, FractionalIdeal.mem_coeIdeal, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨r, hr, hx⟩
    refine ⟨D.host.conj • r, Ideal.smul_mem_pointwise_smul _ _ _ hr, ?_⟩
    show D.host.conj (r : D.host.E) = x
    rw [show (r : D.host.E) = D.host.conj x from hx, GlobalTheory.SeeSaw.conj_conj_host]
  · rintro ⟨r, hr, rfl⟩
    refine ⟨D.host.conj⁻¹ • r, Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hr, ?_⟩
    show D.host.conj.symm (r : D.host.E) = D.host.conj (r : D.host.E)
    rw [AlgEquiv.symm_apply_eq, GlobalTheory.SeeSaw.conj_conj_host]

theorem conjFI_conjFI (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : GlobalTheory.SeeSaw.conjFI D (GlobalTheory.SeeSaw.conjFI D 𝔞) = 𝔞 := by
  ext x
  rw [GlobalTheory.SeeSaw.mem_conjFI, GlobalTheory.SeeSaw.mem_conjFI, GlobalTheory.SeeSaw.conj_conj_host]

theorem conjFI_shiftId {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) :
    GlobalTheory.SeeSaw.conjFI D (shiftId G) = (shiftId G)⁻¹ := by
  have hb : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      GlobalTheory.SeeSaw.conjFI D (G.modul : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := (conjFI_coe _).symm
  unfold shiftId
  rw [hb, map_mul, map_inv₀, conjFI_conjFI, mul_inv, inv_inv, mul_comm]

theorem shiftId_ne_zero {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) : shiftId G ≠ 0 := by
  have hm : (G.modul : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hb : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [show ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      GlobalTheory.SeeSaw.conjFI D (G.modul : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) from (conjFI_coe _).symm]
    exact (RingEquiv.map_ne_zero_iff _).2 hm
  exact mul_ne_zero hm (inv_ne_zero hb)

theorem isSelfDualC_idLat_shiftId {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {S : HSp D} (Λ : Lat S)
    (hΛ : IsSelfDualC S Λ) : IsSelfDualC S (idLat (shiftId G) Λ) := by
  refine GlobalTheory.ScaleSelfDual.isSelfDualC_scaleLat S Λ hΛ (shiftId_ne_zero G) fun c => ?_
  rw [← conjFI_shiftId, GlobalTheory.SeeSaw.mem_conjFI, Formalism.BasicNotions.bridge_star_holds D.R D.host c]

theorem latRow_le_latBig : All fun {D} _ _ _ {G} _ _ => ∀ i, 1 ≤ i → i < D.R.m → latRow G i ≤ latBig G i := by
  intro D hq T L μ0 hL sc G W M hM i hi1 him u hu
  have hS : IsSelfDualC (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0)) :=
    (G.isV (X := .grid (i + 1) 0) ⟨by omega, by omega⟩ (fun j h => by injection h with h1 h2; omega)).sd
  have hT : IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) :=
    (G.isV (X := .grid i 0) ⟨by omega, by omega⟩ (fun j h => by injection h with h1 h2; omega)).sd
  have h1 := idLat_one (G.Λ (.grid i 0))
  have hsh := isSelfDualC_idLat_shiftId G _ hT
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have hu' : u ∈ latO (negSp (G.V (.grid (i + 1) 0))) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
      (G.Λ (.grid i 0) : Set _) (fun _ => True) ∧
      ∀ e : AE D, IsIdemSum e G.pl.W0 → e • u ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) := hu
  have key := GlobalTheory.T.completedHomLattice_modulus_depth_mem_shift hq μ0 hL G (G.Λ (.grid (i + 1) 0)) 1 (G.Λ (.grid i 0)) hS (by rw [h1]; exact hT)
    (by rw [one_mul]; exact hsh) u (by rw [h1]; exact GlobalTheory.RowLoc.mem_latO_negSp.1 hu'.1) ⟨e, he, by rw [h1]; exact hu'.2 e he⟩
  rw [one_mul] at key
  exact key

end GlobalTheory.RowBig

end
