import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MxAtOfMemDepLat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionPropertiesAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitIdealCompletionAtPlaceEqIntegralAdelesAtPlac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulFractionalIdealCompletionSubsetIffMemQuotient
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodIdealZpowCompletionAdeleConjIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiEOffS0ColumnPair

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

noncomputable section
namespace GlobalTheory.CharXFB.PairAt

variable {D : D7}
open GlobalTheory.SeeSaw (idV FI conjFI)

theorem conjFI_modul {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : Consts) :
    conjFI D ((P.modul sc : Ideal (𝓞 D.host.E)) : FI D) = ((P.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) := by
  have h := congrArg (conjFI D) (GlobalTheory.CharXFB.OffPl.conjFI_modulBar P sc)
  rw [GlobalTheory.CharXFB.OffPl.conjFI_conjFI] at h
  exact h.symm

private theorem mul_mem_idAt' {D : D7} {v : GlobalTheory.FinPl.Pl D} {a : AE D} (b : AE D) (ha : a ∈ idAt D (· = v)) :
    a * b ∈ idAt D (· = v) := by
  rw [GlobalTheory.FinPlLoc.mem_idAt_iff] at ha ⊢
  rw [← mul_assoc, ha]

theorem pair_mem_idV_of_maps {S T : HSp D} {ΛS : Lat S} {ΛT : Lat T} (sdT : IsSelfDualC T ΛT) {u : WO S T}
    {v : GlobalTheory.FinPl.Pl D} {yS : Fin S.rank → AE D} {yT : Fin T.rank → AE D} {𝔟S 𝔟T 𝔐 : FI D} (h𝔟S : 𝔟S ≠ 0)
    (h𝔟T : 𝔟T ≠ 0) (h𝔐 : 𝔐 ≠ 0)
    (hu : ∀ y ∈ latV S ΛS (· = v), ∀ s ∈ idV 𝔐 v, s • (u *ᵥ y) ∈ latV T ΛT (· = v))
    (hyS : ∀ t ∈ idV 𝔟S v, t • yS ∈ latV S ΛS (· = v)) (hyT : ∀ r ∈ idV 𝔟T v, r • yT ∈ latV T ΛT (· = v)) :
    GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS) ∈
      idV (1 * 𝔟T⁻¹ * (conjFI D 𝔐)⁻¹ * (conjFI D 𝔟S)⁻¹) v := by
  have hx : GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS) ∈ idAt D (· = v) :=
    mul_mem_idAt' _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)
  have cS : conjFI D 𝔟S ≠ 0 := fun h => h𝔟S ((conjFI D).injective (by rw [h, map_zero]))
  have cM : conjFI D 𝔐 ≠ 0 := fun h => h𝔐 ((conjFI D).injective (by rw [h, map_zero]))
  have n1 : (1 : FI D) * 𝔟T⁻¹ ≠ 0 := mul_ne_zero one_ne_zero (inv_ne_zero h𝔟T)
  have n2 : (1 : FI D) * 𝔟T⁻¹ * (conjFI D 𝔐)⁻¹ ≠ 0 := mul_ne_zero n1 (inv_ne_zero cM)
  refine (GlobalTheory.IdealQuot.mul_subset_iff D v (conjFI D 𝔟S) _ cS n2 _ hx).1 ?_
  intro t ht
  refine (GlobalTheory.IdealQuot.mul_subset_iff D v (conjFI D 𝔐) _ cM n1 _ (mul_mem_idAt' t hx)).1 ?_
  intro m hm
  refine (GlobalTheory.IdealQuot.mul_subset_iff D v 𝔟T 1 h𝔟T one_ne_zero _
    (mul_mem_idAt' m (mul_mem_idAt' t hx))).1 ?_
  intro r hr
  rw [GlobalTheory.SeeSaw.idV_one_eq_intAt]
  have ht' : cA D t ∈ idV 𝔟S v := by
    have h := GlobalTheory.SeeSaw.cA_mem_idV ht
    rwa [GlobalTheory.CharXFB.OffPl.conjFI_conjFI] at h
  have hm' : cA D m ∈ idV 𝔐 v := by
    have h := GlobalTheory.SeeSaw.cA_mem_idV hm
    rwa [GlobalTheory.CharXFB.OffPl.conjFI_conjFI] at h
  have hz := GlobalTheory.CharXFB.OffPl.hA_mem_intAt sdT (hyT r hr) (hu _ (hyS _ ht') _ hm')
  have hprod := GlobalTheory.IdealQuot.intAt_mul (GlobalTheory.FinPlLoc.idem_mem_intAt (D := D) (· = v)) hz
  have e : GlobalTheory.FinPlLoc.idem D (· = v) * hA T (r • yT) (cA D m • (u *ᵥ (cA D t • yS))) =
      GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS) * t * m * r := by
    rw [GlobalTheory.CharXFB.OffPl.hA_smul_left, GlobalTheory.CharXFB.OffPl.hA_smul_right, Matrix.mulVec_smul,
      GlobalTheory.CharXFB.OffPl.hA_smul_right, GlobalTheory.SeeSaw.cA_cA, GlobalTheory.SeeSaw.cA_cA]
    ring
  rw [← e]
  exact hprod

private theorem stairId_ne_zero_twisted_operators {D : D7} {A B : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hA : A ≠ 0) (hB : B ≠ 0)
    (c : ℕ) (p : Fin c) : GlobalTheory.ChiGrid.stairId A B c p ≠ 0 := by
  rw [GlobalTheory.ChiGrid.stairId]
  exact mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB))

theorem pair_mem_AA_AAbar : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (σ : ℕ) (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (u : WO (G.V (.grid (2 * σ + 2 + 1) 0)) (G.V (.grid (2 * σ + 2) 0))) (v : GlobalTheory.FinPl.Pl D), (∀ y ∈ latV (G.V (.grid (2 * σ + 2 + 1) 0)) (G.Λ (.grid (2 * σ + 2 + 1) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹ * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v, s • (u *ᵥ y) ∈ latV (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) (· = v)) → ∀ p : Fin (σ + 1), GlobalTheory.FinPlLoc.idem D (· = v) * hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) ∈ GlobalTheory.SeeSaw.idV (D.host.AA * D.host.AAbar) v := by
  intro D T L sc G σ h h' u v hu p
  have hAA : (D.host.AA : GlobalTheory.SeeSaw.FI D) ≠ 0 := by
    first
      | exact (GlobalTheory.SeeSaw.ChainIdeals.host_ne_zero D).2.1
      | exact Formalism.IndefR.Fin.PDA.AA_ne_zero (D := D)
      | exact GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign.AA_ne_zero D
      | exact GlobalTheory.SeeSaw.LatAt.AA_ne_zero (D := D)
  have hAbar : (D.host.AAbar : GlobalTheory.SeeSaw.FI D) ≠ 0 := fun e =>
    hAA ((conjFI D).injective (by rw [GlobalTheory.SeeSaw.conjFI_AA, e, map_zero]))
  have hm : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (G.pl.modul_ne_bot sc)
  have hmB : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 := fun e =>
    hm ((conjFI D).injective (by rw [conjFI_modul G.pl sc, e, map_zero]))
  have hstA : G.pl.stA sc ≠ 0 := by
    rw [GlobalTheory.ChiGrid.Places.stA]
    exact mul_ne_zero hAA (inv_ne_zero hmB)
  have hstAbar : G.pl.stAbar sc ≠ 0 := by
    rw [GlobalTheory.ChiGrid.Places.stAbar]
    exact mul_ne_zero hAbar (inv_ne_zero hm)
  have sdT : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.sp.V_is (2 * σ + 2) 0 (by omega) h' (Nat.zero_le _)).sd
  have hyT : ∀ r ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.ChiGrid.stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1)
      (Fin.castLE (by omega) p)) v,
      r • ratV (fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) ∈
        latV (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) (· = v) := by
    intro r hr
    have hl := GlobalTheory.CharXFB.OffPl.scaled_auxiliary_vector_mem_lattice_completion (G.colDec (2 * σ + 2) (by omega) h') (G.sp.P (2 * σ + 2)).lat _ _ v hr
    rw [show G.Λ (.grid (2 * σ + 2) 0) = _ from G.sp.colLat (2 * σ + 2) (by omega) h']
    exact hl
  have hyS : ∀ t ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.ChiGrid.stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * (σ + 1) + 1 - 1)
      (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) v,
      t • ratV (fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k
        (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) ∈
        latV (G.V (.grid (2 * σ + 2 + 1) 0)) (G.Λ (.grid (2 * σ + 2 + 1) 0)) (· = v) := by
    intro t ht
    have hl := GlobalTheory.CharXFB.OffPl.scaled_auxiliary_vector_mem_lattice_completion (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega))
      (G.sp.P (2 * (σ + 1) + 1)).lat _ _ v ht
    rw [show G.Λ (.grid (2 * σ + 2 + 1) 0) = _ from G.sp.colLat (2 * (σ + 1) + 1) (by omega) (by omega)]
    exact hl
  have key := pair_mem_idV_of_maps (ΛS := G.Λ (.grid (2 * σ + 2 + 1) 0)) sdT (u := u) (v := v)
    (stairId_ne_zero_twisted_operators hstA hstAbar _ _) (stairId_ne_zero_twisted_operators hstA hstAbar _ _)
    (mul_ne_zero (inv_ne_zero hAA) (inv_ne_zero hm)) hu hyS hyT
  have hcM : conjFI D (D.host.AA⁻¹ * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) =
      D.host.AAbar⁻¹ * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ := by
    rw [map_mul, map_inv₀, map_inv₀, GlobalTheory.SeeSaw.conjFI_AA, conjFI_modul]
  have hst := GlobalTheory.CharXFB.OffPl.stair_prod hstA hstAbar (GlobalTheory.CharXFB.OffPl.conjFI_stA G.pl sc)
    (GlobalTheory.CharXFB.OffPl.conjFI_stAbar G.pl sc) σ p (by omega) (by omega)
  have hid : ∀ X Y : GlobalTheory.SeeSaw.FI D, 1 * X⁻¹ * (D.host.AAbar⁻¹)⁻¹ * Y⁻¹ = D.host.AAbar * G.pl.stA sc →
      1 * X⁻¹ * (D.host.AAbar⁻¹ * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹)⁻¹ * Y⁻¹ =
        D.host.AA * D.host.AAbar := by
    intro X Y hXY
    rw [mul_inv, inv_inv (((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D))]
    calc 1 * X⁻¹ * ((D.host.AAbar⁻¹)⁻¹ * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)) * Y⁻¹
        = (1 * X⁻¹ * (D.host.AAbar⁻¹)⁻¹ * Y⁻¹) * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) := by
          ring
      _ = D.host.AAbar * (D.host.AA * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) *
          ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) := by
          rw [hXY, GlobalTheory.ChiGrid.Places.stA]
      _ = D.host.AA * D.host.AAbar * (((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ *
          ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)) := by ring
      _ = D.host.AA * D.host.AAbar := by rw [inv_mul_cancel₀ hmB, mul_one]
  rw [hcM] at key
  rw [← hid _ _ hst]
  exact key

end GlobalTheory.CharXFB.PairAt
