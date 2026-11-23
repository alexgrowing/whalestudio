import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.BesIso

theorem symplO_negSp_eq {D : D7} (S T : HSp D) (x y : WO S T) : symplO (negSp S) T x y = -symplO S T x y := by
  have hinv : (-S.gram)⁻¹ = -S.gram⁻¹ :=
    Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul _ (gram_isUnit_det S)])
  have h : hO (negSp S) T x y = -hO S T x y := by
    simp only [hO, negSp_gram, hinv, Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]
  rw [symplO_eq, symplO_eq, h, mul_neg, map_neg]

theorem hO_extX_eq {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (a : Mx D T.rank ρ) (u : WO S T) :
    hO S T (d.extX T a) u = hO S T (d.extX T a) (d.extY T (u ⬝ d.jY)) := by
  have hu : u = d.extX T (u ⬝ d.jX) + d.ext0 T (u ⬝ d.j0) + d.extY T (u ⬝ d.jY) := ((d.coordS T).symm_apply_apply u).symm
  have h1 := d.hO_ext T a (u ⬝ d.jX) 0 (u ⬝ d.jY) 0 (u ⬝ d.j0)
  have h2 := d.hO_ext T a 0 0 (u ⬝ d.jY) 0 0
  simp only [map_zero, add_zero, zero_add] at h1 h2
  rw [← hu] at h1
  rw [h1, h2]
  simp [pairS, hO]

end GlobalTheory.AscFin.BesIso

open GlobalTheory.AscFin.BesIso in

theorem GlobalTheory.AscFin.BesIso.splits_iso : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * ρ + 1), MxAt (fun _ => True) (u ⬝ (F.dB ρ h).jY) ∧ ∀ a, (F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) a ∈ latRow G (2 * ρ + 1) → W.ψ (symplO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) ((F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) a) ((F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY))) = 1 := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  have sd : ∀ i, i ≤ D.R.m → 1 ≤ i → IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) := fun i hi h1 =>
    (G.isV (X := .grid i 0) ⟨hi, Nat.zero_le _⟩ (fun j hj => by injection hj with e1 e2; omega)).sd
  have sdV := isSelfDualC_neg (sd (2 * ρ + 2) h (by omega))
  have sdW := sd (2 * ρ + 1) (by omega) (by omega)
  have hmx : ∀ w, w ∈ latRow G (2 * ρ + 1) → MxAt (fun _ => True) w := fun w hw =>
    ((GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ sdV sdW (fun _ => True) w).1 hw.1).1
  refine ⟨fun i j => ?_, fun a ha => ?_⟩
  · simp only [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hmx u hu i k)
  · have key := (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ sdV sdW (fun _ => True) _ (hmx _ ha)).1 ha.1 u hu.1
    rw [symplO_negSp_eq, AddChar.map_neg_eq_inv, inv_eq_one] at key
    rw [symplO_eq] at key ⊢
    rw [← hO_extX_eq]
    exact key
