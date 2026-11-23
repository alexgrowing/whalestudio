import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.BesselPieceB

variable {D : D7}

theorem mxAt_mul_left {P : GlobalTheory.FinPl.Pl D → Prop} {k m n : ℕ} (M : Mx D k m) {x : Mx D m n} (hx : MxAt P x) :
    MxAt P (M ⬝ x) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)

theorem mxAt_mul_right {P : GlobalTheory.FinPl.Pl D → Prop} {k m n : ℕ} {x : Mx D k m} (hx : MxAt P x) (M : Mx D m n) :
    MxAt P (x ⬝ M) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

theorem finLat_comap_mul {k n k' m' : ℕ} {A : AddSubgroup (Mx D k' m')} (hA : FinLat A) (f : Mx D k n →+ Mx D k' m')
    (M : Mx D k' k) (N : Mx D n m') (M' : Mx D k k') (N' : Mx D m' n) (hf : ∀ x : Mx D k n, f x = M ⬝ x ⬝ N)
    (hM : M' ⬝ M = 1) (hN : N ⬝ N' = 1) : FinLat (A.comap f) := by
  haveI : T2Space (Mx D k' m') := (lattice_Mx D k' m').2.2.2.1
  have hfc : Continuous f := by
    have : (f : Mx D k n → Mx D k' m') = fun x : Mx D k n => M ⬝ x ⬝ N := funext hf
    rw [this]; exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hgc : Continuous fun y : Mx D k' m' => M' ⬝ y ⬝ N' :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hgf : ∀ x, M' ⬝ f x ⬝ N' = x := fun x => by
    have e : M' ⬝ f x ⬝ N' = (M' ⬝ M) ⬝ x ⬝ (N ⬝ N') := by rw [hf]; simp only [Matrix.mul_assoc]
    rw [e, hM, hN, Matrix.one_mul, Matrix.mul_one]
  refine ⟨fun a ha => ?_, ?_, ?_⟩
  · rw [← hgf a]; exact mxAt_mul_right (mxAt_mul_left _ (hA.fin _ ha)) _
  · refine (hA.cpt.image hgc).of_isClosed_subset (hA.cpt.isClosed.preimage hfc) fun a ha => ⟨f a, ha, hgf a⟩
  · obtain ⟨U, hU, h0, hUA⟩ := hA.opn
    refine ⟨f ⁻¹' U, hU.preimage hfc, by simpa using h0, fun a ha hfin => hUA _ ha ?_⟩
    rw [hf]; exact mxAt_mul_right (mxAt_mul_left _ hfin) _

end GlobalTheory.BesselPieceB

open GlobalTheory.BesselPieceB in

theorem GlobalTheory.BesselPieceB.finLat_pcBF_B : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m),
    FinLat (pcBF W F ρ h).B₁ ∧ FinLat (pcBF W F ρ h).B₂ := by
  intro D hD T L μ0 hL sc G W M hM F hF ρ h
  have hB : FinLat (latBig G (2 * ρ + 1)) :=
    ((GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hD T L μ0 hL sc G W M hM F hF).1 (2 * ρ + 1) (by omega)).2.2.1
  exact ⟨finLat_comap_mul hB _ (F.dJ ρ h).jX (F.dB ρ h).p0 (F.dJ ρ h).pX (F.dB ρ h).j0 (fun _ => rfl)
      (F.dJ ρ h).pX_jX (F.dB ρ h).p0_j0,
    finLat_comap_mul hB _ (F.dJ ρ h).jY (F.dB ρ h).p0 (F.dJ ρ h).pY (F.dB ρ h).j0 (fun _ => rfl)
      (F.dJ ρ h).pY_jY (F.dB ρ h).p0_j0⟩
