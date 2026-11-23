import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionCoreProjMulCoreEqOne

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.MonoJac

variable {D : D7}

open GlobalTheory.SeeSaw.SplitLat (colProj colProj_mulVec colMul_rat rat_mulVec_mem_latV mulVec_eq_sum_colMul)

theorem monoAt_of_proj {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀)
    (hX : ∀ i : Fin ρ, ∀ x ∈ L, colProj d.qX d.e i *ᵥ x ∈ L)
    (hY : ∀ i : Fin ρ, ∀ x ∈ L, colProj d.qY d.e' i *ᵥ x ∈ L)
    (h0 : ∀ x ∈ L, d.q0 *ᵥ x ∈ L₀) (hi : ∀ x ∈ L₀, d.i₀ *ᵥ x ∈ L) (v : GlobalTheory.FinPl.Pl D) :
    MonoAt d L L₀ v := by
  intro y
  constructor
  · intro hy
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · change GlobalTheory.FinPl.colMul (rat d.e) i ((rat d.qX *ᵥ y) i) ∈ _
      rw [colMul_rat]
      exact rat_mulVec_mem_latV _ (hX i) _ hy
    · change GlobalTheory.FinPl.colMul (rat d.e') i ((rat d.qY *ᵥ y) i) ∈ _
      rw [colMul_rat]
      exact rat_mulVec_mem_latV _ (hY i) _ hy
    · exact rat_mulVec_mem_latV d.q0 h0 _ hy
  · rintro ⟨h1, h3, h2⟩
    have e : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
        d.sum_eq_one, Matrix.one_mulVec]
    rw [e, mulVec_eq_sum_colMul d.jX, mulVec_eq_sum_colMul d.jY]
    refine add_mem (add_mem (sum_mem fun i _ => h1 i) ?_) (sum_mem fun i _ => h3 i)
    exact rat_mulVec_mem_latV d.i₀ hi _ h2

open GlobalTheory.SeeSaw.SplitLat (colProj)

theorem sumLat_map {n k c : ℕ} {M : Matrix (Fin n) (Fin k) D.host.E} {Λ : Submodule (𝓞 D.host.E) (Fin k → D.host.E)}
    {a : Matrix (Fin n) (Fin c) D.host.E} {𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}
    (N : Matrix (Fin n) (Fin n) D.host.E) (w : Fin c → D.host.E) (hM : N * M = 0) (ha : N * a = a * Matrix.diagonal w)
    (hw : ∀ p, w p = 0 ∨ w p = 1) : ∀ x ∈ sumLat M Λ a 𝔟, N *ᵥ x ∈ sumLat M Λ a 𝔟 := by
  rintro _ ⟨y, -, u, hu, rfl⟩
  refine ⟨0, Λ.zero_mem, Matrix.diagonal w *ᵥ u, fun p => ?_, ?_⟩
  · rw [Matrix.mulVec_diagonal]
    rcases hw p with h | h
    · rw [h, zero_mul]; exact (𝔟 p).zero_mem
    · rw [h, one_mul]; exact hu p
  · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM, ha, ← Matrix.mulVec_mulVec,
      Matrix.zero_mulVec, Matrix.mulVec_zero, zero_add]

theorem sumLat_proj {n k c : ℕ} {M : Matrix (Fin n) (Fin k) D.host.E} {Λ : Submodule (𝓞 D.host.E) (Fin k → D.host.E)}
    {a : Matrix (Fin n) (Fin c) D.host.E} {𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}
    (q : Matrix (Fin k) (Fin n) D.host.E) (hM : q * M = 1) (ha : q * a = 0) : ∀ x ∈ sumLat M Λ a 𝔟, q *ᵥ x ∈ Λ := by
  rintro _ ⟨y, hy, u, -, rfl⟩
  rwa [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM, ha, Matrix.one_mulVec, Matrix.zero_mulVec,
    add_zero]

theorem mem_sumLat_of {n k c : ℕ} {M : Matrix (Fin n) (Fin k) D.host.E} {Λ : Submodule (𝓞 D.host.E) (Fin k → D.host.E)}
    {a : Matrix (Fin n) (Fin c) D.host.E} {𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {y : Fin k → D.host.E}
    (hy : y ∈ Λ) : M *ᵥ y ∈ sumLat M Λ a 𝔟 :=
  ⟨y, hy, 0, fun p => (𝔟 p).zero_mem, by rw [Matrix.mulVec_zero, add_zero]⟩

theorem colProj_mul {S : HSp D} {ρ m l : ℕ} (q : Matrix (Fin ρ) (Fin m) D.host.E) (f : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (i : Fin ρ) (N : Matrix (Fin m) (Fin l) D.host.E) : colProj (S := S) q f i * N = colProj (S := S) (q * N) f i := by
  ext k j
  simp only [colProj, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, mul_assoc]

theorem colProj_zero {S : HSp D} {ρ m : ℕ} (f : Matrix (Fin S.rank) (Fin ρ) D.host.E) (i : Fin ρ) :
    colProj (S := S) (0 : Matrix (Fin ρ) (Fin m) D.host.E) f i = 0 := by
  ext k j
  simp [colProj]

section SlopeTestRemainingChoices

variable {A B : HSp D} {c ρ : ℕ}

def cfE (c : ℕ) : Matrix (Fin ρ) (Fin c) D.host.E := fun p q => if p.1 = q.1 then ((-D.host.xi0) ^ (p.1 + 1))⁻¹ else 0

def cfE' (c : ℕ) (s : Fin ρ → D.host.E) : Matrix (Fin ρ) (Fin c) D.host.E := fun p q => if q.1 + p.1 + 1 = c then (s p)⁻¹ else 0

theorem eq_idempotent_mul_add_of_mul_sub_eq {n : ℕ} (a : Matrix (Fin n) (Fin c) D.host.E) (hc : c = 2 * ρ) (h : ρ ≤ c) (s : Fin ρ → D.host.E)
    (hs : ∀ p, s p ≠ 0) :
    a = (colsOf a (Fin.castLE h) (fun p : Fin ρ => (-D.host.xi0) ^ (p.1 + 1)) : Matrix (Fin n) (Fin ρ) D.host.E) *
        (cfE c : Matrix (Fin ρ) (Fin c) D.host.E) +
      (colsOf a (fun p : Fin ρ => (Fin.castLE h p : Fin c).rev) s : Matrix (Fin n) (Fin ρ) D.host.E) *
        (cfE' c s : Matrix (Fin ρ) (Fin c) D.host.E) := by
  have hx : ∀ p : ℕ, ((-D.host.xi0) ^ (p + 1)) ≠ 0 := fun p => pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)
  refine Matrix.ext fun k q => ?_
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [colsOf, cfE, cfE']
  by_cases hq : q.1 < ρ
  · rw [Finset.sum_eq_single ⟨q.1, hq⟩, Finset.sum_eq_zero]
    · rw [if_pos rfl, add_zero, show (Fin.castLE h ⟨q.1, hq⟩ : Fin c) = q from Fin.ext rfl, mul_comm,
        ← mul_assoc, inv_mul_cancel₀ (hx _), one_mul]
    · intro p _
      rw [if_neg (by omega), mul_zero]
    · intro p _ hp
      rw [if_neg (fun e => hp (Fin.ext e)), mul_zero]
    · intro hn; exact absurd (Finset.mem_univ _) hn
  · have hp' : c - 1 - q.1 < ρ := by have := q.2; omega
    rw [Finset.sum_eq_zero, Finset.sum_eq_single ⟨c - 1 - q.1, hp'⟩]
    · rw [if_pos (by have := q.2; simp only [Fin.val_mk]; omega), zero_add,
        show ((Fin.castLE h ⟨c - 1 - q.1, hp'⟩ : Fin c).rev) = q from Fin.ext (by simp [Fin.val_rev]; omega),
        mul_comm, ← mul_assoc, inv_mul_cancel₀ (hs _), one_mul]
    · intro p _ hp
      rw [if_neg (fun e => hp (Fin.ext (show p.1 = c - 1 - q.1 by omega))), mul_zero]
    · intro hn; exact absurd (Finset.mem_univ _) hn
    · intro p _
      rw [if_neg (by have := p.2; omega), mul_zero]

end SlopeTestRemainingChoices

open GlobalTheory.SeeSaw.SplitLat (colProj)

theorem auxiliaryLattice_splitsAlongWitt_at_place {A B : HSp D} {c ρ : ℕ} (t : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B A ρ) (hc : c = 2 * ρ)
    (hh : IsAuxiliaryVectorWittDec t d) (hi : d.i₀ = frameMat B A t.ι) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : GlobalTheory.FinPl.Pl D) : MonoAt d (t.lat Λ 𝔟) Λ v := by
  obtain ⟨h2, he, s, he'⟩ := hh
  have hρ : ρ ≤ c := by omega
  have hx : ∀ p : ℕ, ((-D.host.xi0) ^ (p + 1)) ≠ 0 := fun p => pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)
  have hs : ∀ p, s p ≠ 0 := by
    intro p hp
    have h1 := congrFun (congrFun d.e'e p) p
    rw [Matrix.one_apply_eq] at h1
    have hcol : ∀ k, d.e' k p = 0 := fun k => by rw [he']; simp [colsOf, hp]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hcol] at h1
  have ha := eq_idempotent_mul_add_of_mul_sub_eq t.a hc hρ s hs
  rw [← he, ← he'] at ha
  have hX : d.qX * t.a = cfE c := by
    rw [ha, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.SeeSaw.SplitLat.qX_e, GlobalTheory.SeeSaw.SplitLat.qX_e',
      Matrix.one_mul, Matrix.zero_mul, add_zero]
  have hY : d.qY * t.a = cfE' c s := by
    rw [ha, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.SeeSaw.SplitLat.qY_e, GlobalTheory.SeeSaw.SplitLat.qY_e',
      Matrix.one_mul, Matrix.zero_mul, zero_add]
  have h0 : d.q0 * t.a = 0 := by
    rw [ha, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.SeeSaw.SplitLat.wittDecomposition_coreProj_mul_e_eq_zero, GlobalTheory.SeeSaw.SplitLat.wittZeroProjection_mul_dualBasis_eq_zero,
      Matrix.zero_mul, Matrix.zero_mul, add_zero]
  refine monoAt_of_proj d _ _ (fun i => ?_) (fun i => ?_) ?_ ?_ v
  · refine sumLat_map _ (Pi.single (Fin.castLE hρ i) 1) ?_ ?_ ?_
    · rw [colProj_mul, ← hi, GlobalTheory.SeeSaw.SplitLat.qX_i₀, colProj_zero]
    · rw [colProj_mul, hX]
      refine Matrix.ext fun k q => ?_
      rw [Matrix.mul_diagonal, he]
      simp only [colProj, Matrix.of_apply, colsOf, cfE]
      by_cases hq : i.1 = q.1
      · have e : (Fin.castLE hρ i : Fin c) = q := Fin.ext hq
        subst e
        rw [if_pos hq, Pi.single_eq_same, mul_one, mul_comm ((-D.host.xi0) ^ _), mul_assoc, mul_inv_cancel₀ (hx _),
          mul_one]
      · have e : q ≠ (Fin.castLE hρ i : Fin c) := fun e => hq (by rw [e]; rfl)
        rw [if_neg hq, mul_zero, Pi.single_apply, if_neg e, mul_zero]
    · intro p
      rw [Pi.single_apply]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
  · refine sumLat_map _ (Pi.single (Fin.castLE hρ i : Fin c).rev 1) ?_ ?_ ?_
    · rw [colProj_mul, ← hi, GlobalTheory.SeeSaw.SplitLat.qY_i₀, colProj_zero]
    · rw [colProj_mul, hY]
      refine Matrix.ext fun k q => ?_
      rw [Matrix.mul_diagonal, he']
      simp only [colProj, Matrix.of_apply, colsOf, cfE']
      by_cases hq : q.1 + i.1 + 1 = c
      · have e : (Fin.castLE hρ i : Fin c).rev = q := Fin.ext (by simp [Fin.val_rev]; omega)
        subst e
        rw [if_pos hq, Pi.single_eq_same, mul_one, mul_comm (s i), mul_assoc, mul_inv_cancel₀ (hs _), mul_one]
      · have e : q ≠ (Fin.castLE hρ i : Fin c).rev := fun e => hq (by rw [e]; simp [Fin.val_rev]; omega)
        rw [if_neg hq, mul_zero, Pi.single_apply, if_neg e, mul_zero]
    · intro p
      rw [Pi.single_apply]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
  · exact sumLat_proj d.q0 (by rw [← hi]; exact GlobalTheory.SeeSaw.SplitLat.wittDecomposition_coreProj_mul_core_eq_one d) h0
  · intro x hx
    rw [hi]
    exact mem_sumLat_of hx

theorem monoAt_jac : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Frames G), Std F →
    ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D),
      MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v := by
  intro D T L sc G F hF ρ h v
  have H := auxiliaryLattice_splitsAlongWitt_at_place (G.colDec (2 * ρ + 1) (by omega) (by omega)) (F.dJ ρ h) (by omega) (hF.hJ ρ h) (hF.aJ ρ h)
    (G.Λ (.core (2 * ρ + 1))) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) v
  rw [← G.sp.colLat (2 * ρ + 1) (by omega) (by omega)] at H
  exact H

end GlobalTheory.AscFin.MonoJac

end
