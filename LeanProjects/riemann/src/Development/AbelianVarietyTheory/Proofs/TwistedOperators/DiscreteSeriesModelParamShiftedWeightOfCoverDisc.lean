import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDiscreteSeriesConjugateReverseContragredientStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

noncomputable section

namespace GlobalTheory.ArchRec.Direct

def barRev {n : ℕ} (g : Mn n) : Mn n := (g.map (starRingEnd ℂ)).submatrix Fin.rev Fin.rev

theorem barRev_barRev {n : ℕ} (g : Mn n) : barRev (barRev g) = g := by
  ext i j
  simp [barRev]

theorem barRev_mul {n : ℕ} (g h : Mn n) : barRev (g * h) = barRev g * barRev h := by
  ext i j
  simp only [barRev, Matrix.submatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
  exact (Fintype.sum_equiv Fin.revPerm _ _ (fun x => by simp [Fin.revPerm_apply])).symm

theorem barRev_one {n : ℕ} : barRev (1 : Mn n) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [barRev]
  · have h' : i.rev ≠ j.rev := fun h'' => h (Fin.rev_injective h'')
    simp [barRev, Matrix.one_apply, h, h']

theorem barRev_conjTranspose {n : ℕ} (g : Mn n) : barRev gᴴ = (barRev g)ᴴ := by
  ext i j
  simp [barRev, Matrix.conjTranspose_apply]

theorem barRev_Jm {n : ℕ} (ε : Fin n → Bool) : barRev (Formalism.REAL.Jm ε) = Formalism.REAL.Jm (fun a => ε a.rev) := by
  ext i j
  by_cases h : i = j
  · subst h
    by_cases hε : ε i.rev <;> simp [barRev, Formalism.REAL.Jm, hε]
  · have h' : i.rev ≠ j.rev := fun h'' => h (Fin.rev_injective h'')
    simp [barRev, Formalism.REAL.Jm, Matrix.diagonal_apply, h, h']

theorem barRev_mem_K {n : ℕ} {ε : Fin n → Bool} {g : Mn n} (hg : g ∈ Formalism.REAL.Kset ε) :
    barRev g ∈ Formalism.REAL.Kset (fun a => ε a.rev) := by
  simp only [Formalism.REAL.Kset, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hu, hc⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff] at hu ⊢
    rw [Matrix.star_eq_conjTranspose, ← barRev_conjTranspose, ← barRev_mul, ← Matrix.star_eq_conjTranspose, hu,
      barRev_one]
  · rw [← barRev_Jm, ← barRev_mul, hc, barRev_mul]

theorem isKFin_barRev {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Mn n → (H →L[ℂ] H)) (x : H) :
    IsKFin (fun a => ε a.rev) (fun g => σ (barRev g)) x ↔ IsKFin ε σ x := by
  have hK : ∀ g ∈ Formalism.REAL.Kset (fun a => ε a.rev), barRev g ∈ Formalism.REAL.Kset ε := by
    intro g hg
    simpa only [Fin.rev_rev] using barRev_mem_K hg
  simp only [IsKFin, IsKStableOn]
  constructor
  · rintro ⟨S, hS, hx, hst⟩
    refine ⟨S, hS, hx, fun g hg v hv => ?_⟩
    simpa only [barRev_barRev] using hst (barRev g) (barRev_mem_K hg) v hv
  · rintro ⟨S, hS, hx, hst⟩
    exact ⟨S, hS, hx, fun g hg v hv => hst (barRev g) (hK g hg) v hv⟩

theorem isEnum_rev {n : ℕ} {S : SPar} {lam : Fin n → ℝ} {ε : Fin n → Bool} (h : IsEnum S lam ε) :
    IsEnum (dualPar S) (fun a => -lam a.rev) (fun a => ε a.rev) := by
  obtain ⟨hanti, r, hr, hS⟩ := h
  refine ⟨fun a b hab => ?_, fun a => -r a.rev, fun a => by simp [hr], ?_⟩
  · have hba : b.rev < a.rev := Fin.rev_lt_rev.mpr hab
    simpa using hanti hba
  · rw [show dualPar S = S.image fun x => (-x.1, x.2) from rfl, hS, Finset.image_image]
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.rev, by simp⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a.rev, rfl⟩

theorem Jm_rev {n : ℕ} (ε : Fin n → Bool) :
    Formalism.REAL.Jm (fun a => ε a.rev) = (Formalism.REAL.Jm ε).submatrix Fin.revPerm Fin.revPerm := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Formalism.REAL.Jm]
  · have h' : i.rev ≠ j.rev := fun h'' => h (Fin.rev_injective h'')
    simp [Formalism.REAL.Jm, Matrix.diagonal_apply, h, h']

def barModel {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (hds : ∀ τ, letI := M.nacg τ; letI := M.ips τ
      IsDS (fun a => M.ε τ a.rev) (fun a => -M.lam τ a.rev) (fun g => M.σ τ (barRev g))) :
    DSModel V (fun τ => dualPar (S τ)) where
  H := M.H
  nacg := M.nacg
  ips := M.ips
  σ τ g := M.σ τ (barRev g)
  lam τ a := -M.lam τ a.rev
  ε τ a := M.ε τ a.rev
  fr τ := (M.fr τ).submatrix Fin.revPerm (Equiv.refl _)
  enum τ := isEnum_rev (M.enum τ)
  ds := hds
  fr_unit τ := (Matrix.isUnit_submatrix_equiv _ _).2 (M.fr_unit τ)
  fr_gram τ := by
    rw [Jm_rev, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, M.fr_gram]
    rfl

theorem barRev_barMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (g : Mat p q) :
    barRev (barMat (e.trans Fin.revPerm) g) = plainMat e g := by
  ext i j
  simp [barRev, barMat, plainMat, Matrix.reindex_apply]

theorem barRev_plainMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (g : Mat p q) :
    barRev (plainMat (e.trans Fin.revPerm) g) = barMat e g := by
  ext i j
  simp [barRev, barMat, plainMat, Matrix.reindex_apply]

theorem directBridge : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D → DirectBridge D := by
  intro D hB X V S M τ p q l₁ l₂ c hpq h₁ h₂ hpar hhas hS
  obtain ⟨hsrc, htgt⟩ := hB
  have hds : ∀ τ, letI := M.nacg τ; letI := M.ips τ
      IsDS (fun a => M.ε τ a.rev) (fun a => -M.lam τ a.rev) (fun g => M.σ τ (barRev g)) :=
    fun τ => GlobalTheory.T.isDiscreteSeries_conjugate_reverse_contragredient _ _ _ _ _ (M.ds τ)
  have hset : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.HidaSetting X p q l₁ l₂ c (fun τ => dualPar (S τ)) τ := by
    refine ⟨hpq, h₁, h₂, hpar, hhas, ?_⟩
    show dualPar (S τ) = _
    rw [hS]
  obtain ⟨-, m, hm, hU⟩ := hsrc X V _ (barModel M hds) τ p q l₁ l₂ c hset
  obtain ⟨-, m', hm', hU'⟩ := htgt X V _ (barModel M hds) τ p q l₁ l₂ c hset
  obtain rfl : m' = m := by exact_mod_cast hm'.trans hm.symm
  refine ⟨m', hm', fun e he b => ?_⟩
  have he' : SignCompat ((barModel M hds).ε τ) (e.trans Fin.revPerm) := by
    intro a
    change M.ε τ ((e.trans Fin.revPerm) a).rev = a.isLeft
    simp [he a]
  cases b
  · obtain ⟨U, hUm⟩ := hU _ he'
    refine ⟨U, ⟨fun x y => map_add U x y, fun z x => ?_, U.bijective, fun x => U.norm_map x, fun g x => ?_,
      fun x => ?_⟩⟩
    · exact U.map_smul z x
    · have hg := hUm.grp g x
      change _ = _ • U (M.σ τ (barRev (barMat (e.trans Fin.revPerm) _)) x) at hg
      rw [barRev_barMat] at hg
      simpa [phi] using hg
    · exact (isKFin_barRev (M.ε τ) (M.σ τ) x).symm.trans (hUm.kfin x)
  · obtain ⟨U, hUm⟩ := hU' _ he'
    refine ⟨U, ⟨fun x y => map_add U x y, fun z x => ?_, U.bijective, fun x => U.norm_map x, fun g x => ?_,
      fun x => ?_⟩⟩
    · exact U.map_smulₛₗ z x
    · have hg := hUm.grp g x
      change _ = _ • U (M.σ τ (barRev (plainMat (e.trans Fin.revPerm) _)) x) at hg
      rw [barRev_plainMat] at hg
      simpa [phi] using hg
    · exact (isKFin_barRev (M.ε τ) (M.σ τ) x).symm.trans (hUm.kfin x)

end GlobalTheory.ArchRec.Direct

end
