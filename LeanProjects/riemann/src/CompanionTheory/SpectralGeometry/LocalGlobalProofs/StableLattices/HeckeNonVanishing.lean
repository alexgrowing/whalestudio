import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantEquality

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof

open CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open Formalism.REAL (GlRel qdet)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (cminor capelliC capEntry nnPlus eeV capelliAPlus capelliExpand)

theorem eeV_eq_om {n : ℕ} (X : GMod n) : eeV X.E = om X := by
  refine LinearMap.ext fun u => funext fun b => ?_
  simp [eeV, om_apply]

theorem exists_ker {M : Type} [AddCommGroup M] [Module ℂ M] [Nontrivial M] (T : Module.End ℂ M) {k : ℕ}
    (h : T ^ k = 0) : ∃ v : M, v ≠ 0 ∧ T v = 0 := by
  obtain ⟨w, hw⟩ := exists_ne (0 : M)
  have hex : ∃ j : ℕ, (T ^ j) w = 0 := ⟨k, by simp [h]⟩
  classical
  have hj := Nat.find_spec hex
  have hmin := fun i => Nat.find_min hex (m := i)
  set j := Nat.find hex with hjdef
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · rw [h0] at hj
    exact absurd (by simpa using hj) hw
  · refine ⟨(T ^ (j - 1)) w, hmin _ (by omega), ?_⟩
    rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel hpos]
    exact hj

theorem eq_zero_of_nilp {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {c : ℂ} {k : ℕ}
    (hc : c ≠ 0) (h : (T - c • (1 : Module.End ℂ M)) ^ k = 0) {v : M} (hv : T v = 0) : v = 0 := by
  have key : ∀ j : ℕ, ((T - c • (1 : Module.End ℂ M)) ^ j) v = (-c) ^ j • v := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, Module.End.mul_apply]
      have : (T - c • (1 : Module.End ℂ M)) v = (-c) • v := by simp [hv]
      rw [this, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have := key k
  rw [h] at this
  have h2 : (-c) ^ k • v = 0 := by simpa using this.symm
  exact (smul_eq_zero.mp h2).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr hc))

theorem exists_nnPlus_ne {m : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
    (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (hE : GlRel E) (w : ℂ) {v : M} (hv0 : v ≠ 0)
    (hinj : capelliC E (w - 1) v = 0 → v = 0) :
    ∃ y : Fin (m + 1) → ℂ, nnPlus E y w v ≠ 0 := by
  by_contra hall
  push_neg at hall
  have hmin : ∀ d c : Fin (m + 1), cminor E d.succAbove c.succAbove (w - 1) v = 0 := by
    intro d c
    have h := congrFun (hall (Pi.single c 1)) d
    simp only [nnPlus, Pi.zero_apply] at h
    rw [Finset.sum_eq_single c (fun b _ hb => by simp [Pi.single_eq_of_ne hb])
      (fun hc => absurd (Finset.mem_univ c) hc)] at h
    simpa [pow_ne_zero] using h
  have hexp := (capelliExpand (𝒰 := Module.End ℂ M) m E (w - 1) hE).2 0 0
  have happ := LinearMap.congr_fun hexp v
  simp only [if_true, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, hmin, map_zero,
    smul_zero, Finset.sum_const_zero] at happ
  exact hv0 (hinj happ.symm)

theorem nonVan : NonVan := by
  intro n X χ s hX hnt hfree
  have hQ := GlobalTheory.CompanionTheory.RgExhHecke.qdetEq
  obtain ⟨k, hk⟩ := hX
  haveI := hnt
  cases n with
  | zero => exact s.elim0
  | succ m =>
    set w : ℂ := (((m + 1 : ℕ) : ℂ) - 1) / 2 - χ s with hw

    have h1 := hk (-χ s)
    have hcap0 : Formalism.QuantumDeterminants.capP χ (-χ s) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ s) (by simp)
    rw [hcap0, zero_smul, sub_zero] at h1
    obtain ⟨v, hv0, hv⟩ := exists_ker _ h1
    have hCw : capelliC X.E w v = 0 := by
      rw [← hQ]
      rw [show w = -χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2 by rw [hw]; ring]
      exact hv

    have h2 := hk (-χ s - 1)
    have hc : Formalism.QuantumDeterminants.capP χ (-χ s - 1) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun t _ h => hfree t ?_
      linear_combination h
    have hinj : capelliC X.E (w - 1) v = 0 → v = 0 := by
      intro h
      rw [← hQ] at h
      rw [show w - 1 = -χ s - 1 + (((m + 1 : ℕ) : ℂ) - 1) / 2 by rw [hw]; ring] at h
      exact eq_zero_of_nilp _ hc h2 h
    obtain ⟨y, hy⟩ := exists_nnPlus_ne X.E X.gl w hv0 hinj
    have hev := capelliAPlus X.V m X.E y w v X.gl hCw
    rw [eeV_eq_om] at hev
    intro hbot
    apply hy
    have hmem : nnPlus X.E y w v ∈ stepSub X (χ s) := by
      unfold stepSub
      refine Module.End.mem_maxGenEigenspace _ _ _ |>.mpr ⟨1, ?_⟩
      rw [pow_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hev]
      rw [hw, ← sub_smul]
      have : -((((m + 1 : ℕ) : ℂ) - 1) / 2 - χ s) - (χ s - (((m + 1 : ℕ) : ℂ) - 1) / 2) = 0 := by ring
      rw [this, zero_smul]
    rw [hbot] at hmem
    simpa using hmem

end GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof
