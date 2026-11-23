import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.DoubleInd

variable {D : D7} {c : Comm D}

def W (t : Tup c) (k : ℕ) : ℂ :=
  ∏ l ∈ Finset.range k, t.cV (2 * l) * t.cK (2 * l) * t.cK (2 * l + 1)

theorem up_succ (t : Tup c) (k : ℕ) (ψ : t.Col 0) :
    t.up (k + 1) ψ = t.K (2 * k + 1) (t.K (2 * k) (t.S (2 * k) (t.up k ψ))) := rfl

theorem up_mem (t : Tup c) (ht : t.Is) (ψ : t.Col 0) (hψ : ψ ∈ t.Ram 0) :
    ∀ k, 2 * k ≤ D.R.m → t.up k ψ ∈ t.Ram (2 * k) := by
  intro k
  induction k with
  | zero => intro _; exact hψ
  | succ k ih =>
    intro hk
    rw [up_succ]
    have h0 := ih (by omega)
    have h1 := ht.stabS (2 * k) (by omega) _ h0
    have h2 := ht.stabK (2 * k) (by omega) _ h1
    exact ht.stabK (2 * k + 1) (by omega) _ h2

theorem up_ind {𝒯 : Type} (t : 𝒯 → Tup c) (ht : ∀ s, (t s).Is) (hS : StepX t) :
    ∀ k ρ (h : 2 * k + 2 * ρ + 2 = D.R.m) (I : Type) [Fintype I] (s : I → 𝒯) (β : I → ℂ) (ψ : ∀ i, (t (s i)).Col 0)
      (G : ∀ i, (t (s i)).CC (2 * k)), (∀ i, ψ i ∈ (t (s i)).Ram 0) →
      (∀ y v, ∑ i, β i * W (t (s i)) k * (t (s i)).per (2 * k) ρ h ((t (s i)).up k (ψ i)) (G i) y v = 0) →
      ∀ ρ₀ (h₀ : 0 + 2 * ρ₀ + 2 = D.R.m) y v,
        ∑ i, β i * (∏ j ∈ Finset.range (2 * k), (t (s i)).cI j) *
          (t (s i)).per 0 ρ₀ h₀ (ψ i) ((t (s i)).dn (2 * k) (G i)) y v = 0 := by
  intro k
  induction k with
  | zero =>
    intro ρ h I _ s β ψ G hψ hyp ρ₀ h₀ y v
    have hρ : ρ₀ = ρ := by omega
    subst hρ
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hyp y v)
    rw [show (∏ j ∈ Finset.range (2 * 0), (t (s i)).cI j) = (1 : ℂ) by simp,
      show W (t (s i)) 0 = 1 by simp [W]]
    rfl
  | succ k ih =>
    intro ρ h I _ s β ψ G hψ hyp ρ₀ h₀ y v
    have h' : 2 * k + 2 * (ρ + 1) + 2 = D.R.m := by omega
    have hmem : ∀ i, (t (s i)).up k (ψ i) ∈ (t (s i)).Ram (2 * k) :=
      fun i => up_mem _ (ht _) _ (hψ i) k (by omega)
    have hst := hS (2 * k) ρ h' I s (fun i => β i * W (t (s i)) k) (fun i => (t (s i)).up k (ψ i)) G hmem (by
      intro y v
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hyp y v)
      have hp : (t (s i)).per (2 * k + 1 + 1) ρ (idx_step h')
          ((t (s i)).K (2 * k + 1) ((t (s i)).K (2 * k) ((t (s i)).S (2 * k) ((t (s i)).up k (ψ i))))) (G i) y v =
          (t (s i)).per (2 * (k + 1)) ρ h ((t (s i)).up (k + 1) (ψ i)) (G i) y v := rfl
      rw [hp]
      simp only [W, Finset.prod_range_succ]
      ring)
    have hi := ih (ρ + 1) h' I s (fun i => β i * ((t (s i)).cI (2 * k) * (t (s i)).cI (2 * k + 1))) ψ
      (fun i => (t (s i)).io (2 * k) ((t (s i)).io (2 * k + 1) (G i))) hψ (by
        intro y v
        refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hst y v)
        ring) ρ₀ h₀ y v
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hi
    have hp : ∏ j ∈ Finset.range (2 * (k + 1)), (t (s i)).cI j =
        (∏ j ∈ Finset.range (2 * k), (t (s i)).cI j) * ((t (s i)).cI (2 * k) * (t (s i)).cI (2 * k + 1)) := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ]
      ring
    have hd : (t (s i)).per 0 ρ₀ h₀ (ψ i) ((t (s i)).dn (2 * (k + 1)) (G i)) y v =
        (t (s i)).per 0 ρ₀ h₀ (ψ i) ((t (s i)).dn (2 * k) ((t (s i)).io (2 * k) ((t (s i)).io (2 * k + 1) (G i)))) y v := rfl
    rw [hp, hd]
    ring

end GlobalTheory.SeeSaw.DoubleInd

namespace GlobalTheory.SeeSaw

open GlobalTheory.SeeSaw.DoubleInd in

theorem mainX_of_stepX_lastX : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), (∀ s, (t s).Is) → StepX t → LastX t → MainX t := by
  intro D c 𝒯 t ht hS hL
  intro n h h₀ I _ s α ψ F hψ hyp y v
  have hmem : ∀ i, (t (s i)).up n (ψ i) ∈ (t (s i)).Ram (2 * n) :=
    fun i => up_mem _ (ht _) _ (hψ i) n (by omega)
  have hL' := hL (2 * n) h I s (fun i => α i * W (t (s i)) n) (fun i => (t (s i)).up n (ψ i)) F hmem (by
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hyp
    have hp : (t (s i)).tail (2 * n + 1 + 1) h
        ((t (s i)).K (2 * n + 1) ((t (s i)).K (2 * n) ((t (s i)).S (2 * n) ((t (s i)).up n (ψ i))))) (F i) =
        (t (s i)).tail (2 * (n + 1)) h ((t (s i)).up (n + 1) (ψ i)) (F i) := rfl
    rw [hp]
    simp only [Tup.cTop, W, Finset.prod_range_succ]
    ring)
  have hu := up_ind t ht hS n 0 h I s (fun i => α i * ((t (s i)).cI (2 * n) * (t (s i)).cI (2 * n + 1))) ψ
    (fun i => (t (s i)).io (2 * n) ((t (s i)).ioT (2 * n) h (F i))) hψ (by
      intro y v
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hL' y v)
      ring) n h₀ y v
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hu
  have hc : (t (s i)).cBot =
      (∏ j ∈ Finset.range (2 * n), (t (s i)).cI j) * ((t (s i)).cI (2 * n) * (t (s i)).cI (2 * n + 1)) := by
    unfold Tup.cBot
    rw [show D.R.m = 2 * n + 1 + 1 by omega, Finset.prod_range_succ, Finset.prod_range_succ]
    ring
  have hd : (t (s i)).per 0 n h₀ (ψ i) ((t (s i)).dn (2 * n + 1) ((t (s i)).ioT (2 * n) h (F i))) y v =
      (t (s i)).per 0 n h₀ (ψ i) ((t (s i)).dn (2 * n) ((t (s i)).io (2 * n) ((t (s i)).ioT (2 * n) h (F i)))) y v := rfl
  rw [hc, hd]
  ring

end GlobalTheory.SeeSaw

end
