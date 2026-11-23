import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListTailLog
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StBoundingKaehler
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.TailDimZero
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.LinearWeights
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ell errE)

def TailBound.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (F : Family A), (∀ x ∈ F.Yo, Real.exp 1 ≤ F.r x) →
    ∃ CE : ℝ, ∀ (i : Fin D → Fin F.m) (τ : Fin D → ℝ),
      (∀ j, 0 < τ j ∧ (F.sys (i j)).ell₀ ≤ ell (τ j) ∧ errE (F.sys (i j)).C (τ j) ≤ 1) →
      TailLogBound A F.Yo F.r (fun j => (F.sys (i j)).curr (τ j)) CE

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem tailLogBound_congr {A : FinHolAtlas D X} {Yo : Set X} {r r' : X → ℝ}
    (h : ∀ x ∈ Yo, r x = r' x) {T : Fin D → LocPot X} {CE : ℝ}
    (hT : TailLogBound A Yo r T CE) : TailLogBound A Yo r' T CE := by
  intro R₀ hR₀
  have ht : tail Yo r R₀ = tail Yo r' R₀ := Set.ext fun x =>
    ⟨fun hx => ⟨hx.1, by rw [← h x hx.1]; exact hx.2⟩,
      fun hx => ⟨hx.1, by rw [h x hx.1]; exact hx.2⟩⟩
  have hi : (tail Yo r' R₀).indicator (fun x => Real.log (r' x)) =
      (tail Yo r R₀).indicator (fun x => Real.log (r x)) := by
    rw [ht]
    exact Set.indicator_congr fun x hx => by rw [h x hx.1]
  rw [hi]
  exact hT R₀ hR₀

theorem isBoundedPotForm_congr {A : FinHolAtlas D X} {Yo : Set X} {r r' : X → ℝ}
    (h : ∀ x ∈ Yo, r x = r' x) {Om : KaehlerForm A} {C₁ : ℝ} {th : LocPot X} {u : X → ℝ}
    (hT : IsBoundedPotForm A Yo r Om C₁ th u) : IsBoundedPotForm A Yo r' Om C₁ th u :=
  { hT with le_u := fun x hx => by rw [← h x hx]; exact hT.le_u x hx }

theorem isBoundedPotForm_mono {A : FinHolAtlas D X} {Yo : Set X} {r : X → ℝ}
    (hr : ∀ x ∈ Yo, Real.exp 1 ≤ r x) {Om : KaehlerForm A} {C₁ C₁' : ℝ} (hC : C₁ ≤ C₁')
    {th : LocPot X} {u : X → ℝ} (hT : IsBoundedPotForm A Yo r Om C₁ th u) :
    IsBoundedPotForm A Yo r Om C₁' th u :=
  { hT with
    le_u := fun x hx => by
      have h0 : 0 ≤ Real.log (r x) := Real.log_nonneg (le_trans (by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith) (hr x hx))
      have := mul_le_mul_of_nonneg_right hC h0
      have := hT.le_u x hx
      linarith }

theorem TailBound.proof (h₁ : ListTailLog.Statement) (h₂ : BoundingKaehler.Statement) :
    TailBound.Statement := by
  intro X _ _ _ D A F hr
  rcases Nat.eq_zero_or_pos F.m with hm | hm
  · rcases Nat.eq_zero_or_pos D with hD | hD
    · subst hD
      obtain ⟨CE, hCE⟩ := tailLogBound_dim_zero A F.Yo F.r Fin.elim0
      refine ⟨CE, fun i τ _ => ?_⟩
      have e : (fun j => (F.sys (i j)).curr (τ j)) = (Fin.elim0 : Fin 0 → LocPot X) :=
        funext fun j => j.elim0
      rw [e]
      exact hCE
    · exact ⟨0, fun i => absurd (i ⟨0, hD⟩).2 (by omega)⟩
  · set k : Fin F.m := ⟨0, hm⟩
    obtain ⟨Om, hOm⟩ := h₂ D A ⟨(F.R k).om, (F.R k).om_pot, (F.R k).om_pos⟩ F.m
      (fun i => thetaOmega (F.R i))
      (fun i => ReciprocityTheory.AnForm.M.isPotentialAdd A _ _ (F.R i).θ_pot (F.R i).om_pot)
    have hrk : ∀ x ∈ (F.R k).Yo, Real.exp 1 ≤ (F.R k).r x := fun x hx => by
      rw [F.Yo_eq k] at hx
      rw [F.r_eq k x hx]
      exact hr x hx
    obtain ⟨CE, hCE⟩ := h₁ D A (F.R k) hrk Om (∑ i, (|(F.R i).C| + |(F.sys i).C|))
    refine ⟨CE, fun i τ hτ => ?_⟩
    have h := hCE (fun j => thetaOmega (F.R (i j))) (fun j => (F.sys (i j)).uT (τ j)) fun j => by
      have hRi : ∀ x ∈ (F.R (i j)).Yo, Real.exp 1 ≤ (F.R (i j)).r x := fun x hx => by
        rw [F.Yo_eq] at hx
        rw [F.r_eq _ x hx]
        exact hr x hx
      have hT := ((F.sys (i j)).curr_isSmoothPotForm hRi Om (hOm (i j)).1 (hOm (i j)).2 (τ j)
        (hτ j).1 (hτ j).2.1 (hτ j).2.2).1
      have hCi : |(F.R (i j)).C| + |(F.sys (i j)).C| ≤ ∑ l, (|(F.R l).C| + |(F.sys l).C|) :=
        Finset.single_le_sum (f := fun l => |(F.R l).C| + |(F.sys l).C|)
          (fun _ _ => by positivity) (Finset.mem_univ _)
      have hT' := isBoundedPotForm_mono hRi hCi hT
      rw [F.Yo_eq] at hT' ⊢
      exact isBoundedPotForm_congr (fun x hx => by rw [F.r_eq _ x hx, F.r_eq k x hx]) hT'
    rw [F.Yo_eq k] at h
    exact tailLogBound_congr (fun x hx => F.r_eq k x hx) h

end GroundTheory.Heights₂.Heights.AnalyticLimit
