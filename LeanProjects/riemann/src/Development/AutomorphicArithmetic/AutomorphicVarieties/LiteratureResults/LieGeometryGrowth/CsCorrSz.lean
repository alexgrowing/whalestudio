import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsCorrForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAltEv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAppSz
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsCompSz
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsChartSz
open UpperTheory.V.Lit.Geo

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct ContDiff Topology

namespace UpperTheory.V.Lit.Geo.Cs

private theorem term_sz {V W F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (k : ℕ) (τ : V → W) (Θ : V → F) (p : V)
    (hτ : ContDiffAt ℝ ∞ τ p) (hΘ : ContDiffAt ℝ ∞ Θ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : W → ℂ) (b : ℝ), ContDiffAt ℝ ∞ u (τ p) → Sz k u (τ p) b →
      Sz k (fun y => u (τ y) • Θ y) p (C * b) := by
  obtain ⟨c, hc⟩ := exists_sz k τ p
  obtain ⟨t, ht⟩ := exists_sz k Θ p
  obtain ⟨C, hC, H⟩ := compSz V W ℂ k c
  let L : ℂ →L[ℝ] F →L[ℝ] F := ContinuousLinearMap.lsmul ℝ ℂ
  refine ⟨2 ^ k * (‖L‖ * C) * t, by have := ht.nonneg; positivity, fun u b hu hb => ?_⟩
  have h1 := H u τ p b hτ hu (fun i _ hi => hc i hi) hb
  have s1 : ContDiffAt ℝ ∞ (fun y => u (τ y)) p := hu.comp p hτ
  have h2 := (appSz V ℂ (F →L[ℝ] F) k p).2.1 L _ _ s1 h1
  have s2 : ContDiffAt ℝ ∞ (fun y => L (u (τ y))) p := L.contDiff.contDiffAt.comp p s1
  have h3 := (appSz V F F k p).1 _ Θ _ _ s2 hΘ h2 ht
  exact h3.mono (le_of_eq (by ring))

private theorem val_sz (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (q : ℕ) (α : Co Ξ q) (w : Fm U Ξ q) (hw : Corr U Ξ α w) (ρ : GA E a → ℝ) (hρ : ∀ g, 0 ≤ ρ g)
    (hb : ∀ (X : Fin q → Herm E a) (j : Fin Ξ.d) (l : List (Lie E a)), ∃ M : ℝ, ∀ g,
      ‖((l.map (lie E a)).prod (Bor.cmp j (α X))).1 g‖ ≤ M * ρ g) (k : ℕ) (v : Fin q → HV E a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ g x, ContDiffAt ℝ ∞ (fun p => Tw U Ξ w g x p v) (hOne E a) ∧
      Sz k (fun p => Tw U Ξ w g x p v) (hOne E a) (M * ρ (pt g x)) := by
  obtain ⟨ι, _, X, j, Θ, τ, h1, hτ, hΘ, H⟩ := corrForm E a Ξ q v
  choose C hC HC using fun i => term_sz k τ (Θ i) (hOne E a) hτ (hΘ i)
  choose D hD HD using fun i => chartSz E a k ρ hρ (Bor.cmp (j i) (α (X i))) (hb (X i) (j i))
  refine ⟨∑ i, C i * D i, Finset.sum_nonneg fun i _ => mul_nonneg (hC i) (hD i), fun g x => ?_⟩
  have e := H U α w hw g x
  have su : ∀ i, ContDiffAt ℝ ∞ (chart (Bor.cmp (j i) (α (X i))).1 (pt g x)) (τ (hOne E a)) := fun i => by
    rw [h1]; exact contDiffAt_chart (Bor.cmp (j i) (α (X i))).2 _ isUnit_one
  have st : ∀ i, ContDiffAt ℝ ∞ (fun p => chart (Bor.cmp (j i) (α (X i))).1 (pt g x) (τ p) • Θ i p) (hOne E a) :=
    fun i => ((su i).comp _ hτ).smul (hΘ i)
  refine ⟨(ContDiffAt.sum fun i _ => st i).congr_of_eventuallyEq e, ?_⟩
  have := (appSz (HV E a) ℝ (Fin Ξ.d → ℂ) k (hOne E a)).2.2 ι Finset.univ _ _ (fun i _ => st i)
    (fun i _ => HC i _ (D i * ρ (pt g x)) (su i) (by rw [h1]; exact HD i _))
  refine (this.congr e.symm).mono (le_of_eq ?_)
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

end UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.corrSz :
    UpperTheory.V.Lit.Geo.Cs.CorrSz := by
  intro E _ _ _ a U Ξ q α w hw ρ hρ hb k
  obtain ⟨T, C, hC, H⟩ := Cs.altEv (HV E a) (Fin Ξ.d → ℂ) q k
  choose M hM HM using Cs.val_sz E a U Ξ q α w hw ρ hρ hb k
  have h0 : 0 ≤ ∑ v ∈ T, M v := Finset.sum_nonneg fun v _ => hM v
  refine ⟨C * ∑ v ∈ T, M v, mul_nonneg hC h0, fun g x => ?_⟩
  rw [mul_assoc]
  exact H _ _ _ (mul_nonneg h0 (hρ _)) (fun v _ => (HM v g x).1) fun v hv => (HM v g x).2.mono
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun v _ => hM v) hv) (hρ _))
