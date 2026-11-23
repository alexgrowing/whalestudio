import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientJetsFderivDetNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsApproxFirstJetsPositiveStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem sections_coords_and_nonvanishing_at_finset : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (H : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ (T : Finset Y) (G : La), ∃ k0 : ℕ, ∀ k ≥ k0, ∃ (t0 : ι → Y → ℂ) (t : Fin n → ι → Y → ℂ) (a : ι → Y → ℂ), A.IsSec (A.kap + k • H) t0 ∧ (∀ j, A.IsSec (A.kap + k • H) (t j)) ∧ A.IsSec (A.kap + (G + k • H)) a ∧ ∀ P ∈ T, t0 (A.pick P) P ≠ 0 ∧ A.IsCoordAt t0 t P ∧ a (A.pick P) P ≠ 0 := by
  intro n Y _ _ _ _ _ _ ι La _ A H hH T G
  obtain ⟨q, hq, hk9⟩ := GlobalTheory.T.exists_sections_approx_firstJets_positive n Y ι La A H hH T
  obtain ⟨ε, hε, hk10⟩ := GlobalTheory.T.quotient_jets_fderiv_det_ne_zero n
  obtain ⟨k0, hk0⟩ := hk9 0 (fun _ _ => 1) (fun _ => differentiable_const _) ε hε
  have hpj : ∀ j : Fin n, ∀ P : Y,
      Differentiable ℂ (fun v : V n => v j - (A.chart (A.pick P) P) j) := fun j P =>
    ((EuclideanSpace.proj (𝕜 := ℂ) j).differentiable).sub_const _
  choose kj hkj using fun j : Fin n =>
    hk9 0 (fun P v => v j - (A.chart (A.pick P) P) j) (hpj j) ε hε
  obtain ⟨ka, hka⟩ := hk9 G (fun _ _ => 1) (fun _ => differentiable_const _) (1/2) (by norm_num)
  refine ⟨max k0 (max ka (Finset.univ.sup kj)), fun k hk => ?_⟩
  have hk0' : k ≥ k0 := le_trans (le_max_left _ _) hk
  have hka' : k ≥ ka := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkj' : ∀ j, k ≥ kj j := fun j =>
    le_trans (le_trans (Finset.le_sup (f := kj) (Finset.mem_univ j))
      (le_trans (le_max_right _ _) (le_max_right _ _))) hk
  obtain ⟨F0, hF0s, hF0⟩ := hk0 k hk0'
  choose Fj hFjs hFj using fun j => hkj j k (hkj' j)
  obtain ⟨Fa, hFas, hFa⟩ := hka k hka'
  rw [zero_add] at hF0s hFjs
  refine ⟨F0, Fj, Fa, hF0s, hFjs, hFas, fun P hP => ?_⟩
  set i := A.pick P with hi
  set p := A.chart i P with hp
  have hPs : P ∈ (A.chart i).source := A.mem_pick P
  have hpt : p ∈ (A.chart i).target := (A.chart i).map_source hPs
  have hsymm : (A.chart i).symm p = P := (A.chart i).left_inv hPs
  have hdiffF : ∀ F : ι → Y → ℂ, ∀ la, A.IsSec la F →
      DifferentiableAt ℂ (fun v => F i ((A.chart i).symm v)) p := by
    intro F la hF
    have h1 := hF.1 i
    have h2 : (A.chart i).target ∩ (A.chart i).symm ⁻¹' Set.univ = (A.chart i).target := by simp
    rw [h2] at h1
    exact h1.differentiableAt ((A.chart i).open_target.mem_nhds hpt)
  have hE : DifferentiableAt ℂ (fun v => Complex.exp (-((k : ℂ) * q P v))) p :=
    ((((hq P hP) p).const_mul (k : ℂ)).neg).cexp
  set w0 : V n → ℂ := fun v => F0 i ((A.chart i).symm v) * Complex.exp (-((k : ℂ) * q P v)) with hw0
  set w : Fin n → V n → ℂ := fun j v => Fj j i ((A.chart i).symm v) * Complex.exp (-((k : ℂ) * q P v)) with hw
  have hd0 : DifferentiableAt ℂ w0 p := (hdiffF F0 _ hF0s).mul hE
  have hdj : ∀ j, DifferentiableAt ℂ (w j) p := fun j => (hdiffF (Fj j) _ (hFjs j)).mul hE
  obtain ⟨h0a, h0b⟩ := hF0 P hP
  have e1 : ‖w0 p - 1‖ ≤ ε := by
    simp only [hw0, hsymm]; exact h0a
  have e2 : ‖fderiv ℂ (fun v => w0 v - 1) p‖ ≤ ε := h0b
  have e3 : ∀ j, ‖w j p‖ ≤ ε := by
    intro j
    have := (hFj j P hP).1
    simp only [sub_self, sub_zero] at this
    simp only [hw, hsymm]; exact this
  have e4 : ∀ j, ‖fderiv ℂ (fun v : V n => w j v - (v j - p j)) p‖ ≤ ε := fun j => (hFj j P hP).2
  obtain ⟨hne, hdet⟩ := hk10 p w0 w hd0 hdj e1 e2 e3 e4
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    apply hne
    simp only [hw0, hsymm, h0, zero_mul]
  · unfold WeightedAtlas.IsCoordAt
    have hfun : A.zLoc F0 Fj i = fun v : V n => (WithLp.toLp 2 (fun j => w j v / w0 v) : V n) := by
      funext v
      simp only [WeightedAtlas.zLoc, hw, hw0]
      congr 1
      funext j
      rw [mul_div_mul_right _ _ (Complex.exp_ne_zero _)]
    rw [← hi, ← hp, hfun]
    exact hdet
  · intro h0
    have := (hFa P hP).1
    rw [h0, zero_mul, zero_sub, norm_neg, norm_one] at this
    norm_num at this

end GlobalTheory
