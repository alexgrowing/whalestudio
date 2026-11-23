import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumFundCoMulSumIic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MetricQuotientOfMultihomogPairStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MultihomogeneousValueWellDefinedStatement
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

namespace GlobalTheory.CompanionTheory.Ar.Small.GlobDecay

theorem mem_ptsOver_of_mem_mcPts {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : z ∈ ptsOver ℂ P := by
  refine ⟨hz.1, fun f hf => ?_⟩
  have h := hz.2 f hf
  rw [eval_map] at h
  rw [aeval_def]
  simpa [algebraMap_int_eq] using h

end GlobalTheory.CompanionTheory.Ar.Small.GlobDecay

namespace GlobalTheory.CompanionTheory.Ar.Small.GlobDecay

theorem global_decay : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes (mCoordIdeal y) J e) (σ : Type) (S : PB.AnSys e σ) (π : R.X → S.X), HoloMap R.A S.A π → ∀ (Eh : HermLine ι), IsSmoothHerm Eh → ∀ ε : Ω, (∀ x : R.X, ∃ (dg dh : K → ℕ) (G Hf : MRing ι), IsMultiHomog G dg ∧ IsMultiHomog Hf dh ∧ (∀ k, (dg k : ℤ) = dh k + Eh.a k) ∧ aeval y G = ε * aeval y Hf ∧ aeval (R.lift x x) Hf ≠ (0 : ℂ)) → (∀ (x : R.X) (dg dh : K → ℕ) (G Hf : MRing ι), IsMultiHomog G dg → IsMultiHomog Hf dh → (∀ k, (dg k : ℤ) = dh k + Eh.a k) → aeval y G = ε * aeval y Hf → aeval (R.lift x x) G ≠ (0 : ℂ) → aeval (R.lift x x) Hf ≠ (0 : ℂ) → π x ∈ S.open') → ∃ δ C : ℝ, 0 < δ ∧ ∀ x : R.X, π x ∈ S.open' → ∀ v : ℂ, HasVal y Eh.a ε (R.lift x x) v → v ≠ 0 → Real.log ‖v‖ - Real.log (Eh.h (R.lift x x)) ≤ -δ * rW S.L S.s (π x) + C := by
  intro K _ ι _ Ω _ y J e R σ S π hπ Eh hEh ε h1 h2
  choose dg dh G Hf hG hH hd hy hne using h1
  have loc := fun x₀ : R.X => GlobalTheory.T.metric_quotient_of_multihomog_pair K ι (mCoordIdeal y) J e R σ S π hπ Eh hEh (dg x₀) (dh x₀)
    (G x₀) (Hf x₀) (hG x₀) (hH x₀) (hd x₀)
    (fun x a b => h2 x _ _ _ _ (hG x₀) (hH x₀) (hd x₀) (hy x₀) a b) x₀ (hne x₀)
  choose V N C hVo hV hN hb using loc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover V (fun x _ => (hVo x).mem_nhds (hV x))
  refine ⟨1 / (2 * (1 + ∑ x₀ ∈ t, (N x₀ : ℝ))), ∑ x₀ ∈ t, |C x₀|, by positivity, ?_⟩
  intro x hx v hv hv0
  obtain ⟨x₀, hx₀t, hxV⟩ : ∃ x₀ ∈ t, x ∈ V x₀ := by simpa using ht.2 (Set.mem_univ x)
  have hz : R.lift x x ∈ ptsOver ℂ (mCoordIdeal y) :=
    mem_ptsOver_of_mem_mcPts (R.mem x x (R.mem_U x))
  obtain ⟨hHf, hbd⟩ := hb x₀ x hxV
  have hrep := (GlobalTheory.T.multihomogeneous_value_well_defined K ι Ω y ℂ Eh.a ε (R.lift x x) v hz hv).1 _ _ _ _
    (hG x₀) (hH x₀) (hd x₀) (hy x₀)
  have hGne : aeval (R.lift x x) (G x₀) ≠ (0 : ℂ) := by
    rw [hrep]; exact mul_ne_zero hv0 hHf
  have hbd' := hbd hx hGne
  have hval : (aeval (R.lift x x) (G x₀) : ℂ) / aeval (R.lift x x) (Hf x₀) = v := by
    rw [hrep]; exact mul_div_cancel_right₀ v hHf
  rw [hval] at hbd'
  have hr : 0 ≤ rW S.L S.s (π x) := by
    have h0 := S.norm_le (π x)
    have h1 : 0 < Real.exp 1 := Real.exp_pos 1
    unfold rW
    linarith
  have hNpos : (0 : ℝ) < N x₀ := by exact_mod_cast hN x₀
  have hsum : (N x₀ : ℝ) ≤ ∑ a ∈ t, (N a : ℝ) :=
    Finset.single_le_sum (f := fun a => (N a : ℝ)) (fun a _ => Nat.cast_nonneg _) hx₀t
  have hδ : 1 / (2 * (1 + ∑ a ∈ t, (N a : ℝ))) ≤ 1 / (2 * (N x₀ : ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hC : C x₀ ≤ ∑ a ∈ t, |C a| :=
    (le_abs_self _).trans
      (Finset.single_le_sum (f := fun a => |C a|) (fun a _ => abs_nonneg _) hx₀t)
  have hmul := mul_le_mul_of_nonneg_right hδ hr
  linarith

end GlobalTheory.CompanionTheory.Ar.Small.GlobDecay
