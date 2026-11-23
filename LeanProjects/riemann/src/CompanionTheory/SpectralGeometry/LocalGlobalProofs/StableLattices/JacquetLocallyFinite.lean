import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.AbsoluteL2Bound
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PolynomialNilpotentPath

noncomputable section

open Polynomial

namespace GlobalTheory.CompanionTheory.LocFinFilt

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem aeval_mul_of_intertwine (T Y : Module.End ℂ V) (c : ℂ)
    (h : T * Y = Y * (T + algebraMap ℂ _ c)) (f : ℂ[X]) :
    aeval T f * Y = Y * aeval (T + algebraMap ℂ _ c) f := by
  induction f using Polynomial.induction_on with
  | C a =>
    simp only [aeval_C]
    exact (Algebra.commutes a Y)
  | add p q hp hq => simp only [map_add, add_mul, mul_add, hp, hq]
  | monomial m a ih =>
    have e : ∀ S : Module.End ℂ V, aeval S (C a * X ^ (m + 1)) = aeval S (C a * X ^ m) * S := by
      intro S
      simp only [map_mul, map_pow, aeval_X, pow_succ, mul_assoc]
    rw [e, e, mul_assoc, h, ← mul_assoc, ih, mul_assoc]

theorem actM_intertwine {E : Fin n → Fin n → Module.End ℂ V} (hE : Formalism.REAL.GlRel E)
    {A Y : Matrix (Fin n) (Fin n) ℂ} {c : ℂ} (h : A * Y - Y * A = c • Y) :
    actM E A * actM E Y = actM E Y * (actM E A + algebraMap ℂ _ c) := by
  have hb := GlobalTheory.CompanionTheory.PolyNilGrad.actM_bracket E hE A Y
  have hs : actM E (c • Y) = c • actM E Y :=
    (GlobalTheory.CompanionTheory.PolyNilGrad.actL E).map_smul c Y
  rw [h, hs] at hb
  rw [mul_add, ← sub_eq_iff_eq_add', hb, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]

theorem aeval_shift (T : Module.End ℂ V) (c d : ℂ) (h : c + d = 0) (f : ℂ[X]) :
    aeval (T + algebraMap ℂ _ c) (f.comp (X + C d)) = aeval T f := by
  have e : aeval (T + algebraMap ℂ _ c) (X + C d : ℂ[X]) = T := by
    rw [map_add, aeval_X, aeval_C, add_assoc, ← map_add, h, map_zero, add_zero]
  rw [aeval_comp, e]

theorem step_down {M : GMod n} {A : Matrix (Fin n) (Fin n) ℂ} (F : Filt M A) (p q : ℂ[X])
    (hnil : ∀ u : M.V, ∃ (m : ℕ) (Y : Fin m → Matrix (Fin n) (Fin n) ℂ) (v : Fin m → M.V),
      (∀ k, Y k ∈ L.nilpC A) ∧ aeval (actM M.E A) p u = ∑ k, actM M.E (Y k) (v k))
    (s : ℝ) (hq : ∀ u : M.V, aeval (actM M.E A) q u ∈ F.N s) (u : M.V) :
    aeval (actM M.E A) (q.comp (X + C 1) * q.comp (X + C 2) * p) u ∈ F.N (s - 1) := by
  set T := actM M.E A with hT
  set g : ℂ[X] := q.comp (X + C 1) * q.comp (X + C 2) with hg
  obtain ⟨m, Y, v, hY, hu⟩ := hnil u
  have key : aeval T (g * p) u = ∑ k, aeval T g (actM M.E (Y k) (v k)) := by
    rw [map_mul, Module.End.mul_apply, hu, map_sum]
  rw [key]
  refine Submodule.sum_mem _ fun k _ => ?_
  obtain ⟨Y₁, Y₂, hk, h₁, h₂⟩ := hY k
  have hadd : actM M.E (Y k) = actM M.E Y₁ + actM M.E Y₂ := by
    rw [hk]; exact (GlobalTheory.CompanionTheory.PolyNilGrad.actL M.E).map_add Y₁ Y₂
  rw [hadd, LinearMap.add_apply, map_add]
  refine Submodule.add_mem _ ?_ ?_
  · have h₁' : A * Y₁ - Y₁ * A = (-1 : ℂ) • Y₁ := by rw [h₁, neg_smul, one_smul]
    have hc := aeval_mul_of_intertwine T (actM M.E Y₁) (-1) (actM_intertwine M.gl h₁') g
    have e : aeval T g (actM M.E Y₁ (v k)) =
        actM M.E Y₁ (aeval T q (aeval (T + algebraMap ℂ _ (-1)) (q.comp (X + C 2)) (v k))) := by
      have := congrArg (fun f : Module.End ℂ M.V => f (v k)) hc
      simp only [Module.End.mul_apply] at this
      rw [this, hg, map_mul, aeval_shift T (-1) 1 (by norm_num), Module.End.mul_apply]
    rw [e]
    have := F.shift Y₁ (-1) (by simpa using h₁') s _ (hq (aeval (T + algebraMap ℂ _ (-1)) (q.comp (X + C 2)) (v k)))
    simpa [sub_eq_add_neg] using this
  · have h₂' : A * Y₂ - Y₂ * A = (-2 : ℂ) • Y₂ := by rw [h₂, neg_smul]
    have hc := aeval_mul_of_intertwine T (actM M.E Y₂) (-2) (actM_intertwine M.gl h₂') g
    have e : aeval T g (actM M.E Y₂ (v k)) =
        actM M.E Y₂ (aeval T q (aeval (T + algebraMap ℂ _ (-2)) (q.comp (X + C 1)) (v k))) := by
      have := congrArg (fun f : Module.End ℂ M.V => f (v k)) hc
      simp only [Module.End.mul_apply] at this
      rw [this, hg, mul_comm, map_mul, aeval_shift T (-2) 2 (by norm_num), Module.End.mul_apply]
    rw [e]
    have := F.shift Y₂ (-2) (by simpa using h₂') s _ (hq (aeval (T + algebraMap ℂ _ (-2)) (q.comp (X + C 1)) (v k)))
    refine F.mono _ _ ?_ this
    push_cast
    linarith

theorem exists_monic_descend {M : GMod n} {A : Matrix (Fin n) (Fin n) ℂ} (F : Filt M A) (p : ℂ[X])
    (hp : p.Monic)
    (hnil : ∀ u : M.V, ∃ (m : ℕ) (Y : Fin m → Matrix (Fin n) (Fin n) ℂ) (v : Fin m → M.V),
      (∀ k, Y k ∈ L.nilpC A) ∧ aeval (actM M.E A) p u = ∑ k, actM M.E (Y k) (v k))
    (s : ℝ) (hs : F.N s = ⊤) (K : ℕ) :
    ∃ q : ℂ[X], q.Monic ∧ ∀ u : M.V, aeval (actM M.E A) q u ∈ F.N (s - K) := by
  induction K with
  | zero => exact ⟨1, monic_one, fun u => by simp [hs]⟩
  | succ K ih =>
    obtain ⟨q, hq, hu⟩ := ih
    refine ⟨q.comp (X + C 1) * q.comp (X + C 2) * p,
      (hq.comp_X_add_C 1 |>.mul (hq.comp_X_add_C 2)).mul hp, fun u => ?_⟩
    have := step_down F p q hnil _ hu u
    have e : s - ((K + 1 : ℕ) : ℝ) = s - K - 1 := by push_cast; ring
    rwa [e]

theorem locFin : LocFin := by
  intro n ε M A F χ hA hχ t
  obtain ⟨p, hp, hnil⟩ := GlobalTheory.CompanionTheory.PolyNilGrad.polyNilPath n ε M χ A hχ hA
  obtain ⟨s, hs⟩ := F.top
  obtain ⟨K, hK⟩ := exists_nat_ge (s - t)
  obtain ⟨q, hq, hu⟩ := exists_monic_descend F p hp hnil s hs K
  exact ⟨q, hq, fun u => F.mono _ _ (by linarith) (hu u)⟩

end GlobalTheory.CompanionTheory.LocFinFilt
