import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjKInner
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveSolutionExistence

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK GlobalTheory.CompanionTheory.WaveK.Base
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveK.Lin

variable {n : ℕ}

section Ops

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Eu_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (a b : Fin n) :
    ContDiffOn ℝ ∞ (Eu s a b f) (GLs n) := by
  have h := fun X : Mat n => GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hf
  unfold Eu
  exact ((h _).add (contDiffOn_const.smul (h _))).const_smul _

theorem Epow_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, ContDiffOn ℝ ∞ (Epow s m a b f) (GLs n) := by
  induction m with
  | zero =>
    intro a b
    by_cases hab : a = b
    · simpa [Epow, hab] using hf
    · simp only [Epow, if_neg hab]
      exact contDiffOn_const (c := (0 : V))
  | succ m ih =>
    intro a b
    have e : Epow s (m + 1) a b f = fun x => ∑ c, Eu s a c (Epow s m c b f) x := by
      ext x
      simp only [Epow, Finset.sum_apply]
    rw [e]
    exact ContDiffOn.sum fun c _ => Eu_smooth (ih c b) s a c

theorem Eu_add {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n)) (s : Bool)
    (a b : Fin n) : Set.EqOn (Eu s a b (f + f')) (Eu s a b f + Eu s a b f') (GLs n) := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply, GlobalTheory.CompanionTheory.RCalc.Rd_add _ hf hf' hx, smul_add]
  abel

theorem Eu_smul (c : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (a b : Fin n) :
    Set.EqOn (Eu s a b (c • f)) (c • Eu s a b f) (GLs n) := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply, GlobalTheory.CompanionTheory.RCalc.Rd_smul c _ hf hx]
  module

theorem Epow_add {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n))
    (s : Bool) (m : ℕ) : ∀ a b : Fin n, Set.EqOn (Epow s m a b (f + f')) (Epow s m a b f + Epow s m a b f') (GLs n) := by
  induction m with
  | zero =>
    intro a b x hx
    by_cases hab : a = b <;> simp [Epow, hab]
  | succ m ih =>
    intro a b x hx
    simp only [Epow, Finset.sum_apply, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [GlobalTheory.CompanionTheory.WaveAll.Eu_congr GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs (ih c b) s a c hx]
    exact Eu_add (Epow_smooth hf s m c b) (Epow_smooth hf' s m c b) s a c hx

theorem Epow_smul (k : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Set.EqOn (Epow s m a b (k • f)) (k • Epow s m a b f) (GLs n) := by
  induction m with
  | zero =>
    intro a b x hx
    by_cases hab : a = b <;> simp [Epow, hab]
  | succ m ih =>
    intro a b x hx
    simp only [Epow, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [GlobalTheory.CompanionTheory.WaveAll.Eu_congr GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs (ih c b) s a c hx]
    exact Eu_smul k (Epow_smooth hf s m c b) s a c hx

theorem gel_add {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n))
    (s : Bool) (m : ℕ) : Set.EqOn (gel s m (f + f')) (gel s m f + gel s m f') (GLs n) := by
  intro x hx
  simp only [gel, Finset.sum_apply, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => Epow_add hf hf' s m a a hx

theorem gel_smul (k : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m (k • f)) (k • gel s m f) (GLs n) := by
  intro x hx
  simp only [gel, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => Epow_smul k hf s m a a hx

theorem Om_add {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n)) :
    Set.EqOn (Om (f + f')) (Om f + Om f') (GLs n) := by
  intro x hx
  simp only [Om, Pi.smul_apply, Pi.add_apply, gel_add hf hf' _ _ hx, smul_add]
  abel

theorem Om_smul (k : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Om (k • f)) (k • Om f) (GLs n) := by
  intro x hx
  simp only [Om, Pi.smul_apply, Pi.add_apply, gel_smul k hf _ _ hx]
  module

theorem iterated_integral_add {w w' : ℝ → V} (hw : ContDiff ℝ ∞ w) (hw' : ContDiff ℝ ∞ w') (t : ℝ) :
    iteratedDeriv 2 (fun s => w s + w' s) t = iteratedDeriv 2 w t + iteratedDeriv 2 w' t := by
  have h2 : ∀ φ : ℝ → V, iteratedDeriv 2 φ = deriv (deriv φ) := fun φ => by
    rw [iteratedDeriv_eq_iterate]; rfl
  have hd : deriv (fun s => w s + w' s) = fun s => deriv w s + deriv w' s :=
    funext fun s => deriv_fun_add (hw.differentiable (by simp) s) (hw'.differentiable (by simp) s)
  have e1 : Differentiable ℝ (deriv w) := (contDiff_infty_iff_deriv.1 hw).2.differentiable (by simp)
  have e2 : Differentiable ℝ (deriv w') := (contDiff_infty_iff_deriv.1 hw').2.differentiable (by simp)
  rw [h2, h2, h2, hd]
  exact deriv_fun_add (e1 t) (e2 t)

theorem iteratedDeriv_two_smul (k : ℂ) {w : ℝ → V} (hw : ContDiff ℝ ∞ w) (t : ℝ) :
    iteratedDeriv 2 (fun s => k • w s) t = k • iteratedDeriv 2 w t := by
  have h2 : ∀ φ : ℝ → V, iteratedDeriv 2 φ = deriv (deriv φ) := fun φ => by
    rw [iteratedDeriv_eq_iterate]; rfl
  have hd : deriv (fun s => k • w s) = fun s => k • deriv w s :=
    funext fun s => deriv_fun_const_smul k (hw.differentiable (by simp) s)
  have e1 : Differentiable ℝ (deriv w) := (contDiff_infty_iff_deriv.1 hw).2.differentiable (by simp)
  rw [h2, h2, hd]
  exact deriv_fun_const_smul k (e1 t)

end Ops

theorem wave_add {E : KMod n} {u v : ℝ → Mat n → E.V} (hu : IsWave E u) (hv : IsWave E v) :
    IsWave E fun t y => u t y + v t y := by
  refine ⟨hu.1.add hv.1, fun t => ⟨(hu.2.1 t).1.add (hv.2.1 t).1, ?_⟩, fun t g hg => ?_, fun g hg => ?_⟩
  · intro g hg k
    simp only [(hu.2.1 t).2 g hg k, (hv.2.1 t).2 g hg k, map_add]
  · rw [iterated_integral_add (GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg) (GlobalTheory.CompanionTheory.WaveAll.wave_line hv hg), hu.2.2.1 t g hg, hv.2.2.1 t g hg]
    exact (Om_add (hu.2.1 t).1 (hv.2.1 t).1 hg).symm
  · have h1 : DifferentiableAt ℝ (fun s => u s g) 0 :=
      ((GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg).differentiable (by simp)).differentiableAt
    have h2 : DifferentiableAt ℝ (fun s => v s g) 0 :=
      ((GlobalTheory.CompanionTheory.WaveAll.wave_line hv hg).differentiable (by simp)).differentiableAt
    rw [deriv_fun_add h1 h2, hu.2.2.2 g hg, hv.2.2.2 g hg, add_zero]

theorem wave_smul (k : ℂ) {E : KMod n} {u : ℝ → Mat n → E.V} (hu : IsWave E u) :
    IsWave E fun t y => k • u t y := by
  refine ⟨hu.1.const_smul k, fun t => ⟨(hu.2.1 t).1.const_smul k, ?_⟩, fun t g hg => ?_, fun g hg => ?_⟩
  · intro g hg k'
    simp only [(hu.2.1 t).2 g hg k', map_smul]
  · rw [iteratedDeriv_two_smul k (GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg), hu.2.2.1 t g hg]
    exact (Om_smul k (hu.2.1 t).1 hg).symm
  · have h1 : DifferentiableAt ℝ (fun s => u s g) 0 :=
      ((GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg).differentiable (by simp)).differentiableAt
    rw [deriv_fun_const_smul k h1, hu.2.2.2 g hg, smul_zero]

end GlobalTheory.CompanionTheory.WaveK.Lin
