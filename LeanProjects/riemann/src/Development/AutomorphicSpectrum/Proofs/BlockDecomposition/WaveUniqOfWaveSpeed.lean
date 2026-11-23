import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageDerivativeL1Bound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveSolutionExistence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth

noncomputable section

open Matrix
open scoped ContDiff
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveK.Uniq

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

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

theorem Epow_sub {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n))
    (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Set.EqOn (Epow s m a b (f - f')) (Epow s m a b f - Epow s m a b f') (GLs n) := by
  induction m with
  | zero =>
    intro a b x hx
    by_cases hab : a = b <;> simp [Epow, hab]
  | succ m ih =>
    intro a b x hx
    simp only [Epow, Finset.sum_apply, Pi.sub_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [GlobalTheory.CompanionTheory.WaveAll.Eu_congr GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs (ih c b) s a c hx]
    exact GlobalTheory.CompanionTheory.WaveAll.Eu_sub (Epow_smooth hf s m c b) (Epow_smooth hf' s m c b) s a c hx

theorem gel_sub {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n))
    (s : Bool) (m : ℕ) : Set.EqOn (gel s m (f - f')) (gel s m f - gel s m f') (GLs n) := by
  intro x hx
  simp only [gel, Finset.sum_apply, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => Epow_sub hf hf' s m a a hx

theorem Om_sub {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n)) :
    Set.EqOn (Om (f - f')) (Om f - Om f') (GLs n) := by
  intro x hx
  simp only [Om, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, gel_sub hf hf' _ _ hx, smul_sub, smul_add]
  abel

theorem wave_sub {E : KMod n} {u v : ℝ → Mat n → E.V} (hu : IsWave E u) (hv : IsWave E v) :
    IsWave E (u - v) := by
  refine ⟨?_, fun t => ⟨?_, ?_⟩, fun t g hg => ?_, fun g hg => ?_⟩
  · exact hu.1.sub hv.1
  · exact (hu.2.1 t).1.sub (hv.2.1 t).1
  · intro g hg k
    simp only [Pi.sub_apply, (hu.2.1 t).2 g hg k, (hv.2.1 t).2 g hg k, map_sub]
  · have h1 := (GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg).contDiffAt (x := t)
    have h2 := (GlobalTheory.CompanionTheory.WaveAll.wave_line hv hg).contDiffAt (x := t)
    have e : (fun s => (u - v) s g) = (fun s => u s g) - fun s => v s g := rfl
    rw [e, iteratedDeriv_sub (h1.of_le (WithTop.coe_le_coe.2 le_top)) (h2.of_le (WithTop.coe_le_coe.2 le_top)),
      hu.2.2.1 t g hg, hv.2.2.1 t g hg]
    exact (Om_sub (hu.2.1 t).1 (hv.2.1 t).1 hg).symm
  · have h1 : DifferentiableAt ℝ (fun s => u s g) 0 :=
      ((GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg).differentiable (by simp)).differentiableAt
    have h2 : DifferentiableAt ℝ (fun s => v s g) 0 :=
      ((GlobalTheory.CompanionTheory.WaveAll.wave_line hv hg).differentiable (by simp)).differentiableAt
    have e : (fun s => (u - v) s g) = (fun s => u s g) - fun s => v s g := rfl
    rw [e, deriv_sub h1 h2, hu.2.2.2 g hg, hv.2.2.2 g hg, sub_zero]

theorem waveUniq_of_waveSpeed : WaveSpeed → WaveUniq := by
  intro hS n E u v hu hv h0 t x hx
  obtain ⟨c, hc⟩ := hS n
  have hw := wave_sub hu hv
  have h := hc E (u - v) hw t x hx fun y hy _ => by
    simp only [Pi.sub_apply]
    exact sub_eq_zero.2 (h0 _ (GlobalTheory.CompanionTheory.WaveAll.mul_mem_GLs hx hy))
  exact sub_eq_zero.1 h

end GlobalTheory.CompanionTheory.WaveK.Uniq
