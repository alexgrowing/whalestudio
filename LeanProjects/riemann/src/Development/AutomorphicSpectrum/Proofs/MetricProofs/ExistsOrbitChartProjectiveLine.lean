import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Line

abbrev LPt : Type := (Σ _ : Unit, Fin 2) → ℂ

def lineφ (w : Fin 1 → ℂ) : LPt := fun q => ![1, w 0] q.2

def lineρ (z : LPt) : Fin 1 → ℂ := fun _ => z ⟨(), 1⟩ / z ⟨(), 0⟩

@[simp] theorem lineφ_zero (w : Fin 1 → ℂ) : lineφ w ⟨(), 0⟩ = 1 := rfl

@[simp] theorem lineφ_one (w : Fin 1 → ℂ) : lineφ w ⟨(), 1⟩ = w 0 := rfl

theorem lineφ_mem (w : Fin 1 → ℂ) :
    lineφ w ∈ mcPts (⊥ : Ideal (MRing fun _ : Unit => Fin 2)) := by
  refine ⟨fun k => ⟨0, by cases k; simp⟩, fun f hf => ?_⟩
  have : f = 0 := by simpa using hf
  simp [this]

theorem lineφ_analytic (q : Σ _ : Unit, Fin 2) :
    AnalyticOnNhd ℂ (fun w : Fin 1 → ℂ => lineφ w q) Set.univ := by
  obtain ⟨⟨⟩, i⟩ := q
  fin_cases i
  · exact analyticOnNhd_const
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticOnNhd _

theorem lineρ_lineφ (w : Fin 1 → ℂ) : lineρ (lineφ w) = w := by
  funext i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [lineρ]

theorem lineρ_affCoord (p : (k : Unit) → Fin 2) (w : Fin 1 → ℂ) :
    lineρ (affCoord p (lineφ w)) = w := by
  funext i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have hp : p () = 0 ∨ p () = 1 := by
    rcases h : p () with ⟨n, hn⟩
    interval_cases n
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hp with hp | hp
  · simp [lineρ, affCoord, hp]
  · by_cases h : w 0 = 0
    · simp [lineρ, affCoord, hp, h]
    · simp [lineρ, affCoord, hp, h]

theorem line_diff_div {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ} {x : E}
    (hf : DifferentiableAt ℂ f x) (hg : DifferentiableAt ℂ g x) (h : g x ≠ 0) :
    DifferentiableAt ℂ (fun y => f y / g y) x := by
  simp only [div_eq_mul_inv]
  exact hf.fun_mul ((differentiableAt_inv h).comp x hg)

theorem line_immersion (w : Fin 1 → ℂ) (p : (k : Unit) → Fin 2)
    (hw : ∀ k, lineφ w ⟨k, p k⟩ ≠ 0) :
    (fderiv ℂ (fun w' => affCoord p (lineφ w')) w).ker = ⊥ := by
  have hφ : ∀ q, DifferentiableAt ℂ (fun w' : Fin 1 → ℂ => lineφ w' q) w := fun q =>
    ((lineφ_analytic q) w (Set.mem_univ _)).differentiableAt
  have hF : DifferentiableAt ℂ (fun w' => affCoord p (lineφ w')) w :=
    differentiableAt_pi.2 fun q => by
      show DifferentiableAt ℂ (fun w' => lineφ w' q / lineφ w' ⟨q.1, p q.1⟩) w
      exact line_diff_div (hφ q) (hφ ⟨q.1, p q.1⟩) (hw q.1)
  have h0 : affCoord p (lineφ w) ⟨(), 0⟩ ≠ 0 := by
    have hp : p () = 0 ∨ p () = 1 := by
      rcases h : p () with ⟨n, hn⟩
      interval_cases n
      · exact Or.inl rfl
      · exact Or.inr rfl
    have := hw ()
    rcases hp with hp | hp
    · simp [affCoord, hp]
    · rw [hp] at this
      simpa [affCoord, hp] using this
  have hG : DifferentiableAt ℂ lineρ (affCoord p (lineφ w)) :=
    differentiableAt_pi.2 fun _ => by
      exact line_diff_div (differentiableAt_apply (𝕜 := ℂ) (⟨(), 1⟩ : Σ _ : Unit, Fin 2) _)
        (differentiableAt_apply (𝕜 := ℂ) (⟨(), 0⟩ : Σ _ : Unit, Fin 2) _) h0
  have hcomp := hG.hasFDerivAt.comp w hF.hasFDerivAt
  have hid : (lineρ ∘ fun w' => affCoord p (lineφ w')) = id := by
    funext w'
    exact lineρ_affCoord p w'
  rw [hid] at hcomp
  have hEq := hcomp.unique (hasFDerivAt_id w)
  refine LinearMap.ker_eq_bot.2 fun a b hab => ?_
  have := congrArg (fun L : (Fin 1 → ℂ) →L[ℂ] (Fin 1 → ℂ) => L a) hEq
  have h2 := congrArg (fun L : (Fin 1 → ℂ) →L[ℂ] (Fin 1 → ℂ) => L b) hEq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this h2
  rw [← this, ← h2]
  exact congrArg _ hab

def lineChart : OrbitChart (⊥ : Ideal (MRing fun _ : Unit => Fin 2)) 1 where
  D := Set.univ
  isOpen_D := isOpen_univ
  φ := lineφ
  holo := lineφ_analytic
  mem w _ := lineφ_mem w
  O := {z | z ∈ mcPts (⊥ : Ideal (MRing fun _ : Unit => Fin 2)) ∧ z ⟨(), 0⟩ ≠ 0}
  O_open := by
    refine ⟨{z | z ⟨(), 0⟩ ≠ 0}, isOpen_ne_fun (continuous_apply _) continuous_const, ?_⟩
    ext z
    exact and_comm
  O_orbit := by
    rintro z ⟨_, hz⟩ z' hz' ⟨c, hc, rfl⟩
    exact ⟨hz', mul_ne_zero (hc _) hz⟩
  ρ := lineρ
  ρ_cont := by
    refine continuousOn_pi.2 fun _ => ?_
    exact (continuous_apply _).continuousOn.div (continuous_apply _).continuousOn fun z hz => hz.2
  ρ_orbit := by
    rintro z ⟨_, hz⟩ z' _ ⟨c, hc, rfl⟩
    funext i
    exact mul_div_mul_left _ _ (hc _)
  φ_mem_O w _ := ⟨lineφ_mem w, by simp⟩
  ρ_φ w _ := lineρ_lineφ w
  ρ_mem _ _ := Set.mem_univ _
  φ_ρ := by
    rintro z ⟨_, hz⟩
    refine ⟨fun _ => (z ⟨(), 0⟩)⁻¹, fun _ => inv_ne_zero hz, ?_⟩
    funext q
    obtain ⟨⟨⟩, i⟩ := q
    fin_cases i
    · simp [hz]
    · simp [lineρ, div_eq_inv_mul]
  immersion w _ p hw := line_immersion w p hw

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Line

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

end GlobalTheory.CompanionTheory.Ar.PB.WMan
