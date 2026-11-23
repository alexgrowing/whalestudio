import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.DblKer

open Classical in

def regFam {Y : Type} (Ei : ℂ → Y → ℂ) (s : ℂ) (y : Y) : ℂ :=
  if h : ∀ y, ∃ c, Tendsto (fun t => Ei t y) (𝓝[≠] s) (𝓝 c) then (h y).choose else 0

theorem regFam_eq_of_tendsto {Y : Type} {Ei : ℂ → Y → ℂ} {s : ℂ} {v : Y → ℂ}
    (h : ∀ y, Tendsto (fun t => Ei t y) (𝓝[≠] s) (𝓝 (v y))) (y : Y) : regFam Ei s y = v y := by
  have h' : ∀ y, ∃ c, Tendsto (fun t => Ei t y) (𝓝[≠] s) (𝓝 c) := fun y => ⟨v y, h y⟩
  rw [regFam, dif_pos h']
  exact tendsto_nhds_unique (h' y).choose_spec (h y)

theorem regFam_of_continuousAt {Y : Type} {Ei : ℂ → Y → ℂ} {s : ℂ} (h : ∀ y, ContinuousAt (fun t => Ei t y) s)
    (y : Y) : regFam Ei s y = Ei s y :=
  regFam_eq_of_tendsto (fun y => (h y).tendsto.mono_left nhdsWithin_le_nhds) y

theorem regFam_of_not {Y : Type} {Ei : ℂ → Y → ℂ} {s : ℂ}
    (h : ¬ ∀ y, ∃ c, Tendsto (fun t => Ei t y) (𝓝[≠] s) (𝓝 c)) (y : Y) : regFam Ei s y = 0 := by
  rw [regFam, dif_neg h]

example {Y : Type} (f : Y → ℂ) (s : ℂ) (y : Y) : regFam (fun _ => f) s y = f y :=
  regFam_of_continuousAt (Ei := fun _ => f) (s := s) (fun y => continuousAt_const (y := f y)) y

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def chiInv (χ : Chr F E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : UA σ J) : ℂ :=
  (((χ (Matrix.GeneralLinearGroup.det h.1))⁻¹ : Circle) : ℂ)

def dblKer {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} (κ : ℂ)
    (Ei : ℂ → UA σ J₂ → ℂ) (i : UA σ J × UA σ J →* UA σ J₂) (χ : Chr F E) (s : ℂ) (h h' : UA σ J) : ℂ :=
  κ * (regFam Ei s (i (h, h')) * chiInv χ h')

def dbl {n : ℕ} (W : Spc F E n) : Spc F E (n + n) where
  J := GlobalTheory.Doubling.dblGram finSumFinEquiv W.J
  L := GlobalTheory.Doubling.sumLat finSumFinEquiv W.L W.L
  θ := fun w => GlobalTheory.Doubling.blkMat finSumFinEquiv (W.θ w) (-W.θ w)
  bas := fun _ => 1

end GlobalTheory.ThK.DblKer

end
