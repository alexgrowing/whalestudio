import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCI

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : InfF D) (V : HSp D)

def Smo (φ : GA D V → ℂ) : Prop :=
  ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)

variable {θ V}

theorem Smo.two {φ : GA D V → ℂ} (h : Smo θ V φ) (k : ℕ) (τs : Fin k → D.what₂.Tau)
    (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : ∀ i, Xs i ∈ lieAt V (τs i)) (τ : D.what₂.Tau)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hτ : X ∈ lieAt V τ) (g : GA D V) :
    ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ =>
      φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (p.1 i)).prod * oneP θ V τ X p.2) := by
  have h1 := h (k + 1) (Fin.snoc (α := fun _ => D.what₂.Tau) τs τ)
    (Fin.snoc (α := fun _ => Matrix (Fin V.rank) (Fin V.rank) ℂ) Xs X)
    (fun i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hτ
      · simpa using hX j) g
  have h2 : ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => (Fin.snoc (α := fun _ => ℝ) p.1 p.2 : Fin (k + 1) → ℝ) := by
    refine contDiff_pi.2 fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using contDiff_snd
    · simpa [Function.comp_def] using (contDiff_apply ℝ ℝ j).comp contDiff_fst
  convert h1.comp h2 using 2 with p
  rw [Function.comp_apply, List.ofFn_succ', List.prod_concat, mul_assoc]
  simp

theorem Smo.add {φ φ' : GA D V → ℂ} (h : Smo θ V φ) (h' : Smo θ V φ') : Smo θ V (φ + φ') :=
  fun k τs Xs hX g => (h k τs Xs hX g).add (h' k τs Xs hX g)

theorem Smo.smul {φ : GA D V → ℂ} (h : Smo θ V φ) (c : ℂ) : Smo θ V (c • φ) :=
  fun k τs Xs hX g => (h k τs Xs hX g).const_smul c

theorem gramAt_herm (V : HSp D) (τ : D.what₂.Tau) : (gramAt D V τ)ᴴ = gramAt D V τ := gram_herm V (tauE D τ)

theorem gramAt_unit (V : HSp D) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ).det := by
  have : (gramAt D V τ).det = tauE D τ V.gram.det := ((tauE D τ).map_det V.gram).symm
  rw [this]
  exact ((map_ne_zero _).2 (gram_det_ne V)).isUnit

variable (θ V) in

def smoSub : Submodule ℂ (GA D V → ℂ) where
  carrier := {φ | Smo θ V φ}
  zero_mem' := fun _ _ _ _ _ => contDiff_const
  add_mem' := Smo.add
  smul_mem' := fun c _ h => h.smul c

end Formalism.L2.Fam.ThC

end
