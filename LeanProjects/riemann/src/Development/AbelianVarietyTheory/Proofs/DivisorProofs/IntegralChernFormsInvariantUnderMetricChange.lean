import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MIntEqOfLeviEq
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Mean4O

noncomputable section

namespace GlobalTheory.MassConst

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem leviAt_add {A : FinHolAtlas e X} {P Q : LocPot X} (hP : IsPotential A P) (hQ : IsPotential A Q) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (w : Fin e → ℂ) :
    leviAt A (P + Q) j y w = leviAt A P j y w + leviAt A Q j y w := by
  have h := levi_add_smul 1 (LeviOnly.pot_two hP _ j hy (P.mem_U _)) (LeviOnly.pot_two hQ _ j hy (Q.mem_U _)) w
  simp only [one_mul] at h
  exact h

theorem mInt_const (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (a : ℝ) :
    mInt A Φ (fun _ => a) = a * mInt A Φ (fun _ => 1) := by
  unfold mInt
  split_ifs
  · unfold integralWith
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext y
    ring
  · simp

theorem chern_form_add_arakelov_function {M : Man e} (K : Calc M) (w : K.V) (f : M.Fun) (hf : M.Smooth f) (σ : Fin (M.n + 1)) :
    LeviEq (M.A σ) (K.c1 (w + K.ar f) σ) (K.c1 w σ + LocPot.ofFun (f σ)) := by
  intro j y hy v
  rw [K.isOneCochain_add w (K.ar f) σ j y hy v, leviAt_add (K.firstChern_isPotential _ σ) (K.firstChern_isPotential _ σ) j hy,
    leviAt_add (K.firstChern_isPotential _ σ) (isPotential_ofFun _ _ (hf σ)) j hy, K.c1_ar f hf σ j y hy v]

theorem integral_chern_forms_family_invariant {M : Man e} (K : Calc M) (w : Fin e → K.V) (f : Fin e → M.Fun) (a : ℝ)
    (hf : ∀ i, M.Smooth (f i)) :
    M.int (fun i => K.c1 (w i + K.ar (f i))) (fun _ _ => a) = M.int (fun i => K.c1 (w i)) (fun _ _ => a) := by
  refine congrArg (M.κ * ·) (Finset.sum_congr rfl fun σ _ => ?_)
  show mInt (M.A σ) (fun i => K.c1 (w i + K.ar (f i)) σ) (fun _ => a) =
    mInt (M.A σ) (fun i => K.c1 (w i) σ) (fun _ => a)
  rw [(LeviOnly.mInt_eq_of_leviEq e (M.X σ) (M.A σ) (fun i => K.c1 (w i + K.ar (f i)) σ)
    (fun i => K.c1 (w i) σ + LocPot.ofFun (f i σ)) (fun _ => a) (fun _ => K.firstChern_isPotential _ σ)
    (fun i => isPotentialAdd _ _ _ (K.firstChern_isPotential _ σ) (isPotential_ofFun _ _ (hf i σ)))
    (fun i => chern_form_add_arakelov_function K (w i) (f i) (hf i) σ)).1, mInt_const, mInt_const (M.A σ) (fun i => K.c1 (w i) σ),
    massIndep (M.A σ) (fun i => K.c1 (w i) σ) (fun i => f i σ) (fun _ => K.firstChern_isPotential _ σ) (fun i => hf i σ)]

theorem integral_chern_forms_invariant_under_metric_change : ∀ {e : ℕ} (M : Man e) (K : Calc M) (w : K.V) (f : M.Fun) (a : ℝ), M.Smooth f →
    M.int (fun _ => K.c1 (w + K.ar f)) (fun _ _ => a) = M.int (fun _ => K.c1 w) (fun _ _ => a) :=
  fun _ K w f a hf => integral_chern_forms_family_invariant K (fun _ => w) (fun _ => f) a fun _ => hf

end GlobalTheory.MassConst
