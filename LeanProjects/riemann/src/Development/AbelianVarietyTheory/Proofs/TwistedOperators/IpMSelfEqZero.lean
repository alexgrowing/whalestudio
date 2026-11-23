import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvalAtUnitVector

theorem ipM_self_eq_zero {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (T : MMap M) (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) (h0 : T v = 0) :
    ipM M μ 𝓕 T T = 0 := by
  by_cases h : ∃ c, IsMultIP M μ 𝓕 T T c
  · have h1 := (ipM_spec M μ 𝓕 T T h v v).2
    have h2 : (∏ τ, inner ℂ (v τ : M.H τ) (v τ : M.H τ)) = 1 :=
      Finset.prod_eq_one fun τ _ => by
        rw [inner_self_eq_norm_sq_to_K, hv τ]
        simp
    rw [h2, mul_one, h0] at h1
    rw [← h1]
    simp
  · unfold ipM
    exact dif_neg h

theorem evInj {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (he : R.models_HW)
    (hv : ∀ i σ, IsChosenExtremalVector R i σ (v₀ i σ)) : EvInj T R v₀ := by
  intro i σ _ x y hxy
  have h0 : (R.HW i σ).e (x - y) (v₀ i σ) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.2 hxy
  have h1 := (he i σ).2.2 (x - y) (x - y)
  rw [ipAt, ipM_self_eq_zero _ _ _ _ (v₀ i σ) (IsChosenExtremalVector.norm R (hv i σ)) h0, mul_zero] at h1
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h1)

end GlobalTheory.EvalAtUnitVector
