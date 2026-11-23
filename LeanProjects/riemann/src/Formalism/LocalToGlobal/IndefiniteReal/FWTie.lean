import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.IndefR.FWT

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Arith Formalism.IndefR.Mult Formalism.L2.Pj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 1000000 in

structure FWTie (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) where

  alg_eq : ∀ x : 𝓞 T.Q.c.F, algebraMap T.Q.c.F D.what₂.LL (x : T.Q.c.F) = D.what₂.OtoLL (T.Q.eO x)

  e : ∀ i : Fin D.R.m, T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n ≃ₗ[T.Q.c.F] (R.FW i).WK

  ks : ∀ i : Fin D.R.m, (R.FW i).IsKsForm

  kap : ∀ (i : Fin D.R.m) (τ : D.what₂.Tau),
    (∀ k : Fin (D.R.sigW ((i : ℕ) + 1)).1, (κ i).aP τ k = aPl D i ((Wc D i).sig (tauE D τ)).1 τ k) ∧
    (∀ k : Fin (D.R.sigW ((i : ℕ) + 1)).2,
      (κ i).aM τ k = aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ k) ∧ (κ i).n = D.R.nV

  pt : ∀ (i : Fin D.R.m) (la : HeightOneSpectrum (𝓞 T.Q.c.F)), (R.FW i).Pt la ≃ T.PtM ((i : ℕ) + 1) la

  nrm_eq : ∀ (i : Fin D.R.m) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : (R.FW i).Pt la) (f : T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n),
    (R.FW i).nrm la y (e i f) = T.nrmM ((i : ℕ) + 1) la (pt i la y) (f : T.R ((i : ℕ) + 1))

  laws : LawsJ T

  chiR : ChiR T R

  hv₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), IsChosenExtremalVector R i σ (v₀ i σ)

  x0 : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) →
    IsModelBaseFrameFamily (R.MW i σ) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)))

  ev0 : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) →
    ∀ hV : T.V ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) = Wc D i,
    (¬ ∃ j' : (Fin (R.nW i) → D.what₂.LL) →ₛₗ[σ] (R.HW i σ).H, ∀ f : T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
      ((R.HW i σ).e (j' ((e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL))) (v₀ i σ) =
        hV ▸ T.phiJ ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) (wtA (κ i)) (f : T.R ((i : ℕ) + 1))) →
    (R.FW i).j σ = 0

  ev : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) →
    ∀ hV : T.V ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) = Wc D i,
    (∃ j' : (Fin (R.nW i) → D.what₂.LL) →ₛₗ[σ] (R.HW i σ).H, ∀ f : T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
      ((R.HW i σ).e (j' ((e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL))) (v₀ i σ) =
        hV ▸ T.phiJ ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) (wtA (κ i)) (f : T.R ((i : ℕ) + 1))) →
    ∀ f : T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
      ((R.HW i σ).e ((R.FW i).j σ ((e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL))) (v₀ i σ) =
        hV ▸ T.phiJ ((i : ℕ) + 1) (σ.comp (algebraMap T.Q.c.F D.what₂.LL)) (wtA (κ i)) (f : T.R ((i : ℕ) + 1))

end Formalism.IndefR.FWT
