import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def minfDensity (N : ℕ) : ENNReal := ((2 : ENNReal) ^ (N * (N - 1) / 2))⁻¹

def petCOf (D : D7) (petF : HSp D → ℝ) (petR : ℕ → ℕ → ℝ) (V : HSp D) : ℝ :=
  petF V * ∏ τ : D.what₂.Tau, petR (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2

structure ThetaTied (D : D7) (X : ThetaX D) where

  ev : ∀ V, X.AF V →ₗ[ℂ] (GA D V → ℂ)
  ev_inj : ∀ V, Function.Injective (ev V)

  ev_aut : ∀ V F, IsAutFun V (ev V F)

  cusp : ∀ V F, F ∈ X.cusp V ↔ IsCuspFun V (ev V F)

  eGf : ∀ V, X.Gf V ≃* GfC V

  actF : ∀ V g F x, ev V (X.actF V g F) x = ev V F (x * (eGf V g : GA D V))

  actR : AllSome (IsInfFam (D := D)) fun θ => ∀ (V : HSp D) (τ : D.what₂.Tau),
    ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), AllSome (IsAtTau θ V τ g) fun h =>
      ∀ F x, ev V (X.actR V τ g F) x = ev V F (x * h)

  ksph : ∀ V S g, g ∈ X.Ksph V S ↔ (eGf V g : GA D V) ∈ KsphC V S

  conj : ∀ V F x, ev V (X.conjAF V F) x = star (ev V F x)

  petF : HSp D → ℝ
  petF_pos : ∀ V, 0 < petF V

  petR : ℕ → ℕ → ℝ
  petR_pos : ∀ p q, 0 < petR p q

  petR_def : ∀ N, petR N 0 = 1 ∧ petR 0 N = 1

  petR_minf : ∀ p q, 0 < p → 0 < q →
    OmegaDensity (ENNReal.ofReal (petR p q) • D.cd.cd p q) (minfDensity (p + q))

  pet : ∀ V : HSp D, V.SigOK → ∀ μ 𝓕, IsVolPair D V μ 𝓕 → ∀ (F : X.AF V) (G : X.cusp V),
    X.pet V F G = (petCOf D petF petR V : ℂ) * ∫ h in 𝓕, star (ev V F h) * ev V (G : X.AF V) h ∂μ

  btop : ∀ (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V), B.SigOK → HSpace.IsIsomEmb B A ι →
    ∀ μ 𝓕, IsVolPair D B μ 𝓕 → ∀ s : GA D B → GA D A, (∀ h, EmbRel A B ι (s h) h) →
    ∀ (φ : X.AF A) (F : X.cusp B),
      X.Btop A B ι φ F = (petCOf D petF petR B : ℂ) * ∫ h in 𝓕, star (ev A φ (s h)) * ev B (F : X.AF B) h ∂μ

  eChr : X.Chr →* ((AE D)ˣ →* Circle)
  eChr_inj : Function.Injective eChr
  eChr_range : Set.range eChr = {χ | IsHeckeChar D χ ∧ ∀ τ, ∃ a, HasInfExp D χ τ a}

  infTy : ∀ χ τ, HasInfExp D (eChr χ) τ (X.infTy χ τ)

  chrOf_res : ∀ μ j, 1 ≤ j → j ≤ D.R.m → ResEta D (eChr (X.chrOf μ j)) 0

  etaT_res : ResEta D (eChr X.etaT) 1
  etaT_unr : UnramEverywhere D (eChr X.etaT)

  etaT_exp : ∀ τ, X.infTy X.etaT τ = 1 / 2

  xs_pos : ∀ t j, j ≤ D.R.m → (X.Xs t j).IsPosDef
  ys_sig : ∀ t j, j ≤ D.R.m → ∀ τ, (X.Ys t j).sig τ = (D.R.r + j * t - (D.R.m - j) / 2, (D.R.m - j) / 2)

  ysLow : ∀ t j i, (∃ C : Matrix (Fin (X.Ys t j).rank) (Fin i) D.host.E, IsIsoSub (X.Ys t j) C) →
    IsWittLower (X.Ys t j) (X.YsLow t j i) i ∧ (X.YsLow t j i).SigOK

def ThetaTied.petC {D : D7} {X : ThetaX D} (T : ThetaTied D X) (V : HSp D) : ℝ := petCOf D T.petF T.petR V

theorem ThetaTied.petC_pos {D : D7} {X : ThetaX D} (T : ThetaTied D X) (V : HSp D) : 0 < T.petC V :=
  mul_pos (T.petF_pos V) (Finset.prod_pos fun _ _ => T.petR_pos _ _)

structure RealTied (D : D7) : Prop where

  cdScale : cdScaleTie D

  dsig : ∀ τ, IsDsig D τ (D.dsig τ)

  dsig_all : dsigTie D

  vol : VolTieG D

structure ProvisionCompatibility (D : D7) (A : TH.ProvA) : Prop where

  haar : TH.HaarCd D A

  ds : ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → NoncompactGapAtLeastRange p q lam → HasParam (A.ds p q lam) lam

end Formalism.L2.Theta

end
