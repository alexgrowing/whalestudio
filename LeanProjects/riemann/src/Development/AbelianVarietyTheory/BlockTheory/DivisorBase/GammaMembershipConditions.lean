import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr
open GlobalTheory.SW hiding Level
open GlobalTheory.Ker
open scoped TensorProduct ComplexConjugate ENNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.RealPointEmbeddings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev WRe (S T : HSp D) : Type := D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ

abbrev Sq (T : HSp D) : Type := D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ

variable {S T : HSp D}

def ptR (θ : InfFam D) (z : WRe S T) : WO S T := ∑ τ, lineAt θ τ (z τ) 1

def embQ (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : WRe S T := fun τ => γ.map (tauE D τ)

def EFr (x x' : WRe S T) : ℝ :=
  -∑ τ, 2 * (tauE D τ D.host.xi0 * ((gramAt D S τ)⁻¹ * (x' τ)ᴴ * gramAt D T τ * x τ).trace).re

def Jc (s : Sq T) (x : WRe S T) : WRe S T := fun τ => cplxO 1 (s τ) (x τ)

def Hc (s : Sq T) (u v : WRe S T) : ℂ := (EFr (Jc s u) v : ℂ) + Complex.I * (EFr u v : ℂ)

def gInf (θ : InfFam D) (g : GA D T) : Sq T := fun τ => compAt θ τ (mt T g)

def mvS (θ : InfFam D) (g : GA D T) (s : Sq T) : Sq T := fun τ => gInf θ g τ * s τ * gInf θ g⁻¹ τ

def mvO (θ : InfFam D) (g : GA D T) (B : Sq T) : Sq T := fun τ => gInf θ g τ * B τ

def lie (s B : Sq T) (ζ : FVar D T.rank S.rank → ℂ) : WRe S T := fun τ =>
  ∑ i, ∑ j, ((2 / fockScale D τ : ℝ) : ℂ) •
    (((ζ (τ, i, j)).re : ℂ) • unitMap 1 (B τ) i j + ((ζ (τ, i, j)).im : ℂ) • cplxO 1 (s τ) (unitMap 1 (B τ) i j))

def InGam (L : Lt D.host.E T.rank) (g : GA D T) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : Prop :=
  ∃ u ∈ latO S T (stdL D.host.E S.rank) L (fun _ => True),
    (ratW T S γ).map (finPart D) = (actO S T 1 g u).map (finPart D)

def IsLatOf (L : Lt D.host.E T.rank) (g : GA D T) (H : Lt D.host.E T.rank) : Prop :=
  ∀ v, v ∈ H ↔ ∃ u ∈ latHat D.host.F D.host.E {x | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ t ∈ L, x = a • t},
    toAf v = fmt T g *ᵥ u

def hQ (x x' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : D.host.E :=
  (S.gram⁻¹ * x'ᴴ * T.gram * x).trace

def HasQ (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (m : ℤ) : Prop :=
  Algebra.trace D.host.K D.host.E (hQ x x) = (Ideal.absNorm D.host.ccK : D.host.K) * (m : D.host.K)

def wZero (D : D7) : D.host.E := (1 + D.host.sqrtMinusD) / 2

def IsCanTheta (L : Lt D.host.E T.rank) (g : GA D T) (s B : Sq T) (G : WRe S T → ℂ) : Prop :=
  Differentiable ℂ (fun ζ : FVar D T.rank S.rank → ℂ => G (lie s B ζ)) ∧
    ∀ γ, InGam L g γ → ∃ m : ℤ, HasQ γ m ∧ ∀ z : WRe S T,
      G (z + embQ γ) = (-1 : ℂ) ^ m *
        Complex.exp (Real.pi * Hc s z (embQ γ) + Real.pi * Hc s (embQ γ) (embQ γ) / 2) * G z

def latC (S : HSp D) (L : Lt D.host.E T.rank) (g : GA D T) (s B : Sq T) :
    AddSubgroup (FVar D T.rank S.rank → ℂ) :=
  AddSubgroup.closure {ζ | ∃ γ, InGam (S := S) L g γ ∧ lie s B ζ = embQ γ}

def HasMeanSq (L : Lt D.host.E T.rank) (g : GA D T) (s B : Sq T) (G : WRe S T → ℂ) (m : ℝ≥0∞) : Prop :=
  AllSome (fun 𝓕 : Set (FVar D T.rank S.rank → ℂ) => IsAddFundamentalDomain (latC S L g s B) 𝓕 volume) fun 𝓕 =>
    0 < volume 𝓕 ∧ volume 𝓕 < ⊤ ∧
      ∫⁻ ζ in 𝓕, ‖G (lie s B ζ)‖ₑ ^ 2 *
        ENNReal.ofReal (Real.exp (-(Real.pi * (Hc s (lie (S := S) s B ζ) (lie s B ζ)).re))) = m * volume 𝓕

def IsInertIdem (D : D7) (ε : AF D.host.F) : Prop :=
  (∃ v, IsPlaceIdem D v ε) ∧ ¬ ∃ e, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε

def UnramInert (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ ε, IsInertIdem D ε → ∀ x : (AE D)ˣ,
    algebraMap (AF D.host.F) (AE D) ε * ((x : AE D) - 1) = (x : AE D) - 1 →
    finPart D (x : AE D) ∈ intAE D → finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → χ x = 1

def IsSplitDet (k : GA D T) (x : (AE D)ˣ) : Prop :=
  infPart D (x : AE D) = 1 ∧
    (∀ e, IsSplitIdem D e →
      (e * (x : AE D) = e * (mt T k).det ∧ cA D e * (x : AE D) = cA D e) ∨
      (cA D e * (x : AE D) = cA D e * (mt T k).det ∧ e * (x : AE D) = e)) ∧
    ∀ ε, IsInertIdem D ε →
      algebraMap (AF D.host.F) (AE D) ε * (x : AE D) = algebraMap (AF D.host.F) (AE D) ε

def detOn {m : ℕ} (s k : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  ((1 / 2 : ℂ) • (1 + s) * k + (1 / 2 : ℂ) • (1 - s)).det

def jChar (n : ℕ) (a : D.what₂.Tau → ℤ) (s k : Sq T) : ℂ :=
  ∏ τ, detOn (s τ) (k τ) ^ (a τ + ((n / 2 : ℕ) : ℤ)) * detOn (-s τ) (k τ) ^ (a τ - ((n / 2 : ℕ) : ℤ))

def eFr (θ : InfFam D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (s : Sq T) (f : WO S T → ℂ)
    (g : GA D T) (z : WRe S T) : ℂ :=
  Complex.exp (Real.pi * Hc (mvS θ g s) z z / 2) * om (1, g) f (ptR θ z)

open Classical in

structure FrameLaws (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χS : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (L : Lt D.host.E T.rank) (s B : Sq T)
    (f : WO S T → ℂ) : Prop where

  can : ∀ g, IsCanTheta L g (mvS θ g s) (mvO θ g B) (eFr θ om s f g)

  line : ∀ g (G : WRe S T → ℂ), IsCanTheta L g (mvS θ g s) (mvO θ g B) G → ∃ c : ℂ, G = c • eFr θ om s f g

  norm : ∀ g, HasMeanSq L g (mvS θ g s) (mvO θ g B) (eFr θ om s f g) 1

  jet : ∀ g (P : MvPolynomial (FVar D T.rank S.rank) ℂ),
    I2.polyDeriv P (fun k => (Pi.single k 1 : FVar D T.rank S.rank → ℂ))
        (fun ζ => eFr θ om s f g (lie (mvS θ g s) (mvO θ g B) ζ)) 0 =
      om (1, g) (pureTensorO ψ θ S T (fun _ => 1) s (fun _ => 1) B f P) 0

  rat : ∀ γ ∈ GQ T, ∀ g (z : WRe S T),
    eFr θ om s f (γ * g) (fun τ => gInf θ γ τ * z τ) = eFr θ om s f g z

  fin : UnramInert χS → ∀ k ∈ GfC T, IsMov (fmt T k) L L → AllSome (IsSplitDet k) fun x =>
    ∀ g, eFr θ om s f (g * k) = ((χS x : Circle) : ℂ) • eFr θ om s f g

  inf : ∀ a : D.what₂.Tau → ℤ, (∀ τ, HasInfExp D χS τ (a τ)) →
    ∀ k ∈ GinfC T, (∀ τ, gInf θ k τ * s τ = s τ * gInf θ k τ) →
      ∀ g, eFr θ om s f (g * k) = jChar S.rank a s (gInf θ k) • eFr θ om s f g

  classical : ∀ C : Ctx S T, C.θ = θ → C.IsB B → ∀ g, AllSome (IsLatOf L g) fun H =>
    (∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, InGam L g γ ↔ γᵀ ∈ tens (stdL D.host.E S.rank) H) ∧
    AllSome (IsVac C.X C.bas (wZero D) (tens (stdL D.host.E S.rank) H)) fun φ =>
      ∃ c : ℂ,
        (∀ z : WRe S T, eFr θ om s f g z =
          c * thA C.X C.bas C.idx φ (C.xB (C.mvB g B)) (C.zOf (C.xB (C.mvB g B)) (ptR θ z))) ∧
        (∃ m : ℝ≥0∞, HasMeanSq L g (mvS θ g s) (mvO θ g B)
          (fun z : WRe S T => thA C.X C.bas C.idx φ (C.xB (C.mvB g B)) (C.zOf (C.xB (C.mvB g B)) (ptR θ z))) m ∧
          ‖c‖ₑ ^ 2 * m = 1) ∧
        ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ,
          om (1, g) (pureTensorO ψ θ S T (fun _ => 1) s (fun _ => 1) B f P) 0 =
            c * thP C.X C.hr C.bas C.idx φ (C.toH P) (C.xB (C.mvB g B))

def VacuumFrame : Prop :=
  ∀ (D : D7) (S T : HSp D), S.gram = 1 → Even S.rank →
    ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
      (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (L : Lt D.host.E T.rank), IsSelfDualC T L →
    ∀ (p : ℕ) (s B : Sq T), (∀ τ, IsCartanInv (gramAt D T τ) (s τ)) →
      (∀ τ, IsONBasis (gramAt D T τ) (s τ) (B τ) p) →
    ∀ (θ : InfFam D) (f : WO S T → ℂ),
      IsVacO ψ θ S T (fun _ => 1) s (stdL D.host.E S.rank) L f → FrameLaws ψ θ χS om L s B f

example (u v : ℂ) : detOn !![1, 0; 0, -1] !![u, 0; 0, v] = u := by
  simp [detOn, Matrix.det_fin_two, Matrix.one_fin_two]; ring

example (u v : ℂ) : detOn (-!![1, 0; 0, -1]) !![u, 0; 0, v] = v := by
  simp [detOn, Matrix.det_fin_two, Matrix.one_fin_two]; ring

end GlobalTheory.IndefiniteRowSideFullHecke.RealPointEmbeddings

end
