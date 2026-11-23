import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr
open GlobalTheory.SW hiding Level
open GlobalTheory.Ker
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate ComplexOrder Classical ENNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.VacuumCharacterDeterminant

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev Fam (D : D7) (m n : ℕ) : Type := D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ

def comps (θ : InfFam D) {m n : ℕ} (w : Mx D m n) : Fam D m n := fun τ => compAt θ τ w

def realOf (θ : InfFam D) {m n : ℕ} (z : Fam D m n) : Mx D m n := ∑ τ, lineAt θ τ (z τ) 1

def ratFam {m n : ℕ} (γ : Matrix (Fin m) (Fin n) D.host.E) : Fam D m n := fun τ => γ.map (tauE D τ)

section Forms

variable (S T : HSp D)

def hAt (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) : ℂ :=
  Matrix.trace ((gramAt D S τ)⁻¹ * yᴴ * gramAt D T τ * x)

def efR (x y : Fam D T.rank S.rank) : ℝ :=
  -∑ τ, 2 * (tauE D τ D.host.xi0 * hAt S T τ (x τ) (y τ)).re

def cxJ (s : Fam D T.rank T.rank) (x : Fam D T.rank S.rank) : Fam D T.rank S.rank :=
  fun τ => cplxO 1 (s τ) (x τ)

def hermH (s : Fam D T.rank T.rank) (x y : Fam D T.rank S.rank) : ℂ :=
  (efR S T (cxJ S T s x) y : ℂ) + Complex.I * (efR S T x y : ℂ)

def hQ (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : D.host.E :=
  Matrix.trace (S.gram⁻¹ * yᴴ * T.gram * x)

def qExp (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : ℚ :=
  Algebra.trace ℚ D.host.E (hQ S T x x) / (2 * (Ideal.absNorm D.host.ccK : ℚ))

def coordPt (s : Fam D T.rank T.rank) (BS : Fam D S.rank S.rank) (BT : Fam D T.rank T.rank)
    (c : FVar D T.rank S.rank → ℂ) : Fam D T.rank S.rank := fun τ =>
  ((2 / fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j,
    ((((c (τ, i, j)).re : ℝ) : ℂ) • unitMap (BS τ) (BT τ) i j +
      (((c (τ, i, j)).im : ℝ) : ℂ) • cplxO 1 (s τ) (unitMap (BS τ) (BT τ) i j))

end Forms

section Moved

variable (θ : InfFam D) (S T : HSp D)

def movS (sT : Fam D T.rank T.rank) (g : GA D T) : Fam D T.rank T.rank :=
  fun τ => compAt θ τ (mt T g) * sT τ * compAt θ τ (mt T g⁻¹)

def movB (BT : Fam D T.rank T.rank) (g : GA D T) : Fam D T.rank T.rank :=
  fun τ => compAt θ τ (mt T g) * BT τ

def latG (ΛS : Lt D.host.E S.rank) (ΛT : Lt D.host.E T.rank) (g : GA D T) :
    Set (Matrix (Fin T.rank) (Fin S.rank) D.host.E) :=
  {γ | ∃ u ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True),
    (ratW T S γ).map (finPart D) = (actO S T 1 g u).map (finPart D)}

def frameFn (sT : Fam D T.rank T.rank) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ)
    (g : GA D T) (z : Fam D T.rank S.rank) : ℂ :=
  Complex.exp (Real.pi * hermH S T (movS θ T sT g) z z / 2) * om (1, g) f (realOf θ z)

end Moved

section Canon

variable (S T : HSp D) (s : Fam D T.rank T.rank) (BS : Fam D S.rank S.rank) (BT : Fam D T.rank T.rank)
  (Γ : Set (Matrix (Fin T.rank) (Fin S.rank) D.host.E))

def IsCanon (G : Fam D T.rank S.rank → ℂ) : Prop :=
  Differentiable ℂ (fun c => G (coordPt S T s BS BT c)) ∧
    ∀ γ ∈ Γ, ∃ m : ℤ, qExp S T γ = m ∧ ∀ z, G (z + ratFam γ) = (-1) ^ m *
      Complex.exp (Real.pi * hermH S T s z (ratFam γ) + Real.pi * hermH S T s (ratFam γ) (ratFam γ) / 2) * G z

def coordLat : AddSubgroup (FVar D T.rank S.rank → ℂ) :=
  AddSubgroup.closure {c | ∃ γ ∈ Γ, coordPt S T s BS BT c = ratFam γ}

def MeanSq (G : Fam D T.rank S.rank → ℂ) (m : ℝ≥0∞) : Prop :=
  AllSome (fun Fd : Set (FVar D T.rank S.rank → ℂ) => IsAddFundamentalDomain (coordLat S T s BS BT Γ) Fd volume)
    fun Fd => volume Fd ≠ 0 ∧ volume Fd ≠ ⊤ ∧
      ∫⁻ c in Fd, ‖G (coordPt S T s BS BT c)‖ₑ ^ 2 *
        ENNReal.ofReal (Real.exp (-(Real.pi *
          (hermH S T s (coordPt S T s BS BT c) (coordPt S T s BS BT c)).re))) = m * volume Fd

end Canon

section Chars

def UnramInert (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → finPart D (x : AE D) ∈ intAE D →
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → (∀ e, IsSplitIdem D e → e * (x : AE D) = e) → χ x = 1

def IsSplitDet (T : HSp D) (k : GA D T) (x : (AE D)ˣ) : Prop :=
  infPart D (x : AE D) = 1 ∧ ∀ v ε, IsPlaceIdem D v ε →
    (∃ e, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε ∧
      e * (x : AE D) = e * (mt T k).det ∧ cA D e * (x : AE D) = cA D e) ∨
    ((¬ ∃ e, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧
      algebraMap (AF D.host.F) (AE D) ε * (x : AE D) = algebraMap (AF D.host.F) (AE D) ε)

def detPos {r : ℕ} (s k : Matrix (Fin r) (Fin r) ℂ) : ℂ :=
  (k * ((1 / 2 : ℂ) • (1 + s)) + (1 / 2 : ℂ) • (1 - s)).det

def detNeg {r : ℕ} (s k : Matrix (Fin r) (Fin r) ℂ) : ℂ := detPos (-s) k

def vacChar (θ : InfFam D) (T : HSp D) (sT : Fam D T.rank T.rank) (n : ℕ) (a : D.what₂.Tau → ℤ) (k : GA D T) : ℂ :=
  ∏ τ, detPos (sT τ) (compAt θ τ (mt T k)) ^ (a τ + ((n / 2 : ℕ) : ℤ)) *
    detNeg (sT τ) (compAt θ τ (mt T k)) ^ (a τ - ((n / 2 : ℕ) : ℤ))

end Chars

def FrameLaws (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (sT : Fam D T.rank T.rank) (BS : Fam D S.rank S.rank)
    (BT : Fam D T.rank T.rank) (ΛS : Lt D.host.E S.rank) (ΛT : Lt D.host.E T.rank) (f : WO S T → ℂ) : Prop :=

  (∀ g, IsCanon S T (movS θ T sT g) BS (movB θ T BT g) (latG S T ΛS ΛT g) (frameFn θ S T sT om f g) ∧
    (∀ G, IsCanon S T (movS θ T sT g) BS (movB θ T BT g) (latG S T ΛS ΛT g) G →
      ∃ c : ℂ, G = c • frameFn θ S T sT om f g) ∧
    MeanSq S T (movS θ T sT g) BS (movB θ T BT g) (latG S T ΛS ΛT g) (frameFn θ S T sT om f g) 1) ∧

  (∀ g (P : MvPolynomial (FVar D T.rank S.rank) ℂ),
    polyDeriv P (fun l => Pi.single l (1 : ℂ))
      (fun c => frameFn θ S T sT om f g (coordPt S T (movS θ T sT g) BS (movB θ T BT g) c)) 0 =
      thetaKO om 1 g (pureTensorO ψ θ S T (fun _ => 1) sT BS BT f P)) ∧

  (∀ γ ∈ GQ T, ∀ g z, frameFn θ S T sT om f (γ * g) (fun τ => compAt θ τ (mt T γ) * z τ) =
    frameFn θ S T sT om f g z) ∧

  (∀ k ∈ GfC T, IsMov (fmt T k) ΛT ΛT → AllSome (IsDetRoot T k) fun x =>
    ∀ g, frameFn θ S T sT om f (g * k) = ((χS x : Circle) : ℂ) • frameFn θ S T sT om f g) ∧

  (UnramInert χS → ∀ k ∈ GfC T, IsMov (fmt T k) ΛT ΛT → AllSome (IsSplitDet T k) fun x =>
    ∀ g, frameFn θ S T sT om f (g * k) = ((χS x : Circle) : ℂ) • frameFn θ S T sT om f g) ∧

  AllSome (fun a : D.what₂.Tau → ℤ => ∀ τ, HasInfExp D χS τ (a τ)) fun a =>
    ∀ k ∈ GinfC T, (∀ τ, compAt θ τ (mt T k) * sT τ = sT τ * compAt θ τ (mt T k)) →
      ∀ g, frameFn θ S T sT om f (g * k) = vacChar θ T sT S.rank a k • frameFn θ S T sT om f g

def AdelicFrame (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (sT : Fam D T.rank T.rank) (BS : Fam D S.rank S.rank)
    (BT : Fam D T.rank T.rank) (pT : D.what₂.Tau → ℕ) (ΛS : Lt D.host.E S.rank) (ΛT : Lt D.host.E T.rank)
    (f : WO S T → ℂ),
    Even S.rank → Odd T.rank → (∀ τ, (gramAt D S τ).PosDef) →
    (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) →
    (∀ τ, IsONBasis (gramAt D S τ) 1 (BS τ) S.rank) → (∀ τ, IsONBasis (gramAt D T τ) (sT τ) (BT τ) (pT τ)) →
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsWeilDatumO ψ S T χS χT om →
    IsVacO ψ θ S T (fun _ => 1) sT ΛS ΛT f →
    FrameLaws ψ θ S T χS om sT BS BT ΛS ΛT f

def wZero (D : D7) : D.host.E := (1 + D.host.sqrtMinusD) / 2

def IsHomology (T : HSp D) (L : Lt D.host.E T.rank) (g : GA D T) (H : Lt D.host.E T.rank) : Prop :=
  ∃ Λ : Lt D.host.E T.rank, IsAA Λ L ∧ ∀ v, v ∈ H ↔ ∃ u ∈ hatV Λ, toAf v = fmt T g *ᵥ u

def ClassicalFrame (D : D7) : Prop :=
  ∀ (S T : HSp D) (C : Ctx S T) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (B : C.Bas) (L : Lt D.host.E T.rank) (f : WO S T → ℂ),
    Odd T.rank → C.IsB B → IsSelfDualC T L → IsWeilDatumO C.ψ S T χS χT om →
    IsVacO C.ψ C.θ S T (fun _ => 1) (C.sB B) (GlobalTheory.SW.stdL D.host.E S.rank) L f →
    ∀ g, AllSome (IsHomology T L g) fun H =>
      (∀ γ, γ ∈ latG S T (GlobalTheory.SW.stdL D.host.E S.rank) L g ↔ ∀ k, (fun a => γ a k) ∈ H) ∧
      AllSome (IsVac C.X C.bas (wZero D) (tens (GlobalTheory.SW.stdL D.host.E S.rank) H)) fun φ =>
        ∃ (c : ℂ) (m : ℝ), ‖c‖ ^ 2 * m = 1 ∧
          MeanSq S T (movS C.θ T (C.sB B) g) (fun _ => 1) (C.mvB g B) (latG S T (GlobalTheory.SW.stdL D.host.E S.rank) L g)
            (fun z => thA C.X C.bas C.idx φ (C.xB (C.mvB g B)) (C.zOf (C.xB (C.mvB g B)) (realOf C.θ z)))
            (ENNReal.ofReal m) ∧
          (∀ z, frameFn C.θ S T (C.sB B) om f g z =
            c * thA C.X C.bas C.idx φ (C.xB (C.mvB g B)) (C.zOf (C.xB (C.mvB g B)) (realOf C.θ z))) ∧
          ∀ Q, thetaKO om 1 g (C.fvec B f Q) = c * thP C.X C.hr C.bas C.idx φ (C.toH Q) (C.xB (C.mvB g B))

def VacuumFrame : Prop := ∀ D : D7, AdelicFrame D ∧ ClassicalFrame D

end GlobalTheory.IndefiniteRowSideFullHecke.VacuumCharacterDeterminant

end
