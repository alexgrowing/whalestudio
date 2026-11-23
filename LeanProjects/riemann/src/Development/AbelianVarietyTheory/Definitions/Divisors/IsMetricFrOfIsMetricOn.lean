import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ChernWeilNumbers

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

section Point

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

def curvEv (G : V n → Matrix r r ℂ) (v : V n) : Matrix r r (Ev n) := (curvPoly G v).map (MvPolynomial.aeval sym)

def powAt (G : V n → Matrix r r ℂ) (v : V n) (k : ℕ) : Ev n := (curvEv G v ^ k).trace

def transAt (G G' : V n → Matrix r r ℂ) (v : V n) (k : ℕ) : Alt n :=
  ∑ a, ∑ i ∈ Finset.range k, ((curvEv G v ^ i *
    (conn G v (coordVec a) - conn G' v (coordVec a)).map (algebraMap ℂ (Ev n)) * curvEv G' v ^ (k - 1 - i)).trace : Ev n) * dz a

end Point

section Minors

variable {s : ℕ}

def leadMinor (G : Matrix (Fin s) (Fin s) ℂ) (j : ℕ) : ℂ :=
  (G.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j} → Fin s) Subtype.val).det

def grD (G : Matrix (Fin s) (Fin s) ℂ) (i : Fin s) : ℝ := (leadMinor G (i + 1)).re / (leadMinor G i).re

def ldPart (G : Matrix (Fin s) (Fin s) ℂ) : Matrix (Fin s) (Fin s) ℂ := Matrix.of fun i j =>
  (G.submatrix (fun a : {a : Fin s // (a : ℕ) < j + 1} => if a.1 = j then i else a.1) Subtype.val).det / leadMinor G j

end Minors

section Manifold

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {r : Type} [Fintype r] [DecidableEq r]

def HolUnitAt (T : M → Matrix r r ℂ) (y : M) : Prop :=
  IsUnit (T y).det ∧ ∀ i, y ∈ (A.e i).source → ∀ a b,
    ∀ᶠ v in 𝓝 (A.e i y), DifferentiableAt ℂ (fun u => T ((A.e i).symm u) a b) v

def SmoothUnitAt (G : M → Matrix r r ℂ) (y : M) : Prop :=
  IsUnit (G y).det ∧ ∀ i, y ∈ (A.e i).source → ∀ᶠ v in 𝓝 (A.e i y), MContDiffAt ∞ (fun u => G ((A.e i).symm u)) v

structure IsGramPair (G G' : M → M → Matrix r r ℂ) : Prop where

  smooth : ∀ y, SmoothUnitAt A (G y) y ∧ SmoothUnitAt A (G' y) y

  trans : ∀ y, ∀ᶠ z in 𝓝 y, ∃ T K K' : M → Matrix r r ℂ, HolUnitAt A T z ∧ HolUnitAt A K z ∧ HolUnitAt A K' z ∧
    ∀ᶠ w in 𝓝 z, G z w = T w * G y w * (K w)ᴴ ∧ G' z w = T w * G' y w * (K' w)ᴴ

def powFld (G : M → M → Matrix r r ℂ) (k : ℕ) (x : A.Pt) : Ev n := powAt (fun v => G x.pt (x.ch.symm v)) x.crd k

def chernFld (G : M → M → Matrix r r ℂ) (j : ℕ) (x : A.Pt) : Ev n := A.chern (G x.pt) j x

def transFld (G G' : M → M → Matrix r r ℂ) (k : ℕ) : A.Fld := fun x =>
  transAt (fun v => G x.pt (x.ch.symm v)) (fun v => G' x.pt (x.ch.symm v)) x.crd k

def DbarCoh (w w' : A.Pt → Ev n) : Prop :=
  A.IsForm (LineForm.fld A w) ∧ A.IsForm (LineForm.fld A w') ∧ A.dbar (LineForm.fld A w) = 0 ∧
    A.dbar (LineForm.fld A w') = 0 ∧ ∃ u, A.IsForm u ∧ LineForm.fld A w - LineForm.fld A w' = A.dbar u

end Manifold

section Variety

variable {F : Type} [Field F] {ι : Type} {m k : ι → ℕ} {X Y : Var F} {σ : F →+* ℂ}

def atlas (X : Var F) (σ : F →+* ℂ) : HolAtlas (CxPts X.str σ) X.dim where
  ι := AlgChart X.str σ X.dim
  e c := c.e
  cover y := have := X.smooth_str; AlgChart.exists_mem_source y
  holo c c' := c.holo_trans c'

structure IsMetricFr (E : Fr (ratOf X) m k) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) : Prop where

  posDef : ∀ y, ∀ A ∈ E.S (under y), ∀ τ, (H A y τ).PosDef

  smooth : ∀ y, ∀ A ∈ E.S (under y), ∀ τ i j, CInfAt (fun z => (H A z τ i j).re) y ∧ CInfAt (fun z => (H A z τ i j).im) y

  trans : ∀ y, ∀ A ∈ E.S (under y), ∀ A' ∈ E.S (under y), ∀ τ,
    H A' y τ = (A' * A⁻¹).map (ratVal · y) τ * H A y τ * ((A' * A⁻¹).map (ratVal · y) τ)ᴴ

theorem isMetricFr_of_isMetricOn {E : Fr (ratOf X) m 0} {H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ}
    (h : IsMetricOn E ⊤ H) : IsMetricFr E H :=
  ⟨fun y => h.posDef y mem_ptsIn_top, fun y => h.smooth y mem_ptsIn_top, fun y => h.trans y mem_ptsIn_top⟩

variable (E : Fr (ratOf X) m k) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)

def gramAt (τ : ι) (y z : CxPts X.str σ) : Matrix (Fin (m τ)) (Fin (m τ)) ℂ := H (E.nonempty (under y)).choose z τ

def chernF (x : ι × ℕ) : (atlas X σ).Pt → Ev X.dim := chernFld (atlas X σ) (gramAt E H x.1) x.2

def grF (x : Root m) (p : (atlas X σ).Pt) : Ev X.dim :=
  ofValues (ddc (fun v => -Real.log (grD (gramAt E H x.1 p.pt (p.ch.symm v)) x.2)) p.crd)

def c1W {L : LB X.X} (ψ : Weight X.str σ L) (p : (atlas X σ).Pt) : Ev X.dim :=
  ofValues (ddc (fun v => ψ.φ (pick ψ.isLB p.pt) (p.ch.symm v)) p.crd)

def ptMap (σ : F →+* ℂ) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str) : CxPts Y.str σ → CxPts X.str σ := PtsOver.map f hf _

def pullGram (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str) (B : Mat m Y.Fn) (z : CxPts Y.str σ) : Mat m ℂ :=
  fun τ => (B * (Mat.map (E.nonempty (under (ptMap σ f hf z))).choose φ)⁻¹).map (ratVal · z) τ *
    H (E.nonempty (under (ptMap σ f hf z))).choose (ptMap σ f hf z) τ *
    ((B * (Mat.map (E.nonempty (under (ptMap σ f hf z))).choose φ)⁻¹).map (ratVal · z) τ)ᴴ

end Variety

section Inhabitants

def expGram {n : ℕ} (r : Type) [Fintype r] [DecidableEq r] (u : V n → ℝ) (v : V n) : Matrix r r ℂ :=
  ((Real.exp (u v) : ℝ) : ℂ) • 1

end Inhabitants

end GlobalTheory.ChernCalc
