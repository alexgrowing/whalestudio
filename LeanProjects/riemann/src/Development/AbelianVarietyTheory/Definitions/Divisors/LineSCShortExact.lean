import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSumSwap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CovTest.SwapLine

namespace GlobalTheory.LineForm

def hs (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  ∑ j ∈ Finset.range (m + 1), C ((-1) ^ j * ((m - j).choose j : ℝ)) * X 0 ^ (m - 2 * j) * X 1 ^ j

def pm (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  ∑ j ∈ Finset.range (m + 1), C ((m.choose j * j.factorial * j.factorial : ℝ) / (2 * j + 1).factorial) *
    X 1 ^ (m - j) * (X 0 ^ 2 - 4 * X 1) ^ j

def upperParabolic {ι : Type} (s : Finset ι) (m : ι → ℕ) (W : ι → MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 5) ℝ :=
  ∑ x ∈ s, (X 0 * (X 3 + X 4 - X 0)) ^ m x * aeval ![X 2, X 3, X 4] (W x)

def downP {ι : Type} (s : Finset ι) (m : ι → ℕ) (W : ι → MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 4) ℝ :=
  ∑ x ∈ s, aeval ![X 1 + X 2, X 3] (pm (m x)) * aeval ![X 0, X 1, X 2] (W x)

def idx (d : ℕ) : Finset (ℕ × ℕ) := (Finset.range (d + 3) ×ˢ Finset.range (d + 3)).filter fun x => x.2 < x.1

def expo (x : ℕ × ℕ) : ℕ := x.1 - 1 - x.2

def coefW (R : ℕ → MvPolynomial (Fin 2) ℝ) (x : ℕ × ℕ) : MvPolynomial (Fin 3) ℝ :=
  (X 1 * X 2) ^ x.2 * aeval ![X 1 + X 2, X 0] (R x.1)

def baseT (d : ℕ) (R : ℕ → MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 3) ℝ :=
  ∑ x ∈ idx d, X 1 ^ x.2 * aeval ![X 0, X 1] (pm (expo x)) * aeval ![X 0, X 2] (R x.1)

section Manifold

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

def fld (w : A.Pt → Ev n) : A.Fld := fun x => w x

def evalF {ι : Type} (w : ι → A.Pt → Ev n) (P : MvPolynomial ι ℝ) : A.Fld :=
  fld A fun x => aeval (fun i => w i x) (P.map (algebraMap ℝ ℂ))

def wInt [MeasurableSpace M] (g : M → ℝ) (α : A.Fld) : ℝ := ∫ y, g y ∂A.part α 1 - ∫ y, g y ∂A.part α (-1)

theorem wInt_one [MeasurableSpace M] (α : A.Fld) : wInt A (fun _ => 1) α = A.integral α := by
  simp [wInt, HolAtlas.integral]

end Manifold

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {p' : Y ⟶ Sp k} {D D' : ℕ}

abbrev lineSC {E : X.Modules} (fl : Vert.Flag E 2) : ShortComplex X.Modules :=
  .mk (fl.ι 1) (Limits.cokernel.π _) (Limits.cokernel.condition _)

theorem lineSC_shortExact {E : X.Modules} (fl : Vert.Flag E 2) : (lineSC fl).ShortExact :=
  { exact := ShortComplex.exact_cokernel _ }

def frameAt {E : X.Modules} (fl : Vert.Flag E 2) {σ : k →+* ℂ} (y : CxPts p σ) : VBExt.AdaptedChart (lineSC fl) 1 1 :=
  (Met.exists_adapted (r := 1) (s := 1) (lineSC_shortExact fl) (fl.isVB 1) (fl.isVB_cokernel 1) y).choose

theorem mem_frameAt {E : X.Modules} (fl : Vert.Flag E 2) {σ : k →+* ℂ} (y : CxPts p σ) :
    y ∈ ptsIn p σ (frameAt fl y).U :=
  (Met.exists_adapted (r := 1) (s := 1) (lineSC_shortExact fl) (fl.isVB 1) (fl.isVB_cokernel 1) y).choose_spec

variable (h : IsRegVar p D) (h' : IsRegVar p' D') (σ : k →+* ℂ)

def c1F (L : HermLB p) (x : (h.atlas σ).Pt) : Ev D :=
  ofValues (ddc (fun v => (L.φ σ).φ (pick (L.φ σ).isLB x.pt) (x.ch.symm v)) x.crd)

def c2F {E : X.Modules} (m : VMetric p E 2) (fl : Vert.Flag E 2) (x : (h.atlas σ).Pt) : Ev D :=
  (h.atlas σ).chern ((m.met σ).gram (frameAt fl x.pt).frame) 2 x

def omF {E : X.Modules} (m : VMetric p E 2) (fl : Vert.Flag E 2) (x : (h.atlas σ).Pt) : Ev D :=
  ofValues (extTrace (fun v => (m.met σ).gram (frameAt fl x.pt).frame (x.ch.symm v)) x.crd)

def fam4 {E : X.Modules} {m : VMetric p E 2} (H : m.IsCInf) (fl : Vert.Flag E 2) (A : HermLB p) :
    Fin 4 → (h.atlas σ).Pt → Ev D :=
  ![c1F h σ A, c1F h σ (VMetric.grLB fl 0 H), c1F h σ (VMetric.grLB fl 1 H), c2F h σ m fl]

def pullF (π : Y ⟶ X) (w : π ≫ p = p') (α : (h.atlas σ).Fld) : (h'.atlas σ).Fld :=
  (h.atlas σ).pullback (h'.atlas σ) (PtsOver.map π w _) α

end GlobalTheory.LineForm
