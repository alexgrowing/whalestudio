import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BoundaryPolynomialFunctions

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Set Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.ArchLim

section Dens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

def densInt (ρ : AlgChart p σ D → CxPts p σ → ℝ) (f : CxPts p σ → ℝ) : ℝ :=
  ∫ y, f y ∂part ρ - ∫ y, f y ∂part fun c y => -ρ c y

def IntegrableDens (ρ : AlgChart p σ D → CxPts p σ → ℝ) (f : CxPts p σ → ℝ) : Prop :=
  Integrable f (part ρ) ∧ Integrable f (part fun c y => -ρ c y)

def IsMDens (ρ : AlgChart p σ D → CxPts p σ → ℝ) : Prop :=
  (∀ (c c' : AlgChart p σ D) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source →
    ρ c y = ‖ChartGlue.transDet c.e c'.e y‖ ^ 2 * ρ c' y) ∧
  ∀ c : AlgChart p σ D, AEMeasurable (fun v => ρ c (c.e.symm v)) (volume.restrict c.e.target)

theorem isMDens_of_isDens {ρ : AlgChart p σ D → CxPts p σ → ℝ} (h : IsDens ρ) : IsMDens ρ :=
  ⟨h.1, fun c => (h.2 c).aemeasurable c.e.open_target.measurableSet⟩

theorem densInt_chernDens {B : LB X} (φ : Weight p σ B) (f : CxPts p σ → ℝ) :
    densInt (fun (c : AlgChart p σ D) y => c.chernDens φ y) f = φ.chernInt D univ f ∧
      (IntegrableDens (fun (c : AlgChart p σ D) y => c.chernDens φ y) f ↔ φ.ChernIntegrableOn D univ f) := by
  simp [densInt, IntegrableDens, Weight.chernInt, Weight.ChernIntegrableOn, (MixDens.chernPart_eq φ).1,
    (MixDens.chernPart_eq φ).2, integrableOn_univ]

def secondChernDensity (e : ℕ) (Θ : V (e + 2) → V (e + 2) → V (e + 2) → V (e + 2) → ℂ)
    (A : Matrix (Fin (e + 2)) (Fin (e + 2)) ℂ) : ℝ :=
  -(∑ s : Equiv.Perm (Fin (e + 2)), ∑ t : Equiv.Perm (Fin (e + 2)),
    ((Equiv.Perm.sign s * Equiv.Perm.sign t : ℤˣ) : ℤ) *
      (Θ (bas _ (s 0)) (bas _ (t 0)) (bas _ (s 1)) (bas _ (t 1)) * ∏ i : Fin e, A (s i.succ.succ) (t i.succ.succ))).re /
    Real.pi ^ e

def secondChernDensityOfMetric {E : X.Modules} {r : ℕ} (h : Met p σ E r) {L : LB X} (φ : Weight p σ L) (e : ℕ)
    (c : AlgChart p σ (e + 2)) (y : CxPts p σ) : ℝ :=
  secondChernDensity e (chTwo (fun u => h.G (h.isVB.pick y) (c.e.symm u)) (c.e y)) (chernMat φ c y)

end Dens

section Cell

variable {n r D : ℕ} (ε : Fin D ≃ Fin n ⊕ Low r)

def base (v : V D) : V n := WithLp.toLp 2 fun a => v (ε.symm (.inl a))

def fib (v : V D) : Low r → ℂ := fun s => v (ε.symm (.inr s))

def pt (u : V n) (x : Low r → ℂ) : V D := WithLp.toLp 2 fun j => Sum.elim (fun a => u a) x (ε j)

theorem base_pt (u : V n) (x : Low r → ℂ) : base ε (pt ε u x) = u := by
  ext j
  simp [base, pt]

theorem fib_pt (u : V n) (x : Low r → ℂ) : fib ε (pt ε u x) = x := by
  ext s
  simp [fib, pt]

def rootWt (G : V n → Matrix (Fin r) (Fin r) ℂ) (i : Fin r) (v : V D) : ℝ :=
  -Real.log (quotGram ((chg (uni (fib ε v)) (G (base ε v))).submatrix (emb i) (emb i))).det.re

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {σ : k →+* ℂ} (π : Y ⟶ B) (w : π ≫ q = p)

def IsCell (c : AlgChart q σ n) (c' : AlgChart p σ D) : Prop :=
  c'.e.source = PtsOver.map π w (spMap σ) ⁻¹' c.e.source ∩ ptsIn p σ c'.U ∧
    c'.e.target = {v | base ε v ∈ c.e.target} ∧
    ∀ y ∈ c'.e.source, base ε (c'.e y) = c.e (PtsOver.map π w (spMap σ) y)

end Cell

section Pot

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {q : Y ⟶ Sp k} {σ : k →+* ℂ} {n : ℕ} {X : Type} [TopologicalSpace X]

def potMat (P : LocPot X) (u : CxPts q σ → X) (c : AlgChart q σ n) (y : CxPts q σ) : Matrix (Fin n) (Fin n) ℂ :=
  cHess n (fun v => (P.φ (u y) (u (c.e.symm v)) : ℂ)) (c.e y)

open Classical in

def potDens (P : LocPot X) (S : Set X) (u : CxPts q σ → X) (c : AlgChart q σ n) (y : CxPts q σ) : ℝ :=
  if u y ∈ S then n.factorial * (2 / Real.pi) ^ n * (potMat P u c y).det.re else 0

end Pot

open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
  {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

def up {Y : Scheme.{0}} {q : Y ⟶ Sp Oz} (j : Y ⟶ Z.X) (hj : j ≫ Z.s = q) (σ : c.F →+* ℂ) (y : CxPts q (σ.comp β)) :
    CxPts (genStr Z) σ :=
  ⟨pullback.lift (y.1 ≫ j) (spMap σ) (by rw [Category.assoc, hj, y.2, ← Spec.map_comp]; rfl), pullback.lift_snd _ _ _⟩

theorem up_ι {Y : Scheme.{0}} {q : Y ⟶ Sp Oz} (j : Y ⟶ Z.X) (hj : j ≫ Z.s = q) (σ : c.F →+* ℂ) (y : CxPts q (σ.comp β)) :
    (up j hj σ y).1 ≫ genι Z = y.1 ≫ j := pullback.lift_fst _ _ _

theorem continuous_up {Y : Scheme.{0}} {q : Y ⟶ Sp Oz} (j : Y ⟶ Z.X) (hj : j ≫ Z.s = q) (σ : c.F →+* ℂ) :
    Continuous (up j hj σ) := by
  refine Continuous.subtype_mk ?_ _
  rw [(isEmbedding_of_isPullback (C := ℂ) (IsPullback.of_hasPullback Z.s (spMap β))).continuous_iff]
  refine (((continuous_comp j).comp continuous_subtype_val).prodMk (continuous_const (y := spMap σ))).congr fun y => ?_
  exact Prod.ext (pullback.lift_fst _ _ _).symm (pullback.lift_snd _ _ _).symm

theorem inner_up {Y : Scheme.{0}} {q : Y ⟶ Sp Oz} (j : Y ⟶ Z.X) (hj : j ≫ Z.s = q) (σ : c.F →+* ℂ)
    (y : CxPts q (σ.comp β)) : Inner (up j hj σ y) ↔ j (y.1 (IsLocalRing.closedPoint ℂ)) ∈ abLocus Z.t.G := by
  have e : genι Z ((up j hj σ y).1 (IsLocalRing.closedPoint ℂ)) = j (y.1 (IsLocalRing.closedPoint ℂ)) :=
    congrArg (fun g : Sp ℂ ⟶ Z.X => g (IsLocalRing.closedPoint ℂ)) (up_ι j hj σ y)
  rw [← e]
  exact not_not.trans (Set.ext_iff.1 Z.ab_gen _).symm

def eigGram {σ : c.F →+* ℂ} (G : EigMet Z σ) {W : Type} (a : W → CxFr Z σ) (τ : E →+* ℂ) (u : W) :
    Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ := (G.gram (a u).1 (a u).2 τ)ᵀ

end Model

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

def CurvBound (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) (P : LocPot (CxPts (genStr s.T.Z) σ)) (C : ℝ) : Prop :=
  ∀ (n : ℕ) (U : Set (V n)) (a : V n → CxFr s.T.Z σ), IsOpen U → HolFam U a → ContinuousOn (fun u => (a u).1) U →
    ∀ u ∈ U, Inner (a u).1 → (cHess n (fun v => (P.φ (a u).1 (a v).1 : ℂ)) u).PosSemidef ∧
      ∀ R : ℝ, 2 ≤ R → ∀ (τ : D.host.E →+* ℂ) (ξ η : V n),
        opNorm (eigGram (x.eigMetAt σ (some R)) a τ u) (eigGram (x.eigMetAt σ (some R)) a τ u)
          (curv (eigGram (x.eigMetAt σ (some R)) a τ) u ξ η) ≤
          C * gnorm (cHess n (fun v => (P.φ (a u).1 (a v).1 : ℂ)) u) ξ.ofLp *
            gnorm (cHess n (fun v => (P.φ (a u).1 (a v).1 : ℂ)) u) η.ofLp

end GlobalTheory.ArchLim

end
