import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTorsionFormWithPoint
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CharChPartZero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat transl IsFactor IsMetric)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points (PtsOver)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm (IsRegVar BottChern ArChow hermMat eval₂ bas relCot dRel IsRelAcyclic IsGenSmooth)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (om0)
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

namespace GlobalTheory.TorsionForm

variable {k : Type} [CommRing k] {S : Scheme.{0}} {p : S ⟶ Sp k} {σ : k →+* ℂ} {A : Over S}
  {g D : ℕ}

def cot (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ) (W : A.left.Opens) (f : Γ(A.left, W)) (v : V D) :
    Fin g → ℂ := fun a => fderiv ℂ (fun z => ev (A.hom ≫ p) σ W f (ex (v, z))) 0 (Pi.single a 1)

def IsPeriodChart [GrpObj A] (h : VMetric p (omega A) g) (c : AlgChart p σ D)
    (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ) : Prop :=
  IsPeriodMap c.e.target τ ∧ IsHolTo (cov c.e.target g) (fun P => (ex P).1) ∧ ∀ v ∈ c.e.target,
    (∀ z, (ex (v, z)).1 ≫ A.hom = (c.e.symm v).1) ∧
    (∀ z w, ∀ x y : Over.mk (c.e.symm v).1 ⟶ A, x.left = (ex (v, z)).1 → y.left = (ex (v, w)).1 →
      (x * y).left = (ex (v, z + w)).1) ∧
    (∀ x : Over.mk (c.e.symm v).1 ⟶ A, ∃ z, x.left = (ex (v, z)).1) ∧
    (∀ z, (ex (v, z)).1 = (c.e.symm v).1 ≫ unitSec A ↔ ∃ l ∈ stdLat g, z = per (τ v) l) ∧
    ∀ (U : S.Opens) (W : A.left.Opens) (hU : U ≤ unitSec A ⁻¹ᵁ W) (f f' : Γ(A.left, W)),
      c.e.symm v ∈ ptsIn p σ U → (h.met σ).form (dUnit A hU f) (dUnit A hU f') (c.e.symm v) =
        HermFrame.form ((2 : ℂ) • imPart τ v) (cot ex W f v) (cot ex W f' v)

def IsFramed (L : HermLB (A.hom ≫ p)) (B : Set (V D)) (τ : V D → Matrix (Fin g) (Fin g) ℂ)
    (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ) (j : Fl g → Pt (V D) g → ℂ) (m : Pt (V D) g → ℝ) : Prop :=
  ∃ fr : L.B.ι → Pt (V D) g → ℂ, ∀ i,
    DifferentiableOn ℂ (fr i) (cov B g ∩ ex ⁻¹' ptsIn _ σ (L.B.U i)) ∧
    ∀ P ∈ cov B g, ex P ∈ ptsIn _ σ (L.B.U i) → fr i P ≠ 0 ∧
      (∀ i', ex P ∈ ptsIn _ σ (L.B.U i') → fr i P = gv _ σ L.B i i' (ex P) * fr i' P) ∧
      m P = ‖fr i P‖ ^ 2 * Real.exp (-(L.φ σ).φ i (ex P)) ∧
      ∀ l ∈ stdLat g, fr i P = j l P * fr i (transl τ l P)

def IsL2OnDiagonal (L : HermLB (A.hom ≫ p)) (M : HermLB p)
    (ψ : toMod M.B ≅ (Scheme.Modules.pushforward A.hom).obj (toMod L.B)) (c : AlgChart p σ D)
    (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ) : Prop :=
  ∀ v ∈ c.e.target, ∀ (U : S.Opens) (s : Γ(toMod M.B, U)), c.e.symm v ∈ ptsIn p σ U →
    ((VMetric.ofLB M).met σ).form s s (c.e.symm v) = ((2 * π : ℂ) ^ g)⁻¹ *
      ∫ x in Icc (0 : Fl g) 1, ((VMetric.ofLB L).met σ).form (V := A.hom ⁻¹ᵁ U)
        (ψ.hom.app U s) (ψ.hom.app U s) (ex (v, per (τ v) x))

def IsTopForm (ρ : ∀ σ : k →+* ℂ, AlgChart p σ 1 → CxPts p σ → ℝ) (I : ℝ) : Prop :=
  (∀ σ (c : AlgChart p σ 1), ContDiffOn ℝ ∞ (ρ σ c ∘ c.e.symm) c.e.target ∧
    ∀ c' : AlgChart p σ 1, ∀ y ∈ c.e.source, y ∈ c'.e.source →
      ρ σ c y = ‖ChartGlue.transDet c.e c'.e y‖ ^ 2 * ρ σ c' y) ∧
  (∀ σ (ε : ℤˣ), ChartGlue.glueMeas (fun c : AlgChart p σ 1 => c.e)
    (fun c y => ENNReal.ofReal ((ε : ℤ) * ρ σ c y)) univ ≠ ⊤) ∧
  I = ∑ᶠ σ, ∑ ε : ℤˣ, ((ε : ℤ) : ℝ) * (ChartGlue.glueMeas (fun c : AlgChart p σ 1 => c.e)
    (fun c y => ENNReal.ofReal ((ε : ℤ) * ρ σ c y)) univ).toReal

def curveForm (t ρ : ℝ) : Ext (1 + 1) := fun I =>
  if I = ∅ then t else if I = Finset.univ then Complex.I / 2 * ρ else 0

def rOne : ℝ := (2 * deriv riemannZeta (-1) + riemannZeta (-1)).re

theorem gdeg_eq (N : HermLB p) : gdeg N 1 = ∑ᶠ σ, ∑ ε : ℤˣ, ((ε : ℤ) : ℝ) *
    (ChartGlue.glueMeas (fun c : AlgChart p σ 1 => c.e)
      (fun c y => ENNReal.ofReal ((ε : ℤ) * c.chernDens (N.φ σ) y)) univ).toReal := by
  unfold gdeg chInt
  refine finsum_congr fun σ => ?_
  rw [Fintype.sum_eq_add 1 (-1) (by decide) (fun x hx =>
    (Int.units_eq_one_or x).elim (fun h => absurd h hx.1) (fun h => absurd h hx.2))]
  simp [Weight.chernInt, Weight.chernPart, integral_const, sub_eq_add_neg]
  rfl
private theorem per_zero_lemma {n : ℕ} (t : Matrix (Fin n) (Fin n) ℂ) : per t (0 : Fl n) = 0 := by
  unfold per
  ext i
  simp [Matrix.vecMul]

def ChartsExist : Prop :=
  ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p → ∀ (P : PPAS S)
    (h : VMetric p (omega P.A) P.g), P.IsDualRiemann (1 / 2) h → ∀ (L : HermLB (P.A.hom ≫ p))
    (σ : k →+* ℂ) (y : CxPts p σ), ∃ (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ)
      (ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ) (j : Fl P.g → Pt (V 1) P.g → ℂ)
      (m : Pt (V 1) P.g → ℝ), y ∈ c.e.source ∧ IsPeriodChart h c τ ex ∧
        IsFramed L c.e.target τ ex j m ∧ IsDatum c.e.target τ (stdLat P.g) j m

section Global

variable {D' r : ℕ}

def IsUnifChart (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ)
    (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ) : Prop :=
  IsPeriodMap c.e.target τ ∧ IsHolTo (cov c.e.target g) (fun P => (ex P).1) ∧ ∀ v ∈ c.e.target,
    (∀ z, (ex (v, z)).1 ≫ A.hom = (c.e.symm v).1) ∧
    (∀ y : CxPts (A.hom ≫ p) σ, y.1 ≫ A.hom = (c.e.symm v).1 → ∃ z, ex (v, z) = y) ∧
    ∀ z w, ex (v, z) = ex (v, w) ↔ ∃ l ∈ stdLat g, z = w + per (τ v) l

theorem IsPeriodChart.isUnifChart [GrpObj A] {h : VMetric p (omega A) g} {c : AlgChart p σ D}
    {τ : V D → Matrix (Fin g) (Fin g) ℂ} {ex : Pt (V D) g → CxPts (A.hom ≫ p) σ}
    (H : IsPeriodChart h c τ ex) : IsUnifChart c τ ex := by
  obtain ⟨hP, hH, hv⟩ := H
  refine ⟨hP, hH, fun v hv' => ?_⟩
  obtain ⟨hproj, hmul, hsurj, hzero, -⟩ := hv v hv'
  let xz : ∀ z, Over.mk (c.e.symm v).1 ⟶ A := fun z => Over.homMk (ex (v, z)).1 (hproj z)
  have hm : ∀ z w, xz z * xz w = xz (z + w) := fun z w => by
    ext1
    exact hmul z w _ _ rfl rfl
  have h1 : xz 0 = 1 := by
    have e := hm 0 0
    rw [add_zero] at e
    exact mul_left_cancel (a := xz 0) (by rw [_root_.mul_one]; exact e)
  have hu : (ex (v, 0)).1 = (c.e.symm v).1 ≫ unitSec A :=
    (hzero 0).2 ⟨0, Submodule.zero_mem _, (per_zero_lemma _).symm⟩
  refine ⟨hproj, fun y hy => ?_, fun z w => ⟨fun hzw => ?_, fun ⟨l, hl, hzw⟩ => ?_⟩⟩
  · obtain ⟨z, hz⟩ := hsurj (Over.homMk y.1 hy)
    exact ⟨z, Subtype.ext hz.symm⟩
  · have e1 : xz z = xz w := by
      ext1
      exact congrArg Subtype.val hzw
    have e2 : xz (z + -w) = xz 0 := by rw [← hm, e1, hm, add_neg_cancel]
    have e3 : (ex (v, z + -w)).1 = (ex (v, 0)).1 := congrArg (fun f => f.left) e2
    obtain ⟨l, hl, hl'⟩ := (hzero (z + -w)).1 (e3.trans hu)
    exact ⟨l, hl, by rw [← hl']; abel⟩
  · have hp : xz (per (τ v) l) = 1 := by
      rw [← h1]
      ext1
      exact ((hzero _).2 ⟨l, hl, rfl⟩).trans hu.symm
    have e1 : xz z = xz w := by rw [hzw, ← hm, hp, _root_.mul_one]
    exact Subtype.ext (congrArg (fun f => f.left) e1)

def IsFlatOn (h' : IsRegVar (A.hom ≫ p) D') (Ω : (h'.atlas σ).Fld) (B : Set (V D))
    (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ) : Prop :=
  ∀ P ∈ cov B g, ∀ x : (h'.atlas σ).Pt, x.pt = ex P → ∀ v w : Pt (V D) g,
    eval₂ (Ω x) (fderiv ℂ (x.ch ∘ ex) P v) (fderiv ℂ (x.ch ∘ ex) P w) = om0 τ P ![v, w]

def fibForm (h : IsRegVar p D) (h' : IsRegVar (A.hom ≫ p) D') (Ω₀ : (h'.atlas σ).Fld) (κ : (h.atlas σ).Fld) :
    (h'.atlas σ).Fld :=
  Ω₀ + (h.atlas σ).pullback (h'.atlas σ) (PtsOver.map A.hom rfl _) κ

variable (g) in

def IsFlatFibration (h : IsRegVar p D) (h' : IsRegVar (A.hom ≫ p) D') (Ω₀ : (h'.atlas σ).Fld)
    (κ : (h.atlas σ).Fld) : Prop :=
  (h.atlas σ).IsRealForm 1 κ ∧ (h'.atlas σ).IsRealForm 1 (fibForm h h' Ω₀ κ) ∧
    (h'.atlas σ).del (fibForm h h' Ω₀ κ) = 0 ∧ (h'.atlas σ).dbar (fibForm h h' Ω₀ κ) = 0 ∧
    ∀ y : CxPts p σ, ∃ (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ)
      (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ),
      y ∈ c.e.source ∧ IsUnifChart c τ ex ∧ IsFlatOn h' Ω₀ c.e.target τ ex

def cotAt (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ) (W : A.left.Opens) (f : Γ(A.left, W)) (P : Pt (V D) g) :
    Fin g → ℂ := fun a => fderiv ℂ (fun z => ev (A.hom ≫ p) σ W f (ex (P.1, z))) P.2 (Pi.single a 1)

def IsFibreMetric (m : VMetric (A.hom ≫ p) (relCot A.hom) g) (B : Set (V D))
    (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ) : Prop :=
  ∀ P ∈ cov B g, ∀ (W : A.left.Opens) (f f' : Γ(A.left, W)), ex P ∈ ptsIn _ σ W →
    (m.met σ).form (dRel A.hom W f) (dRel A.hom W f') (ex P) =
      HermFrame.form ((2 : ℂ) • imPart τ P.1) (cotAt ex W f P) (cotAt ex W f' P)

def IsL2Metric (L : HermLB (A.hom ≫ p)) (M : HermVB p r)
    (ψ : M.E ≅ (Scheme.Modules.pushforward A.hom).obj (toMod L.B)) (c : AlgChart p σ D)
    (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ) : Prop :=
  ∀ v ∈ c.e.target, ∀ (U : S.Opens) (s t : Γ(M.E, U)), c.e.symm v ∈ ptsIn p σ U →
    (M.h.met σ).form s t (c.e.symm v) = ((2 * π : ℂ) ^ g)⁻¹ *
      ∫ x in Icc (0 : Fl g) 1, ((VMetric.ofLB L).met σ).form (V := A.hom ⁻¹ᵁ U)
        (ψ.hom.app U s) (ψ.hom.app U t) (ex (v, per (τ v) x))

variable (g) in

def IsTorsionOn (h : IsRegVar p D) (h' : IsRegVar (A.hom ≫ p) D') (Ω₀ : (h'.atlas σ).Fld)
    (κ : (h.atlas σ).Fld) (L : HermLB (A.hom ≫ p)) (T : ℕ → (h.atlas σ).Fld) : Prop :=
  (∀ i, (h.atlas σ).IsRealForm i (T i)) ∧ ∀ (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ)
    (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ) (j : Fl g → Pt (V D) g → ℂ) (m : Pt (V D) g → ℝ),
    IsUnifChart c τ ex → IsFlatOn h' Ω₀ c.e.target τ ex → IsFramed L c.e.target τ ex j m →
    ∀ v ∈ c.e.target, IsTorsionFormWith τ (stdLat g) j m coordVec v (hermMat ((h.atlas σ).loc κ c v))
      ((bas D).repr ((h.atlas σ).loc (∑ i ∈ Finset.range (D + 1), T i) c v))

end Global

end GlobalTheory.TorsionForm

namespace GlobalTheory.Published

open GlobalTheory.TorsionForm MvPolynomial

def BismutKoehlerTorsion : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (g n : ℕ) (B : Set E)
    (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ)
    (h : Pt E g → ℝ), IsDatum B τ M j h → (∀ b ∈ B, IsAcyclicAt τ M j h b) → ∀ β : Fin n → E,
    ∃ T : E → Ext (n + n), ContDiffOn ℝ ∞ T B ∧ ∀ b ∈ B,
      (∀ T', IsTorsionForm τ M j h β b T' ↔ T' = T b) ∧
      (∀ I, (I.filter (·.val < n)).card ≠ (I.filter (n ≤ ·.val)).card → T b I = 0) ∧
      (T b ∅).im = 0 ∧
      ∀ i l : Fin n, T b {l.castAdd n, i.natAdd n} = -star (T b {i.castAdd n, l.natAdd n})

def ArithRiemannRochAbelian : Prop :=
  ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) [IsIntegral S], IsRegSurf p →
  ∀ (A : Over S) [GrpObj A] [IsIntegral A.left] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → IsArithVar (A.hom ≫ p) (g + 1) →
  ∀ (h : VMetric p (omega A) g) (H : h.IsCInf) (L : HermLB (A.hom ≫ p)), Out.RelAmple A L.B →
  ∀ (M : HermLB p) (ψ : toMod M.B ≅ (Scheme.Modules.pushforward A.hom).obj (toMod L.B)),
    (∀ σ (y : CxPts p σ), ∃ (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin g) (Fin g) ℂ)
      (ex : Pt (V 1) g → CxPts (A.hom ≫ p) σ),
      y ∈ c.e.source ∧ IsPeriodChart h c τ ex ∧ IsL2OnDiagonal L M ψ c τ ex) →
  ∃ (t : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) (ρ : ∀ σ : k →+* ℂ, AlgChart p σ 1 → CxPts p σ → ℝ) (I : ℝ),
    (∀ σ y, CInfAt (t σ) y) ∧ IsTopForm ρ I ∧
    (∀ σ (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin g) (Fin g) ℂ)
      (ex : Pt (V 1) g → CxPts (A.hom ≫ p) σ) (j : Fl g → Pt (V 1) g → ℂ) (m : Pt (V 1) g → ℝ),
      IsPeriodChart h c τ ex → IsFramed L c.e.target τ ex j m → ∀ y ∈ c.e.source,
        IsTorsionForm τ (stdLat g) j m ![EuclideanSpace.single 0 1] (c.e y)
          (curveForm (t σ y) (ρ σ c y))) ∧
    ∀ (N : HermLB p) (Ψ Φ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ),
      IsArFun ![M, VMetric.det H, N] 1 Ψ →
      IsArFun ![L, (VMetric.det H).pull A.hom rfl, N.pull A.hom rfl] (g + 1) Φ →
      Ψ (X 0 * X 2) - chInt N 1 t / 2 =
        Φ (X 0 ^ (g + 1) * X 2) / (g + 1).factorial - Ψ (X 1 * X 2) / 2 ∧
      ∀ (fl : Vert.Flag (omega A) g) (a : ℝ), VMetric.IsFlagCh2 H fl a →
        Ψ (X 0 ^ 2) / 2 - I / 2 =
          Φ (X 0 ^ (g + 2)) / (g + 2).factorial - Φ (X 0 ^ (g + 1) * X 1) / (2 * (g + 1).factorial) +
            Ψ (X 1 ^ 2) / 8 - a / 12 + rOne / 2 * gdeg (VMetric.det H) 1

def BismutKoehlerTorsionWith : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (g n : ℕ) (B : Set E)
    (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ)
    (h : Pt E g → ℝ), IsDatum B τ M j h → (∀ b ∈ B, IsAcyclicAt τ M j h b) →
    ∀ κ : E → E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ, IsClosedHerm B κ → ∀ β : Fin n → E,
    ∃ T : E → Ext (n + n), ContDiffOn ℝ ∞ T B ∧ ∀ b ∈ B,
      (∀ T', IsTorsionFormWith τ M j h β b (of fun i l => κ b (β i) (β l)) T' ↔ T' = T b) ∧
      (∀ I, (I.filter (·.val < n)).card ≠ (I.filter (n ≤ ·.val)).card → T b I = 0) ∧
      (T b ∅).im = 0 ∧
      ∀ i l : Fin n, T b {l.castAdd n, i.natAdd n} = -star (T b {i.castAdd n, l.natAdd n})

theorem BismutKoehlerTorsionWith.flat (H : BismutKoehlerTorsionWith) : BismutKoehlerTorsion := by
  intro E _ _ _ g n B τ M j h hD hA β
  have key : ∀ b T', IsTorsionFormWith τ M j h β b (of fun i l => (0 : E → E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ) b (β i) (β l)) T' ↔
      IsTorsionForm τ M j h β b T' := by
    intro b T'
    have key2 : ∀ F, IsHeatTraceWith τ M j h β b (of fun i l => (0 : E → E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ) b (β i) (β l)) F ↔
        IsHeatTrace τ M j h β b F := by
      intro F
      unfold IsHeatTraceWith IsHeatTrace
      simp only [Matrix.of_apply, Pi.zero_apply, LinearMap.zero_apply]
      simp [baseMul]
    unfold IsTorsionFormWith IsTorsionForm
    exact exists_congr fun F => and_congr_left' (key2 F)
  have hC : IsClosedHerm B (0 : E → E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ) := by
    unfold IsClosedHerm
    simp
    refine ⟨contDiffOn_const, fun b _ u v => ?_⟩
    simp [d10]
  obtain ⟨T, hT, hb⟩ := H E g n B τ M j h hD hA 0 hC β
  exact ⟨T, hT, fun b hb' => ⟨fun T' => (key b T').symm.trans ((hb b hb').1 T'), (hb b hb').2⟩⟩

def BismutKoehlerGlobal : Prop :=
  ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (D : ℕ) (h : IsRegVar p D) (A : Over S) (D' : ℕ)
    (h' : IsRegVar (A.hom ≫ p) D') (g : ℕ), SmoothOfRelativeDimension g A.hom →
    ∀ L : HermLB (A.hom ≫ p), IsRelAcyclic (A.hom ≫ p) A.hom L.B →
    ∀ (σ : k →+* ℂ) (Ω₀ : (h'.atlas σ).Fld) (κ : (h.atlas σ).Fld), IsFlatFibration g h h' Ω₀ κ →
    ∃ T, IsTorsionOn g h h' Ω₀ κ L T

def TorsionAnomaly : Prop :=
  ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (D : ℕ) (h : IsRegVar p D) (A : Over S) (D' : ℕ)
    (h' : IsRegVar (A.hom ≫ p) D') (g : ℕ), SmoothOfRelativeDimension g A.hom →
    ∀ L : HermLB (A.hom ≫ p), IsRelAcyclic (A.hom ≫ p) A.hom L.B →
    ∀ (σ : k →+* ℂ) (Ω₀ : (h'.atlas σ).Fld) (κ κ' : (h.atlas σ).Fld), IsFlatFibration g h h' Ω₀ κ →
    IsFlatFibration g h h' Ω₀ κ' → ∀ T T', IsTorsionOn g h h' Ω₀ κ L T → IsTorsionOn g h h' Ω₀ κ' L T' →
    ∀ i, (h.atlas σ).IsExact (T i - T' i)

def GilletRoesslerSoule : Prop :=
  ∃ B : BottChern, ∀ (k : Type) [CommRing k], ∃ (C : ArChow B k) (P : C.Push),
    ∀ (S : Scheme.{0}) (p : S ⟶ Sp k) (D : ℕ) (h : IsRegVar p D) (A : Over S) (D' : ℕ)
      (h' : IsRegVar (A.hom ≫ p) D') (g : ℕ), SmoothOfRelativeDimension g A.hom →
    ∀ (hs : IsGenSmooth (A.hom ≫ p) A.hom) (Ω₀ : h'.Fld) (κ : h.Fld),
      (∀ σ, IsFlatFibration g h h' (Ω₀ σ) (κ σ)) → h'.IsArForm 1 (fun σ => fibForm h h' (Ω₀ σ) (κ σ)) →
      (∀ σ x, (hermMat (fibForm h h' (Ω₀ σ) (κ σ) x)).PosDef) →
    ∀ (m : VMetric (A.hom ≫ p) (relCot A.hom) g) (H : m.IsCInf) (L : HermLB (A.hom ≫ p)),
      IsRelAcyclic (A.hom ≫ p) A.hom L.B →
    ∀ (r : ℕ) (M : HermVB p r) (ψ : M.E ≅ (Scheme.Modules.pushforward A.hom).obj (toMod L.B)),
      (∀ σ (y : CxPts p σ), ∃ (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ)
        (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ), y ∈ c.e.source ∧ IsUnifChart c τ ex ∧
          IsFlatOn h' (Ω₀ σ) c.e.target τ ex ∧ IsFibreMetric m c.e.target τ ex ∧ IsL2Metric L M ψ c τ ex) →
    ∃ T T' : ℕ → h.Fld, (∀ σ, IsTorsionOn g h h' (Ω₀ σ) (κ σ) L fun i => T i σ) ∧
      (∀ i, h.IsArForm i (T' i) ∧ ∀ σ, (h.atlas σ).IsExact (T i σ - T' i σ)) ∧
      (C.ring h).ch M - (C.ring h).a (∑ i ∈ Finset.range (D + 1), T' i) =
        P.push h h' A.hom rfl hs ((C.ring h').td (HermVB.dual ⟨_, m, H⟩) *
          (1 - (C.ring h').a ((C.ring h').rForm (HermVB.dual ⟨_, m, H⟩))) * (C.ring h').ch (.ofLB L))

def AmpleVanishing : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
    ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → IsRelAcyclic A.hom A.hom L

def ArithRiemannRoch : Prop :=
  BismutKoehlerTorsion ∧ BismutKoehlerTorsionWith ∧ BismutKoehlerGlobal ∧ TorsionAnomaly ∧ GilletRoesslerSoule ∧
    AmpleVanishing

end GlobalTheory.Published
