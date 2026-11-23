import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt
open GlobalTheory.VBExt (AdaptedChart)
open GlobalTheory.FlagFibre (Low uni)
open GlobalTheory.MixDens (emb)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

namespace GlobalTheory.BigCell

variable {ι : Type} {r : ι → ℕ} {n D : ℕ} (ε : Fin D ≃ Fin n ⊕ (Σ a, Low (r a)))

def base (v : V D) : V n := WithLp.toLp 2 fun b => v (ε.symm (.inl b))

def fib (v : V D) (a : ι) : Low (r a) → ℂ := fun s => v (ε.symm (.inr ⟨a, s⟩))

def pt (z : V n) (u : ∀ a, Low (r a) → ℂ) : V D :=
  WithLp.toLp 2 fun j => Sum.elim (fun b => z b) (fun s => u s.1 s.2) (ε j)

theorem base_pt (z : V n) (u : ∀ a, Low (r a) → ℂ) : base ε (pt ε z u) = z := by
  ext j
  simp [base, pt]

theorem fib_pt (z : V n) (u : ∀ a, Low (r a) → ℂ) : fib ε (pt ε z u) = u := by
  ext a s
  simp [fib, pt]

def baseL : V D →L[ℂ] V n :=
  LinearMap.toContinuousLinearMap
    { toFun := base ε
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem baseL_apply (v : V D) : baseL ε v = base ε v := rfl

def stepGram (G : ∀ a, V n → Matrix (Fin (r a)) (Fin (r a)) ℂ) (a : ι) (i : Fin (r a)) (v : V D) :
    Matrix (Fin i ⊕ Fin 1) (Fin i ⊕ Fin 1) ℂ :=
  (chg (uni (fib ε v a)) (G a (base ε v))).submatrix (emb i) (emb i)

def rootWt (G : ∀ a, V n → Matrix (Fin (r a)) (Fin (r a)) ℂ) (z : Σ a, Fin (r a)) (v : V D) : ℝ :=
  -Real.log (quotGram (stepGram ε G z.1 z.2 v)).det.re

def blk (N : Matrix (Fin n) (Fin n) ℂ) (δ : (Σ a, Low (r a)) → ℝ) : Matrix (Fin D) (Fin D) ℂ :=
  (fromBlocks N 0 0 (diagonal fun s => (δ s : ℂ))).submatrix ε ε

variable {k : Type} [CommRing k] {σ : k →+* ℂ} {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B)
  (w : π ≫ q = p)

def IsCell (c : AlgChart q σ n) (c' : AlgChart p σ D) : Prop :=
  c'.e.source = PtsOver.map π w (spMap σ) ⁻¹' c.e.source ∩ ptsIn p σ c'.U ∧
    c'.e.target = {v | base ε v ∈ c.e.target} ∧
    ∀ y ∈ c'.e.source, base ε (c'.e y) = c.e (PtsOver.map π w (spMap σ) y)

def IsCellFrame (c' : AlgChart p σ D) (a : ι) {E : B.Modules} (h : VMetric q E (r a))
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) (r a)) (cE : Chart E (r a)) : Prop :=
  ∀ i, ∃ ac : AdaptedChart (VMetric.stepSeq fl i) i 1, ∀ y ∈ c'.e.source, y ∈ ptsIn p σ ac.U ∧
    (((h.pull π w).stepMet fl i).met σ).gram ac.frame y =
      (chg (uni (fib ε (c'.e y) a)) ((h.met σ).G cE (PtsOver.map π w (spMap σ) y))).submatrix (emb i) (emb i)

end GlobalTheory.BigCell
