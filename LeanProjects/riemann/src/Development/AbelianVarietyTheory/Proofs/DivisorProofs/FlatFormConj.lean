import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAndExistsConjChart
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0 dflat herm)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas IsType IsReal Alt delAt dbarAt)
open GlobalTheory.ConjChart (conjCoord conjPts conjChart)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

noncomputable section

namespace GlobalTheory.FlatFormConj

open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (riem flat flatOf symp)

def conjPtL (D g : ℕ) : Pt (V D) g →ₗ[ℝ] Pt (V D) g where
  toFun P := (conjCoord D P.1, star P.2)
  map_add' P Q := by
    ext <;> simp [conjCoord]
  map_smul' c P := by
    ext <;> simp [conjCoord]

theorem conjPtL_invol (D g : ℕ) (P : Pt (V D) g) : conjPtL D g (conjPtL D g P) = P := by
  ext <;> simp [conjPtL, conjCoord]

def conjPt (D g : ℕ) : Pt (V D) g ≃L[ℝ] Pt (V D) g :=
  (LinearEquiv.ofInvolutive (conjPtL D g) (conjPtL_invol D g)).toContinuousLinearEquiv

theorem conjPt_apply (D g : ℕ) (P : Pt (V D) g) : conjPt D g P = (conjCoord D P.1, star P.2) := rfl

theorem conjPt_invol (D g : ℕ) (P : Pt (V D) g) : conjPt D g (conjPt D g P) = P :=
  conjPtL_invol D g P

def reflL (g : ℕ) : Fl g →ₗ[ℝ] Fl g where
  toFun x := Sum.elim (fun i => -x (Sum.inl i)) (fun i => x (Sum.inr i))
  map_add' x y := by
    funext i; cases i <;> simp; ring
  map_smul' c x := by
    funext i; cases i <;> simp

theorem reflL_invol (g : ℕ) (x : Fl g) : reflL g (reflL g x) = x := by
  funext i; cases i <;> simp [reflL]

def refl (g : ℕ) : Fl g ≃L[ℝ] Fl g :=
  (LinearEquiv.ofInvolutive (reflL g) (reflL_invol g)).toContinuousLinearEquiv

theorem refl_inl (g : ℕ) (x : Fl g) (i : Fin g) : refl g x (Sum.inl i) = -x (Sum.inl i) := rfl
theorem refl_inr (g : ℕ) (x : Fl g) (i : Fin g) : refl g x (Sum.inr i) = x (Sum.inr i) := rfl

theorem riem_refl (g : ℕ) (x y : Fl g) : riem (refl g x) (refl g y) = -riem x y := by
  simp only [riem, refl_inl, refl_inr, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem flatOf_conj (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    flatOf (-τ.map (starRingEnd ℂ)) (star z) = refl g (flatOf τ z) := by
  have him : (-τ.map (starRingEnd ℂ)).map Complex.im = τ.map Complex.im := by
    ext i j; simp
  have hre : (-τ.map (starRingEnd ℂ)).map Complex.re = -τ.map Complex.re := by
    ext i j; simp
  have hz : (fun i => (star z i).im) = -(fun i => (z i).im) := by
    funext i; simp
  have hz' : (fun i => (star z i).re) = (fun i => (z i).re) := by
    funext i; simp
  funext i
  cases i with
  | inl i => simp only [flatOf, him, hz, Sum.elim_inl, refl_inl, Matrix.neg_vecMul, Pi.neg_apply]
  | inr i => simp only [flatOf, him, hre, hz, hz', Sum.elim_inr, refl_inr, Matrix.neg_vecMul, Matrix.vecMul_neg, neg_neg]

theorem flat_conj (D g : ℕ) (τ : V D → Matrix (Fin g) (Fin g) ℂ) :
    flat (fun v => -(τ (conjCoord D v)).map (starRingEnd ℂ)) = refl g ∘ flat τ ∘ conjPt D g := by
  funext Q
  simp only [Function.comp_apply, flat, conjPt_apply]
  rw [← flatOf_conj, star_star]

open ContinuousLinearMap in

theorem om0_conj : ∀ (D g : ℕ) (τ : V D → Matrix (Fin g) (Fin g) ℂ) (P u u' : Pt (V D) g), om0 (fun v => -(τ (conjCoord D v)).map (starRingEnd ℂ)) (conjCoord D P.1, star P.2) ![(conjCoord D u.1, star u.2), (conjCoord D u'.1, star u'.2)] = -om0 τ P ![u, u'] := by
  intro D g τ P u u'
  have hd : ∀ w : Pt (V D) g, dflat (fun v => -(τ (conjCoord D v)).map (starRingEnd ℂ)) (conjPt D g P) (conjPt D g w) =
      refl g (dflat τ P w) := by
    intro w
    unfold dflat
    rw [flat_conj, ← Function.comp_assoc, (conjPt D g).comp_right_fderiv, conjPt_invol,
      (refl g).comp_fderiv]
    simp [conjPt_invol]
  have h1 := hd u
  have h2 := hd u'
  simp only [conjPt_apply] at h1 h2
  show riem _ _ = -riem _ _
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  exact (congrArg₂ riem h1 h2).trans (riem_refl _ _ _)

end GlobalTheory.FlatFormConj
