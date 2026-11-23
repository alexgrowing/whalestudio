import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.LineForm
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.FibTriv

def prodPt {d : ℕ} (z : V d) (x : ℂ) : V (d + 1) := WithLp.toLp 2 (Fin.snoc (α := fun _ => ℂ) z.ofLp x)

def basePt {d : ℕ} (v : V (d + 1)) : V d := WithLp.toLp 2 fun a => v a.castSucc

@[simp] theorem prodPt_castSucc {d : ℕ} (z : V d) (x : ℂ) (a : Fin d) : prodPt z x a.castSucc = z a := by
  simp [prodPt]

@[simp] theorem prodPt_last {d : ℕ} (z : V d) (x : ℂ) : prodPt z x (Fin.last d) = x := by simp [prodPt]

@[simp] theorem basePt_apply {d : ℕ} (v : V (d + 1)) (a : Fin d) : basePt v a = v a.castSucc := rfl

@[simp] theorem basePt_prodPt {d : ℕ} (z : V d) (x : ℂ) : basePt (prodPt z x) = z := by
  ext a; simp

@[simp] theorem prodPt_basePt {d : ℕ} (v : V (d + 1)) : prodPt (basePt v) (v (Fin.last d)) = v := by
  ext a
  induction a using Fin.lastCases <;> simp

theorem differentiable_basePt {d : ℕ} : Differentiable ℂ (basePt (d := d)) :=
  differentiable_euclidean.2 fun a => by simp only [basePt_apply]; fun_prop

theorem differentiable_prodPt {d : ℕ} : Differentiable ℂ fun z : V d × ℂ => prodPt z.1 z.2 :=
  differentiable_euclidean.2 fun a => by
    induction a using Fin.lastCases
    · simp only [prodPt_last]; fun_prop
    · simp only [prodPt_castSucc]; fun_prop

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {σ : k →+* ℂ}
  (π : Y ⟶ B) (w : π ≫ q = p) {E : B.Modules} (hE : IsVB E 2) (cE : Chart E 2)
  (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2)

def lineVec (y : CxPts p σ) : Fin 2 → ℂ := (cE.pull hE π).crd p σ ((frameAt fl y).frame (.inl 0)) y

def slope (y : CxPts p σ) : ℂ := lineVec π hE cE fl y 1 / lineVec π hE cE fl y 0

def finPart (σ : k →+* ℂ) : Set (CxPts p σ) :=
  {y | PtsOver.map π w (spMap σ) y ∈ ptsIn q σ cE.U ∧ lineVec π hE cE fl y 0 ≠ 0}

def infPart (σ : k →+* ℂ) : Set (CxPts p σ) :=
  {y | PtsOver.map π w (spMap σ) y ∈ ptsIn q σ cE.U ∧ lineVec π hE cE fl y 0 = 0}

include w in

theorem lineVec_ne_zero {y : CxPts p σ} (hy : PtsOver.map π w (spMap σ) y ∈ ptsIn q σ cE.U) :
    lineVec π hE cE fl y ≠ 0 := fun h => by
  have hu := (cE.pull hE π).isUnit_tr ((frameAt fl y).mid (lineSC_shortExact fl)) (y := y) hy (mem_frameAt fl y)
  refine ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero (Matrix.det_eq_zero_of_column_eq_zero 0 fun i => ?_)
  exact congrFun h i

theorem infPart_eq : infPart π w hE cE fl σ =
    PtsOver.map π w (spMap σ) ⁻¹' ptsIn q σ cE.U \ finPart π w hE cE fl σ := by
  ext y
  simp only [infPart, finPart, Set.mem_diff, Set.mem_preimage, Set.mem_setOf_eq]
  tauto

end GlobalTheory.FibTriv
