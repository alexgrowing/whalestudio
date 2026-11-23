import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum

set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.ChernMeas

def measPoly (X σ : Type) [MeasurableSpace X] : Subalgebra ℝ (X → MvPolynomial σ ℂ) where
  carrier := {f | ∀ d, Measurable fun x => coeff d (f x)}
  mul_mem' := by
    classical
    intro f g hf hg d
    simp only [Pi.mul_apply, coeff_mul]
    exact Finset.measurable_sum _ fun p _ => (hf p.1).mul (hg p.2)
  add_mem' := by
    intro f g hf hg d
    simp only [Pi.add_apply, coeff_add]
    exact (hf d).add (hg d)
  algebraMap_mem' := by
    intro c d
    exact measurable_const (a := coeff d (algebraMap ℝ (MvPolynomial σ ℂ) c))

theorem C_mem {X σ : Type} [MeasurableSpace X] {f : X → ℂ} (hf : Measurable f) :
    (fun x => (C (f x) : MvPolynomial σ ℂ)) ∈ measPoly X σ := by
  classical
  intro d
  simp only [coeff_C]
  split_ifs
  · exact hf
  · exact measurable_const

theorem const_mem {X σ : Type} [MeasurableSpace X] (p : MvPolynomial σ ℂ) :
    (fun _ : X => p) ∈ measPoly X σ := fun _ => measurable_const

def evalAt {X σ : Type} [MeasurableSpace X] (x : X) : measPoly X σ →ₐ[ℝ] MvPolynomial σ ℂ :=
  (Pi.evalAlgHom ℝ (fun _ : X => MvPolynomial σ ℂ) x).comp (measPoly X σ).val

theorem charpolyRev_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {r : Type} [Fintype r] [DecidableEq r]
    (M : Matrix r r A) : (M.map f).charpolyRev = M.charpolyRev.map f := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem measurable_curv {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (ξ η : V n) (i j : r) :
    Measurable fun v => curv G v ξ η i j := by
  let f : V n → ℂ := fun x => conn G x ξ i j
  change Measurable fun v => -((1 / 2 : ℂ) * (fderiv ℝ f v η + Complex.I * fderiv ℝ f v (Complex.I • η)))
  exact (((measurable_fderiv_apply_const ℝ f η).add
    ((measurable_fderiv_apply_const ℝ f (Complex.I • η)).const_mul _)).const_mul _).neg

theorem curvPoly_mem {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (i j : r) :
    (fun v => curvPoly G v i j) ∈ measPoly (V n) (Fin n × Fin n) := by
  have e : (fun v => curvPoly G v i j) = ∑ a, ∑ b, (fun v => (C (curv G v (coordVec a) (coordVec b) i j) :
      MvPolynomial (Fin n × Fin n) ℂ)) * fun _ => X (a, b) := by
    funext v
    simp [curvPoly, Finset.sum_apply]
  rw [e]
  exact Subalgebra.sum_mem _ fun a _ => Subalgebra.sum_mem _ fun b _ =>
    Subalgebra.mul_mem _ (C_mem (measurable_curv G _ _ i j)) (const_mem _)

theorem chernPoly_mem {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (k : ℕ) :
    (fun v => chernPoly G v k) ∈ measPoly (V n) (Fin n × Fin n) := by
  let M : Matrix r r (measPoly (V n) (Fin n × Fin n)) := Matrix.of fun i j => ⟨_, curvPoly_mem G i j⟩
  have e : (fun v => chernPoly G v k) = ((Matrix.charpolyRev (-M)).coeff k).1 := by
    funext v
    have h : -curvPoly G v = (-M).map (evalAt v).toRingHom := by
      ext i j : 2
      rfl
    rw [chernPoly, h, charpolyRev_map, Polynomial.coeff_map]
    rfl
  rw [e]
  exact Subtype.property _

theorem measurable_chernTop {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ) (G : V n → Mat m ℂ) :
    Measurable (fun v => chernTop R G v) := by
  let P : measPoly (V n) (Fin n × Fin n) :=
    aeval (fun x : ι × ℕ => (⟨_, chernPoly_mem (fun u => G u x.1) x.2⟩ : measPoly (V n) (Fin n × Fin n))) R
  have e (v : V n) : aeval (fun x : ι × ℕ => chernPoly (fun u => G u x.1) v x.2) R = P.1 v := by
    change _ = evalAt v P
    rw [← AlgHom.comp_apply, comp_aeval]
    rfl
  simp only [chernTop, e, topCoeff]
  refine Measurable.const_mul (Complex.measurable_re.comp ?_) _
  exact Finset.measurable_sum _ fun w _ => (P.2 _).const_mul _

end GlobalTheory.ChernMeas
