import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankRiemannRochNsmulHyperplane
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped Matrix ComplexOrder

namespace GlobalTheory.ProjVar.Var

variable {F : Type} [Field F] (Y : Var F) {κ : Type} (Δ : κ → Y.Dv)

open Classical in

def interPoly : MvPolynomial κ ℝ →ₗ[ℝ] ℝ :=
  (basisMonomials κ ℝ).constr ℝ fun d =>
    if h : ∃ s : Fin Y.dim → κ, ∑ i, Finsupp.single (s i) 1 = d then (Y.inter (Δ ∘ h.choose) : ℝ) else 0

private theorem inter_comp_eq_of_sum_single_eq (s t : Fin Y.dim → κ)
    (h : ∑ i, Finsupp.single (t i) 1 = ∑ i, Finsupp.single (s i) (1 : ℕ)) :
    Y.inter (Δ ∘ t) = Y.inter (Δ ∘ s) := by
  classical
  have hc : ∀ k, Fintype.card {i // t i = k} = Fintype.card {i // s i = k} := by
    intro k
    have hk := congrArg (fun f : κ →₀ ℕ => f k) h
    simp only [Finsupp.finsetSum_apply, Finsupp.single_apply] at hk
    simpa [Fintype.card_subtype, Finset.sum_boole] using hk
  let σ : Fin Y.dim ≃ Fin Y.dim := (Equiv.sigmaFiberEquiv t).symm.trans
    ((Equiv.sigmaCongrRight fun k => Fintype.equivOfCardEq (hc k)).trans (Equiv.sigmaFiberEquiv s))
  have hσ : ∀ i, s (σ i) = t i := fun i => ((Fintype.equivOfCardEq (hc (t i))) ⟨i, rfl⟩).2
  have hcomp : Δ ∘ t = (Δ ∘ s) ∘ σ := funext fun i => by simp only [Function.comp_apply, hσ]
  rw [hcomp, inter_comp_perm]

theorem interPoly_prod (s : Fin Y.dim → κ) : Y.interPoly Δ (∏ i, MvPolynomial.X (s i)) = Y.inter (Δ ∘ s) := by
  classical
  have hprod : (∏ i, MvPolynomial.X (s i) : MvPolynomial κ ℝ) =
      (basisMonomials κ ℝ) (∑ i, Finsupp.single (s i) 1) := by
    simp only [coe_basisMonomials]
    rw [monomial_sum_one]
    rfl
  have h : ∃ t : Fin Y.dim → κ, ∑ i, Finsupp.single (t i) 1 = ∑ i, Finsupp.single (s i) 1 := ⟨s, rfl⟩
  rw [hprod]
  unfold interPoly
  rw [Module.Basis.constr_basis, dif_pos h]
  exact_mod_cast inter_comp_eq_of_sum_single_eq Y Δ s h.choose h.choose_spec

theorem interPoly_prod_sum [Fintype κ] (a : Fin Y.dim → κ → ℤ) :
    Y.interPoly Δ (∏ i, ∑ x, C (a i x : ℝ) * MvPolynomial.X x) = Y.inter fun i => ∑ x, a i x • Δ x := by
  classical
  rw [Fintype.prod_sum, map_sum, ← interForm_apply, MultilinearMap.map_sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [interForm_apply]
  have e1 : (∏ i, C (a i (p i) : ℝ) * MvPolynomial.X (p i) : MvPolynomial κ ℝ) =
      ((∏ i, a i (p i) : ℤ) : ℝ) • ∏ i, MvPolynomial.X (p i) := by
    rw [Finset.prod_mul_distrib, ← map_prod, C_mul']
    push_cast
    rfl
  rw [e1, map_smul, interPoly_prod, smul_eq_mul]
  rw [show (fun i => a i (p i) • Δ (p i)) = fun i => a i (p i) • (Δ ∘ p) i from rfl, inter_zsmul]
  push_cast
  rfl

end GlobalTheory.ProjVar.Var

namespace GlobalTheory.GoodMetric

section Forms

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

def topCoeff (P : MvPolynomial (Fin n × Fin n) ℂ) : ℂ :=
  ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) * coeff (∑ a, Finsupp.single (a, w a) 1) P

abbrev coordVec (a : Fin n) : V n := EuclideanSpace.single a 1

def curvPoly (G : V n → Matrix r r ℂ) (v : V n) : Matrix r r (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => ∑ a, ∑ b, C (curv G v (coordVec a) (coordVec b) i j) * X (a, b)

def chernPoly (G : V n → Matrix r r ℂ) (v : V n) (k : ℕ) : MvPolynomial (Fin n × Fin n) ℂ :=
  (Matrix.charpolyRev (-curvPoly G v)).coeff k

def chernTop {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ) (G : V n → Mat m ℂ) (v : V n) : ℝ :=
  (Real.pi ^ n)⁻¹ * (topCoeff (aeval (fun x : ι × ℕ => chernPoly (fun u => G u x.1) v x.2) R)).re

def poinWt (S : Finset (Fin n)) (v : V n) (a : Fin n) : ℝ := if a ∈ S then ‖v a‖ * |Real.log ‖v a‖| else 1

structure GoodBound (S : Finset (Fin n)) (c : ℝ) (N : ℕ) (G : V n → Matrix r r ℂ) (v : V n) : Prop where
  entry : ∀ i j, ‖G v i j‖ ≤ c * (∑ a ∈ S, |Real.log ‖v a‖|) ^ N
  det : ‖(G v).det‖⁻¹ ≤ c * (∑ a ∈ S, |Real.log ‖v a‖|) ^ N
  form : ∀ a i j, ‖conn G v (coordVec a) i j‖ * poinWt S v a ≤ c
  dbar : ∀ a b i j, ‖curv G v (coordVec a) (coordVec b) i j‖ * (poinWt S v a * poinWt S v b) ≤ c
  del : ∀ a b i j, ‖(mdel (fun u => conn G u (coordVec b)) v (coordVec a) -
    mdel (fun u => conn G u (coordVec a)) v (coordVec b)) i j‖ * (poinWt S v a * poinWt S v b) ≤ c

end Forms

variable {F : Type} [Field F] {ι : Type} {m : ι → ℕ}

section Metric

variable {X : Var F} {σ : F →+* ℂ}

def IsHoloChart (e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)) : Prop :=
  ∀ (W : X.X.Opens) (f : Γ(X.X, W)),
    DifferentiableOn ℂ (ev X.str σ W f ∘ e.symm) (e.target ∩ e.symm ⁻¹' ptsIn X.str σ W)

variable (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)

structure IsMetricOn : Prop where
  posDef : ∀ y ∈ ptsIn X.str σ O, ∀ A ∈ E.S (under y), ∀ τ, (H A y τ).PosDef
  smooth : ∀ y ∈ ptsIn X.str σ O, ∀ A ∈ E.S (under y), ∀ τ i j,
    CInfAt (fun z => (H A z τ i j).re) y ∧ CInfAt (fun z => (H A z τ i j).im) y
  trans : ∀ y ∈ ptsIn X.str σ O, ∀ A ∈ E.S (under y), ∀ A' ∈ E.S (under y), ∀ τ,
    H A' y τ = (A' * A⁻¹).map (ratVal · y) τ * H A y τ * ((A' * A⁻¹).map (ratVal · y) τ)ᴴ

def IsGood : Prop :=
  ∀ y ∉ ptsIn X.str σ O, ∃ (e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)) (S : Finset (Fin X.dim)),
    IsHoloChart e ∧ y ∈ e.source ∧ (∀ a ∈ S, e y a = 0) ∧ (∀ z ∈ e.source, z ∉ ptsIn X.str σ O ↔ ∃ a ∈ S, e z a = 0) ∧
      ∃ A ∈ E.S (under y), ∃ (c : ℝ) (N : ℕ), ∀ᶠ z in 𝓝[ptsIn X.str σ O] y, ∀ τ,
        GoodBound S c N (fun v => H A (e.symm v) τ) (e z)

def chernTopPart (R : MvPolynomial (ι × ℕ) ℝ) (ε : ℤˣ) : Measure (CxPts X.str σ) :=
  glueMeas (fun c : AlgChart X.str σ X.dim => c.e) fun c y =>
    ENNReal.ofReal ((ε : ℤ) * chernTop R (fun v => H (E.nonempty (under y)).choose (c.e.symm v)) (c.e y))

def HasChernIntegral (R : MvPolynomial (ι × ℕ) ℝ) (t : ℝ) : Prop :=
  (∀ ε, chernTopPart E H R ε (ptsIn X.str σ O) ≠ ⊤) ∧
    (chernTopPart E H R 1).real (ptsIn X.str σ O) - (chernTopPart E H R (-1)).real (ptsIn X.str σ O) = t

end Metric

abbrev Root (m : ι → ℕ) : Type := Σ τ, Fin (m τ)

def IsGraded {Y : Var F} (E' : Fr (ratOf Y) m m) (gr : Root m → Y.Dv) : Prop :=
  ∃ B ∈ E'.S (genericPoint Y.X), ∀ (y : Y.X) (x : Root m), ∃ A ∈ E'.S y, ∃ t : Y.Fnˣ,
    (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t

variable (m)

def chernRoots : MvPolynomial (ι × ℕ) ℝ →ₐ[ℝ] MvPolynomial (Root m) ℝ :=
  aeval fun x => rename (Sigma.mk x.1) (esymm (Fin (m x.1)) ℝ x.2)

variable [Fintype ι]

def fibrePoint : MvPolynomial (Root m) ℝ := ∏ x : Root m, (-X x) ^ (m x.1 - 1 - x.2)

def rootDiscr : MvPolynomial (Root m) ℝ :=
  ∏ τ, ∏ j : Fin (m τ), ∏ i ∈ Finset.Iio j, (X ⟨τ, j⟩ - X ⟨τ, i⟩)

variable {m} in
open Classical in

def antisymm (Q : MvPolynomial (Root m) ℝ) : MvPolynomial (Root m) ℝ :=
  ∑ w : ∀ τ, Equiv.Perm (Fin (m τ)),
    ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) Q

end GlobalTheory.GoodMetric
