import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

set_option autoImplicit false

noncomputable section

open MvPowerSeries NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.IndefiniteRowSideFullHecke.BalancedFrameGauge

section Frames

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

structure IsBalancedGauge (B : FB R d O) (h : PS k 2 d) : Prop where
  ax0 : ev (n := 1) ![0, pt k d 0] h = 0
  ax1 : ev (n := 1) ![pt k d 0, 0] h = 0
  ph1 : FB.toK k B.ph1 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h -
    ev (n := 3) ![addOf (B.FK k) (pt k d 0) (pt k d 1), pt k d 2] h)
  ph2 : FB.toK k B.ph2 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h -
    ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] h)
  ad : ∀ a : O, FB.toK k (B.ad a) = FB.expS k (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
    ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h)

theorem isBalancedGauge_of_canon (B : FB R d O) (h : PS k 2 d) (hh : B.IsCanonGauge k h) :
    IsBalancedGauge k B h :=
  ⟨hh.ax0, hh.ax1, hh.ph1, hh.ph2, hh.ad⟩

end Frames

section Columns

variable {k : Type} [CommRing k] {d n : ℕ}

def DCol (F : Fin d → PS k 2 d) (u : Fin d → k) (b : Fin n) (f : PS k n d) : PS k n d :=
  ∑ j : Fin d, (∑ i : Fin d, C (u i) * ev (n := n) ![pt k d b, 0] (pderiv k ((1 : Fin 2), i) (F j))) *
    pderiv k (b, j) f

def DPolyCols (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (P : MvPolynomial (ι × Fin n) k) (f : PS k n d) : PS k n d :=
  ∑ m ∈ P.support, C (P.coeff m) *
    (Finset.univ : Finset (ι × Fin n)).toList.foldr (fun p g => (DCol F (u p.1) p.2)^[m p] g) f

example (F : Fin d → PS k 2 d) (u : Fin d → k) (f : PS k 1 d) : DCol F u 0 f = Dof F u f := rfl

end Columns

section Value

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

def quotCols (B : FB R d O) (h : PS k 2 d) (w0 : O) (N : ℕ) {n : ℕ} (f : PS k n d) : PS k n d :=
  f * ∏ b : Fin n, FB.expS k (ev (n := n) ![pt k d b, comp1 (B.actK k w0) (pt k d b)] h) ^ N

def valCols (B : FB R d O) (h : PS k 2 d) (w0 : O) (N : ℕ) {n : ℕ} (f : PS k n d) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) (P : MvPolynomial (ι × Fin n) k) : k :=
  constantCoeff (DPolyCols (B.FK k) u P (quotCols k B h w0 N f))

end Value

section Letters

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

def conjType {k : Type} [Field k] (τ : E →+* k) : E →+* k :=
  τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom

variable {E}

def lieEigen {R : Type} [CommRing R] {d : ℕ} [StarRing (𝓞 E)] (k : Type) [Field k] [Algebra R k]
    (B : FB R d (𝓞 E)) (τ : E →+* k) : Submodule k (Fin d → k) where
  carrier := {v | ∀ a : 𝓞 E, (dAct k B a).mulVec v = τ (a : E) • v}
  add_mem' := fun {v w} hv hw a => by
    rw [Matrix.mulVec_add, hv a, hw a, smul_add]
  zero_mem' := fun a => by simp
  smul_mem' := fun c v hv a => by
    rw [Matrix.mulVec_smul, hv a, smul_comm]

def IsHarmonic {k : Type} [Field k] (r : (E →+* k) → ℕ) {n : ℕ}
    (P : MvPolynomial ((Σ τ : E →+* k, Fin (r τ)) × Fin n) k) : Prop :=
  ∀ (τ : E →+* k) (i : Fin (r τ)) (i' : Fin (r (conjType E τ))),
    ∑ b : Fin n, MvPolynomial.pderiv ((⟨τ, i⟩ : Σ τ : E →+* k, Fin (r τ)), b)
      (MvPolynomial.pderiv ((⟨conjType E τ, i'⟩ : Σ τ : E →+* k, Fin (r τ)), b) P) = 0

example {k : Type} [Field k] (r : (E →+* k) → ℕ) {n : ℕ} (c : k) :
    IsHarmonic r (n := n) (MvPolynomial.C c) := by
  intro τ i i'
  simp

example {k : Type} [Field k] (r : (E →+* k) → ℕ) {n : ℕ} (p : (Σ τ : E →+* k, Fin (r τ)) × Fin n) :
    IsHarmonic r (n := n) (MvPolynomial.X p) := by
  classical
  intro τ i i'
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [MvPolynomial.pderiv_X, Pi.single_apply]
  split_ifs <;> simp

end Letters

def BalancedFrameValue : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)],
    (∀ a : 𝓞 E, ((star a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) →
  ∀ (k : Type) [Field k] [CharZero k], Fintype.card (E →+* k) = Module.finrank ℚ E →
  ∀ (R : Type) [CommRing R] [Algebra R k] (d : ℕ) (B : FB R d (𝓞 E)) (w0 : 𝓞 E), w0 + star w0 = 1 →
  ∀ (r : (E →+* k) → ℕ) (u : (Σ τ : E →+* k, Fin (r τ)) → Fin d → k),
    (∀ τ : E →+* k, LinearIndependent k (fun i : Fin (r τ) => u ⟨τ, i⟩) ∧
      Submodule.span k (Set.range fun i : Fin (r τ) => u ⟨τ, i⟩) = lieEigen k B τ) →
  ∀ (n N : ℕ) (P : MvPolynomial ((Σ τ : E →+* k, Fin (r τ)) × Fin n) k), IsHarmonic r P →
  ∀ (h h' : PS k 2 d), B.IsCanonGauge k h → IsBalancedGauge k B h' →
  ∀ f : PS k n d, valCols k B h w0 N f u P = valCols k B h' w0 N f u P

section Inhabitant

variable {k : Type} [CommRing k] {g m n : ℕ} {O : Type} [CommRing O]

def addSeries (k : Type) [CommRing k] (g : ℕ) : Fin g → PS k 2 g :=
  fun i => X ((0 : Fin 2), i) + X ((1 : Fin 2), i)

theorem eval_addSeries_two (a : Fin 2 → Pt k n g) (ha : ∀ p : Fin 2 × Fin g, constantCoeff (a p.1 p.2) = 0) (i : Fin g) :
    ev a (addSeries k g i) = a 0 i + a 1 i := by
  unfold addSeries ev
  rw [subst_add (hasSubst_of_constantCoeff_zero ha), subst_X (hasSubst_of_constantCoeff_zero ha),
    subst_X (hasSubst_of_constantCoeff_zero ha)]

theorem eval_const_mul_X (a : Fin 1 → Pt k n g) (ha : ∀ p : Fin 1 × Fin g, constantCoeff (a p.1 p.2) = 0) (c : k)
    (i : Fin g) : ev a (C c * X ((0 : Fin 1), i) : PS k 1 g) = C c * a 0 i := by
  unfold ev
  rw [subst_mul (hasSubst_of_constantCoeff_zero ha), subst_X (hasSubst_of_constantCoeff_zero ha)]
  congr 1
  rw [subst_C]

theorem addOf_addSeries (a b : Pt k n g) (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) : addOf (addSeries k g) a b = a + b := by
  funext i
  exact eval_addSeries_two ![a, b] (fun ⟨j, l⟩ => by fin_cases j; exacts [ha l, hb l]) i

theorem expS_zero [Algebra ℚ k] : FB.expS k (0 : PS k n g) = 1 := by
  ext e
  rw [FB.expS, PowerSeries.coeff_subst PowerSeries.HasSubst.zero, finsum_eq_single _ 0]
  · simp [PowerSeries.coeff_exp]
  · intro j hj
    simp [zero_pow hj]

theorem cc_pt (j : Fin n) (i : Fin g) : constantCoeff (pt k g j i) = 0 := by simp [pt]

def addLaw (k : Type) [CommRing k] (g : ℕ) : FGLaw k g where
  F := addSeries k g
  const i := by simp [addSeries]
  unit i := by
    rw [eval_addSeries_two _ (fun ⟨j, l⟩ => by fin_cases j <;> simp [pt])]
    simp [pt]
  comm i := by
    rw [eval_addSeries_two _ (fun ⟨j, l⟩ => by fin_cases j <;> simp [pt])]
    simp [pt, addSeries, add_comm]
  assoc i := by
    have h01 : (fun l => ev (n := 3) ![pt k g 0, pt k g 1] (addSeries k g l)) =
        fun l => (X ((0 : Fin 3), l) + X ((1 : Fin 3), l) : PS k 3 g) :=
      funext fun l => by rw [eval_addSeries_two _ (fun ⟨j, l⟩ => by fin_cases j <;> simp [pt])]; simp [pt]
    have h12 : (fun l => ev (n := 3) ![pt k g 1, pt k g 2] (addSeries k g l)) =
        fun l => (X ((1 : Fin 3), l) + X ((2 : Fin 3), l) : PS k 3 g) :=
      funext fun l => by rw [eval_addSeries_two _ (fun ⟨j, l⟩ => by fin_cases j <;> simp [pt])]; simp [pt]
    rw [h01, h12, eval_addSeries_two _ (fun ⟨j, l⟩ => by fin_cases j <;> simp [pt]),
      eval_addSeries_two _ (fun ⟨j, l⟩ => by fin_cases j <;> simp [pt])]
    simp [pt, add_assoc]

def diagSeries (χ : Fin g → (O →+* k)) (a : O) : Pt k 1 g := fun l => C (χ l a) * X ((0 : Fin 1), l)

theorem cc_diag (χ : Fin g → (O →+* k)) (a : O) (i : Fin g) : constantCoeff (diagSeries χ a i) = 0 := by
  simp [diagSeries]

theorem comp_diagonalSeries (χ : Fin g → (O →+* k)) (a : O) (b : Pt k n g) (hb : ∀ i, constantCoeff (b i) = 0) :
    comp1 (diagSeries χ a) b = fun i => C (χ i a) * b i := by
  funext i
  exact eval_const_mul_X ![b] (fun ⟨j, l⟩ => by fin_cases j; exact hb l) _ i

def diagAct (χ : Fin g → (O →+* k)) : OAct O (addLaw k g) where
  act := diagSeries χ
  const := cc_diag χ
  hom a := by
    show comp1 (diagSeries χ a) (addOf (addSeries k g) (pt k g 0) (pt k g 1)) =
      addOf (addSeries k g) (comp1 (diagSeries χ a) (pt k g 0)) (comp1 (diagSeries χ a) (pt k g 1))
    rw [addOf_addSeries _ _ (cc_pt 0) (cc_pt 1), comp_diagonalSeries _ _ _ (fun i => by simp [pt]),
      comp_diagonalSeries _ _ _ (cc_pt 0), comp_diagonalSeries _ _ _ (cc_pt 1), addOf_addSeries _ _ (fun i => by simp [pt])
        (fun i => by simp [pt])]
    funext i
    simp [mul_add]
  add_act a b := by
    show diagSeries χ (a + b) = addOf (addSeries k g) (diagSeries χ a) (diagSeries χ b)
    rw [addOf_addSeries _ _ (cc_diag χ a) (cc_diag χ b)]
    funext i
    simp [diagSeries, add_mul]
  mul_act a b := by
    show diagSeries χ (a * b) = comp1 (diagSeries χ a) (diagSeries χ b)
    rw [comp_diagonalSeries _ _ _ (cc_diag χ b)]
    funext i
    simp [diagSeries, mul_assoc]
  one_act := by
    funext i
    simp [diagSeries, pt]

end Inhabitant

end GlobalTheory.IndefiniteRowSideFullHecke.BalancedFrameGauge
