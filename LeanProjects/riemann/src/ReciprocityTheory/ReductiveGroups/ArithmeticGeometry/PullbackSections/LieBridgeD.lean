import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeC

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S] {x : Sp S ⟶ Xo.X}

theorem tv_sum {κ : Type} (s : Finset κ) (f : κ → TanM x Xo.univ.t.G) : tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => first | rfl | simp [tv]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, tv_add, ih]

variable {c}

def tvOf {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) : TanM x Xo.univ.t.G :=
  mkT (ovT (t := Xo.univ.t) hv) (smT_zero_ovT hv)

theorem tv_tvOf {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) : tv (tvOf hv) = ovT (t := Xo.univ.t) hv := rfl

variable (c) in
theorem eigAt_iff {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) (τ : E →+* ℂ) :
    IsEigAt c τ v ↔ IsEigV (actR (x0 := x) (S := S) Xo.univ.t.act) (embK c τ) (tvOf hv) := by
  refine (isEigAt_iff (c := c) τ (ovT (t := Xo.univ.t) hv)).trans ?_
  constructor
  · intro h a
    apply tanM_ext
    show tv (tvOf hv) ≫ Xo.univ.t.act.act a = _
    rw [tv_smul, tv_tvOf]
    exact h a
  · intro h a
    have h2 := congrArg tv (h a)
    change tv (tvOf hv) ≫ Xo.univ.t.act.act a = _ at h2
    rw [tv_smul, tv_tvOf] at h2
    exact h2

theorem combAt_iff {m : ℕ} (u : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (hu : ∀ i, IsTanAt x (u i))
    (cf : Fin m → S) {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hw : IsTanAt x w) :
    IsCombAt x u cf w ↔ tvOf hw = ∑ i, cf i • tvOf (hu i) := by
  have e1 : tv (∑ i, cf i • tvOf (hu i)) = combT x (fun j => ovT (t := Xo.univ.t) (hu j)) cf := by
    rw [tv_sum]
    simp only [tv_smul, tv_tvOf]
    rfl
  have key := isCombAtG_iff Xo.univ.t x (fun j => ovT (t := Xo.univ.t) (hu j)) cf w
  constructor
  · intro h
    apply tanM_ext
    rw [e1, tv_tvOf]
    exact Over.OverMorphism.ext (key.1 h).symm
  · intro h
    have h2 := congrArg tv h
    rw [e1, tv_tvOf] at h2
    exact key.2 (by rw [← h2]; rfl)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
