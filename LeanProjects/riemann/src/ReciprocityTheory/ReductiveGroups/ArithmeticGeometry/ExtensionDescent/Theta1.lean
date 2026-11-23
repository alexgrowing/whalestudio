import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.InhVV

open Semi Inh

variable (S : Scheme.{0}) (T : Over S)

def rig1 : LB.Gen ((zeroPolAV S).L.pull (eSec (zeroPolAV S).A)) := ⟨fun _ => 1⟩

def one1 (x : T ⟶ (zeroPolAV S).A) (k : ℤ) :
    LB.Gen (LB.LinComb (zeroPolAV S).L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => k)) :=
  ⟨fun _ => 1⟩

macro "ones" : tactic => `(tactic| (repeat (first | erw [map_one] | erw [one_zpow] | erw [one_pow] | erw [inv_one] | erw [_root_.mul_one] | erw [_root_.one_mul])))

example : IsTorsFrame (zeroPolAV S) (rig1 S) 3 (1 : T ⟶ (zeroPolAV S).A) (one1 S T 1 1) := by
  refine ⟨one_pow _, ?_, ⟨fun _ => 1⟩, ?_, ?_, ?_⟩
  · intro i j
    erw [linComb_triv_g, _root_.one_mul]; dsimp only [one1]; repeat erw [map_one]
  · intro i j
    erw [linComb_triv_g, _root_.one_mul]; repeat erw [map_one]
  · intro j j' _ _ _
    dsimp only [LB.pullGen, LB.mulGen, LB.invGen, rigPow, rig1]
    ones
  · intro j j' _ _ _
    dsimp only [LB.pullGen, LB.mulGen, rigT, powFrame, rig1, one1]
    ones

def theta1 (k : ℤ) : ThetaGrp (zeroPolAV S).A (zeroPolAV S).L k T where
  pt := 1
  φ := ⟨fun _ => 1⟩
  isGen := by
    intro i j
    erw [linComb_triv_g, _root_.one_mul]; repeat erw [map_one]

example (k : ℤ) : IsThetaFrame (zeroPolAV S) (rig1 S) k (theta1 S T k) ⟨fun _ => 1⟩ := by
  refine ⟨?_, ?_⟩
  · intro i j
    erw [linComb_triv_g, _root_.one_mul]; repeat erw [map_one]
  · intro j j' _ _ _
    dsimp only [LB.pullGen, LB.mulGen, rigT, rig1]
    erw [show (theta1 S T k).φ.s = fun _ => 1 from rfl]
    ones

example (a : ℤ) : (fun _ => 1) ∈ SecM (zeroPolAV S).A (zeroPolAV S).L a T := by
  intro i j
  erw [linComb_triv_g]; simp only [Units.val_one]; ones; rfl

def oneSec (a : ℤ) (T : Over S) : LB.Sec (LPow (zeroPolAV S).A (zeroPolAV S).L a T) :=
  ⟨fun _ => 1, by intro i j; erw [linComb_triv_g]; simp only [Units.val_one]; ones; rfl⟩

example (N m : ℕ) : (oneSec S (N : ℤ) T).f ∈ VVsub (zeroPolAV S) N m T := by
  refine Submodule.subset_span ⟨(oneSec S N T).compat, ?_⟩
  intro p
  refine ⟨⊤, trivial, oneSec S N _, ?_, ?_⟩
  · intro j
    simp only [SecM.toSec, oneSec]
    (repeat erw [map_one])
  · refine ⟨1, fun _ => 1, fun _ => oneSec S N _, fun _ => ?_, ?_⟩
    · refine ⟨oneSec S 1 _, oneSec S N _, ⟨fun _ => 1⟩, theta1 S _ N, ?_, ?_, ?_⟩
      · intro i j
        erw [linComb_triv_g, _root_.one_mul]; repeat erw [map_one]
      · intro j
        simp only [oneSec, Units.val_one]
        (repeat erw [map_one]); (try erw [_root_.one_mul])
      · intro j
        simp only [oneSec, Units.val_one]
        (repeat erw [map_one]); (try erw [_root_.one_mul])
    · intro j
      dsimp only [oneSec]
      simp only [liftFun, map_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul,
        _root_.mul_one]

example : de (zeroPolAV S) T := 0

end ReciprocityTheory.ChartRestriction.G.Out.InhVV
