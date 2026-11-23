import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.DiagonalPowerBalanced

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out

section Defs

variable {R : Type} [CommRing R] [IsDomain R]

def CLinear (D : DegPre R) (f : D.P.A ⟶ D.P.A) (a : D.X → D.X) : Prop :=
  ∀ y : D.X, D.c (a y) = D.c y ≫ f

def DiagOnB {D' D : DegPre R} {n : ℕ} (p : IsPowDeg D' D n) (F : D'.P.A ⟶ D'.P.A)
    (f : D.P.A ⟶ D.P.A) : Prop :=
  ∀ i : Fin n, F ≫ p.pw.pr i = p.pw.pr i ≫ f

def DiagOnX {D' D : DegPre R} {n : ℕ} (p : IsPowDeg D' D n) (A : D'.X → D'.X)
    (a : D.X → D.X) : Prop :=
  ∀ (x : D'.X) (i : Fin n), p.xe (A x) i = a (p.xe x i)

def diagB {D' D : DegPre R} {n : ℕ} (p : IsPowDeg D' D n) (f : D.P.A ⟶ D.P.A) :
    D'.P.A ⟶ D'.P.A :=
  p.pw.lim.lift (Fan.mk D'.P.A (fun i => p.pw.pr i ≫ f))

def diagX {D' D : DegPre R} {n : ℕ} (p : IsPowDeg D' D n) (a : D.X → D.X) : D'.X → D'.X :=
  fun x => p.xe.symm (fun i => a (p.xe x i))

theorem diagOnB_iff {D' D : DegPre R} {n : ℕ} (p : IsPowDeg D' D n) (F : D'.P.A ⟶ D'.P.A)
    (f : D.P.A ⟶ D.P.A) : DiagOnB p F f ↔ F = diagB p f := by
  have hfac : ∀ i, diagB p f ≫ p.pw.pr i = p.pw.pr i ≫ f := fun i =>
    p.pw.lim.fac (Fan.mk D'.P.A (fun i => p.pw.pr i ≫ f)) ⟨i⟩
  constructor
  · intro h
    apply p.pw.lim.hom_ext
    rintro ⟨i⟩
    exact (h i).trans (hfac i).symm
  · rintro rfl
    exact hfac

theorem diagOnX_iff {D' D : DegPre R} {n : ℕ} (p : IsPowDeg D' D n) (A : D'.X → D'.X)
    (a : D.X → D.X) : DiagOnX p A a ↔ A = diagX p a := by
  constructor
  · intro h
    funext x
    apply p.xe.injective
    funext i
    simp [diagX, h x i]
  · rintro rfl x i
    simp [diagX]

theorem CLinear.pow {D' D : DegPre R} {n : ℕ} (p : IsPowDeg D' D n) {F : D'.P.A ⟶ D'.P.A}
    {f : D.P.A ⟶ D.P.A} {A : D'.X → D'.X} {a : D.X → D.X} (hF : DiagOnB p F f)
    (hA : DiagOnX p A a) (h : CLinear D f a) : CLinear D' F A := by
  intro x
  apply p.pw.lim.hom_ext
  rintro ⟨i⟩
  change D'.c (A x) ≫ p.pw.pr i = (D'.c x ≫ F) ≫ p.pw.pr i
  rw [p.c_pr, hA x i, h, Category.assoc, hF i, ← Category.assoc, p.c_pr]

end Defs

def PowTauBalanced : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) (n : ℕ) (p : IsPowDeg D' D n)
    (f g : D.P.A ⟶ D.P.A) (a a' : D.X → D.X)
    (F G : D'.P.A ⟶ D'.P.A) (A A' : D'.X → D'.X),
    DiagOnB p F f → DiagOnB p G g → DiagOnX p A a → DiagOnX p A' a' →
    CLinear D f a → CLinear D g a' →
    D.TauBal f g a a' → D'.TauBal F G A A'

def PowTauBalancedAct : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) (n : ℕ)
    (p : IsPowDeg D'.toPre D.toPre n) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X]
    (act : DegData.OAct O D) (a : O),
    D'.toPre.TauBal (diagB p (act.onB.act a)) (diagB p (act.onB.act (star a)))
      (diagX p (fun y => a • y)) (diagX p (fun y => star a • y))

theorem PowTauBalanced.act (h : PowTauBalanced) : PowTauBalancedAct := by
  intro R _ _ I D D' n p O _ _ _ act a
  exact h R D.toPre D'.toPre n p _ _ _ _ _ _ _ _
    ((diagOnB_iff p _ _).2 rfl) ((diagOnB_iff p _ _).2 rfl)
    ((diagOnX_iff p _ _).2 rfl) ((diagOnX_iff p _ _).2 rfl)
    (act.c_lin a) (act.c_lin (star a)) (act.tau_bal a)

example {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) : CLinear D (𝟙 _) id :=
  fun _ => (Category.comp_id _).symm

end GlobalTheory.IndefiniteRowSideFullHecke.DiagonalPowerBalanced
