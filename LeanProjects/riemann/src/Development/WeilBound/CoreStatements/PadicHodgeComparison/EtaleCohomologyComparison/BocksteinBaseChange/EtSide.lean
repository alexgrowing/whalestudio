import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HarishChandraFormulaStatement

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

namespace Model

abbrev spc (M : Model l K) : GlobalTheory.EtC.Spc := GlobalTheory.EtC.sch.obj (GlobalTheory.Et.geom (PadicAlgCl l) M.q)

def T (M : Model l K) (n : ℕ) : Type 1 := GlobalTheory.EtC.Hl l M.spc n 0

instance (M : Model l K) (n : ℕ) : AddCommGroup (M.T n) := inferInstanceAs (AddCommGroup (GlobalTheory.EtC.Hl l M.spc n 0))

instance (M : Model l K) (n : ℕ) : Module ℤ_[l] (M.T n) := inferInstanceAs (Module ℤ_[l] (GlobalTheory.EtC.Hl l M.spc n 0))

def T.lev {M : Model l K} {n : ℕ} (x : M.T n) (k : ℕ) : GlobalTheory.EtC.Ht (l ^ k) M.spc n 0 := (show GlobalTheory.EtC.Hl l M.spc n 0 from x).1 k

def toV (M : Model l K) (n : ℕ) (x : M.T n) : M.V n := (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] (show GlobalTheory.EtC.Hl l M.spc n 0 from x)

def actT (M : Model l K) (n : ℕ) (σ : K.fixingSubgroup) : M.T n →ₗ[ℤ_[l]] M.T n :=
  GlobalTheory.EtC.galHl l (PadicAlgCl l) M.q n 0 (IntermediateField.fixingSubgroupEquiv K σ)

def pullT {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) : N.T n →ₗ[ℤ_[l]] M.T n :=
  GlobalTheory.EtC.pullHl l (GlobalTheory.EtC.sch.map (GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (genMap u hu) (genMap_q u hu))) n 0

def CupT (M : Model l K) {i j : ℕ} (x : M.T i) (y : M.T j) (z : M.T (i + j)) : Prop :=
  ∀ k, z.lev k = (GlobalTheory.EtC.cup (l ^ k) (x.lev k) (y.lev k)).cast (by push_cast; rfl) (add_zero 0)

def Conn (M : Model l K) (d : ℕ) : Prop := ConnectedSpace M.gen ∧ SmoothOfRelativeDimension d M.q

def Sm (M : Model l K) : Prop := M.Good ∧ Smooth M.p

end Model

variable (G : Model l K → Prop)

def Model.Dual (M : Model l K) (d : ℕ) : Prop :=
  (∀ i, 2 * d < i → Subsingleton (M.V i)) ∧
  ∀ i j : ℕ, i + j = 2 * d → ∃ (r : ℕ) (g : Fin r → M.V (i + j)),
    Submodule.span ℚ_[l] (Set.range g) = ⊤ ∧
    (∀ s s', ∃ (σ : K.fixingSubgroup) (z : ℚ_[l]), z ≠ 0 ∧ M.act (i + j) σ (g s) = z • g s') ∧
    Submodule.span ℚ_[l] {f : Module.Dual ℚ_[l] (M.V i) | ∃ (s : Fin r) (y : M.T j),
      ∀ x : M.T i, ∃ z, M.CupT x y z ∧ M.toV (i + j) z = f (M.toV i x) • g s} = ⊤

structure EtSide : Prop where
  cup_ex : ∀ (M : Model l K) {i j : ℕ} (x : M.T i) (y : M.T j), ∃ z, M.CupT x y z
  fin : ∀ (M : Model l K), G M → ∀ j : ℕ, FiniteDimensional ℚ_[l] (M.V j)
  dual : ∀ (M : Model l K), G M → ∀ d : ℕ, M.Conn d → M.Dual d
  comp : ∀ (M : Model l K), G M → ∃ (r : ℕ) (P : Fin r → Model l K) (d : Fin r → ℕ) (u : ∀ a, (P a).X ⟶ M.X)
    (hu : ∀ a, u a ≫ M.p = (P a).p), (∀ a, G (P a) ∧ (P a).Conn (d a)) ∧
    ∀ (j : ℕ) (v : M.V j), (∀ a, Model.pullV (u a) (hu a) j v = 0) → v = 0

open GlobalTheory.EtC in

def InBock : Prop := ∀ (p a b : ℕ) [Fact p.Prime] (X : Scheme.{0}), IsUnit (p : Γ(X, ⊤)) → ∀ (n i : ℤ)
  (z : Ht (p ^ (a + b)) (sch.obj X) n i), red (p ^ (a + b)) (p ^ b) _ n i z = 0 →
    p ^ a • z = 0 ∧ ∃ w : Ht (p ^ a) (sch.obj X) n i, red (p ^ (a + b)) (p ^ a) _ n i z = p ^ b • w

open GlobalTheory.EtC in

def InRoot : Prop := ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}), Nonempty (Prim q Γ(X, ⊤)) → ∀ i : ℤ,
  ∃ (u : Ht q (sch.obj X) 0 i) (v : Ht q (sch.obj X) 0 (-i)), cup q v u = (one q (sch.obj X)).cast (by ring) (by ring)

def IsSum {X : Scheme.{0}} {r : ℕ} {Y : Fin r → Scheme.{0}} (j : ∀ s, Y s ⟶ X) : Prop :=
  (∀ s, IsOpenImmersion (j s)) ∧ (∀ x : X, ∃ s, x ∈ Set.range (j s)) ∧
    ∀ s s', s ≠ s' → Disjoint (Set.range (j s)) (Set.range (j s'))

open GlobalTheory.EtC in

def InSum : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {X : Scheme.{0}} {r : ℕ} {Y : Fin r → Scheme.{0}} (j : ∀ s, Y s ⟶ X),
  IsSum j → ∀ n : ℤ, Function.Bijective fun (x : H R (sch.obj X) F n) (s : Fin r) => pull R (sch.map (j s)) F n x

structure ZIn : Prop where
  nat : GlobalTheory.EtC.DivisorNaturality
  ring : GlobalTheory.EtC.DivisorRingCompatibility
  a9 : GlobalTheory.EtC.A9
  a11 : GlobalTheory.EtC.A11
  e4 : GlobalTheory.EtC.E4
  e8 : GlobalTheory.EtC.E8
  bock : InBock
  root : InRoot
  sum : InSum

def CompM : Prop := ∀ (M : Model l K), G M → ∃ (r : ℕ) (P : Fin r → Model l K) (d : Fin r → ℕ) (u : ∀ a, (P a).X ⟶ M.X)
  (_ : ∀ a, u a ≫ M.p = (P a).p), IsSum u ∧ ∀ a, G (P a) ∧ (P a).Conn (d a)

def Model.Geo (M : Model l K) : Prop := ∃ (r : ℕ) (Y : Fin r → Scheme.{0}) (j : ∀ s, Y s ⟶ GlobalTheory.Et.geom (PadicAlgCl l) M.q),
  IsSum j ∧ (∀ s, IsIntegral (Y s)) ∧
  (∀ σ : K.fixingSubgroup, ∃ (π : Equiv.Perm (Fin r)) (θ : ∀ s, Y s ≅ Y (π s)),
    ∀ s, j s ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K σ) = (θ s).hom ≫ j (π s)) ∧
  ∀ s s', ∃ (σ : K.fixingSubgroup) (θ : Y s ⟶ Y s'),
    j s ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K σ) = θ ≫ j s'

end CrystallineSemistableComparison
