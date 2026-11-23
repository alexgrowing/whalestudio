import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import GroundTheory.PAdicHodge.PerfectoidField

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge GlobalTheory.LogCris

namespace CrystallineSemistableComparison

abbrev infBase (K : Type) [CommRing K] : Base where
  R := K
  I := ⊥
  γ := dividedPowersBot K
  t := 1
  p := 0

def smFun {K : Type} [CommRing K] (X : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) : (infBase K).Fun where
  ι := Empty
  A := Unit
  Pt := ptFun X q (Ideal.Quotient.mk (⊥ : Ideal K))
  str y := y.1.1
  str_map _ _ := rfl
  In _ _ _ := True
  in_map _ _ _ := trivial
  f _ i := i.elim
  f_map i := i.elim
  g _ _ i := i.elim
  g_map i := i.elim
  f_eq i := i.elim
  g_self i := i.elim
  g_comp i := i.elim
  prod_f {_ _ y} _ := by simp
  prod_g _ _ := by simp

def smMor {K : Type} [CommRing K] {X Y : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of K)} {q : Y ⟶ Spec (CommRingCat.of K)}
    (u : X ⟶ Y) (hu : u ≫ q = p) : Mor (smFun Y q) (smFun X p) (RingHom.id K) where
  hp := rfl
  hI := ⟨by rw [Ideal.map_id], fun _ _ => rfl⟩
  a := 1
  ha := by simp
  m := 1
  ht := by simp
  e i := i.elim
  he j := j.elim
  c α := α
  pt := { app := fun B => TypeCat.ofHom fun z => ⟨(z.1.1, z.1.2 ≫ u), by rw [Category.assoc, hu]; exact z.2⟩
          naturality := fun B B' φ => by
            ext z
            refine Subtype.ext (Prod.ext rfl ?_)
            exact Category.assoc _ _ _ }
  str _ _ := rfl
  inc _ := trivial
  w _ i := i.elim
  w_map i := i.elim
  hf i := i.elim
  hg i := i.elim
  hw _ := Finset.prod_of_isEmpty (ι := Empty) _

def HdR {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) : Type 1 := H (smFun X q) n

section
variable {K : Type} [CommRing K] {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)

instance : AddCommGroup (HdR p n) := inferInstanceAs (AddCommGroup (H (smFun X p) n))
instance : Module K (HdR p n) := inferInstanceAs (Module (infBase K).R (H (smFun X p) n))

def FilR (r : ℕ) : Set (HdR p n) := Fil (smFun X p) n r

variable {p} in

def pullR {q : Y ⟶ Spec (CommRingCat.of K)} (u : X ⟶ Y) (hu : u ≫ q = p) : HdR q n →ₗ[K] HdR p n := (smMor u hu).pull n
end

variable (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))

def OK : Subring K := (normInteger (PadicAlgCl l)).comap K.val.toRingHom

structure Model : Type 1 where
  X : Scheme.{0}
  p : X ⟶ Spec (CommRingCat.of (OK l K))

variable {l K}

namespace Model

abbrev gen (M : Model l K) : Scheme.{0} := pullback M.p (Spec.map (CommRingCat.ofHom (OK l K).subtype))

abbrev q (M : Model l K) : M.gen ⟶ Spec (CommRingCat.of K) := pullback.snd _ _

def Good (M : Model l K) : Prop :=
  ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver M.p ∧ ∃ ϖ : OK l K, Irreducible ϖ ∧ GlobalTheory.Et.IsStrictlySemistable ϖ M.p

def genMap {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) : M.gen ⟶ N.gen :=
  pullback.lift (pullback.fst _ _ ≫ u) (pullback.snd _ _) (by rw [Category.assoc, hu, pullback.condition])

theorem genMap_q {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) : genMap u hu ≫ N.q = M.q := pullback.lift_snd _ _ _

def V (M : Model l K) (n : ℕ) : Type 1 := GlobalTheory.EtC.HQ l (GlobalTheory.EtC.sch.obj (GlobalTheory.Et.geom (PadicAlgCl l) M.q)) n 0

instance (M : Model l K) (n : ℕ) : AddCommGroup (M.V n) :=
  inferInstanceAs (AddCommGroup (GlobalTheory.EtC.HQ l (GlobalTheory.EtC.sch.obj (GlobalTheory.Et.geom (PadicAlgCl l) M.q)) n 0))

instance (M : Model l K) (n : ℕ) : Module ℚ_[l] (M.V n) :=
  inferInstanceAs (Module ℚ_[l] (GlobalTheory.EtC.HQ l (GlobalTheory.EtC.sch.obj (GlobalTheory.Et.geom (PadicAlgCl l) M.q)) n 0))

def act (M : Model l K) (n : ℕ) (σ : K.fixingSubgroup) : M.V n →ₗ[ℚ_[l]] M.V n :=
  GlobalTheory.EtC.galHQ l (PadicAlgCl l) M.q n 0 (IntermediateField.fixingSubgroupEquiv K σ)

def mat (M : Model l K) (n : ℕ) {a : ℕ} (b : Module.Basis (Fin a) ℚ_[l] (M.V n)) (σ : K.fixingSubgroup) :
    Matrix (Fin a) (Fin a) ℚ_[l] := LinearMap.toMatrix b b (M.act n σ)

def pullV {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ) : N.V n →ₗ[ℚ_[l]] M.V n :=
  GlobalTheory.EtC.pullHQ l (GlobalTheory.EtC.sch.map (GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (genMap u hu) (genMap_q u hu))) n 0

end Model

end CrystallineSemistableComparison
