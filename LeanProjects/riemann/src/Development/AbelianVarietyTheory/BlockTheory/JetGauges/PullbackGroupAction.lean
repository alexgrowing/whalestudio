import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PullbackGroupAction

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

variable {S S' : Scheme.{0}}

abbrev pullGrp (f : S' ⟶ S) (G : Over S) : Over S' := (Over.pullback f).obj G

abbrev pullFst (f : S' ⟶ S) (G : Over S) : (pullGrp f G).left ⟶ G.left := pullback.fst G.hom f

theorem pullGrp_comm (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] : IsCommMonObj (pullGrp f G) :=
  inferInstance

def pullAct {O : Type} [CommRing O] (f : S' ⟶ S) {G : Over S} [GrpObj G] (A : OAct O G) :
    OAct O (pullGrp f G) where
  act a := (Over.pullback f).map (A.act a)
  hom a := by
    have := A.hom a
    infer_instance
  one := by rw [A.one, CategoryTheory.Functor.map_id]
  mul a b := by rw [A.mul, CategoryTheory.Functor.map_comp]
  add a b := by rw [A.add, CategoryTheory.Functor.map_mul]

theorem pullAct_fst {O : Type} [CommRing O] (f : S' ⟶ S) {G : Over S} [GrpObj G] (A : OAct O G) (a : O) :
    ((pullAct f A).act a).left ≫ pullFst f G = pullFst f G ≫ (A.act a).left := by
  exact pullback.lift_fst _ _ _

theorem eSec_pullFst (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    eSec (pullGrp f G) ≫ pullFst f G = (show (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left from f) ≫ eSec G := by
  simp [eSec, pullFst]
  have h : pullback.fst (𝟙 S) f = pullback.snd (𝟙 S) f ≫ f := by simpa using pullback.condition (f := 𝟙 S) (g := f)
  refine (pullback.lift_fst _ _ _).trans ?_
  rw [← Category.assoc]
  exact congrArg (· ≫ _) h

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def HasPullWith {H : Host E} (t : SAB H S) (f : S' ⟶ S) (L' : RigLB (pullGrp f t.G)) : Prop :=
  ∃ (semi : IsSemiAbelian (pullGrp f t.G)) (cub : CubicalStr (pullGrp f t.G) L') (sym : L'.IsSymmetric)
    (adj : ∀ a : 𝓞 E,
      LBIso (cubeLB (pullGrp f t.G) ![fst _ _ ≫ (pullAct f t.act).act a, snd _ _] L'.L)
        (cubeLB (pullGrp f t.G) ![fst _ _, snd _ _ ≫ (pullAct f t.act).act (H.bar a)] L'.L))
    (prim : LBIso L'.L (cubeLB (pullGrp f t.G) ![𝟙 _, (pullAct f t.act).act H.w0] L'.L))
    (m : SABMap
      ({ G := pullGrp f t.G, semi := semi, act := pullAct f t.act, PP := L', cub := cub, sym := sym,
         adj := adj, prim := prim } : SAB H S') t f),
    m.φ = pullFst f t.G

def IsRigPull (f : S' ⟶ S) {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) (L' : RigLB (pullGrp f G)) : Prop :=
  ∃ w : LB.Iso L'.L (L.L.pull (pullFst f G)), w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec (pullGrp f G)) (fun _ => 1)) L'.rig
      (rigPullOf (pullFst f G) f (eSec_pullFst f G) L.L L.rig)

def RigPullExists : Prop :=
  ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G),
    ∃ L' : RigLB (pullGrp f G), IsRigPull f L L'

def SABPull : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (t : SAB H S)
    (L' : RigLB (pullGrp f t.G)), LBIso L'.L (t.PP.L.pull (pullFst f t.G)) → HasPullWith t f L'

def SABPullRig : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (t : SAB H S)
    (L' : RigLB (pullGrp f t.G)), IsRigPull f t.PP L' → HasPullWith t f L'

def SABPullExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (t : SAB H S),
    ∃ L' : RigLB (pullGrp f t.G), HasPullWith t f L'

example (h : SABPull) : SABPullRig :=
  fun E _ _ _ H S S' f t L' ⟨w, hw, _⟩ => h E H S S' f t L' ⟨w, hw⟩

example (h : SABPullRig) (h' : RigPullExists) : SABPullExists := fun E _ _ _ H S S' f t =>
  let ⟨L', hL⟩ := h' f t.G t.PP
  ⟨L', h E H S S' f t L' hL⟩

example {H : Host E} (t : SAB H S) (f : S' ⟶ S) (L' : RigLB (pullGrp f t.G)) (h : HasPullWith t f L') :
    LBIso L'.L (t.PP.L.pull (pullFst f t.G)) := by
  obtain ⟨_, _, _, _, _, m, hm⟩ := h
  obtain ⟨w, hw, _⟩ := m.lin
  rw [← hm]
  exact ⟨w, hw⟩

end GlobalTheory.IndefiniteRowSideFullHecke.PullbackGroupAction
