import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumOfDescendedMultiplicationImpor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.DescKP

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

abbrev sqR (N : Near π G) : Over (Sp R) :=
  Over.mk ((Desc.UT N ⊗ Desc.UT N).hom ≫ pullback.fst π π ≫ π)

def fstU (N : Near π G) : sqR N ⟶ N.U :=
  Over.homMk ((fst (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _)
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Over.w (fst (Desc.UT N) (Desc.UT N)))))))

def sndU (N : Near π G) : sqR N ⟶ N.U :=
  Over.homMk ((snd (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _)
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Over.w (snd (Desc.UT N) (Desc.UT N)))))))

def pairU (N : Near π G) : (Desc.UT N ⊗ Desc.UT N).left ⟶ (N.U ⊗ N.U).left :=
  (lift (fstU N) (sndU N)).left

abbrev VT (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) : (Desc.UT N ⊗ Desc.UT N).left.Opens :=
  pairU N ⁻¹ᵁ V

theorem pairU_over (N : Near π G) :
    pairU N ≫ (N.U ⊗ N.U).hom = (Desc.UT N ⊗ Desc.UT N).hom ≫ pullback.fst π π ≫ π :=
  Over.w (lift (fstU N) (sndU N))

def mT (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left)
    (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom) : (VT N V).toScheme ⟶ (Desc.UT N).left :=
  pullback.lift ((pairU N ∣_ V) ≫ m) ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom) (by
    have e : (pairU N ∣_ V) ≫ V.ι = (VT N V).ι ≫ pairU N := morphismRestrict_ι _ _
    refine (Category.assoc _ _ _).trans ?_
    rw [hm, ← Category.assoc, e, Category.assoc, pairU_over, Category.assoc])

variable [GrpObj G]

def trip (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    (Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N ⟶ (Over.pullback p).obj G :=
  (snd _ _ ≫ Desc.emb N p hp)⁻¹ * (fst _ _ ≫ Desc.sum N p hp)

def Pk (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) : Over (pullback π π) :=
  Over.mk (pullback.snd (Desc.emb N p hp).left (trip N p hp).left ≫ ((Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N).hom)

def dP (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) : Pk N p hp ⟶ Desc.UT N :=
  Over.homMk (pullback.fst _ _) (by
    show pullback.fst _ _ ≫ (Desc.UT N).hom = pullback.snd _ _ ≫ _
    rw [← Over.w (Desc.emb N p hp), ← Category.assoc, pullback.condition, Category.assoc, Over.w (trip N p hp)])

def abP (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Pk N p hp ⟶ Desc.UT N ⊗ Desc.UT N :=
  Over.homMk (pullback.snd _ _ ≫ (fst (Desc.UT N ⊗ Desc.UT N) (Desc.UT N)).left)
    ((Category.assoc _ _ _).trans (congrArg (pullback.snd _ _ ≫ ·) (Over.w (fst (Desc.UT N ⊗ Desc.UT N) (Desc.UT N)))))

def cP (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) : Pk N p hp ⟶ Desc.UT N :=
  Over.homMk (pullback.snd _ _ ≫ (snd (Desc.UT N ⊗ Desc.UT N) (Desc.UT N)).left)
    ((Category.assoc _ _ _).trans (congrArg (pullback.snd _ _ ≫ ·) (Over.w (snd (Desc.UT N ⊗ Desc.UT N) (Desc.UT N)))))

def cdP (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Pk N p hp ⟶ Desc.UT N ⊗ Desc.UT N :=
  lift (cP N p hp) (dP N p hp)

def Wk (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (V : (N.U ⊗ N.U).left.Opens) :
    (Pk N p hp).left.Opens :=
  (abP N p hp).left ⁻¹ᵁ VT N V ⊓ (cdP N p hp).left ⁻¹ᵁ VT N V

def q3 (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Pk N p hp ⟶ (Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N :=
  Over.homMk (pullback.snd _ _) rfl

theorem abP_eq (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    abP N p hp = q3 N p hp ≫ fst _ _ := Over.OverMorphism.ext rfl

theorem indicatorIdempotent_eq_add_sum (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    cP N p hp = q3 N p hp ≫ snd _ _ := Over.OverMorphism.ext rfl

theorem dP_emb (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    dP N p hp ≫ Desc.emb N p hp = q3 N p hp ≫ trip N p hp := Over.OverMorphism.ext pullback.condition

theorem abP_sum (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    abP N p hp ≫ Desc.sum N p hp = cdP N p hp ≫ Desc.sum N p hp := by
  have e4 : cdP N p hp ≫ Desc.sum N p hp = (cP N p hp ≫ Desc.emb N p hp) * (dP N p hp ≫ Desc.emb N p hp) := by
    rw [cdP, Desc.sum, comp_mul, ← Category.assoc, lift_fst, ← Category.assoc, lift_snd]
  rw [e4, dP_emb, trip, comp_mul, GrpObj.comp_inv, indicatorIdempotent_eq_add_sum, abP_eq]
  simp only [Category.assoc]
  exact (mul_inv_cancel_left _ _).symm

theorem exists_lift (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (Z : Scheme.{0})
    (g g' : Z ⟶ (Desc.UT N ⊗ Desc.UT N).left) (h : g ≫ (Desc.sum N p hp).left = g' ≫ (Desc.sum N p hp).left) :
    ∃ z : Z ⟶ (Pk N p hp).left, z ≫ (abP N p hp).left = g ∧ z ≫ (cdP N p hp).left = g' := by
  let FinalForm : Over (pullback π π) := Over.mk (g ≫ (Desc.UT N ⊗ Desc.UT N).hom)
  have hw : g' ≫ (Desc.UT N ⊗ Desc.UT N).hom = g ≫ (Desc.UT N ⊗ Desc.UT N).hom := by
    rw [← Over.w (Desc.sum N p hp), ← Category.assoc, ← h, Category.assoc]
  let a : FinalForm ⟶ Desc.UT N ⊗ Desc.UT N := Over.homMk g rfl
  let b : FinalForm ⟶ Desc.UT N ⊗ Desc.UT N := Over.homMk g' hw
  have hab : a ≫ Desc.sum N p hp = b ≫ Desc.sum N p hp := Over.OverMorphism.ext h
  let t : FinalForm ⟶ (Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N := lift a (b ≫ fst _ _)
  have ht : (b ≫ snd _ _) ≫ Desc.emb N p hp = t ≫ trip N p hp := by
    rw [trip, comp_mul, GrpObj.comp_inv, ← Category.assoc, lift_snd, ← Category.assoc t, lift_fst, hab, Desc.sum,
      comp_mul]
    simp only [Category.assoc]
    exact (inv_mul_cancel_left _ _).symm
  let zo : FinalForm ⟶ Pk N p hp := Over.homMk (pullback.lift (b ≫ snd _ _).left t.left (congrArg Over.Hom.left ht))
    (by show pullback.lift _ _ _ ≫ pullback.snd _ _ ≫ _ = _
        rw [← Category.assoc, pullback.lift_snd]; exact Over.w t)
  have h1 : zo ≫ abP N p hp = a := by rw [abP_eq, ← Category.assoc]; exact (congrArg (· ≫ fst _ _)
    (Over.OverMorphism.ext (pullback.lift_snd _ _ _) : zo ≫ q3 N p hp = t)).trans (lift_fst _ _)
  have h2 : zo ≫ cdP N p hp = b := by
    have hc : zo ≫ cP N p hp = b ≫ fst _ _ := by
      rw [indicatorIdempotent_eq_add_sum, ← Category.assoc]; exact (congrArg (· ≫ snd _ _)
        (Over.OverMorphism.ext (pullback.lift_snd _ _ _) : zo ≫ q3 N p hp = t)).trans (lift_snd _ _)
    have hd : zo ≫ dP N p hp = b ≫ snd _ _ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    rw [cdP, comp_lift, hc, hd]
    exact (lift_comp_fst_snd b)
  exact ⟨zo.left, congrArg Over.Hom.left h1, congrArg Over.Hom.left h2⟩

end GlobalTheory.Mum.DescKP
