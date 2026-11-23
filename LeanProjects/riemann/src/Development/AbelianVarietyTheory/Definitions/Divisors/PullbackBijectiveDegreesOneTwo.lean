import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace GlobalTheory.CxCoh

universe u u' u''

structure Coef (C : Type u) [Category.{0} C] where

  obj : C → Type
  [grp : ∀ T, AddCommGroup (obj T)]

  map : ∀ {T T' : C}, (T ⟶ T') → obj T →+ obj T'
  map_id : ∀ (T : C) (x : obj T), map (𝟙 T) x = x
  map_comp : ∀ {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (x : obj T), map (φ ≫ ψ) x = map ψ (map φ x)

attribute [instance] Coef.grp

variable {C : Type u} [Category.{0} C] {C' : Type u'} [Category.{0} C'] {C'' : Type u''} [Category.{0} C'']

namespace Coef

variable (M : Coef C)

abbrev c0 := ∀ T : C, M.obj T

abbrev c1 := ∀ (T T' : C) (_ : T ⟶ T'), M.obj T'

abbrev c2 := ∀ (T T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), M.obj T''

def Ac0 : Prop := ∀ g : M.c0, (∀ T T' (φ : T ⟶ T'), g T' = M.map φ (g T)) → g = 0

def Ac1 : Prop := ∀ f : M.c1,
  (∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''), f T T'' (φ ≫ ψ) = M.map ψ (f T T' φ) + f T' T'' ψ) →
  ∃ g : M.c0, ∀ T T' (φ : T ⟶ T'), f T T' φ = g T' - M.map φ (g T)

def Ac2 : Prop := ∀ z : M.c2,
  (∀ T T' T'' T''' (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T'''),
    M.map χ (z T T' T'' φ ψ) + z T T'' T''' (φ ≫ ψ) χ = z T T' T''' φ (ψ ≫ χ) + z T' T'' T''' ψ χ) →
  ∃ f : M.c1, ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''),
    z T T' T'' φ ψ = M.map ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ

@[reducible] def res (G : C' ⥤ C) : Coef C' where
  obj T := M.obj (G.obj T)
  map φ := M.map (G.map φ)
  map_id T x := by rw [G.map_id, M.map_id]
  map_comp φ ψ x := by rw [G.map_comp, M.map_comp]

@[reducible] def zero (C : Type u) [Category.{0} C] : Coef C where
  obj _ := PUnit
  map _ := 0
  map_id _ _ := rfl
  map_comp _ _ _ := rfl

end Coef

structure IsQ {A0 A1 A2 A3 B0 B1 B2 B3 : Type} [AddCommGroup A0] [AddCommGroup A1] [AddCommGroup A2]
    [AddCommGroup A3] [AddCommGroup B0] [AddCommGroup B1] [AddCommGroup B2] [AddCommGroup B3]
    (d0 : A0 →+ A1) (d1 : A1 →+ A2) (d2 : A2 →+ A3) (e0 : B0 →+ B1) (e1 : B1 →+ B2) (e2 : B2 →+ B3)
    (a0 : A0 →+ B0) (a1 : A1 →+ B1) (a2 : A2 →+ B2) : Prop where
  inj0 : ∀ x, d0 x = 0 → a0 x = 0 → x = 0
  surj0 : ∀ y, e0 y = 0 → ∃ x, d0 x = 0 ∧ a0 x = y
  inj1 : ∀ x y, d1 x = 0 → a1 x = e0 y → ∃ w, d0 w = x
  surj1 : ∀ y, e1 y = 0 → ∃ x w, d1 x = 0 ∧ y = a1 x + e0 w
  inj2 : ∀ x y, d2 x = 0 → a2 x = e1 y → ∃ w, d1 w = x
  surj2 : ∀ y, e2 y = 0 → ∃ x w, d2 x = 0 ∧ y = a2 x + e1 w

structure Cx (C : Type u) [Category.{0} C] where

  M0 : Coef C

  M1 : Coef C

  M2 : Coef C

  M3 : Coef C

  d0 : ∀ T, M0.obj T →+ M1.obj T

  d1 : ∀ T, M1.obj T →+ M2.obj T

  d2 : ∀ T, M2.obj T →+ M3.obj T
  diffZero_natural : ∀ {T T' : C} (φ : T ⟶ T') x, d0 T' (M0.map φ x) = M1.map φ (d0 T x)
  diffOne_natural : ∀ {T T' : C} (φ : T ⟶ T') x, d1 T' (M1.map φ x) = M2.map φ (d1 T x)
  diffTwo_natural : ∀ {T T' : C} (φ : T ⟶ T') x, d2 T' (M2.map φ x) = M3.map φ (d2 T x)
  diffOne_diffZero : ∀ T x, d1 T (d0 T x) = 0
  diffTwo_comp_diffOne : ∀ T x, d2 T (d1 T x) = 0

namespace Cx

variable (K : Cx C)

abbrev T1 := K.M0.c1 × K.M1.c0

abbrev T2 := K.M0.c2 × K.M1.c1 × K.M2.c0

def D0 : K.M0.c0 →+ K.T1 where
  toFun g := (fun T T' φ ↦ g T' - K.M0.map φ (g T), fun T ↦ K.d0 T (g T))
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp; abel

def D1 : K.T1 →+ K.T2 where
  toFun c := (fun T T' T'' φ ψ ↦ K.M0.map ψ (c.1 T T' φ) - c.1 T T'' (φ ≫ ψ) + c.1 T' T'' ψ,
    fun T T' φ ↦ c.2 T' - K.M1.map φ (c.2 T) - K.d0 T' (c.1 T T' φ), fun T ↦ K.d1 T (c.2 T))
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp <;> abel

def H0 : AddSubgroup K.M0.c0 := K.D0.ker

def Z1 : AddSubgroup K.T1 := K.D1.ker

def Z2 : AddSubgroup K.T2 where
  carrier := {c | (∀ T T' T'' T''' (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T'''),
      K.M0.map χ (c.1 T T' T'' φ ψ) + c.1 T T'' T''' (φ ≫ ψ) χ = c.1 T T' T''' φ (ψ ≫ χ) + c.1 T' T'' T''' ψ χ) ∧
    (∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''), c.2.1 T T'' (φ ≫ ψ) =
      K.M1.map ψ (c.2.1 T T' φ) + c.2.1 T' T'' ψ + K.d0 T'' (c.1 T T' T'' φ ψ)) ∧
    (∀ T T' (φ : T ⟶ T'), c.2.2 T' = K.M2.map φ (c.2.2 T) + K.d1 T' (c.2.1 T T' φ)) ∧
    ∀ T, K.d2 T (c.2.2 T) = 0}
  zero_mem' := by simp
  add_mem' {a b} ha hb := ⟨fun T T' T'' T''' φ ψ χ ↦ by
      have h1 := ha.1 T T' T'' T''' φ ψ χ
      have h2 := hb.1 T T' T'' T''' φ ψ χ
      simp only [Prod.fst_add, Pi.add_apply, map_add]
      linear_combination (norm := abel1) h1 + h2,
    fun T T' T'' φ ψ ↦ by simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, ha.2.1 T T' T'', hb.2.1 T T' T'']; abel,
    fun T T' φ ↦ by simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, ha.2.2.1 T T' φ, hb.2.2.1 T T' φ]; abel,
    fun T ↦ by simp only [Prod.snd_add, Pi.add_apply, map_add, ha.2.2.2 T, hb.2.2.2 T, add_zero]⟩
  neg_mem' {a} ha := ⟨fun T T' T'' T''' φ ψ χ ↦ by
      have h1 := ha.1 T T' T'' T''' φ ψ χ
      simp only [Prod.fst_neg, Pi.neg_apply, map_neg]
      linear_combination (norm := abel1) -h1,
    fun T T' T'' φ ψ ↦ by simp only [Prod.fst_neg, Prod.snd_neg, Pi.neg_apply, map_neg, ha.2.1 T T' T'']; abel,
    fun T T' φ ↦ by simp only [Prod.fst_neg, Prod.snd_neg, Pi.neg_apply, map_neg, ha.2.2.1 T T' φ]; abel,
    fun T ↦ by simp only [Prod.snd_neg, Pi.neg_apply, map_neg, ha.2.2.2 T, neg_zero]⟩

abbrev H1 := K.Z1 ⧸ K.D0.range.addSubgroupOf K.Z1

abbrev H2 := K.Z2 ⧸ K.D1.range.addSubgroupOf K.Z2

def QAt {T T' : C} (φ : T ⟶ T') : Prop :=
  IsQ (K.d0 T) (K.d1 T) (K.d2 T) (K.d0 T') (K.d1 T') (K.d2 T') (K.M0.map φ) (K.M1.map φ) (K.M2.map φ)

@[reducible] def res (G : C' ⥤ C) : Cx C' where
  M0 := K.M0.res G
  M1 := K.M1.res G
  M2 := K.M2.res G
  M3 := K.M3.res G
  d0 T := K.d0 (G.obj T)
  d1 T := K.d1 (G.obj T)
  d2 T := K.d2 (G.obj T)
  diffZero_natural φ := K.diffZero_natural (G.map φ)
  diffOne_natural φ := K.diffOne_natural (G.map φ)
  diffTwo_natural φ := K.diffTwo_natural (G.map φ)
  diffOne_diffZero _ := K.diffOne_diffZero _
  diffTwo_comp_diffOne _ := K.diffTwo_comp_diffOne _

@[reducible] def single (M : Coef C) : Cx C where
  M0 := M
  M1 := Coef.zero C
  M2 := Coef.zero C
  M3 := Coef.zero C
  d0 _ := 0
  d1 _ := 0
  d2 _ := 0
  diffZero_natural _ _ := rfl
  diffOne_natural _ _ := rfl
  diffTwo_natural _ _ := rfl
  diffOne_diffZero _ _ := rfl
  diffTwo_comp_diffOne _ _ := rfl

end Cx

structure CxMap (K : Cx C) (K' : Cx C') where

  G : C' ⥤ C

  a0 : ∀ T, K.M0.obj (G.obj T) →+ K'.M0.obj T

  a1 : ∀ T, K.M1.obj (G.obj T) →+ K'.M1.obj T

  a2 : ∀ T, K.M2.obj (G.obj T) →+ K'.M2.obj T

  a3 : ∀ T, K.M3.obj (G.obj T) →+ K'.M3.obj T
  compDegreeZero_natural : ∀ {T T' : C'} (φ : T ⟶ T') x, a0 T' (K.M0.map (G.map φ) x) = K'.M0.map φ (a0 T x)
  compDegreeOne_natural : ∀ {T T' : C'} (φ : T ⟶ T') x, a1 T' (K.M1.map (G.map φ) x) = K'.M1.map φ (a1 T x)
  compDegreeTwo_natural : ∀ {T T' : C'} (φ : T ⟶ T') x, a2 T' (K.M2.map (G.map φ) x) = K'.M2.map φ (a2 T x)
  comp_commutes_diffZero : ∀ T x, a1 T (K.d0 _ x) = K'.d0 T (a0 T x)
  comp_commutes_diffOne : ∀ T x, a2 T (K.d1 _ x) = K'.d1 T (a1 T x)
  comp_commutes_diffTwo : ∀ T x, a3 T (K.d2 _ x) = K'.d2 T (a2 T x)

namespace CxMap

variable {K : Cx C} {K' : Cx C'} {K'' : Cx C''} (m : CxMap K K')

def p0 : K.M0.c0 →+ K'.M0.c0 where
  toFun g T := m.a0 T (g _)
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

def p1 : K.T1 →+ K'.T1 where
  toFun c := (fun _ T' φ ↦ m.a0 T' (c.1 _ _ (m.G.map φ)), fun T ↦ m.a1 T (c.2 _))
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

def p2 : K.T2 →+ K'.T2 where
  toFun c := (fun _ _ T'' φ ψ ↦ m.a0 T'' (c.1 _ _ _ (m.G.map φ) (m.G.map ψ)),
    fun _ T' φ ↦ m.a1 T' (c.2.1 _ _ (m.G.map φ)), fun T ↦ m.a2 T (c.2.2 _))
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

theorem pullback_firstDifferential (g : K.M0.c0) : m.p1 (K.D0 g) = K'.D0 (m.p0 g) := by
  ext <;> simp [p0, p1, Cx.D0, m.compDegreeZero_natural, m.comp_commutes_diffZero]

theorem pullback_secondDifferential (c : K.T1) : m.p2 (K.D1 c) = K'.D1 (m.p1 c) := by
  ext <;> simp [p1, p2, Cx.D1, m.compDegreeZero_natural, m.compDegreeOne_natural, m.comp_commutes_diffZero, m.comp_commutes_diffOne]

theorem p2_mem_Z2_of_mem_Z2 {c : K.T2} (h : c ∈ K.Z2) : m.p2 c ∈ K'.Z2 := by
  refine ⟨fun T T' T'' T''' φ ψ χ ↦ ?_, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
  · have := congrArg (m.a0 T''') (h.1 _ _ _ _ (m.G.map φ) (m.G.map ψ) (m.G.map χ))
    simpa [p2, m.compDegreeZero_natural] using this
  · have := congrArg (m.a1 T'') (h.2.1 _ _ _ (m.G.map φ) (m.G.map ψ))
    simpa [p2, m.compDegreeOne_natural, m.comp_commutes_diffZero] using this
  · have := congrArg (m.a2 T') (h.2.2.1 _ _ (m.G.map φ))
    simpa [p2, m.compDegreeTwo_natural, m.comp_commutes_diffOne] using this
  · have := congrArg (m.a3 T) (h.2.2.2 (m.G.obj T))
    simpa [p2, m.comp_commutes_diffTwo] using this

def h0 : K.H0 →+ K'.H0 := (m.p0.comp K.H0.subtype).codRestrict _ fun c ↦ by
  have h : K.D0 c.1 = 0 := c.2
  change K'.D0 (m.p0 c.1) = 0
  rw [← pullback_firstDifferential, h, map_zero]

def z1 : K.Z1 →+ K'.Z1 := (m.p1.comp K.Z1.subtype).codRestrict _ fun c ↦ by
  have h : K.D1 c.1 = 0 := c.2
  change K'.D1 (m.p1 c.1) = 0
  rw [← pullback_secondDifferential, h, map_zero]

def z2 : K.Z2 →+ K'.Z2 := (m.p2.comp K.Z2.subtype).codRestrict _ fun c ↦ m.p2_mem_Z2_of_mem_Z2 c.2

def h1 : K.H1 →+ K'.H1 := QuotientAddGroup.map _ _ m.z1 (by
  rintro c ⟨g, hg⟩
  exact ⟨m.p0 g, (m.pullback_firstDifferential g).symm.trans (congrArg m.p1 hg)⟩)

def h2 : K.H2 →+ K'.H2 := QuotientAddGroup.map _ _ m.z2 (by
  rintro c ⟨g, hg⟩
  exact ⟨m.p1 g, (m.pullback_secondDifferential g).symm.trans (congrArg m.p2 hg)⟩)

def comp (n : CxMap K' K'') : CxMap K K'' where
  G := n.G ⋙ m.G
  a0 T := (n.a0 T).comp (m.a0 _)
  a1 T := (n.a1 T).comp (m.a1 _)
  a2 T := (n.a2 T).comp (m.a2 _)
  a3 T := (n.a3 T).comp (m.a3 _)
  compDegreeZero_natural φ x := (congrArg (n.a0 _) (m.compDegreeZero_natural (n.G.map φ) x)).trans (n.compDegreeZero_natural φ _)
  compDegreeOne_natural φ x := (congrArg (n.a1 _) (m.compDegreeOne_natural (n.G.map φ) x)).trans (n.compDegreeOne_natural φ _)
  compDegreeTwo_natural φ x := (congrArg (n.a2 _) (m.compDegreeTwo_natural (n.G.map φ) x)).trans (n.compDegreeTwo_natural φ _)
  comp_commutes_diffZero T x := (congrArg (n.a1 _) (m.comp_commutes_diffZero _ x)).trans (n.comp_commutes_diffZero T _)
  comp_commutes_diffOne T x := (congrArg (n.a2 _) (m.comp_commutes_diffOne _ x)).trans (n.comp_commutes_diffOne T _)
  comp_commutes_diffTwo T x := (congrArg (n.a3 _) (m.comp_commutes_diffTwo _ x)).trans (n.comp_commutes_diffTwo T _)

theorem cohomZero_pullback_comp (n : CxMap K' K'') (c : K.H0) : (m.comp n).h0 c = n.h0 (m.h0 c) := rfl

theorem cohomOne_pullback_comp (n : CxMap K' K'') (c : K.H1) : (m.comp n).h1 c = n.h1 (m.h1 c) := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c; rfl

theorem cohomTwo_pullback_comp (n : CxMap K' K'') (c : K.H2) : (m.comp n).h2 c = n.h2 (m.h2 c) := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c; rfl

def QAll : Prop := ∀ T, IsQ (K.d0 _) (K.d1 _) (K.d2 _) (K'.d0 T) (K'.d1 T) (K'.d2 T) (m.a0 T) (m.a1 T) (m.a2 T)

def PullbackBijectiveDegreesOneTwo : Prop := Function.Bijective m.h1 ∧ Function.Bijective m.h2

def Bij : Prop := Function.Bijective m.h0 ∧ m.PullbackBijectiveDegreesOneTwo

structure Joined (m m' : CxMap K K') (θ : m.G ⟶ m'.G) : Prop where
  e0 : ∀ T x, m'.a0 T (K.M0.map (θ.app T) x) = m.a0 T x
  e1 : ∀ T x, m'.a1 T (K.M1.map (θ.app T) x) = m.a1 T x
  e2 : ∀ T x, m'.a2 T (K.M2.map (θ.app T) x) = m.a2 T x

def vert : CxMap (K.res m.G) K' := { m with G := 𝟭 C' }

end CxMap

def Cx.resMap (K : Cx C) (G : C' ⥤ C) : CxMap K (K.res G) where
  G := G
  a0 _ := AddMonoidHom.id _
  a1 _ := AddMonoidHom.id _
  a2 _ := AddMonoidHom.id _
  a3 _ := AddMonoidHom.id _
  compDegreeZero_natural _ _ := rfl
  compDegreeOne_natural _ _ := rfl
  compDegreeTwo_natural _ _ := rfl
  comp_commutes_diffZero _ _ := rfl
  comp_commutes_diffOne _ _ := rfl
  comp_commutes_diffTwo _ _ := rfl

def Cx.fnMap (K : Cx C) : CxMap K (Cx.single K.M0) where
  G := 𝟭 C
  a0 _ := AddMonoidHom.id _
  a1 _ := 0
  a2 _ := 0
  a3 _ := 0
  compDegreeZero_natural _ _ := rfl
  compDegreeOne_natural _ _ := rfl
  compDegreeTwo_natural _ _ := rfl
  comp_commutes_diffZero _ _ := rfl
  comp_commutes_diffOne _ _ := rfl
  comp_commutes_diffTwo _ _ := rfl

section Alg

open GlobalTheory.CatCoh GlobalTheory.CechDR KaehlerDifferential

variable {R : Type} [CommRing R] (F : C ⥤ CommAlgCat.{0} R)

@[reducible] def Coef.ofAlg : Coef C where
  obj T := F.obj T
  map φ := (mp F φ : F.obj _ →+* F.obj _).toAddMonoidHom
  map_id := mp_id F
  map_comp := mp_comp F

@[reducible] def Cx.dR : Cx C where
  M0 := Coef.ofAlg F
  M1 := ⟨fun T ↦ Ω[F.obj T⁄R], fun φ ↦ (p1 F φ).toAddMonoidHom, fun _ ↦ oneFormsMapOfFunctorMorphism_id F, fun φ ψ ↦ oneFormsMapOfFunctorMorphism_comp F φ ψ⟩
  M2 := ⟨fun T ↦ Om R (F.obj T) 2, fun φ ↦ (pOm F 2 φ).toAddMonoidHom, fun _ ↦ pOm_id F, fun φ ψ ↦ pOm_comp F φ ψ⟩
  M3 := ⟨fun T ↦ Om R (F.obj T) 3, fun φ ↦ (pOm F 3 φ).toAddMonoidHom, fun _ ↦ pOm_id F, fun φ ψ ↦ pOm_comp F φ ψ⟩
  d0 T := (D R (F.obj T)).toLinearMap.toAddMonoidHom
  d1 T := (dOne R (F.obj T)).toAddMonoidHom
  d2 T := (dTwo R (F.obj T)).toAddMonoidHom
  diffZero_natural φ x := (p1_D F φ x).symm
  diffOne_natural φ x := (pOm_dOne F φ x).symm
  diffTwo_natural φ x := (pOm_dTwo F φ x).symm
  diffOne_diffZero _ := dOne_D
  diffTwo_comp_diffOne _ := dTwo_dOne

end Alg

def JoinedOne.{a, b} : Prop := ∀ {C : Type a} [Category.{0} C] {C' : Type b} [Category.{0} C'] {K : Cx C} {K' : Cx C'}
  (m m' : CxMap K K') (θ : m.G ⟶ m'.G), m.Joined m' θ → (∀ c, m.h0 c = m'.h0 c) ∧ ∀ c, m.h1 c = m'.h1 c

def JoinedTwo.{a, b} : Prop := ∀ {C : Type a} [Category.{0} C] {C' : Type b} [Category.{0} C'] {K : Cx C} {K' : Cx C'}
  (m m' : CxMap K K') (θ : m.G ⟶ m'.G), m.Joined m' θ → ∀ c, m.h2 c = m'.h2 c

def VertHas.{a, b} (p : ∀ {C' : Type b} [Category.{0} C'] {K K' : Cx C'}, CxMap K K' → Prop) : Prop :=
  ∀ {C : Type a} [Category.{0} C] {C' : Type b} [Category.{0} C'] {K : Cx C} {K' : Cx C'} (m : CxMap K K'),
    m.QAll → p m.vert

end GlobalTheory.CxCoh
