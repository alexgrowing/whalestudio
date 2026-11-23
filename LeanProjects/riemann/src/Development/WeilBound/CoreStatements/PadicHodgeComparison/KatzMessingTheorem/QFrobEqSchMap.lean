import Development.WeilBound.CoreStatements.PadicHodgeComparison.KatzMessingTheorem.KatzMessingT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison

namespace CompanionTheory.KM.Cris

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [Fintype k] [CharP k p]

abbrev DX {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) : Type 1 :=
  Wc.D p (B.schFn q) (RingHom.id k) n

abbrev Dcr (Y : Var k) (n : ℕ) : Type 1 := DX p Y.s n

def pullX {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of k)} {q' : X' ⟶ Spec (CommRingCat.of k)} (u : X ⟶ X')
    (hu : u ≫ q' = q) (n : ℕ) : DX p q' n →ₗ[Wc.K₀ p k] DX p q n :=
  Wc.pullD p (RingHom.id k) (B.schMap u hu) n

omit [Fact p.Prime] [Fintype k] in

theorem p_zero {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k)) {B₀ : CommRingCat.{0}} (y : Spec B₀ ⟶ X) :
    ((p : ℕ) : B₀) = 0 := by
  let g : k →+* B₀ := (Scheme.ΓSpecIso B₀).hom.hom.comp
    (((y ≫ q).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
  rw [← map_natCast g, CharP.cast_eq_zero, map_zero]

def frbq (f : ℕ) {B₀ : Type} [CommRing B₀] (h : ((p : ℕ) : B₀) = 0) : B₀ →+* B₀ := Wc.frb (l := p) h ^ f

theorem frbq_apply (f : ℕ) {B₀ : Type} [CommRing B₀] (h : ((p : ℕ) : B₀) = 0) (x : B₀) : frbq p f h x = x ^ p ^ f := by
  induction f generalizing x with
  | zero =>
    unfold frbq
    rw [pow_zero, pow_zero, pow_one]
    rfl
  | succ n ih =>
    have e : frbq p (n + 1) h x = frbq p n h (Wc.frb h x) := by
      unfold frbq
      rw [pow_succ]
      rfl
    rw [e, ih]
    change (x ^ p) ^ p ^ n = _
    rw [← pow_mul, ← pow_succ']

variable {p}

def qFrob {f : ℕ} (hq : Fintype.card k = p ^ f) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k)) :
    B.Fn.Map (B.schFn q) (B.schFn q) where
  u := { app := fun B₀ => TypeCat.ofHom fun (y : Spec B₀ ⟶ X) =>
            Spec.map (CommRingCat.ofHom (frbq p f (p_zero p q y))) ≫ y
         naturality := fun B₀ B₁ φ => by
           ext y
           change Spec.map (CommRingCat.ofHom (frbq p f (p_zero p q (Spec.map φ ≫ y)))) ≫ (Spec.map φ ≫ y) =
             Spec.map φ ≫ (Spec.map (CommRingCat.ofHom (frbq p f (p_zero p q y))) ≫ y)
           rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
           congr 2
           ext x
           simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, frbq_apply, map_pow] }
  ov {B₀ y g} h := by
    change (Spec.map (CommRingCat.ofHom (frbq p f (p_zero p q y))) ≫ y) ≫ q = Spec.map (CommRingCat.ofHom g)
    rw [Category.assoc, h, ← Spec.map_comp]
    congr 2
    ext x
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, frbq_apply, ← map_pow, ← hq,
      FiniteField.pow_card]

theorem qFrob_eq_schMap {f : ℕ} (hq : Fintype.card k = p ^ f) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k))
    (u : X ⟶ X) (hu : u ≫ q = q)
    (hF : ∀ (B₀ : CommRingCat.{0}) (y : Spec B₀ ⟶ X), y ≫ u = Spec.map (CommRingCat.ofHom (frbq p f (p_zero p q y))) ≫ y) :
    qFrob hq q = B.schMap u hu := by
  have e : (qFrob hq q).u = (B.schMap u hu).u := by
    ext B₀ y
    exact (hF B₀ y).symm
  cases h : qFrob hq q
  cases h' : B.schMap u hu
  rw [h, h'] at e
  cases e
  rfl

variable (p)

def frobD {f : ℕ} (hq : Fintype.card k = p ^ f) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    DX p q n →ₗ[Wc.K₀ p k] DX p q n :=
  Wc.pullD p (RingHom.id k) (qFrob hq q) n

variable (k)

def FrobPhi : Prop :=
  ∀ {f : ℕ} (hq : Fintype.card k = p ^ f) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) (x : DX p q n),
    frobD p hq q n x = (Wc.phiD p (B.schFn q) (RingHom.id k) n)^[f] x

def PullFrob : Prop :=
  ∀ {f : ℕ} (hq : Fintype.card k = p ^ f) {X X' : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k))
    (q' : X' ⟶ Spec (CommRingCat.of k)) (u : X ⟶ X') (hu : u ≫ q' = q) (n : ℕ) (x : DX p q' n),
    pullX p u hu n (frobD p hq q' n x) = frobD p hq q n (pullX p u hu n x)

def PullComp : Prop :=
  ∀ {X X' X'' : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k)) (q' : X' ⟶ Spec (CommRingCat.of k))
    (q'' : X'' ⟶ Spec (CommRingCat.of k)) (u : X ⟶ X') (v : X' ⟶ X'') (hu : u ≫ q' = q) (hv : v ≫ q'' = q') (n : ℕ)
    (x : DX p q'' n), pullX p u hu n (pullX p v hv n x) = pullX p (u ≫ v) (by rw [Category.assoc, hv, hu]) n x

abbrev Push : Type 1 :=
  ∀ {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of k)} {q' : X' ⟶ Spec (CommRingCat.of k)} (g : X ⟶ X')
    (_ : g ≫ q' = q), IsFinite g → Etale g → ∀ n : ℕ, DX p q n →ₗ[Wc.K₀ p k] DX p q' n

variable {k}

def PushFrob (push : Push p k) : Prop :=
  ∀ {f : ℕ} (hq : Fintype.card k = p ^ f) {X X' : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k))
    (q' : X' ⟶ Spec (CommRingCat.of k)) (g : X ⟶ X') (hg : g ≫ q' = q) (hfin : IsFinite g) (het : Etale g) (n : ℕ)
    (x : DX p q n), push g hg hfin het n (frobD p hq q n x) = frobD p hq q' n (push g hg hfin het n x)

def actD (push : Push p k) {Y : Var k} (c : Corr Y) (n : ℕ) : Dcr p Y n →ₗ[Wc.K₀ p k] Dcr p Y n :=
  push c.c₂ c.base.symm c.fin₂ c.et₂ n ∘ₗ pullX p c.c₁ rfl n

variable (k)

class FinDim : Prop where
  fin : ∀ (Y : Var k) (n : ℕ), FiniteDimensional (Wc.K₀ p k) (Dcr p Y n)

def Vanish : Prop := ∀ Y : Var k, ∃ N : ℕ, ∀ n, N < n → Subsingleton (Dcr p Y n)

variable {k}

instance [h : FinDim p k] (Y : Var k) (n : ℕ) : FiniteDimensional (Wc.K₀ p k) (Dcr p Y n) := h.fin Y n

instance [FinDim p k] (Y : Var k) (n : ℕ) : Small.{0} (Dcr p Y n) := Module.Finite.small.{0} (Wc.K₀ p k) _

abbrev HS [FinDim p k] (Y : Var k) (n : ℕ) : Type := Shrink.{0} (Dcr p Y n)

def eS [FinDim p k] (Y : Var k) (n : ℕ) : HS p Y n ≃ₗ[Wc.K₀ p k] Dcr p Y n := Shrink.linearEquiv (Wc.K₀ p k) (Dcr p Y n)

def conjS [FinDim p k] {Y : Var k} {n : ℕ} (L : Dcr p Y n →ₗ[Wc.K₀ p k] Dcr p Y n) : HS p Y n →ₗ[Wc.K₀ p k] HS p Y n :=
  (eS p Y n).symm.toLinearMap ∘ₗ L ∘ₗ (eS p Y n).toLinearMap

theorem conjS_comp [FinDim p k] {Y : Var k} {n : ℕ} (L M : Dcr p Y n →ₗ[Wc.K₀ p k] Dcr p Y n) :
    conjS p L ∘ₗ conjS p M = conjS p (L ∘ₗ M) := by
  ext x
  simp [conjS]

def model [FinDim p k] {f : ℕ} (hq : Fintype.card k = p ^ f) (push : Push p k) (hV : Vanish p k) (hP : PullFrob p k)
    (hT : PushFrob p push) : CohModel (k := k) (Wc.K₀ p k) where
  H Y n := HS p Y n
  top Y := Classical.choose (hV Y)
  vanish Y n hn := by
    have := Classical.choose_spec (hV Y) n hn
    exact (eS p Y n).toEquiv.subsingleton
  frob Y n := conjS p (frobD p hq Y.s n)
  act c n := conjS p (actD p push c n)
  comm c n := by
    rw [conjS_comp, conjS_comp]
    congr 1
    ext x
    simp only [actD, LinearMap.comp_apply]
    rw [hP hq _ _ c.c₁ rfl n x, hT hq _ _ c.c₂ c.base.symm c.fin₂ c.et₂ n]

end CompanionTheory.KM.Cris
