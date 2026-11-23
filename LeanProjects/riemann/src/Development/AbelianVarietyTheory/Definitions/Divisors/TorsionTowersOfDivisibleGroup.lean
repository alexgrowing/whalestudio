import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct Coalgebra Bialgebra WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent OAct IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open ReciprocityTheory.ChartRestriction.G.Semi (Gm)
open GlobalTheory.DeRham (spOver spOver_comp GrpMor)
open GlobalTheory.Cris (dp0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace PDiv

variable {O O' : Type} [CommRing O] [CommRing O']

abbrev SpAlg (O B : Type) [CommRing O] [CommRing B] [Algebra O B] : Over (Sp O) :=
  Over.mk (spMap (algebraMap O B))

@[simp] theorem spOver_id (B : Type) [CommRing B] [Algebra O B] :
    spOver (AlgHom.id O B) = 𝟙 (SpAlg O B) :=
  Over.OverMorphism.ext (Cris.spMap_id B)

theorem spOver_left {B C : Type} [CommRing B] [Algebra O B] [CommRing C] [Algebra O C]
    (φ : B →ₐ[O] C) : (spOver φ).left = spMap (φ : B →+* C) := rfl

section Down

variable {R R' : Type} [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'}
  {κ : DividedPowers I} {κ' : DividedPowers I'} {u : Sp O ⟶ Sp R} {u' : Sp O' ⟶ Sp R'}
  {ρ : R →+* R'} {σ : O →+* O'} {A : Over (Sp O)} [GrpObj A] {A' : Over (Sp O')} [GrpObj A']
  {φ : A'.left ⟶ A.left}

def ptsDown (m : GrpMor κ u A κ' u' A' ρ (spMap σ) φ) (B : Type) [CommRing B] [Algebra O B]
    [Algebra O' B] (hB : ∀ r, algebraMap O B r = algebraMap O' B (σ r)) :
    (SpAlg O' B ⟶ A') →* (SpAlg O B ⟶ A) :=
  have e : spMap (algebraMap O' B) ≫ spMap σ = spMap (algebraMap O B) := by
    rw [← Cris.spMap_comp]; exact congrArg spMap (RingHom.ext hB).symm
  MonoidHom.mk' (fun z => Over.homMk (z.left ≫ φ) (by
      rw [Category.assoc, m.w, ← Category.assoc, Over.w]; exact e))
    fun x y => Over.OverMorphism.ext (by
      let j : Over.mk ((SpAlg O' B).hom ≫ spMap σ) ⟶ SpAlg O B := Over.homMk (𝟙 _) (by
        rw [Category.id_comp]; exact e.symm)
      have key : ∀ x₀ y₀ : SpAlg O B ⟶ A, x₀.left = x.left ≫ φ → y₀.left = y.left ≫ φ →
          (x * y).left ≫ φ = (x₀ * y₀).left := fun x₀ y₀ hx hy => by
        have h := m.mul _ x y (j ≫ x₀) (j ≫ y₀) ((Category.id_comp _).trans hx)
          ((Category.id_comp _).trans hy)
        rw [← MonObj.comp_mul] at h
        exact h.symm.trans (Category.id_comp _)
      exact key _ _ rfl rfl)

@[simp] theorem ptsDown_left (m : GrpMor κ u A κ' u' A' ρ (spMap σ) φ) (B : Type) [CommRing B]
    [Algebra O B] [Algebra O' B] (hB : ∀ r, algebraMap O B r = algebraMap O' B (σ r))
    (z : SpAlg O' B ⟶ A') : (ptsDown m B hB z).left = z.left ≫ φ := rfl

theorem grpMor_of_isGrpPullback (h : IsGrpPullback A' A (spMap σ) φ) :
    GrpMor (dp0 O) (𝟙 _) A (dp0 O') (𝟙 _) A' σ (spMap σ) φ :=
  GrpMor.of_isGrpPullback (Cris.isDPMorphism_of_eq_bot _ rfl _ _) (by simp) h

theorem ptsDown_bijective (m : GrpMor κ u A κ' u' A' ρ (spMap σ) φ)
    (h : IsPullback φ A'.hom A.hom (spMap σ)) (B : Type) [CommRing B]
    [Algebra O B] [Algebra O' B] (hB : ∀ r, algebraMap O B r = algebraMap O' B (σ r)) :
    Function.Bijective (ptsDown m B hB) := by
  refine ⟨fun x y e => Over.OverMorphism.ext (h.hom_ext (congrArg Over.Hom.left e)
    ((Over.w x).trans (Over.w y).symm)), fun z => ?_⟩
  have e : z.left ≫ A.hom = spMap (algebraMap O' B) ≫ spMap σ := by
    rw [Over.w, ← Cris.spMap_comp]; exact congrArg spMap (RingHom.ext hB)
  exact ⟨Over.homMk (h.lift _ _ e) (h.lift_snd _ _ e), Over.OverMorphism.ext (h.lift_fst _ _ e)⟩

end Down

section Gm

variable {B C : Type} [CommRing B] [Algebra O B] [CommRing C] [Algebra O C]

def gmCoord (z : SpAlg O B ⟶ Gm (Sp O)) : B := Diag.charVal z (ULift.up 1)

theorem gmCoord_comp (φ : B →ₐ[O] C) (z : SpAlg O B ⟶ Gm (Sp O)) :
    gmCoord (spOver φ ≫ z) = φ (gmCoord z) :=
  (Diag.left_eq_iff (φ : B →+* C) (Over.w (spOver φ)).symm (spOver φ ≫ z) z).1 rfl _

def gmCoordHom : (SpAlg O B ⟶ Gm (Sp O)) →* B where
  toFun := gmCoord
  map_one' := Diag.charVal_one _
  map_mul' x y := Diag.charVal_mul x y _

theorem gmCoord_ext {x y : SpAlg O B ⟶ Gm (Sp O)} (h : gmCoord x = gmCoord y) : x = y := by
  let f : (SpAlg O B ⟶ Gm (Sp O)) → (Multiplicative ℤ →* Bˣ) := fun z => MonoidHom.toHomUnits
    { toFun := fun k => Diag.charVal z (ULift.up k.toAdd)
      map_one' := Diag.charVal_zero z
      map_mul' := fun k l => Diag.charVal_add z ⟨k.toAdd⟩ ⟨l.toAdd⟩ }
  have e : f x = f y := MonoidHom.ext_mint (Units.ext h)
  exact Diag.charVal_ext fun k =>
    congrArg (fun g : Multiplicative ℤ →* Bˣ => (g (Multiplicative.ofAdd k.down) : B)) e

variable (O) in

def gmPoint (u : Bˣ) : SpAlg O B ⟶ Gm (Sp O) :=
  Diag.ofVal _ ((Units.coeHom B).comp ((zpowersHom Bˣ u).comp
    (AddMonoidHom.toMultiplicative (AddEquiv.ulift : ULift.{0} ℤ ≃+ ℤ).toAddMonoidHom)))

@[simp] theorem gmCoord_gmPoint (u : Bˣ) : gmCoord (gmPoint O u) = u :=
  (Diag.charVal_ofVal _ _).trans (congrArg Units.val (zpow_one u))

end Gm

end PDiv

namespace PDivGroup

open PDiv

variable {p : ℕ} {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O'']

@[ext] structure TorsionTower (G : PDivGroup p O) (A : Over (Sp O)) [GrpObj A] : Type where

  y : ∀ n, SpAlg O (G.A n) ⟶ A

  mul : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra O B] (φ ψ : WithConv (G.A n →ₐ[O] B)),
    spOver (φ * ψ).ofConv ≫ y n = (spOver φ.ofConv ≫ y n) * (spOver ψ.ofConv ≫ y n)

  inj : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra O B] (φ ψ : G.A n →ₐ[O] B),
    spOver φ ≫ y n = spOver ψ ≫ y n → φ = ψ

  surj : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra O B] (z : SpAlg O B ⟶ A),
    z ^ p ^ n = 1 → ∃ φ : G.A n →ₐ[O] B, spOver φ ≫ y n = z

  res : ∀ n, spOver (G.res n : G.A (n + 1) →ₐ[O] G.A n) ≫ y (n + 1) = y n

section Mu

variable (p O) [Fact p.Prime]

def muIncl (n : ℕ) : SpAlg O ((mu p O).A n) ⟶ Gm (Sp O) :=
  gmPoint O (Units.ofPowEqOne (muT O (p ^ n)) (p ^ n) (muT_pow_self O _) (NeZero.ne _))

variable {p O} in

theorem gmCoord_muIncl {n : ℕ} {B : Type} [CommRing B] [Algebra O B]
    (φ : (mu p O).A n →ₐ[O] B) : gmCoord (spOver φ ≫ muIncl p O n) = φ (muT O (p ^ n)) := by
  rw [gmCoord_comp, muIncl, gmCoord_gmPoint]; rfl

def muTower : (mu p O).TorsionTower (Gm (Sp O)) where
  y := muIncl p O
  mul n B _ _ φ ψ := gmCoord_ext <| by
    refine Eq.trans ?_ (map_mul gmCoordHom _ _).symm
    exact (gmCoord_muIncl _).trans ((convMul_apply_groupLike φ ψ (isGroupLikeElem_muT O _)).trans
      (congrArg₂ (· * ·) (gmCoord_muIncl _) (gmCoord_muIncl _)).symm)
  inj n B _ _ φ ψ h := mu_algHom_ext
    ((gmCoord_muIncl φ).symm.trans ((congrArg gmCoord h).trans (gmCoord_muIncl ψ)))
  surj n B _ _ z hz := by
    have h : gmCoord z ^ p ^ n = 1 :=
      (map_pow gmCoordHom z _).symm.trans ((congrArg gmCoordHom hz).trans (map_one _))
    exact ⟨muPoint O _ h, gmCoord_ext ((gmCoord_muIncl _).trans (muPoint_muT _ h))⟩
  res n := gmCoord_ext <| by
    rw [gmCoord_muIncl, muIncl, gmCoord_gmPoint]
    exact muRes_muT p O n

variable {p O} in

theorem gmCoord_muTower {n : ℕ} {B : Type} [CommRing B] [Algebra O B]
    (φ : (mu p O).A n →ₐ[O] B) :
    gmCoord (spOver φ ≫ (muTower p O).y n) = φ (muT O (p ^ n)) := gmCoord_muIncl φ

end Mu

namespace TorsionTower

variable {G H K : PDivGroup p O} {A A₁ A₂ : Over (Sp O)} [GrpObj A] [GrpObj A₁] [GrpObj A₂]

section Basic

variable (t : G.TorsionTower A) (n : ℕ) (B : Type) [CommRing B] [Algebra O B]

def pts : WithConv (G.A n →ₐ[O] B) →* (SpAlg O B ⟶ A) :=
  MonoidHom.mk' (fun φ => spOver φ.ofConv ≫ t.y n) (t.mul n B)

variable {B} in

@[simp] theorem pts_apply (φ : WithConv (G.A n →ₐ[O] B)) :
    t.pts n B φ = spOver φ.ofConv ≫ t.y n := rfl

theorem pts_injective : Function.Injective (t.pts n B) := fun _ _ h =>
  ofConv_injective (t.inj n B _ _ h)

variable {B}

theorem exists_iff (z : SpAlg O B ⟶ A) :
    (∃ φ : G.A n →ₐ[O] B, spOver φ ≫ t.y n = z) ↔ z ^ p ^ n = 1 := by
  refine ⟨?_, t.surj n B z⟩
  rintro ⟨φ, rfl⟩
  rw [← ofConv_toConv φ, ← pts_apply, ← map_pow, G.pts_pow_self, map_one]

variable (B) in

theorem range_pts : Set.range (t.pts n B) = {z | z ^ p ^ n = 1} :=
  Set.ext fun z => Iff.trans ⟨fun ⟨φ, h⟩ => ⟨φ.ofConv, h⟩, fun ⟨φ, h⟩ => ⟨toConv φ, h⟩⟩
    (t.exists_iff n z)

theorem y_pow : t.y n ^ p ^ n = 1 :=
  (t.exists_iff n _).1 ⟨AlgHom.id O _, by rw [spOver_id, Category.id_comp]⟩

def lift (z : SpAlg O B ⟶ A) (hz : z ^ p ^ n = 1) : G.A n →ₐ[O] B := (t.surj n B z hz).choose

@[simp] theorem lift_y (z : SpAlg O B ⟶ A) (hz : z ^ p ^ n = 1) :
    spOver (t.lift n z hz) ≫ t.y n = z := (t.surj n B z hz).choose_spec

theorem eq_one_iff (φ : G.A n →ₐ[O] B) :
    spOver φ ≫ t.y n = 1 ↔ ∀ a, φ a = algebraMap O B (counit a) := by
  rw [← map_one (t.pts n B), ← ofConv_toConv φ, ← pts_apply, (t.pts_injective n B).eq_iff]
  exact ⟨fun h a => DFunLike.congr_fun (congrArg ofConv h) a,
    fun h => ofConv_injective (AlgHom.ext h)⟩

theorem mulBy_y (k : ℕ) :
    spOver (mulBy O (G.A n) k : G.A n →ₐ[O] G.A n) ≫ t.y n = t.y n ^ k := by
  have h := map_pow (t.pts n (G.A n)) (toConv (AlgHom.id O _)) k
  rw [pts_apply, pts_apply, ← comp_mulBy_pts, ofConv_toConv, spOver_id, Category.id_comp] at h
  exact h

theorem mulP_y : spOver (G.mulP n : G.A n →ₐ[O] G.A (n + 1)) ≫ t.y n = t.y (n + 1) ^ p := by
  rw [← t.res n, ← Category.assoc, spOver_comp, ← t.mulBy_y, ← G.mulP_comp_res]
  rfl

def ofIso (e : H ≅ G) : H.TorsionTower A where
  y n := spOver (e.hom.app n : G.A n →ₐ[O] H.A n) ≫ t.y n
  mul n B _ _ φ ψ := by
    simp only [← Category.assoc, spOver_comp]
    exact (congrArg (t.pts n B) (map_mul (pointsMap B (e.hom.app n)) φ ψ)).trans (map_mul _ _ _)
  inj n B _ _ φ ψ h := by
    simp only [← Category.assoc, spOver_comp] at h
    refine AlgHom.ext fun a => ?_
    have h1 := DFunLike.congr_fun (t.inj n B _ _ h) (e.inv.app n a)
    have h2 : e.hom.app n (e.inv.app n a) = a :=
      DFunLike.congr_fun (congrArg (Hom.app · n) e.hom_inv_id) a
    exact (congrArg φ h2).symm.trans (h1.trans (congrArg ψ h2))
  surj n B _ _ z hz := ⟨(t.lift n z hz).comp (e.inv.app n), by
    rw [← Category.assoc, spOver_comp]
    refine Eq.trans (congrArg (spOver · ≫ t.y n) (AlgHom.ext fun a => ?_)) (t.lift_y n z hz)
    exact congrArg (t.lift n z hz) (DFunLike.congr_fun (congrArg (Hom.app · n) e.inv_hom_id) a)⟩
  res n := by
    rw [← t.res n, ← Category.assoc, ← Category.assoc, spOver_comp, spOver_comp]
    congr 2
    exact AlgHom.ext (res_app e.hom n)

end Basic

section Semi

variable {R R' : Type} [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'}
  {κ : DividedPowers I} {κ' : DividedPowers I'} {u : Sp O ⟶ Sp R} {u' : Sp O' ⟶ Sp R'}
  {ρ : R →+* R'} {σ : O →+* O'} {G' : PDivGroup p O'} {A' : Over (Sp O')} [GrpObj A']
  {φ : A'.left ⟶ A.left} (t' : G'.TorsionTower A') (t : G.TorsionTower A)

theorem ringHom_ext {n : ℕ} {B : Type} [CommRing B] {f g : G.A n →+* B}
    (h : spMap f ≫ (t.y n).left = spMap g ≫ (t.y n).left) : f = g := by
  let _ : Algebra O B := (f.comp (algebraMap O _)).toAlgebra
  have e : g.comp (algebraMap O (G.A n)) = f.comp (algebraMap O _) := by
    have h1 := congrArg (· ≫ A.hom) h
    simp only [Category.assoc, Over.w] at h1
    have h2 : spMap (f.comp (algebraMap O _)) = spMap (g.comp (algebraMap O (G.A n))) := by
      rw [Cris.spMap_comp, Cris.spMap_comp]; exact h1
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2).symm
  exact congrArg AlgHom.toRingHom (t.inj n B { f with commutes' := fun _ => rfl }
    { g with commutes' := RingHom.congr_fun e } (Over.OverMorphism.ext h))

theorem exists_ringHom (m : GrpMor κ u A κ' u' A' ρ (spMap σ) φ) (n : ℕ) :
    ∃ g : G.A n →+* G'.A n, (∀ r, g (algebraMap O _ r) = algebraMap O' _ (σ r)) ∧
      spMap g ≫ (t.y n).left = (t'.y n).left ≫ φ := by
  let _ : Algebra O (G'.A n) := ((algebraMap O' _).comp σ).toAlgebra
  obtain ⟨g, hg⟩ := t.surj n (G'.A n) (ptsDown m _ (fun _ => rfl) (t'.y n))
    (by rw [← map_pow, t'.y_pow, map_one])
  exact ⟨g, g.commutes, congrArg Over.Hom.left hg⟩

theorem pts_eq_ptsDown (m : GrpMor κ u A κ' u' A' ρ (spMap σ) φ) {n : ℕ} {g : G.A n →+* G'.A n}
    (hg : spMap g ≫ (t.y n).left = (t'.y n).left ≫ φ) {B : Type} [CommRing B] [Algebra O B]
    [Algebra O' B] (hB : ∀ r, algebraMap O B r = algebraMap O' B (σ r))
    (x : WithConv (G'.A n →ₐ[O'] B)) (x₀ : WithConv (G.A n →ₐ[O] B)) :
    t.pts n B x₀ = ptsDown m B hB (t'.pts n B x) ↔ ∀ a, x₀.ofConv a = x.ofConv (g a) := by
  have e : (ptsDown m B hB (t'.pts n B x)).left =
      spMap ((x.ofConv : G'.A n →+* B).comp g) ≫ (t.y n).left := by
    rw [Cris.spMap_comp, Category.assoc, hg]; exact Category.assoc _ _ _
  constructor
  · intro h
    exact RingHom.congr_fun (t.ringHom_ext ((congrArg Over.Hom.left h).trans e))
  · intro h
    refine Over.OverMorphism.ext (Eq.trans ?_ e.symm)
    rw [← show (x₀.ofConv : G.A n →+* B) = (x.ofConv : G'.A n →+* B).comp g from RingHom.ext h]
    rfl

def semiOf (m : GrpMor κ u A κ' u' A' ρ (spMap σ) φ) : SemiHom σ G' G where
  app n :=
    have h := (t'.exists_ringHom t m n).choose_spec
    .ofPts (t'.exists_ringHom t m n).choose h.1
      (fun a => by
        let _ : Algebra O O' := σ.toAlgebra
        exact ((t'.pts_eq_ptsDown t m h.2 (B := O') (fun _ => rfl) 1 1).1
          (by rw [map_one, map_one, map_one]) a).symm)
      fun B _ _ _ hB x y x₀ y₀ hx hy => (t'.pts_eq_ptsDown t m h.2 hB _ _).1 (by
        rw [map_mul, map_mul, map_mul, (t'.pts_eq_ptsDown t m h.2 hB _ _).2 hx,
          (t'.pts_eq_ptsDown t m h.2 hB _ _).2 hy])
  res_app n := by
    have h := fun n => (t'.exists_ringHom t m n).choose_spec.2
    refine RingHom.congr_fun (t.ringHom_ext (n := n + 1)
      (f := (G'.res n : G'.A (n + 1) →+* G'.A n).comp (t'.exists_ringHom t m (n + 1)).choose)
      (g := (t'.exists_ringHom t m n).choose.comp (G.res n : G.A (n + 1) →+* G.A n)) ?_)
    rw [Cris.spMap_comp, Cris.spMap_comp, Category.assoc, Category.assoc, h, ← Category.assoc]
    exact (congrArg (·.left ≫ φ) (t'.res n)).trans ((h n).symm.trans
      (congrArg (_ ≫ ·.left) (t.res n)).symm)

theorem semiOf_y (m : GrpMor κ u A κ' u' A' ρ (spMap σ) φ) (n : ℕ) :
    spMap ((t'.semiOf t m).app n).toRingHom ≫ (t.y n).left = (t'.y n).left ≫ φ :=
  (t'.exists_ringHom t m n).choose_spec.2

theorem eq_semiOf_iff (m : GrpMor κ u A κ' u' A' ρ (spMap σ) φ) (s : SemiHom σ G' G) :
    s = t'.semiOf t m ↔ ∀ n, spMap (s.app n).toRingHom ≫ (t.y n).left = (t'.y n).left ≫ φ :=
  ⟨fun h => h ▸ t'.semiOf_y t m, fun h => SemiHom.ext_apply fun n =>
    RingHom.congr_fun (t.ringHom_ext ((h n).trans (t'.semiOf_y t m n).symm))⟩

abbrev semiHom (m : GrpMor (dp0 O) (𝟙 _) A (dp0 O') (𝟙 _) A' σ (spMap σ) φ) : SemiHom σ G' G :=
  t'.semiOf t m

theorem semiOf_semiOf {τ : O' →+* O''} {υ : O →+* O''} {G'' : PDivGroup p O''}
    {A'' : Over (Sp O'')} [GrpObj A''] {ψ : A''.left ⟶ A'.left} (t'' : G''.TorsionTower A'')
    {s : SemiHom σ G' G} {s' : SemiHom τ G'' G'} {s'' : SemiHom υ G'' G}
    (h : ∀ n, spMap (s.app n).toRingHom ≫ (t.y n).left = (t'.y n).left ≫ φ)
    (h' : ∀ n, spMap (s'.app n).toRingHom ≫ (t'.y n).left = (t''.y n).left ≫ ψ)
    (h'' : ∀ n, spMap (s''.app n).toRingHom ≫ (t.y n).left = (t''.y n).left ≫ ψ ≫ φ)
    (n : ℕ) (a : G.A n) : s''.app n a = s'.app n (s.app n a) :=
  RingHom.congr_fun (t.ringHom_ext (g := (s'.app n).toRingHom.comp (s.app n).toRingHom) (by
    rw [Cris.spMap_comp, Category.assoc, h, h'', ← Category.assoc, ← Category.assoc, h'])) a

end Semi

section Map

variable (t : G.TorsionTower A) (t₁ : H.TorsionTower A₁) (t₂ : K.TorsionTower A₂)

theorem _root_.GlobalTheory.PDiv.grpMor_of_hom (f : A ⟶ A₁) [IsMonHom f] :
    GrpMor (dp0 O) (𝟙 _) A₁ (dp0 O) (𝟙 _) A (RingHom.id O) (spMap (RingHom.id O)) f.left := by
  rw [Cris.spMap_id]; exact DeRham.homMor _ _ f

def map (f : A ⟶ A₁) [IsMonHom f] : G ⟶ H := (t.semiHom t₁ (grpMor_of_hom f)).toHom

theorem map_y (f : A ⟶ A₁) [IsMonHom f] (n : ℕ) :
    spOver ((t.map t₁ f).app n : H.A n →ₐ[O] G.A n) ≫ t₁.y n = t.y n ≫ f :=
  Over.OverMorphism.ext (t.semiOf_y t₁ (grpMor_of_hom f) n)

theorem hom_ext_y {g g' : G ⟶ H} (h : ∀ n, spOver (g.app n : H.A n →ₐ[O] G.A n) ≫ t₁.y n =
    spOver (g'.app n : H.A n →ₐ[O] G.A n) ≫ t₁.y n) : g = g' :=
  hom_ext fun n => BialgHom.coe_toAlgHom_injective (t₁.inj n _ _ _ (h n))

theorem eq_map_iff (f : A ⟶ A₁) [IsMonHom f] (g : G ⟶ H) :
    g = t.map t₁ f ↔ ∀ n, spOver (g.app n : H.A n →ₐ[O] G.A n) ≫ t₁.y n = t.y n ≫ f :=
  ⟨fun h => h ▸ t.map_y t₁ f, fun h => t₁.hom_ext_y fun n => (h n).trans (t.map_y t₁ f n).symm⟩

theorem map_congr {f g : A ⟶ A₁} [IsMonHom f] [IsMonHom g] (e : f = g) :
    t.map t₁ f = t.map t₁ g := by subst e; rfl

@[simp] theorem map_id : t.map t (𝟙 A) = 𝟙 G :=
  ((t.eq_map_iff t _ _).2 fun n => by
    rw [Category.comp_id]; exact (congrArg (· ≫ t.y n) (spOver_id _)).trans (Category.id_comp _)).symm

theorem map_comp (f : A ⟶ A₁) (g : A₁ ⟶ A₂) [IsMonHom f] [IsMonHom g] :
    t.map t₂ (f ≫ g) = t.map t₁ f ≫ t₁.map t₂ g :=
  ((t.eq_map_iff t₂ _ _).2 fun n => by
    rw [← Category.assoc, ← t.map_y t₁, Category.assoc, ← t₁.map_y t₂, ← Category.assoc,
      spOver_comp]
    rfl).symm

theorem map_mul (f g : A ⟶ A₁) [IsMonHom f] [IsMonHom g] [IsMonHom (f * g)] :
    t.map t₁ (f * g) = t.map t₁ f + t.map t₁ g :=
  ((t.eq_map_iff t₁ _ _).2 fun n => by
    rw [MonObj.comp_mul, ← t.map_y t₁, ← t.map_y t₁]
    exact t₁.mul n _ (toPts ((t.map t₁ f).conv n)) (toPts ((t.map t₁ g).conv n))).symm

theorem map_one [IsMonHom (1 : A ⟶ A₁)] : t.map t₁ 1 = 0 :=
  ((t.eq_map_iff t₁ _ _).2 fun n => by
    rw [MonObj.comp_one]; exact _root_.map_one (t₁.pts n _)).symm

@[simps] def mapIso (e : A ≅ A₁) [IsMonHom e.hom] [IsMonHom e.inv] : G ≅ H where
  hom := t.map t₁ e.hom
  inv := t₁.map t e.inv
  hom_inv_id := by rw [← map_comp, t.map_congr t e.hom_inv_id, map_id]
  inv_hom_id := by rw [← map_comp, t₁.map_congr t₁ e.inv_hom_id, map_id]

@[simps] def uniqueIso (t' : H.TorsionTower A) : G ≅ H where
  hom := t.map t' (𝟙 A)
  inv := t'.map t (𝟙 A)
  hom_inv_id := by rw [← map_comp, t.map_congr t (Category.comp_id _), map_id]
  inv_hom_id := by rw [← map_comp, t'.map_congr t' (Category.comp_id _), map_id]

theorem existsUnique_iso (t' : H.TorsionTower A) : ∃! e : G ≅ H,
    ∀ n, spOver (e.hom.app n : H.A n →ₐ[O] G.A n) ≫ t'.y n = t.y n :=
  ⟨t.uniqueIso t', fun n => (t.map_y t' _ n).trans (Category.comp_id _), fun _ h =>
    Iso.ext ((t.eq_map_iff t' _ _).2 fun n => (h n).trans (Category.comp_id _).symm)⟩

theorem semi_map {σ : O →+* O'} {G' H' : PDivGroup p O'} {A' A₁' : Over (Sp O')} [GrpObj A']
    [GrpObj A₁'] (t' : G'.TorsionTower A') (t₁' : H'.TorsionTower A₁') {φ : A'.left ⟶ A.left}
    {φ₁ : A₁'.left ⟶ A₁.left} {s : SemiHom σ G' G} {s₁ : SemiHom σ H' H}
    (h : ∀ n, spMap (s.app n).toRingHom ≫ (t.y n).left = (t'.y n).left ≫ φ)
    (h₁ : ∀ n, spMap (s₁.app n).toRingHom ≫ (t₁.y n).left = (t₁'.y n).left ≫ φ₁)
    (f : A ⟶ A₁) (f' : A' ⟶ A₁') [IsMonHom f] [IsMonHom f'] (e : φ ≫ f.left = f'.left ≫ φ₁)
    (n : ℕ) (a : H.A n) :
    s.app n ((t.map t₁ f).app n a) = (t'.map t₁' f').app n (s₁.app n a) := by
  refine RingHom.congr_fun (t₁.ringHom_ext
    (f := (s.app n).toRingHom.comp ((t.map t₁ f).app n : H.A n →+* G.A n))
    (g := ((t'.map t₁' f').app n : H'.A n →+* G'.A n).comp (s₁.app n).toRingHom) ?_) a
  have h2 : spMap ((t.map t₁ f).app n : H.A n →+* G.A n) ≫ (t₁.y n).left =
    (t.y n).left ≫ f.left := congrArg Over.Hom.left (t.map_y t₁ f n)
  have h3 : spMap ((t'.map t₁' f').app n : H'.A n →+* G'.A n) ≫ (t₁'.y n).left =
    (t'.y n).left ≫ f'.left := congrArg Over.Hom.left (t'.map_y t₁' f' n)
  rw [Cris.spMap_comp, Cris.spMap_comp, Category.assoc, Category.assoc, h2, h₁, reassoc_of% h,
    reassoc_of% h3, e]

variable [Fact p.Prime]

theorem map_pow_id (k : ℕ) [IsMonHom (𝟙 A ^ k)] : t.map t (𝟙 A ^ k) = (k : ℤ_[p]) • 𝟙 G :=
  ((t.eq_map_iff t _ _).2 fun n => by
    rw [natCast_smul_id_app, mulBy_y, MonObj.comp_pow, Category.comp_id]).symm

def ringAct [IsCommMonObj A] {Λ : Type} [Ring Λ] (a : RingAct A Λ) : Action Λ G :=
  RingHom.mk'
    { toFun x := haveI := a.hom x; t.map t (a.act x)
      map_one' := haveI := a.hom 1; (t.map_congr t a.map_one).trans t.map_id
      map_mul' x y := by
        have := a.hom
        exact (t.map_congr t (a.map_mul x y)).trans (t.map_comp t t _ _) }
    fun x y ↦ by
      have := a.hom
      have e : a.act (x + y) = a.act x * a.act y := a.map_add x y
      have : IsMonHom (a.act x * a.act y) := e ▸ a.hom _
      exact (t.map_congr t e).trans (t.map_mul t _ _)

theorem ringAct_apply [IsCommMonObj A] {Λ : Type} [Ring Λ] (a : RingAct A Λ) (x : Λ)
    [IsMonHom (a.act x)] : t.ringAct a x = t.map t (a.act x) := rfl

def act {Λ : Type} [CommRing Λ] (a : OAct Λ A) : Action Λ G :=
  RingHom.mk'
    { toFun x := haveI := a.hom x; t.map t (a.act x)
      map_one' := haveI := a.hom 1; (t.map_congr t a.one).trans t.map_id
      map_mul' x y := by
        have := a.hom
        exact (t.map_congr t ((congrArg a.act (mul_comm x y)).trans (a.mul y x))).trans
          (t.map_comp t t _ _) }
    fun x y ↦ by
      have := a.hom
      have : IsMonHom (a.act x * a.act y) := a.add x y ▸ a.hom _
      exact (t.map_congr t (a.add x y)).trans (t.map_mul t _ _)

theorem act_apply {Λ : Type} [CommRing Λ] (a : OAct Λ A) (x : Λ) [IsMonHom (a.act x)] :
    t.act a x = t.map t (a.act x) := rfl

def _root_.GlobalTheory.PDivGroup.Action.padicExtend {Λ : Type} [Ring Λ] (ρ : Action Λ G) :
    Action (ℤ_[p] ⊗[ℤ] Λ) G :=
  letI : Algebra ℤ (End G) := Ring.toIntAlgebra _
  (Algebra.TensorProduct.lift (algebraMap ℤ_[p] (End G)).toIntAlgHom (RingHom.toIntAlgHom ρ)
    fun r _ ↦ Algebra.commutes r _).toRingHom

@[simp] theorem _root_.GlobalTheory.PDivGroup.Action.padicExtend_tmul {Λ : Type} [Ring Λ] (ρ : Action Λ G)
    (c : ℤ_[p]) (x : Λ) : ρ.padicExtend (c ⊗ₜ x) = c • ρ x := (Algebra.smul_def c (ρ x)).symm

end Map

section BaseChange

variable [Algebra O O'] {A' : Over (Sp O')} [GrpObj A'] {φ : A'.left ⟶ A.left}
  (t : G.TorsionTower A) (h : IsGrpPullback A' A (spMap (algebraMap O O')) φ)

def baseChangeY (n : ℕ) : SpAlg O' (O' ⊗[O] G.A n) ⟶ A' :=
  ((ptsDown_bijective (grpMor_of_isGrpPullback h) h.1 (O' ⊗[O] G.A n) fun _ => rfl).2
    (spOver Algebra.TensorProduct.includeRight ≫ t.y n)).choose

theorem baseChangeY_left (n : ℕ) : (t.baseChangeY h n).left ≫ φ =
    spMap (toBaseChange O O' (G.A n)).toRingHom ≫ (t.y n).left :=
  congrArg Over.Hom.left ((ptsDown_bijective (grpMor_of_isGrpPullback h) h.1 (O' ⊗[O] G.A n)
    fun _ => rfl).2 (spOver Algebra.TensorProduct.includeRight ≫ t.y n)).choose_spec

theorem ptsDown_baseChangeY (n : ℕ) (B : Type) [CommRing B] [Algebra O B] [Algebra O' B]
    (hB : ∀ r, algebraMap O B r = algebraMap O' B (algebraMap O O' r))
    (x : WithConv (O' ⊗[O] G.A n →ₐ[O'] B)) :
    ptsDown (grpMor_of_isGrpPullback h) B hB (spOver x.ofConv ≫ t.baseChangeY h n) =
      t.pts n B ((toBaseChange O O' (G.A n)).pts B hB x) :=
  Over.OverMorphism.ext (by
    rw [ptsDown_left, Over.comp_left, Category.assoc, baseChangeY_left, spOver_left,
      ← Category.assoc, ← Cris.spMap_comp]
    rfl)

def baseChange : (G.baseChange O').TorsionTower A' where
  y := t.baseChangeY h
  mul n B _ _ x y := by
    let _ : Algebra O B := ((algebraMap O' B).comp (algebraMap O O')).toAlgebra
    refine (ptsDown_bijective (grpMor_of_isGrpPullback h) h.1 B fun _ => rfl).1 ?_
    rw [_root_.map_mul, ptsDown_baseChangeY, ptsDown_baseChangeY, ptsDown_baseChangeY,
      _root_.map_mul, _root_.map_mul]
  inj n B _ _ x y e := by
    let _ : Algebra O B := ((algebraMap O' B).comp (algebraMap O O')).toAlgebra
    have e' := congrArg (ptsDown (grpMor_of_isGrpPullback h) B fun _ => rfl) e
    exact congrArg ofConv ((toBaseChange_pts_bijective O' B _).1 (t.pts_injective n B
      ((t.ptsDown_baseChangeY h n B _ (toConv x)).symm.trans
        (e'.trans (t.ptsDown_baseChangeY h n B _ (toConv y))))))
  surj n B _ _ z hz := by
    let _ : Algebra O B := ((algebraMap O' B).comp (algebraMap O O')).toAlgebra
    obtain ⟨x₀, hx₀⟩ := t.surj n B (ptsDown (grpMor_of_isGrpPullback h) B (fun _ => rfl) z)
      (by rw [← map_pow, hz, _root_.map_one])
    obtain ⟨x, hx⟩ := (toBaseChange_pts_bijective (R := O) O' B fun _ => rfl).2 (toConv x₀)
    exact ⟨x.ofConv, (ptsDown_bijective (grpMor_of_isGrpPullback h) h.1 B fun _ => rfl).1
      (by rw [ptsDown_baseChangeY, hx]; exact hx₀)⟩
  res n := by
    refine Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [Over.comp_left, Category.assoc, baseChangeY_left, baseChangeY_left, ← t.res n,
      Over.comp_left, spOver_left, spOver_left, ← Category.assoc, ← Category.assoc,
      ← Cris.spMap_comp, ← Cris.spMap_comp]
    rfl

theorem toBase_y (n : ℕ) : spMap ((G.toBase O').app n).toRingHom ≫ (t.y n).left =
    ((t.baseChange h).y n).left ≫ φ := (t.baseChangeY_left h n).symm

theorem semiHom_baseChange :
    (t.baseChange h).semiHom t (grpMor_of_isGrpPullback h) = G.toBase O' :=
  (((t.baseChange h).eq_semiOf_iff t (grpMor_of_isGrpPullback h) (G.toBase O')).2
    (t.toBase_y h)).symm

def baseChangeIso {G' : PDivGroup p O'} (t' : G'.TorsionTower A') : G' ≅ G.baseChange O' :=
  t'.uniqueIso (t.baseChange h)

theorem baseChangeIso_hom {G' : PDivGroup p O'} (t' : G'.TorsionTower A') :
    (t.baseChangeIso h t').hom = (t'.semiHom t (grpMor_of_isGrpPullback h)).lift := by
  refine baseChange_hom_ext fun n a => ?_
  rw [SemiHom.lift_app, one_smul]
  have h1 : ∀ n, spMap ((SemiHom.ofHom (t.baseChangeIso h t').hom).app n).toRingHom ≫
      ((t.baseChange h).y n).left = (t'.y n).left ≫ 𝟙 _ := fun n =>
    congrArg Over.Hom.left (t'.map_y (t.baseChange h) (𝟙 A') n)
  have h2 : ∀ n, spMap ((t'.semiHom t (grpMor_of_isGrpPullback h)).app n).toRingHom ≫
      (t.y n).left = (t'.y n).left ≫ 𝟙 _ ≫ φ := fun n => by
    rw [Category.id_comp]; exact t'.semiOf_y t _ n
  exact ((t.baseChange h).semiOf_semiOf t t' (t.toBase_y h) h1 h2 n a).symm

end BaseChange

section Lie

variable (O) in

def _root_.GlobalTheory.PDiv.epsTo (B : Type) [CommRing B] [Algebra O B] :
    DualNumber O →ₐ[O] DualNumber B :=
  { ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap O B) with
    commutes' := fun r => by
      ext <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl'] }

@[simp] theorem _root_.GlobalTheory.PDiv.fst_epsTo (B : Type) [CommRing B] [Algebra O B]
    (z : DualNumber O) : (epsTo O B z).fst = algebraMap O B z.fst := add_zero _

@[simp] theorem _root_.GlobalTheory.PDiv.snd_epsTo (B : Type) [CommRing B] [Algebra O B]
    (z : DualNumber O) : (epsTo O B z).snd = algebraMap O B z.snd := zero_add _

variable (p O) in

abbrev _root_.GlobalTheory.PDiv.ModPow (n : ℕ) : Type := O ⧸ Ideal.span {(p : O) ^ n}

variable (p) in

abbrev _root_.GlobalTheory.PDiv.epsRedPow {A : Over (Sp O)} (n : ℕ) (v : epsR O ⟶ A) :
    SpAlg O (DualNumber (ModPow p O n)) ⟶ A := spOver (epsTo O (ModPow p O n)) ≫ v

theorem _root_.GlobalTheory.PDiv.epsScale_eq (c : O) : GrpTangent.epsScale c =
    spOver (TrivSqZeroExt.map (c • (LinearMap.id : O →ₗ[O] O))) := rfl

theorem _root_.GlobalTheory.PDiv.epsRedPow_pow {v : epsR O ⟶ A} (hv : IsTangent v) (n : ℕ) :
    epsRedPow p n v ^ p ^ n = 1 := by
  have h : spOver (epsTo O (ModPow p O n)) ≫ GrpTangent.epsScale ((p ^ n : ℕ) : O) =
      spOver (epsTo O (ModPow p O n)) ≫ GrpTangent.epsScale 0 := by
    rw [epsScale_eq, epsScale_eq, spOver_comp, spOver_comp]
    refine congrArg spOver (AlgHom.ext fun z => ?_)
    have h0 : (p : ModPow p O n) ^ n = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    ext <;> simp [h0]
  rw [← MonObj.comp_pow, GrpTangent.pow_eq_epsScale_comp hv, ← Category.assoc, h, Category.assoc,
    GrpTangent.epsScale_zero_comp hv, MonObj.comp_one]

variable (t : G.TorsionTower A) (t₁ : H.TorsionTower A₁)

def LieCorr (x : G.Lie) (v : epsR O ⟶ A) : Prop :=
  IsTangent v ∧ ∀ n, ∃ ψ : G.A n →ₐ[O] DualNumber (ModPow p O n),
    spOver ψ ≫ t.y n = epsRedPow p n v ∧
      ∀ (w : G.omega) (a : G.A n), dUnit O a = w.1 n → Ideal.Quotient.mk _ (x w) = (ψ a).snd

variable {v v' : epsR O ⟶ A}

def tanPt (hv : IsTangent v) (n : ℕ) : G.A n →ₐ[O] DualNumber (ModPow p O n) :=
  t.lift n _ (epsRedPow_pow hv n)

theorem tanPt_y (hv : IsTangent v) (n : ℕ) :
    spOver (t.tanPt hv n) ≫ t.y n = epsRedPow p n v := t.lift_y ..

theorem fst_tanPt (hv : IsTangent v) (n : ℕ) (a : G.A n) :
    (t.tanPt hv n a).fst = algebraMap O _ (counit a) := by
  refine (t.eq_one_iff n ((TrivSqZeroExt.fstHom O _ _).comp (t.tanPt hv n))).1 ?_ a
  rw [← spOver_comp, Category.assoc, tanPt_y, ← MonObj.comp_one (spOver
    ((TrivSqZeroExt.fstHom O _ _).comp (epsTo O (ModPow p O n)))),
    ← GrpTangent.epsScale_zero_comp hv, epsScale_eq, ← Category.assoc, ← Category.assoc,
    spOver_comp, spOver_comp]
  exact congrArg (spOver · ≫ v) (AlgHom.ext fun z => by simp)

def tanDer (hv : IsTangent v) (n : ℕ) : Cot O (G.A n) →ₗ[O] ModPow p O n :=
  AugCot.lift _ ((TrivSqZeroExt.sndHom _ _).restrictScalars O ∘ₗ (t.tanPt hv n).toLinearMap)
    fun a b => by simp [t.fst_tanPt hv, Algebra.smul_def, mul_comm]

@[simp] theorem tanDer_d (hv : IsTangent v) (n : ℕ) (a : G.A n) :
    t.tanDer hv n (dUnit O a) = (t.tanPt hv n a).snd := AugCot.lift_d ..

theorem lieCorr_iff (hv : IsTangent v) (x : G.Lie) : t.LieCorr x v ↔
    ∀ (n : ℕ) (w : G.omega), Ideal.Quotient.mk _ (x w) = t.tanDer hv n (w.1 n) := by
  constructor
  · intro h n w
    obtain ⟨ψ, h1, h2⟩ := h.2 n
    obtain ⟨a, ha⟩ := AugCot.d_surjective _ (w.1 n)
    rw [h2 w a ha, ← ha, tanDer_d, t.inj n _ _ _ (h1.trans (t.tanPt_y hv n).symm)]
  · exact fun h => ⟨hv, fun n => ⟨_, t.tanPt_y hv n, fun w a ha => by rw [h, ← ha, tanDer_d]⟩⟩

variable {t} {x x' : G.Lie}

theorem lieCorr_zero : t.LieCorr 0 1 :=
  ⟨(GrpTangent.isTangent_iff _).2 (MonObj.comp_one _), fun n =>
    ⟨(1 : WithConv (G.A n →ₐ[O] DualNumber (ModPow p O n))).ofConv, (_root_.map_one (t.pts n _)).trans (MonObj.comp_one _).symm, fun w a _ => by
      rw [LinearMap.zero_apply, map_zero]; rfl⟩⟩

theorem LieCorr.add (h : t.LieCorr x v) (h' : t.LieCorr x' v') : t.LieCorr (x + x') (v * v') := by
  have hv : IsTangent (v * v') := (GrpTangent.isTangent_iff _).2 (by
    rw [MonObj.comp_mul, (GrpTangent.isTangent_iff _).1 h.1, (GrpTangent.isTangent_iff _).1 h'.1,
      _root_.mul_one])
  refine ⟨hv, fun n => ⟨(toConv (t.tanPt h.1 n) * toConv (t.tanPt h'.1 n)).ofConv, by
    rw [t.mul, tanPt_y, tanPt_y, ← MonObj.comp_mul], fun w a ha => ?_⟩⟩
  rw [LinearMap.add_apply, map_add, (t.lieCorr_iff h.1 x).1 h, (t.lieCorr_iff h'.1 x').1 h', ← ha,
    tanDer_d, tanDer_d, AlgHom.convMul_apply]
  have e1 := congrArg (t.tanPt h.1 n) (congrArg (TensorProduct.rid O _) (lTensor_counit_comul a))
  have e2 := congrArg (t.tanPt h'.1 n) (congrArg (TensorProduct.lid O _) (rTensor_counit_comul a))
  rw [TensorProduct.rid_tmul, one_smul] at e1
  rw [TensorProduct.lid_tmul, one_smul] at e2
  rw [← e1, ← e2]
  generalize comul (R := O) a = c
  induction c with
  | zero => simp
  | add c d hc hd => simp only [map_add, TrivSqZeroExt.snd_add, ← hc, ← hd]; abel
  | tmul b c =>
    rw [Algebra.TensorProduct.lift_tmul, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
      TensorProduct.rid_tmul, TensorProduct.lid_tmul, map_smul, map_smul, DualNumber.snd_mul,
      ofConv_toConv, ofConv_toConv, fst_tanPt, fst_tanPt, TrivSqZeroExt.snd_smul,
      TrivSqZeroExt.snd_smul, Algebra.smul_def, Algebra.smul_def]
    ring

theorem LieCorr.smul (h : t.LieCorr x v) (c : O) :
    t.LieCorr (c • x) (GrpTangent.epsScale c ≫ v) := by
  refine ⟨GrpTangent.isTangent_epsScale c h.1, fun n => ?_⟩
  obtain ⟨ψ, h1, h2⟩ := h.2 n
  refine ⟨((TrivSqZeroExt.map (c • LinearMap.id)).restrictScalars O).comp ψ, ?_, fun w a ha => ?_⟩
  · rw [← spOver_comp, Category.assoc, h1, epsScale_eq, epsRedPow, epsRedPow,
      ← Category.assoc, ← Category.assoc, spOver_comp, spOver_comp]
    exact congrArg (spOver · ≫ v) (AlgHom.ext fun z => by ext <;> simp [Algebra.smul_def])
  · simp [h2 w a ha, Algebra.smul_def]

theorem LieCorr.map [Fact p.Prime] (h : t.LieCorr x v) (f : A ⟶ A₁) [IsMonHom f] :
    t₁.LieCorr (lieMap G H (t.map t₁ f) x) (v ≫ f) := by
  refine ⟨GrpTangent.isTangent_comp h.1 f, fun n => ?_⟩
  obtain ⟨ψ, h1, h2⟩ := h.2 n
  refine ⟨ψ.comp ((t.map t₁ f).app n : H.A n →ₐ[O] G.A n), ?_, fun w a ha => ?_⟩
  · rw [← spOver_comp, Category.assoc, map_y, ← Category.assoc, h1, Category.assoc]
  · exact h2 _ _ (by rw [omegaMap_val, ← ha, cotMap_d]; rfl)

theorem LieCorr.semi_mod {σ : O →+* O'} {G' : PDivGroup p O'} {A' : Over (Sp O')} [GrpObj A']
    {t' : G'.TorsionTower A'} {φ : A'.left ⟶ A.left} {s : SemiHom σ G' G}
    (hs : ∀ n, spMap (s.app n).toRingHom ≫ (t.y n).left = (t'.y n).left ≫ φ)
    {x' : G'.Lie} {v' : epsR O' ⟶ A'} (h : t.LieCorr x v) (h' : t'.LieCorr x' v')
    (e : v'.left ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR σ) ≫ v.left) (w : G.omega) (n : ℕ) :
    (Ideal.Quotient.mk _ (x' (s.omega w)) : ModPow p O' n) = Ideal.Quotient.mk _ (σ (x w)) := by
  obtain ⟨ψ, h1, h2⟩ := h.2 n
  obtain ⟨ψ', h1', h2'⟩ := h'.2 n
  obtain ⟨a, ha⟩ := AugCot.d_surjective _ (w.1 n)
  let τ : ModPow p O n →+* ModPow p O' n := Ideal.quotientMap _ σ (by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_pow, map_natCast]
    exact Ideal.mem_span_singleton_self _)
  have k1 : spMap (ψ : G.A n →+* DualNumber (ModPow p O n)) ≫ (t.y n).left =
    spMap (epsTo O (ModPow p O n)).toRingHom ≫ v.left := congrArg Over.Hom.left h1
  have k2 : spMap (ψ' : G'.A n →+* DualNumber (ModPow p O' n)) ≫ (t'.y n).left =
    spMap (epsTo O' (ModPow p O' n)).toRingHom ≫ v'.left := congrArg Over.Hom.left h1'
  have k := t.ringHom_ext
    (f := (ψ' : G'.A n →+* DualNumber (ModPow p O' n)).comp (s.app n).toRingHom)
    (g := (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR τ).comp (ψ : G.A n →+* DualNumber (ModPow p O n))) (by
      rw [Cris.spMap_comp, Cris.spMap_comp, Category.assoc, Category.assoc, hs, k1,
        reassoc_of% k2, e, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp,
        ← Cris.spMap_comp]
      refine congrArg (spMap · ≫ v.left) (RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_)
      · exact (fst_epsTo ..).trans ((congrArg _ (add_zero _)).trans
          ((add_zero _).trans (congrArg τ (fst_epsTo _ z))).symm)
      · exact (snd_epsTo ..).trans ((congrArg _ (zero_add _)).trans
          ((zero_add _).trans (congrArg τ (snd_epsTo _ z))).symm))
  rw [h2' _ (s.app n a) (by rw [SemiHom.omega_val, ← ha, SemiBialgHom.cot_d])]
  exact (congrArg TrivSqZeroExt.snd (RingHom.congr_fun k a)).trans
    ((zero_add _).trans (congrArg τ (h2 w a ha).symm))

theorem LieCorr.semi {σ : O →+* O'} [IsHausdorff (Ideal.span {(p : O')}) O'] {G' : PDivGroup p O'}
    {A' : Over (Sp O')} [GrpObj A'] {t' : G'.TorsionTower A'} {φ : A'.left ⟶ A.left}
    {s : SemiHom σ G' G}
    (hs : ∀ n, spMap (s.app n).toRingHom ≫ (t.y n).left = (t'.y n).left ≫ φ)
    {x' : G'.Lie} {v' : epsR O' ⟶ A'} (h : t.LieCorr x v) (h' : t'.LieCorr x' v')
    (e : v'.left ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR σ) ≫ v.left) (w : G.omega) :
    x' (s.omega w) = σ (x w) :=
  sub_eq_zero.1 <| IsHausdorff.haus' (I := Ideal.span {(p : O')}) _ fun n => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, ← Ideal.Quotient.eq]
    exact h.semi_mod hs h' e w n

theorem LieCorr.unique_left [IsHausdorff (Ideal.span {(p : O)}) O] (h : t.LieCorr x v)
    (h' : t.LieCorr x' v) : x = x' :=
  LinearMap.ext fun w => sub_eq_zero.1 <| IsHausdorff.haus' (I := Ideal.span {(p : O)}) _ fun n => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, ← Ideal.Quotient.eq,
      (t.lieCorr_iff h.1 x).1 h, (t.lieCorr_iff h.1 x').1 h']

variable (t) in

theorem tanDer_succ (hv : IsTangent v) (n : ℕ) (w : Cot O (G.A (n + 1))) (c : O)
    (hc : Ideal.Quotient.mk _ c = t.tanDer hv (n + 1) w) :
    Ideal.Quotient.mk _ c = t.tanDer hv n (cotMap (G.res n) w) := by
  obtain ⟨a, rfl⟩ := AugCot.d_surjective _ w
  let π : ModPow p O (n + 1) →ₐ[O] ModPow p O n := Ideal.Quotient.factorₐ O
    (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ n.le_succ))
  let _ : Algebra (ModPow p O (n + 1)) (ModPow p O n) := π.toRingHom.toAlgebra
  let π' : DualNumber (ModPow p O (n + 1)) →ₐ[O] DualNumber (ModPow p O n) :=
    { (epsTo (ModPow p O (n + 1)) (ModPow p O n)).toRingHom with
      commutes' := fun r => (epsTo (ModPow p O (n + 1)) (ModPow p O n)).commutes _ }
  have e : (t.tanPt hv n).comp (G.res n : G.A (n + 1) →ₐ[O] G.A n) =
      π'.comp (t.tanPt hv (n + 1)) := t.inj _ _ _ _ (by
    rw [← spOver_comp, ← spOver_comp, Category.assoc, Category.assoc, t.res, tanPt_y, tanPt_y,
      ← Category.assoc, spOver_comp]
    refine congrArg (spOver · ≫ v) (AlgHom.ext fun z => ?_)
    refine TrivSqZeroExt.ext ?_ ?_
    · exact (fst_epsTo ..).trans ((fst_epsTo ..).trans (congrArg π (fst_epsTo _ z))).symm
    · exact (snd_epsTo ..).trans ((snd_epsTo ..).trans (congrArg π (snd_epsTo _ z))).symm)
  rw [tanDer_d] at hc
  rw [cotMap_d, tanDer_d]
  exact ((congrArg TrivSqZeroExt.snd (DFunLike.congr_fun e a)).trans
    ((snd_epsTo ..).trans (congrArg π hc.symm))).symm

variable (t) in

theorem existsUnique_lieCorr [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : IsTangent v) :
    ∃! x : G.Lie, t.LieCorr x v := by
  have hm : ∀ (n : ℕ) (a b : O), a ≡ b [SMOD (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O O)] ↔
      (Ideal.Quotient.mk _ a : ModPow p O n) = Ideal.Quotient.mk _ b := fun n a b => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.Quotient.eq]
  have ex : ∀ w : G.omega, ∃ L : O, ∀ n, Ideal.Quotient.mk _ L = t.tanDer hv n (w.1 n) := fun w => by
    choose c hc using fun n => Ideal.Quotient.mk_surjective (t.tanDer hv n (w.1 n))
    have h1 : ∀ n, c n ≡ c (n + 1) [SMOD (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O O)] :=
      fun n => (hm n _ _).2 <| by rw [hc, t.tanDer_succ hv n _ _ (hc (n + 1)), w.2 n]
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : O)}) c fun {m n} hmn => by
      induction n, hmn using Nat.le_induction with
      | base => rfl
      | succ n hmn ih =>
        exact ih.trans ((h1 n).mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)))
    exact ⟨L, fun n => ((hm n _ _).1 (hL n)).symm.trans (hc n)⟩
  choose L hL using ex
  have hu : ∀ a b : O, (∀ n, (Ideal.Quotient.mk _ a : ModPow p O n) = Ideal.Quotient.mk _ b) →
      a = b := fun a b h => sub_eq_zero.1 <| IsHausdorff.haus' (I := Ideal.span {(p : O)}) _
        fun n => SModEq.zero.2 (SModEq.sub_mem.1 ((hm n a b).2 (h n)))
  let x : G.Lie :=
    { toFun := L
      map_add' := fun w w' => hu _ _ fun n => by rw [map_add, hL, hL, hL, ← map_add]; rfl
      map_smul' := fun c w => hu _ _ fun n => by
        rw [RingHom.id_apply, smul_eq_mul, _root_.map_mul, hL, hL]
        exact (map_smul (t.tanDer hv n) c (w.1 n)).trans (Algebra.smul_def _ _) }
  have hx := (t.lieCorr_iff hv x).2 fun n w => hL w n
  exact ⟨x, hx, fun _ h => h.unique_left hx⟩

end Lie

end TorsionTower

section Values

variable (p O) [Fact p.Prime]

theorem lieCorr_muLieGen [IsAdicComplete (Ideal.span {(p : O)}) O] :
    (muTower p O).LieCorr (muLieGen p O) (Diag.lieVec
      ((Int.castAddHom O).comp (AddEquiv.ulift : ULift.{0} ℤ ≃+ ℤ).toAddMonoidHom)) := by
  refine ((muTower p O).lieCorr_iff (Diag.isTangent_lieVec _) _).2 fun n w => ?_
  obtain ⟨c, rfl⟩ := (toSpanSingleton_dlogT_bijective p O).2 w
  rw [LinearMap.toSpanSingleton_apply, map_smul, muLieGen_dlogT, smul_eq_mul, _root_.mul_one]
  refine Eq.trans ?_ (map_smul ((muTower p O).tanDer _ n) c (dUnit O (muT O (p ^ n)))).symm
  rw [TorsionTower.tanDer_d, ← gmCoord_muTower, TorsionTower.tanPt_y, gmCoord_comp, gmCoord,
    Diag.charVal_lieVec, snd_epsTo]
  simp [Algebra.smul_def, show AddEquiv.ulift (ULift.up (1 : ℤ)) = 1 from rfl]

example (k : ℕ) [IsMonHom (𝟙 (Gm (Sp O)) ^ k)] :
    (muTower p O).map (muTower p O) (𝟙 _ ^ k) = (k : ℤ_[p]) • 𝟙 (mu p O) :=
  (muTower p O).map_pow_id k

example [IsHausdorff (Ideal.span {(p : O)}) O] (v : epsR O ⟶ Gm (Sp O))
    (h : (muTower p O).LieCorr 0 v) : v = 1 := by
  obtain ⟨c, rfl⟩ := (Diag.isTangent_iff_exists v).1 h.1
  refine gmCoord_ext ?_
  have h0 : c ⟨1⟩ = 0 := IsHausdorff.haus' (I := Ideal.span {(p : O)}) _ fun n => by
    have h1 := ((muTower p O).lieCorr_iff h.1 0).1 h n (dlogT p O)
    have h2 : (dlogT p O).1 n = dUnit O (muT O (p ^ n)) := rfl
    rw [h2, TorsionTower.tanDer_d, ← gmCoord_muTower, TorsionTower.tanPt_y, gmCoord_comp, gmCoord,
      Diag.charVal_lieVec, snd_epsTo] at h1
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      ← Ideal.Quotient.eq_zero_iff_mem]
    simpa using h1.symm
  rw [gmCoord, gmCoord, Diag.charVal_lieVec, Diag.charVal_one, h0]
  simp

end Values

end PDivGroup

end GlobalTheory
