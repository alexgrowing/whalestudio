import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassMemHodgeFiltrationOfCechRepZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}

theorem hom_ext' {s : X ⟶ Sp R} {P Q : Pt s} {φ ψ : P.Hom Q} (h : ∀ b, φ.ρ b = ψ.ρ b) : φ = ψ := by
  obtain ⟨ρ, e⟩ := φ
  obtain ⟨ρ', e'⟩ := ψ
  obtain rfl : ρ = ρ' := AlgHom.ext h
  rfl

instance ptCat (s : X ⟶ Sp R) : Category.{0} (Pt s) where
  Hom := Pt.Hom
  id := Pt.Hom.id
  comp := Pt.Hom.comp
  id_comp _ := hom_ext' fun _ ↦ rfl
  comp_id _ := hom_ext' fun _ ↦ rfl
  assoc _ _ _ := hom_ext' fun _ ↦ rfl

@[ext] theorem hom_ext {s : X ⟶ Sp R} {P Q : Pt s} {φ ψ : P ⟶ Q} (h : ∀ b, φ.ρ b = ψ.ρ b) : φ = ψ := hom_ext' h

@[reducible] def FP (s : X ⟶ Sp R) : Pt s ⥤ CommAlgCat.{0} R where
  obj P := CommAlgCat.of R P.B
  map φ := CommAlgCat.ofHom φ.ρ

def toPC (s : X ⟶ Sp R) : CoefMap (RingHom.id R) (O (dp0 R) s) (FP s) where
  G := { obj := fun P ↦ P.triv
         map := fun φ ↦ Pt.Hom.triv φ
         map_id := fun _ ↦ Thick.hom_ext fun _ ↦ rfl
         map_comp := fun _ _ ↦ Thick.hom_ext fun _ ↦ rfl }
  α P := RingHom.id P.B
  naturality _ _ := rfl
  smul _ _ _ := rfl

abbrev H1OnPoints (s : X ⟶ Sp R) : Type 1 := GlobalTheory.CatCoh.H1 (FP s)

def toP (s : X ⟶ Sp R) : FirstDeRham s →ₗ[R] H1OnPoints s := (toPC s).pull1

variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {φ : X' ⟶ X}

@[reducible] def pushPt (h : φ ≫ s = s' ≫ spMap σ) (P : Pt s') : Pt s where
  B := P.B
  alg := ((algebraMap R' P.B).comp σ).toAlgebra
  x := P.x ≫ φ
  w := by rw [Category.assoc, h, ← Category.assoc, P.w, ← GlobalTheory.Cris.spMap_comp]

def pushHom (h : φ ≫ s = s' ≫ spMap σ) {P Q : Pt s'} (f : P ⟶ Q) : pushPt h P ⟶ pushPt h Q where
  ρ := { (f.ρ : P.B →+* Q.B) with commutes' := fun r ↦ f.ρ.commutes (σ r) }
  pt := by
    change spMap (f.ρ : P.B →+* Q.B) ≫ P.x ≫ φ = Q.x ≫ φ
    rw [← Category.assoc, f.pt]

def pushC (h : φ ≫ s = s' ≫ spMap σ) : CoefMap σ (FP s) (FP s') where
  G := { obj := pushPt h
         map := pushHom h
         map_id := fun _ ↦ hom_ext fun _ ↦ rfl
         map_comp := fun _ _ ↦ hom_ext fun _ ↦ rfl }
  α P := RingHom.id P.B
  naturality _ _ := rfl
  smul T r b := (Algebra.smul_def (A := T.B) (σ r) b).symm

def pullP (h : φ ≫ s = s' ≫ spMap σ) : H1OnPoints s →ₛₗ[σ] H1OnPoints s' := (pushC h).pull1

theorem pullP_toP (m : IsMor (dp0 R) s (dp0 R') s' σ φ) (c : FirstDeRham s) :
    pullP m.w (toP s c) = toP s' (m.pull1 c) := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  rfl

theorem pullP_pullP {τ : R' →+* R''} {ψ : X'' ⟶ X'} {ρ : R →+* R''} {χ : X'' ⟶ X}
    (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ) (h'' : χ ≫ s = s'' ≫ spMap ρ)
    (e : ∀ r, τ (σ r) = ρ r) (e' : ψ ≫ φ = χ) (c : H1OnPoints s) : pullP h' (pullP h c) = pullP h'' c :=
  ((pushC h).pullCohomologyOne_comp (pushC h') c).symm.trans (((pushC h).comp (pushC h')).pullCohomologyOne_eq_of_natTrans (pushC h'')
    { app := fun T ↦
        { ρ := { RingHom.id T.B with commutes' := fun r ↦ congrArg (algebraMap R'' T.B) (e r) }
          pt := by
            change spMap (RingHom.id T.B) ≫ (T.x ≫ ψ) ≫ φ = T.x ≫ χ
            rw [GlobalTheory.Cris.spMap_id, ← e']; simp }
      naturality := fun _ _ _ ↦ hom_ext fun _ ↦ rfl } (fun _ _ ↦ rfl) c)

theorem toP_eq_zero_iff (c : FirstDeRham s) : toP s c = 0 ↔ c ∈ F1 s := by
  constructor
  · intro hc
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
    obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 hc
    refine h1_mk_mem_f1_of_isRep_zero R X s Unit (fun _ ↦ ⊤) (by simp) f
      ⟨fun _ P ↦ g P, fun _ P Q φ _ ↦ ?_, fun _ _ _ _ _ ↦ sub_self _⟩
    exact (congrFun (congrFun (congrFun hg P) Q) φ).symm
  · intro hc
    rw [hodgeFiltration_eq_range] at hc
    obtain ⟨f, rfl⟩ := hc
    refine H1.mk_eq_zero.2 ⟨0, ?_⟩
    funext T T' φ
    rw [map_zero]
    exact (f.2 (Pt.Hom.triv φ) rfl rfl).symm

theorem H1OnPoints_eq_zero_of_isIso (s : X ⟶ Sp R) [IsIso s] (c : H1OnPoints s) : c = 0 := by
  have hx : inv s ≫ s = spMap (algebraMap R R) := by rw [IsIso.inv_hom_id]; exact (GlobalTheory.Cris.spMap_id R).symm
  refine H1.eq_zero_of_isInitial _ (T₀ := ⟨R, inv s, hx⟩)
    (Limits.IsInitial.ofUniqueHom (fun T ↦ (⟨Algebra.ofId R T.B, ?_⟩ : Pt.Hom ⟨R, inv s, hx⟩ T)) fun T m ↦ ?_) c
  · rw [IsIso.comp_inv_eq]; exact T.w.symm
  · exact hom_ext fun b ↦ (m.ρ.commutes b).trans ((Algebra.ofId R T.B).commutes b).symm

def epsFn {Y : Scheme.{0}} (t : Y ⟶ Sp (DualNumber R)) : Γ(Y, ⊤) :=
  GlobalTheory.AbLaw.cst t ⊤ DualNumber.eps

theorem epsFn_sq {Y : Scheme.{0}} (t : Y ⟶ Sp (DualNumber R)) : epsFn t * epsFn t = 0 := by
  rw [epsFn, ← map_mul, DualNumber.eps_mul_eps, map_zero]

abbrev ETy : Type 1 := ∀ {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (_ : H1OnPoints s) {Y : Scheme.{0}}
  (_ : Y ⟶ X) (ν : Γ(Y, ⊤)) (_ : ν * ν = 0), Pic Y

structure IsE (E : ETy) : Prop where
  nat : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (c : H1OnPoints s) {Y Y' : Scheme.{0}} (π : Y ⟶ X)
    (ν : Γ(Y, ⊤)) (hν : ν * ν = 0) (ψ : Y' ⟶ Y) (ν' : Γ(Y', ⊤)) (hν' : ν' * ν' = 0), ν' = ψ.appTop.hom ν →
    GlobalTheory.CechPic.pull ψ (E s c π ν hν) = E s c (ψ ≫ π) ν' hν'
  add : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (c c' : H1OnPoints s) {Y : Scheme.{0}} (π : Y ⟶ X)
    (ν : Γ(Y, ⊤)) (hν : ν * ν = 0), E s (c + c') π ν hν = E s c π ν hν + E s c' π ν hν
  smul : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (c : H1OnPoints s) (r : R) {Y : Scheme.{0}} (π : Y ⟶ X)
    (ν : Γ(Y, ⊤)) (hν : ν * ν = 0) (ν' : Γ(Y, ⊤)) (hν' : ν' * ν' = 0), ν' = GlobalTheory.AbLaw.cst (π ≫ s) ⊤ r * ν →
    E s (r • c) π ν hν = E s c π ν' hν'
  chg : ∀ {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'}
    {σ : R →+* R'} {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ) (c : H1OnPoints s) {Y : Scheme.{0}} (π : Y ⟶ X')
    (ν : Γ(Y, ⊤)) (hν : ν * ν = 0), E s' (pullP h c) π ν hν = E s c (π ≫ φ) ν hν
  zero : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (c : H1OnPoints s) {Y : Scheme.{0}} (π : Y ⟶ X)
    (ν : Γ(Y, ⊤)) (hν : ν * ν = 0), ν = 0 → E s c π ν hν = 0
  inj : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (c : H1OnPoints s) {Y : Scheme.{0}} (π : Y ⟶ X)
    (t : Y ⟶ Sp (DualNumber R)), IsPullback π t s (spMap (algebraMap R (DualNumber R))) →
    E s c π (epsFn t) (epsFn_sq t) = 0 → c = 0

def SurjAll : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → Function.Surjective (toP (A.hom ≫ 𝟙 _))

def IsoAll : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left), L.IsLB → ∀ ψ : LinearMap.BilinForm R (HdR A),
      IsPolForm (dp0 R) (𝟙 _) A L ψ → ∀ x ∈ Fil A, ∀ y ∈ Fil A, ψ x y = 0

def PerfField : Prop :=
  ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left), L.IsLB → ∀ ψ : LinearMap.BilinForm K (HdR A),
      IsPolForm (dp0 K) (𝟙 _) A L ψ → ReciprocityTheory.ChartRestriction.G.Out.KTriv A L → LinearMap.IsPerfPair ψ

def AddEps : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB (A ⊗ epsR R).left) (hM : M.IsLB),
      (∀ (Y : Over (Sp R)) (t : Y ⟶ epsR R), GlobalTheory.AbDual.evc hM (1 : Y ⟶ A) t = 0) →
      (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ epsR R), t.left = Y.hom ≫ GlobalTheory.DeRham.epsRed R →
        GlobalTheory.AbDual.evc hM a t = 0) → GlobalTheory.AbDual.IsAdditive M

end CrystallinePoints.Pd
