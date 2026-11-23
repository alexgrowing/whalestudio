import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS.LiftTriv

section General

variable {R₁ R₂ R' : Type} [CommRing R₁] [CommRing R₂] [CommRing R'] {I₁ : Ideal R₁} {I₂ : Ideal R₂}
  {I' : Ideal R'} {X₁ X₂ X' : Scheme.{0}} {κ₁ : DividedPowers I₁} {κ₂ : DividedPowers I₂} {κ' : DividedPowers I'}
  {s₁ : X₁ ⟶ Sp R₁} {s₂ : X₂ ⟶ Sp R₂} {s' : X' ⟶ Sp R'} {σ₁ : R₁ →+* R'} {σ₂ : R₂ →+* R'}
  {p₁ : X' ⟶ X₁} {p₂ : X' ⟶ X₂}

def pv (h : IsMor κ₁ s₁ κ' s' σ₁ p₁) (f : Z1 (O κ₁ s₁)) {T T' : Thick κ' s'} (φ : T ⟶ T') : T'.B :=
  ev f (h.functor.map φ)

theorem exists_of_pull1_eq (h₁ : IsMor κ₁ s₁ κ' s' σ₁ p₁) (h₂ : IsMor κ₂ s₂ κ' s' σ₂ p₂) (f : Z1 (O κ₁ s₁))
    (g b : Z1 (O κ₂ s₂)) (r : R')
    (e : h₁.pull1 (H1.mk _ f) = h₂.pull1 (H1.mk _ g) + r • h₂.pull1 (H1.mk _ b)) :
    ∃ G : ∀ T : Thick κ' s', T.B, ∀ (T T' : Thick κ' s') (φ : T ⟶ T'),
      G T' - φ.φ (G T) = pv h₁ f φ - (pv h₂ g φ + algebraMap R' T'.B r * pv h₂ b φ) := by
  have e' : H1.mk (O κ' s') (h₁.coef.pullbackOneCocycle f) =
      H1.mk (O κ' s') (h₂.coef.pullbackOneCocycle g + r • h₂.coef.pullbackOneCocycle b) := by
    rw [map_add, map_smul]
    exact e
  obtain ⟨G, hG⟩ := H1.mk_eq_mk.1 e'
  refine ⟨G, fun T T' φ ↦ ?_⟩
  rw [← Algebra.smul_def]
  exact congrFun (congrFun (congrFun hG T) T') φ

theorem form_idLift {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (f : Form s)
    {T T' : Thick (dp0 R) s} (Φ : T ⟶ T') (y : Sp T.B ⟶ X) (hy : y ≫ s = spMap (algebraMap R T.B))
    (ey : spMap T.π ≫ y = T.x) (y' : Sp T'.B ⟶ X) (hy' : y' ≫ s = spMap (algebraMap R T'.B))
    (ey' : spMap T'.π ≫ y' = T'.x) (e : spMap (Φ.φ : T.B →+* T'.B) ≫ y = y') :
    ev f.1 Φ = ev f.1 (idLift T' y' hy' ey') - Φ.φ (ev f.1 (idLift T y hy ey)) := by
  let a : Thick.triv T.B y hy ⟶ Thick.triv T'.B y' hy' := Thick.trivHom Φ.φ e
  have k := Form.ev_sq f a (idLift T' y' hy' ey') (idLift T y hy ey) Φ rfl rfl fun _ ↦ rfl
  exact eq_sub_of_add_eq' k.symm

end General

section Eps

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

omit [GrpObj A] in

def epsHom {P Q : GPt A} (φ : P.Hom Q) : P.eps ⟶ Q.eps :=
  letI := P.eps.alg
  letI := Q.eps.alg
  { φ := { dualMap (φ.ρ : P.B →+* Q.B) with
      commutes' := fun r ↦ by
        change dualMap (φ.ρ : P.B →+* Q.B) (dualMap (algebraMap K P.B) r) = dualMap (algebraMap K Q.B) r
        ext <;> simp [dualMap] }
    φ₀ := (φ.ρ : P.B →+* Q.B)
    comm := fun c ↦ by
      change φ.ρ c.fst = (dualMap (φ.ρ : P.B →+* Q.B) c).fst
      simp [dualMap]
    dp := isDPMorphism_sqDP (SqExt.ofModule K P.B P.B).sq (SqExt.ofModule K Q.B Q.B).sq _ fun a ha ↦ by
      have ha' : a.fst = 0 := ha
      change (dualMap (φ.ρ : P.B →+* Q.B) a).fst = 0
      simp [dualMap, ha']
    pt := φ.pt }

def epsSec (P : GPt A) : P.triv ⟶ (constMor A).isMor.obj P.eps :=
  letI := ((constMor A).isMor.obj P.eps).alg
  Thick.trivHom
    { (TrivSqZeroExt.inlAlgHom K P.B P.B : P.B →+* DualNumber P.B) with
      commutes' := fun r ↦ by
        change TrivSqZeroExt.inl (algebraMap K P.B r) =
          dualMap (algebraMap K P.B) (algebraMap K (DualNumber K) r)
        ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl] }
    (by
      change spMap (RingHom.id P.B) ≫ P.x = P.x ≫ (𝟙 A : A ⟶ A).left
      simp [Cris.spMap_id])

def secVal (f : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) (P : GPt A) : DualNumber P.B := ev f (epsSec P)

theorem pv_const (f : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) {P Q : GPt A} (φ : P.Hom Q) :
    (pv (constMor A).isMor f (epsHom φ) : DualNumber Q.B) =
      TrivSqZeroExt.inl (ev f φ.triv : Q.B) + secVal f Q - dualMap (φ.ρ : P.B →+* Q.B) (secVal f P) := by
  have k := Cris.ev_sq f φ.triv (epsSec Q) (epsSec P) ((constMor A).isMor.functor.map (epsHom φ)) fun c ↦ by
    change (TrivSqZeroExt.inl (φ.ρ c) : DualNumber Q.B) = dualMap (φ.ρ : P.B →+* Q.B) (TrivSqZeroExt.inl c)
    ext <;> simp [dualMap]
  exact eq_sub_of_add_eq' (G := DualNumber Q.B) k.symm

variable {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left}

theorem pv_lift (h : IsGrpPullback A A' (DeRham.epsRed K) i) (ω' : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K))))
    {P Q : GPt A} (φ : P.Hom Q) {y : Sp (DualNumber P.B) ⟶ A'.left} {y' : Sp (DualNumber Q.B) ⟶ A'.left}
    (hy : IsLift i P y) (hy' : IsLift i Q y') (e : spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ y = y') :
    (pv (liftMor (epsDP K) h).isMor ω'.1 (epsHom φ) : DualNumber Q.B) =
      liftVal h ω'.1 hy' - dualMap (φ.ρ : P.B →+* Q.B) (liftVal h ω'.1 hy) := by
  exact form_idLift ω' ((liftMor (epsDP K) h).isMor.functor.map (epsHom φ)) y hy.1 hy.2 y' hy'.1 hy'.2 e

end Eps

theorem eps_part_eq_coboundary (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A]
    (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left)
    (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ω' : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K))))
    (ω : Form (A.hom ≫ 𝟙 (Sp K))) (b : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))))
    (hyp : (liftMor (epsDP K) h).isMor.pull1 (Form.cl _ ω') = (constMor A).isMor.pull1 (Form.cl _ ω) +
      (DualNumber.eps : DualNumber K) • (constMor A).isMor.pull1 (H1.mk _ b)) :
    ∃ G : PtFn (A.hom ≫ 𝟙 (Sp K)), ∀ (P Q : GPt A) (φ : P.Hom Q) (y : Sp (DualNumber P.B) ⟶ A'.left)
      (y' : Sp (DualNumber Q.B) ⟶ A'.left) (hy : IsLift i P y) (hy' : IsLift i Q y'),
      spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ y = y' →
      ev b φ.triv = ((liftVal h ω'.1 hy').snd + G Q) - φ.ρ ((liftVal h ω'.1 hy).snd + G P) := by
  obtain ⟨G₀, hG⟩ := exists_of_pull1_eq (liftMor (epsDP K) h).isMor (constMor A).isMor ω'.1 ω.1 b
    DualNumber.eps hyp
  let G₁ : ∀ P : GPt A, DualNumber P.B := fun P ↦ G₀ (Pt.eps P)
  refine ⟨fun P ↦ -(secVal ω.1 P).snd - (secVal b P).fst - (G₁ P).snd, fun P Q φ y y' hy hy' e ↦ ?_⟩
  have k : G₁ Q - dualMap (φ.ρ : P.B →+* Q.B) (G₁ P) =
      (pv (liftMor (epsDP K) h).isMor ω'.1 (epsHom φ) : DualNumber Q.B) -
        ((pv (constMor A).isMor ω.1 (epsHom φ) : DualNumber Q.B) +
          dualMap (algebraMap K Q.B) DualNumber.eps * (pv (constMor A).isMor b (epsHom φ) : DualNumber Q.B)) :=
    hG P.eps Q.eps (epsHom φ)
  rw [pv_lift h ω' φ hy hy' e, pv_const, pv_const] at k
  have k2 := congrArg TrivSqZeroExt.snd k
  simp [dualMap] at k2
  simp only [map_add, map_sub, map_neg]
  linear_combination k2

end GlobalTheory.CechKS.LiftTriv
