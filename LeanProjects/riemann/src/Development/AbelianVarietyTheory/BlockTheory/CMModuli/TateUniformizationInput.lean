import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtPtBridgeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.TorusGraphMaps

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps

section Points

variable {R : Type} [CommRing R] [IsDomain R] {P : DegPre R}
variable {F : Type} [Field F] [Algebra (FractionRing R) F]

def QkZero {k : ℕ} (p : QkPt P F k) : Prop :=
  ∃ z : P.X, p.y = k • z ∧ GtPtF.IsIota z p.g

def QkTower (m : ℕ) {k n : ℕ} (p : QkPt P F k) (p' : QkPt P F n) : Prop :=
  k = n * m ∧ ∃ q : QkPt P F n, q.y = p.y ∧ GtPtF.IsNsmul m p.g q.g ∧ QkPt.Equiv P F q p'

end Points

section Lie

def ringActToOAct {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {O : Type} [CommRing O]
    (ra : RingAct A O) : Geo.Tor.OAct O A where
  act := ra.act
  hom := ra.hom
  one := ra.map_one
  mul := fun a b => by rw [_root_.mul_comm, ra.map_mul]
  add := fun a b => ra.map_add a b

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def torusLieEigen (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] (k : Type) [Field k]
    (τ : 𝓞 E →+* k) : Submodule k (X →+ k) where
  carrier := {v | ∀ (a : 𝓞 E) (χ : X), v (H.bar a • χ) = τ a * v χ}
  add_mem' := fun {v w} hv hw a χ => by
    simp only [AddMonoidHom.add_apply, hv a χ, hw a χ, mul_add]
  zero_mem' := fun a χ => by simp
  smul_mem' := fun c v hv a χ => by
    simp only [AddMonoidHom.smul_apply, hv a χ, smul_eq_mul]
    ring

instance torusLieEigen_finite (H : Host E) (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] [Module (𝓞 E) X] (k : Type) [Field k] (τ : 𝓞 E →+* k) :
    Module.Finite k (torusLieEigen H X k τ) := by
  have : Module.Finite k (X →+ k) :=
    Module.Finite.equiv (addMonoidHomLequivInt (A := X) (B := k) k).symm
  infer_instance

variable {R : Type} [CommRing R] [IsDomain R]

def GtLieMult (H : Host E) {P : DegPre R} [Module (𝓞 E) P.X]
    (ac : letI := hostStar H; P.OAct (𝓞 E)) (k : Type) [Field k] [Algebra (FractionRing R) k]
    (τ : 𝓞 E →+* k) (n : ℕ) : Prop :=
  letI := hostStar H
  ∃ nB : ℕ, LieMult (ringActToOAct ac.onB.toRingAct) (DegPre.jFR (R := R) k) τ nB ∧
    nB + Module.finrank k (torusLieEigen H P.X k τ) = n

def GtDetCond {H : Host E} (D : Datum H) {P : DegPre R} [Module (𝓞 E) P.X]
    (ac : letI := hostStar H; P.OAct (𝓞 E)) (k : Type) [Field k] [Algebra (FractionRing R) k]
    (ρ : k) : Prop :=
  ∀ τ : 𝓞 E →+* k, (τ H.rt = ρ → GtLieMult H ac k τ D.p) ∧ (τ H.rt ≠ ρ → GtLieMult H ac k τ D.q)

end Lie

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Levels

variable {R : Type} [CommRing R] [IsDomain R]

structure QTateIso (D : Datum H) {P : DegPre R} [Module (𝓞 E) P.X]
    (ac : letI := hostStar H; P.OAct (𝓞 E)) (k : Type) [Field k] [Algebra (FractionRing R) k] where
  ζ : ℕ+ → kˣ
  ζ_prim : ∀ n : ℕ+, IsPrimitiveRoot (ζ n) (n : ℕ)
  ζ_pow : ∀ n m : ℕ+, ζ (n * m) ^ (m : ℕ) = ζ n
  ev : ∀ n : ℕ+, D.La → QkPt P k (n : ℕ)
  add : ∀ n a a', QkAdd (ev n a) (ev n a') (ev n (a + a'))
  lin : ∀ n (x : 𝓞 E) a, (letI := hostStar H; QkSmul ac x (ev n a) (ev n (x • a)))
  ker : ∀ n a, QkZero (ev n a) ↔ ∃ a', a = (n : ℕ) • a'
  onto : ∀ (n : ℕ+) (p : QkPt P k (n : ℕ)), ∃ a, QkPt.Equiv P k (ev n a) p
  tower : ∀ (n m : ℕ+) a, QkTower (m : ℕ) (ev (n * m) a) (ev n a)
  isom : ∀ (n : ℕ+) a a', WeilQkIs P k (n : ℕ) (ev n a) (ev n a') ((ζ n ^ D.EF a a' : kˣ) : k)

structure QLevel (D : Datum H) (l : Level H) {P : DegPre R} [Module (𝓞 E) P.X]
    (ac : letI := hostStar H; P.OAct (𝓞 E)) (k : Type) [Field k] [Algebra (FractionRing R) k] where
  eta : D.La → QkPt P k l.M
  eta_add : ∀ a a', QkAdd (eta a) (eta a') (eta (a + a'))
  eta_lin : ∀ (x : 𝓞 E) a, (letI := hostStar H; QkSmul ac x (eta a) (eta (x • a)))
  eta_ker : ∀ a, QkZero (eta a) ↔ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)
  eta_onto : ∀ p : QkPt P k l.M,
    (∀ x ∈ l.Mb, ∃ q : QkPt P k l.M, (letI := hostStar H; QkSmul ac x p q) ∧ QkZero q) →
    ∃ a, QkPt.Equiv P k (eta a) p
  etaA : D.La → QkPt P k l.A
  etaA_add : ∀ a a', QkAdd (etaA a) (etaA a') (etaA (a + a'))
  etaA_lin : ∀ (x : 𝓞 E) a, (letI := hostStar H; QkSmul ac x (etaA a) (etaA (x • a)))
  etaA_ker : ∀ a, QkZero (etaA a) ↔ ∃ a', a = l.A • a'
  etaA_onto : ∀ p : QkPt P k l.A, ∃ a, QkPt.Equiv P k (etaA a) p

abbrev levelM (l : Level H) : ℕ+ := ⟨l.M, lt_of_lt_of_le (by norm_num) l.three_le⟩

abbrev levelA (l : Level H) : ℕ+ := ⟨l.A, l.A_pos⟩

def QTateIso.Induces {D : Datum H} {l : Level H} {P : DegPre R} [Module (𝓞 E) P.X]
    {ac : letI := hostStar H; P.OAct (𝓞 E)} {k k' : Type} [Field k] [Algebra (FractionRing R) k]
    [Field k'] [Algebra (FractionRing R) k'] (I : QTateIso D ac k') (lv : QLevel D l ac k)
    (σ : k →ₐ[FractionRing R] k') (z : k') : Prop :=
  (I.ζ (levelA l) : k') = z ∧
    (∀ a, QkMap (k := l.A) σ (lv.etaA a) (I.ev (levelA l) a)) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      QkMap (k := l.M) σ (lv.eta a) (I.ev (levelM l) a)

end Levels

section Base

variable {l : Level H} (c : Coeff l)

def coeffRt : c.F := IntermediateField.inclusion c.le (baseKA l).ρ

def coeffZeta : c.F := IntermediateField.inclusion c.le (baseKA l).ζ

lemma coeffRt_val : ((coeffRt c : c.F) : ℂ) = H.rt0 := rfl

lemma coeffZeta_val : ((coeffZeta c : c.F) : ℂ) = zeta l.A := rfl

variable {c}

def IsFracImage {O : Type} [CommRing O] (β : O →+* c.F) : Prop :=
  ∀ x : c.F, ∃ a s : O, β s ≠ 0 ∧ x * β s = β a

lemma isFracImage_V (W : ValuationSubring ℂ) : IsFracImage (c.V W).subtype := by
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, 1, by simp, by simp⟩
  rcases (c.V W).mem_or_inv_mem x with h | h
  · exact ⟨⟨x, h⟩, 1, by simp, by simp⟩
  · exact ⟨1, ⟨x⁻¹, h⟩, by simpa using hx, by simpa using mul_inv_cancel₀ hx⟩

lemma IsFracImage.ext {O K : Type} [CommRing O] [Field K] {β : O →+* c.F} (h : IsFracImage β)
    {gam gam' : c.F →+* K} (hgam : ∀ x, gam (β x) = gam' (β x)) : gam = gam' := by
  ext x
  obtain ⟨a, s, hs, hx⟩ := h x
  have h1 : gam x * gam (β s) = gam' x * gam (β s) := by
    rw [← map_mul, hx, hgam a, hgam s, ← map_mul, hx]
  exact mul_right_cancel₀ ((map_ne_zero gam).mpr hs) h1

end Base

structure ArcInput (D : Datum H) {l : Level H} (c : Coeff l) {O : Type} [CommRing O]
    (β : O →+* c.F) (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') where

  frac : IsFracImage β

  gam : c.F →+* FractionRing O'
  gam_over : ∀ x : O, gam (β x) = algebraMap O' (FractionRing O') (b x)

  P : DegPre O'
  psi_even : P.PsiEven
  tau_bimult : P.TauBimult
  [mod : Module (𝓞 E) P.X]

  ac : letI := hostStar H; P.OAct (𝓞 E)
  nontriv : Nontrivial P.X
  psi_gen : ∀ y : P.X, PsiGenOn P y Set.univ
  through : PsiThroughHost H ac

  be : LinearMap.BilinForm ℤ P.X
  be_symm : ∀ y z, be y z = be z y
  be_pos : ∀ y, y ≠ 0 → 0 < be y y
  be_adj : ∀ (a : 𝓞 E) y z, be (a • y) z = be y (H.bar a • z)
  be_dvd : ∀ y z, (2 * l.M' : ℤ) ∣ be y z

  lev : QLevel D l ac (FractionRing O')
  det : GtDetCond D ac (AlgebraicClosure (FractionRing O'))
    (algebraMap (FractionRing O') _ (gam (coeffRt c)))
  induced : ∃ I : QTateIso D ac (AlgebraicClosure (FractionRing O')),
    I.Induces lev (Algebra.ofId (FractionRing O') _)
      (algebraMap (FractionRing O') _ (gam (coeffZeta c)))

attribute [instance] ArcInput.mod

namespace ArcInput

variable {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}

lemma gam_unique (x x' : ArcInput D c β O' b) : x.gam = x'.gam :=
  x.frac.ext fun a => by rw [x.gam_over, x'.gam_over]

lemma gam_rt (x : ArcInput D c β O' b) (r : O) (hr : ((β r : c.F) : ℂ) = H.rt0) :
    x.gam (coeffRt c) = algebraMap O' (FractionRing O') (b r) := by
  rw [← x.gam_over]; congr 1; exact Subtype.ext hr.symm

lemma gam_zeta (x : ArcInput D c β O' b) (z : O) (hz : ((β z : c.F) : ℂ) = zeta l.A) :
    x.gam (coeffZeta c) = algebraMap O' (FractionRing O') (b z) := by
  rw [← x.gam_over]; congr 1; exact Subtype.ext hz.symm

lemma charZero (x : ArcInput D c β O' b) : CharZero (FractionRing O') :=
  x.gam.charZero_iff x.gam.injective |>.mp inferInstance

end ArcInput

end GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput
