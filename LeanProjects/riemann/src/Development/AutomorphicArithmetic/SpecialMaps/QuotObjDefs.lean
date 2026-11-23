import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsStableFlag

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel

noncomputable section
namespace UpperTheory.QO

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R R₁ : Type} [CommRing R] [CommRing R₁]

def gam {T : Scheme.{0}} (s : T ⟶ Sp R) : R →+* Γ(T, ⊤) :=
  s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

structure Link (b : Base D R) (b₁ : Base D R₁) {T : Scheme.{0}} (s : T ⟶ Sp R) (s₁ : T ⟶ Sp R₁) : Prop where
  rho : gam s b.ρ = gam s₁ b₁.ρ
  t : ∀ i c, gam s (b.t i c) = gam s₁ (b₁.t i c)

theorem gam_comp {T T' : Scheme.{0}} (x : T' ⟶ T) (s : T ⟶ Sp R) (a : R) :
    gam (x ≫ s) a = x.appTop.hom (gam s a) := by
  rfl

theorem gam_spMap {R' : Type} [CommRing R'] (β : R →+* R') (a : R) :
    gam (spMap β) a = (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (β a) := by
  have e := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β)
  exact (congrArg (fun g => g.hom a) e).symm

variable {b : Base D R} {b₁ : Base D R₁}

theorem Link.symm {T : Scheme.{0}} {s : T ⟶ Sp R} {s₁ : T ⟶ Sp R₁} (L : Link b b₁ s s₁) : Link b₁ b s₁ s :=
  ⟨L.rho.symm, fun i c => (L.t i c).symm⟩

theorem Link.pull {T T' : Scheme.{0}} {s : T ⟶ Sp R} {s₁ : T ⟶ Sp R₁} (L : Link b b₁ s s₁) (x : T' ⟶ T) :
    Link b b₁ (x ≫ s) (x ≫ s₁) :=
  ⟨by rw [gam_comp, gam_comp, L.rho], fun i c => by rw [gam_comp, gam_comp, L.t]⟩

theorem Link.eval {T : Scheme.{0}} {s : T ⟶ Sp R} {s₁ : T ⟶ Sp R₁} (L : Link b b₁ s s₁) {R' : Type} [CommRing R']
    (β : R →+* R') (β₁ : R₁ →+* R') (x : Sp R' ⟶ T) (h : x ≫ s = spMap β) (h₁ : x ≫ s₁ = spMap β₁) :
    β b.ρ = β₁ b₁.ρ ∧ ∀ i c, β (b.t i c) = β₁ (b₁.t i c) := by
  have inj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of R')).symm.commRingCatIsoToRingEquiv.injective
  have L' := L.pull x
  rw [h, h₁] at L'
  refine ⟨inj ?_, fun i c => inj ?_⟩
  · rw [← gam_spMap, ← gam_spMap]; exact L'.rho
  · rw [← gam_spMap, ← gam_spMap]; exact L'.t i c

def conv {N : ℕ} {T : Scheme.{0}} {s : T ⟶ Sp R} {s₁ : T ⟶ Sp R₁} (L : Link b b₁ s s₁) (o : Obj b N s) :
    Obj b₁ N s₁ :=
  { o with
    lie := fun R' _ β₁ x hx v hv => by
      have hx' : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := (Spec.map_preimage _).symm
      obtain ⟨e1, e2⟩ := L.eval _ β₁ x hx' hx
      obtain ⟨w, h1, h2⟩ := o.lie R' _ x hx' v (by rw [e1]; exact hv)
      exact ⟨w, fun i c => by rw [← e2]; exact h1 i c, h2⟩
    lieRank := fun k _ _ x β₁ hx i => by
      have hx' : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := (Spec.map_preimage _).symm
      obtain ⟨-, e2⟩ := L.eval _ β₁ x hx' hx
      have e : ((Spec.preimage (x ≫ s)).hom).comp (b.t i) = β₁.comp (b₁.t i) := RingHom.ext fun c => e2 i c
      rw [← e]
      exact o.lieRank k x _ hx' i
    geom := fun k _ _ x β₁ hx => o.geom k x _ (Spec.map_preimage (x ≫ s)).symm }

structure RepData (b : Base D R) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) {S : Scheme.{0}} (s : S ⟶ Sp R)
    (o : Obj b N s) where
  Y : Over S
  o₀ : Obj b N (Y.hom ≫ s)
  m₀ : ObjMap o₀ o Y.hom
  o' : Obj b N (Y.hom ≫ s)
  ψ : o₀.A ⟶ o'.A
  fin : IsFinite Y.hom
  et : Etale Y.hom
  isog : IsPIsog c o₀ o' ψ
  tj : IsTj r w j o₀ o' ψ
  univ : ∀ (T : Scheme.{0}) (x : T ⟶ S) (o₁ o₁' : Obj b N (x ≫ s)) (_ : ObjMap o₁ o x) (ψ₁ : o₁.A ⟶ o₁'.A),
    IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : T ⟶ Y.left, y ≫ Y.hom = x ∧
      ∃ (m₀' : ObjMap o₁ o₀ y) (m₁ : ObjMap o₁' o' y), m₀'.φ ≫ ψ.left = ψ₁.left ≫ m₁.φ

structure SubData {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (w : Ideal (𝓞 D.F)) (j : ℕ)
    (o : Obj b N s) where
  K : Over S
  [grp : GrpObj K]
  i : K ⟶ o.A
  hom : IsMonHom i
  mono : Mono i
  fin : IsFinite K.hom
  et : Etale K.hom
  killed : ∀ (T : Over S) (x : T ⟶ o.A), InSub i x → KilledBy o w x
  stable : ∀ a : D.O, ∃ g : K ⟶ K, g ≫ i = i ≫ o.act.act a
  deg : IsIsogDeg (toUnit K) (Ideal.absNorm w ^ j)

attribute [instance] SubData.grp

variable {b : Base D R} {N : ℕ} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R}
  {o : Obj b N s}

def KerAt (Rd : RepData b N r w j c s o) (Sd : SubData w j o) {Tb : Scheme.{0}} (t : Tb ⟶ Rd.Y.left) : Prop :=
  ∀ (T : Over S) (τ : T.left ⟶ Tb) (a₀ : Over.mk (τ ≫ t) ⟶ Rd.o₀.A) (a : T ⟶ o.A), a₀.left ≫ Rd.m₀.φ = a.left →
    ((a₀ ≫ Rd.ψ = 1 ∧ ∃ e : ℕ, KilledBy Rd.o₀ (uIdeal D r ^ e) a₀) ↔ InSub Sd.i a)

def KerGeo (Rd : RepData b N r w j c s o) (Sd : SubData w j o) {k : Type} [Field k] (y : Sp k ⟶ Rd.Y.left) : Prop :=
  ∀ (a₀ : Over.mk y ⟶ Rd.o₀.A) (a : Over.mk (y ≫ Rd.Y.hom) ⟶ o.A), a₀.left ≫ Rd.m₀.φ = a.left →
    ((a₀ ≫ Rd.ψ = 1 ∧ ∃ e : ℕ, KilledBy Rd.o₀ (uIdeal D r ^ e) a₀) ↔ InSub Sd.i a)

end UpperTheory.QO
