import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES

namespace UpperTheory.Gal.Ord

structure Par (p : ℕ) {C : Type} [CommRing C] (w : Ideal C) (f : ℕ) where
  ε : C
  a : C
  g : C
  c : C
  c' : C
  s : C
  idem : (p : C) ∣ ε * ε - ε
  one : ε - 1 ∈ w
  off : ∀ w' : Ideal C, w'.IsMaximal → (p : C) ∈ w' → w' ≠ w → ε ∈ w'
  mem : a ∈ w
  away : a * (1 - ε) = (p : C) ^ f * s
  prod : a * g = (p : C) * c
  inv : (p : C) ∣ c' * c * ε - ε
  geps : (p : C) ∣ ε * g - g
  nil : ∃ e : ℕ, (p : C) ∣ a ^ e * ε
  gen : ∀ x ∈ w, ∃ u, (p : C) ∣ ε * x - a * u
  annG : ∀ x, (p : C) ∣ g * x → ∃ u v, (p : C) ∣ x - a * u - (1 - ε) * v
  annA : ∀ x, (p : C) ∣ a * x → ∃ u, (p : C) ∣ ε * x - g * u

variable (p : ℕ) [Fact p.Prime]

def frobN (X : Scheme.{0}) (h : (p : Γ(X, ⊤)) = 0) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | j + 1 => GlobalTheory.VB.frob X p h ≫ frobN X h j

def NO (T : Type) [CommRing T] (hT : (p : T) = 0) (A : Over (Sp T)) [GrpObj A] (e g : A ⟶ A) [IsMonHom e] [IsMonHom g] (f : ℕ) : Prop :=
  ∀ x ∈ PrimitiveSubmodule A, primPull (dp0 T) (𝟙 _) e x ∈
    Submodule.span T (Set.range fun c => primPull (dp0 T) (𝟙 _) g ((frobDR p T hT A)^[f] c))

variable {p} {k : Type} [Field k]

abbrev SMor (A : Over (Sp k)) [GrpObj A] (σ : k →+* k) (ψ : A.left ⟶ A.left) : Prop :=
  GrpMor (dp0 k) (𝟙 _) A (dp0 k) (𝟙 _) A σ (spMap σ) ψ

def IsConst {Y : Scheme.{0}} (v : Sp (DualNumber k) ⟶ Y) : Prop :=
  spMap ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ v = v

def coh {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {t : Sp k ⟶ Sp R} (o : Obj b N t) (c : 𝓞 D.F) :
    Module.End k (primDR o.A) :=
  haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
  primPull (dp0 k) (𝟙 _) (o.act.act (algebraMap (𝓞 D.F) D.O c))

def hom {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {t : Sp k ⟶ Sp R} (o : Obj b N t) (c : 𝓞 D.F) :
    Module.End k (HdR o.A) := GlobalTheory.HTCount.crysAct o (algebraMap (𝓞 D.F) D.O c)

def NOo {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {T : Type} [CommRing T] (hT : (p : T) = 0) {t : Sp T ⟶ Sp R}
    (o : Obj b N t) {w : Ideal (𝓞 D.F)} {f : ℕ} (π : Par p w f) : Prop :=
  haveI := o.act.hom (algebraMap (𝓞 D.F) D.O π.ε)
  haveI := o.act.hom (algebraMap (𝓞 D.F) D.O π.g)
  NO p T hT o.A (o.act.act (algebraMap (𝓞 D.F) D.O π.ε)) (o.act.act (algebraMap (𝓞 D.F) D.O π.g)) f

def IsDeep {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {t : Sp k ⟶ Sp R} (o : Obj b N t) (w : Ideal (𝓞 D.F)) (q : ℕ)
    (v : epsR k ⟶ o.A) : Prop :=
  ∃ (T : Type) (_ : CommRing T) (_ : Algebra k T) (τ : T →ₐ[k] DualNumber k) (j : DualNumber k →+* T)
    (u : Over.mk (spMap (algebraMap k T)) ⟶ o.A), Function.Injective j ∧ (∀ x, j (τ x) = x ^ q) ∧ KilledBy o w u ∧
      spMap (τ : T →+* DualNumber k) ≫ u.left = v.left

structure Lin (p : ℕ) {k : Type} [Field k] {C : Type} [CommRing C] {w : Ideal C} {f : ℕ} (π : Par p w f) (χ : C →+* k)
    {P : Type 1} [AddCommGroup P] [Module k P] (ρ : C → Module.End k P) (F : Submodule k P) (Φ : P →+ P) : Prop where
  fin : FiniteDimensional k P
  add : ∀ x y, ρ (x + y) = ρ x + ρ y
  mul : ∀ x y, ρ (x * y) = ρ x * ρ y
  one : ρ 1 = 1
  ker : RingHom.ker χ = w
  semi : ∀ (l : k) x, Φ (l • x) = l ^ p • Φ x
  comm : ∀ c x, Φ (ρ c x) = ρ c (Φ x)
  kerΦ : ∀ x, Φ x = 0 ↔ x ∈ F
  stab : ∀ c, ∀ x ∈ F, ρ c x ∈ F
  eig : ∀ c, ∀ x ∈ F, ρ c (ρ π.ε x) = χ c • ρ π.ε x
  line : ∃ x ∈ F, ρ π.ε x ≠ 0 ∧ ∀ y ∈ F, ∃ l : k, ρ π.ε y = l • ρ π.ε x
  annG : ∀ x, ρ π.g x = 0 → ∃ u v, x = ρ π.a u + ρ (1 - π.ε) v
  annA : ∀ x, ρ π.a x = 0 → ∃ u, ρ π.ε x = ρ π.g u
  dims : ∀ j : ℕ, Module.finrank k ↥(⨅ c, (ρ c).maxGenEigenspace (χ c ^ p ^ j)) = Module.finrank k ↥(⨅ c, (ρ c).maxGenEigenspace (χ c))

end UpperTheory.Gal.Ord
