import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BaseOnto
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.FiniteEtaleModels.O

def Cg {M : Type} [AddCommGroup M] (n : ℕ) (x y : M) : Prop := ∃ z, x = y + n • z

def MOne : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q), D.m = 1 →
  Function.Bijective (algebraMap (𝓞 D.F) D.O) ∧ Module.Projective D.O D.La ∧ Module.Finite D.O D.La

def Idem : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (r : ℤ), (q : ℤ) ∣ r ^ 2 - D.tr * r + D.nm → ∃ ε : ℕ → 𝓞 D.F, ∀ e : ℕ,
  1 - ε e ∈ ES.uIdeal D r ^ e ∧ D.bar (ε e) ∈ ES.uIdeal D r ^ e ∧ (∀ x ∈ ES.uIdeal D r ^ e, (q : 𝓞 D.F) ^ e ∣ ε e * x) ∧
  (q : 𝓞 D.F) ^ e ∣ ε e + D.bar (ε e) - 1 ∧ (q : 𝓞 D.F) ^ e ∣ ε (e + 1) - ε e ∧
  ∀ (𝔞 : Ideal (𝓞 D.F)), (∃ f : ℕ, ES.uIdeal D r ^ f ≤ 𝔞) → (q : 𝓞 D.F) ^ e ∈ 𝔞 → ES.uIdeal D r ^ e ≤ 𝔞

def LiftUnit : Prop := ∀ (A M : Type) [CommRing A] [IsDedekindDomain A] [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M]
  (u 𝔞 : Ideal A), u ≠ ⊥ → (∃ f : ℕ, u ^ f ≤ 𝔞) → ∀ g₀ : (M ⧸ (𝔞 • ⊤ : Submodule A M)) ≃ₗ[A] (M ⧸ (𝔞 • ⊤ : Submodule A M)),
  ∃ (g : M →ₗ[A] M) (h : ℕ → (M →ₗ[A] M)), (∀ x, (𝔞 • ⊤ : Submodule A M).mkQ (g x) = g₀ ((𝔞 • ⊤ : Submodule A M).mkQ x)) ∧
    ∀ e x, g (h e x) - x ∈ (u ^ e • ⊤ : Submodule A M) ∧ h e (g x) - x ∈ (u ^ e • ⊤ : Submodule A M)

def Adj : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (e : ℕ), (∀ x : D.La, (∀ y, ((q ^ e : ℕ) : ℤ) ∣ D.EF x y) → Cg (q ^ e) x 0) ∧
  (∀ h : D.La →ₗ[D.O] D.La, ∃ k : D.La →+ D.La, (∀ x y, ((q ^ e : ℕ) : ℤ) ∣ D.EF (h x) y - D.EF x (k y)) ∧
    ∀ (c : D.O) y, Cg (q ^ e) (k (c • y)) (c • k y)) ∧
  ∀ g : D.La →+ D.La, (∀ x y, ((q ^ e : ℕ) : ℤ) ∣ D.EF (g x) (g y) - D.EF x y) →
    (∀ x, Cg (q ^ e) (g x) 0 → Cg (q ^ e) x 0) ∧ ∀ x, ∃ y, Cg (q ^ e) (g y) x

def QSys : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q), D.m = 1 → ∀ (r : ℤ), (q : ℤ) ∣ r ^ 2 - D.tr * r + D.nm → ∀ (𝔞 : Ideal (𝓞 D.F)),
  (∃ e : ℕ, ES.uIdeal D r ^ e ≤ 𝔞) → ∀ g₀ : LevGrp D 𝔞 1, ∃ g : ℕ → D.La →+ D.La, ∀ e : ℕ,
    (∀ (c : D.O) x, Cg (q ^ e) (g e (c • x)) (c • g e x)) ∧ (∀ x y, ((q ^ e : ℕ) : ℤ) ∣ D.EF (g e x) (g e y) - D.EF x y) ∧
    (∀ x, Cg (q ^ e) (g (e + 1) x) (g e x)) ∧ ((q : 𝓞 D.F) ^ e ∈ 𝔞 → ∀ x, (wSub D 𝔞 1).mkQ (g e x) = g₀ ((wSub D 𝔞 1).mkQ x))

structure IsSys {G : GDatum} (g : ℕ → G.La →+ G.La) : Prop where
  lin : ∀ n, 0 < n → ∀ (c : G.O) x, ∃ z, g n (c • x) = c • g n x + n • z
  onto : ∀ n, 0 < n → ∀ x, ∃ y z, g n y = x + n • z
  inj : ∀ n, 0 < n → ∀ x z, g n x = n • z → ∃ v, x = n • v
  iso : ∀ n : ℕ, 0 < n → ∀ x y, (n : ℤ) ∣ G.EF (g n x) (g n y) - G.EF x y
  tow : ∀ n m, 0 < n → 0 < m → ∀ x, ∃ z, g (n * m) x = g n x + n • z

def TResim : Prop := ∀ (G : GDatum) (k : Type) [Field k] (Q : Type) [Group Q] (act : G.O → Q → Q) (e : ℕ → Q → Q → kˣ → Prop)
  (I : GTateIso G k Q act e) (g : ℕ → G.La →+ G.La), IsSys g → ∃ I' : GTateIso G k Q act e, ∀ n, 0 < n → ∀ x, I'.ev n x = I.ev n (g n x)

def OResim : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (R R' : Type) [CommRing R] [CommRing R'] [Algebra ℚ R'] (b : Base D R)
  (gb : GBase D.toG R') (N N₀ c : ℕ), N = N₀ * c → 0 < N → ∀ (X X₁ : Scheme.{0}) (s : X ⟶ Sp R') (s₁ : X₁ ⟶ Sp R) (o : GObj gb N s)
  (u : Obj b N₀ s₁) (f : X ⟶ X₁) (n : QMap o u f c) (g : ℕ → D.La →+ D.La), IsSys (G := D.toG) g → (∀ x, ∃ z, g N₀ x = x + N₀ • z) →
  ∃ (o' : GObj gb N s) (n' : QMap o' u f c), ∀ y : D.La, (o'.eta y).left ≫ n'.φ = (o.eta (g N y)).left ≫ n.φ

def TExt : Prop := ∀ (G : GDatum) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase G R) (N : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
  (σ : Sp Ω ⟶ Sp R) (o : GObj gb N σ)
  (I : GTateIso G Ω (Over.mk (𝟙 (Sp Ω)) ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)))
  (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp Ω),
  ∃ I' : GTateIso G k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)),
    ∀ n, 0 < n → ∀ y, (I'.ev n y).left = x ≫ (I.ev n y).left

def Raise : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (R R' : Type) [CommRing R] [CommRing R'] [Algebra ℚ R'] (b : Base D R)
  (gb : GBase D.toG R') (β : R →+* R'), Match b gb β → ∀ (N N₀ c : ℕ), N = N₀ * c → 0 < N → N₀.Coprime q →
  ∀ (X₁ : Scheme.{0}) (s₁ : X₁ ⟶ Sp R) (u : Obj b N₀ s₁) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (y : Sp Ω ⟶ X₁) (σ : Sp Ω ⟶ Sp R'),
  y ≫ s₁ = σ ≫ spMap β → ∃ o : GObj gb N σ, Nonempty (QMap o u y c)

def ClsAt : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q), D.m = 1 → ∀ (r : ℤ), (q : ℤ) ∣ r ^ 2 - D.tr * r + D.nm →
  ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra ℚ R'] (b : Base D R) (gb : GBase D.toG R') (β : R →+* R'), Match b gb β →
  ∀ (N N₀ c : ℕ) (a : 𝓞 D.F) (𝔞 : Ideal (𝓞 D.F)), N = N₀ * c → 0 < N → N₀.Coprime q → IsGen a N 𝔞 → (∃ e : ℕ, ES.uIdeal D r ^ e ≤ 𝔞) →
  ∀ (Y : EtModel b N₀ 𝔞 1) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (y : Sp Ω ⟶ Y.X) (σ : Sp Ω ⟶ Sp R'), y ≫ Y.s = σ ≫ spMap β →
  ∃ (o : GObj gb N σ) (C : Cls Y β o c a), C.j = y

def EpsEx : Prop := ∀ (A : Type) [CommRing A] [IsDedekindDomain A] [CharZero A] (𝔟₁ 𝔟₂ : Ideal A) (a₁ a₂ : A) (M₁ M₂ t : ℕ), 0 < M₁ →
  M₁ = M₂ * t → 𝔟₁ ≤ 𝔟₂ → IsGen a₁ M₁ 𝔟₁ → IsGen a₂ M₂ 𝔟₂ → ∃ ε : A, (M₁ : A) ∣ ε * a₁ - t * a₂ ∧ (Ideal.span {ε} ⊔ 𝔟₁) * 𝔟₂ = 𝔟₁

def LevDown : Prop := ∀ (q : ℕ) [Fact q.Prime] (D : Datum q), D.m = 1 → ∀ (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R)
  (o : Obj b N s) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (ε : 𝓞 D.F), 𝔟₁ ≠ ⊥ → (Ideal.span {ε} ⊔ 𝔟₁) * 𝔟₂ = 𝔟₁ → ∀ l : D.La → (𝟙_ (Over S) ⟶ o.A),
  IsEtLev o 𝔟₁ 1 l → IsEtLev o 𝔟₂ 1 fun y => l (algebraMap (𝓞 D.F) D.O ε • y)

def DownEx : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.m = 1 → D.a = 1 → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
  (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫)
  (N₀ κ : ℕ) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (X₁ : Ext S (N₀ * κ) 𝔟₁) (X₂ : Ext S N₀ 𝔟₂) (ε : 𝓞 D.F), (Ideal.span {ε} ⊔ 𝔟₁) * 𝔟₂ = 𝔟₁ →
  ∃ (t : X₁.Y.X ⟶ X₂.Y.X) (m : ObjMap (X₁.Y.univ.forget N₀ (Dvd.intro _ rfl) X₁.lev.2.1) X₂.Y.univ t), t ≫ X₂.Y.s = X₁.Y.s ∧ IsFinite t ∧ Etale t ∧
    ∀ y : D.La, (X₁.Y.lv (algebraMap (𝓞 D.F) D.O ε • y)).left ≫ m.φ = t ≫ (X₂.Y.lv y).left

end UpperTheory.Gal.FiniteEtaleModels.O
