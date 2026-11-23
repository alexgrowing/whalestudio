import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BaseOnto
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranslA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibre

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct

namespace UpperTheory.Gal.FiniteEtaleModels

def Sys (G : GDatum) (ℓ : ℕ) (f : ℕ → G.La →+ G.La) (u : ℕ → ℤ) (c κ : ℕ) : Prop :=
  (∀ n, 0 < n → n.Coprime ℓ → ∀ (a : G.O) (x : G.La), ∃ z, f n (a • x) = a • f n x + n • z) ∧
  (∀ n m, 0 < n → 0 < m → (n * m).Coprime ℓ → (∀ x, ∃ z, f (n * m) x = f n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) ∧
  (∀ n, 0 < n → n.Coprime ℓ → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ G.EF (f n x) (f n y) - c * u n * G.EF x y) ∧
  (∀ n, 0 < n → n.Coprime ℓ → ∀ x, ∃ y z, f n y = κ • x + n • z)

theorem Sys.mono {G : GDatum} {f : ℕ → G.La →+ G.La} {u : ℕ → ℤ} {c κ : ℕ} (h : Sys G 1 f u c κ) (ℓ : ℕ) : Sys G ℓ f u c κ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨fun n hn _ => h1 n hn (Nat.coprime_one_right n),
    fun n m hn hm _ => h2 n m hn hm (Nat.coprime_one_right _),
    fun n hn _ => h3 n hn (Nat.coprime_one_right n),
    fun n hn _ => h4 n hn (Nat.coprime_one_right n)⟩

structure Reind {q : ℕ} [Fact q.Prime] (D : Datum q) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (β : D.La → D.La) : Prop where
  add : ∀ x y, β (x + y) - (β x + β y) ∈ wSub D 𝔟₁ 1
  lin : ∀ (c : D.O) x, β (c • x) - c • β x ∈ wSub D 𝔟₁ 1
  ker : ∀ y, β y ∈ wSub D 𝔟₁ 1 ↔ y ∈ wSub D 𝔟₂ 1
  onto : ∀ x, (∀ c ∈ 𝔟₂, algebraMap (𝓞 D.F) D.O c • x ∈ wSub D 𝔟₁ 1) → ∃ y, x - β y ∈ wSub D 𝔟₁ 1

section
variable {q : ℕ} [Fact q.Prime] {D : Datum q} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R'] {b : Base D R}
  {gb : GBase D.toG R'} {S' : Scheme.{0}} {s' : S' ⟶ Sp R'} {M : ℕ}

@[reducible] def low (o : GObj gb M s') (N c : ℕ) (e : M = N * c) (hM : 0 < M) : GObj gb N s' :=
  { o with
    eta := fun x => o.eta (c • x)
    eta_add := fun x y => by rw [smul_add, o.eta_add]
    eta_lin := fun a x => by rw [smul_comm, o.eta_lin]
    eta_ker := fun x => by subst e; rw [smul_comm, smul_smul, o.eta_ker]
    geom := fun K _ _ x β hx => by
      subst e
      obtain ⟨I, hI⟩ := o.geom K x β hx
      refine ⟨I, fun y => ?_⟩
      rw [o.eta_nsmul, MonObj.comp_pow, hI, I.tower N c (Nat.pos_of_mul_pos_right hM) (Nat.pos_of_mul_pos_left hM)] }

@[reducible] def ob {β : R →+* R'} (hm : Match b gb β) (o : GObj gb M s') (N c : ℕ) (e : M = N * c) (hM : 0 < M) :
    Obj b N (s' ≫ spMap β) :=
  GenCmp.toObj hm.1 hm.2 (low o N c e hM) (GenCmp.genericObject_kernelCondition _)

end

def DictP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (h : G.GAf) (κ c' : ℕ), 0 < κ → κ.Coprime p → c'.Coprime p →
    Integ L h → (∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h v' = κ • v) →
    (∃ t t' : AfP p, IsIntAf t ∧ IsIntAf t' ∧ t * t' = 1 ∧
      (((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : (AfP p)ˣ) : AfP p) = (c' : AfP p) * t) →
    ∃ (f : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c : ℕ), c * c' = κ ^ 2 ∧ Sys D.toG p f u c κ ∧
      ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, κ • L.actG h⁻¹ (inAf D x) = inAf D (f n x) + n • w

def SysExt : Prop :=
  ∀ (G : GDatum) (p : ℕ), p.Prime → ∀ (f : ℕ → G.La →+ G.La) (u : ℕ → ℤ) (c c' κ : ℕ), c * c' = κ ^ 2 → c'.Coprime p → Sys G p f u c κ →
    ∃ (f' : ℕ → G.La →+ G.La) (u' : ℕ → ℤ), Sys G 1 f' u' c κ ∧ ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, f' n x = f n x + n • z

def TrEtaK : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase D.toG R)
    (h : G.GAf) (X : Scheme.{0}) (s : X ⟶ Sp R) (M₁ M₂ : Lv p) (o' : GObj gb M₁.1 s) (o : GObj gb M₂.1 s) (ψ : o'.A ⟶ o.A), IsTrans L h o' o ψ →
    ∀ (n κ c₁ c₂ : ℕ), M₁.1 = n * κ * c₁ → M₂.1 = n * c₂ → ∀ x y : D.La,
    (∃ v ∈ LaHat D, L.actG h (inAf D x) = κ • inAf D y + (n * κ) • v) → o'.eta (c₁ • x) ≫ ψ = o.eta (c₂ • y)

def TrKer : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase D.toG R)
    (h : G.GAf) (X : Scheme.{0}) (s : X ⟶ Sp R) (M₁ M₂ : Lv p) (o' : GObj gb M₁.1 s) (o : GObj gb M₂.1 s) (ψ : o'.A ⟶ o.A), IsTrans L h o' o ψ →
    ∀ (n κ c₁ : ℕ), M₁.1 = n * κ * c₁ → (∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h v' = κ • v) → ∀ f : D.La →+ D.La,
    (∀ x, ∃ w ∈ LaHat D, κ • L.actG h⁻¹ (inAf D x) = inAf D (f x) + (n * κ) • w) →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : Sp Ω ⟶ X) (g : Over.mk z ⟶ o'.A), g ≫ ψ = 1 → g ^ κ = 1 →
      ∃ x, g = toUnit (Over.mk z) ≫ o'.eta (c₁ • n • f x)

def GalOfKer : Prop :=
  ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B], IsAbelianScheme A → IsAbelianScheme B →
    ∀ (ψ : A ⟶ B) (ψ' : B ⟶ A) (κ : ℕ), IsMonHom ψ → IsMonHom ψ' → ψ ≫ ψ' = (𝟙 A) ^ κ → ψ' ≫ ψ = (𝟙 B) ^ κ → IsUnit ((κ : ℕ) : Γ(S, ⊤)) →
    ∀ H : Subgroup (𝟙_ (Over S) ⟶ A), Finite H → (∀ g ∈ H, g ≫ ψ = 1) →
    (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : Sp Ω ⟶ S), ∀ g ∈ H, toUnit (Over.mk z) ≫ g = 1 → g = 1) →
    (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : Sp Ω ⟶ S) (g : Over.mk z ⟶ A), g ≫ ψ = 1 → ∃ g₀ ∈ H, g = toUnit (Over.mk z) ≫ g₀) →
    GlobalTheory.ZM.IsGaloisCover H (fun g => (Hecke.transl g.1).left) ψ.left

def TrPull : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (R : Type) [CommRing R] (b : Base D R) (f : D.La →+ D.La) (c k N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (j : S' ⟶ S)
    (o : Obj b (N * k) s) (o' : Obj b N s) (ψ : o.A ⟶ o'.A) (o₁ : Obj b (N * k) s') (o₁' : Obj b N s') (m : ObjMap o₁ o j) (m' : ObjMap o₁' o' j),
    IsTranslA f c k N o o' ψ → ∃ ψ₁ : o₁.A ⟶ o₁'.A, IsTranslA f c k N o₁ o₁' ψ₁ ∧ ψ₁.left ≫ m'.φ = m.φ ≫ ψ.left

def TrSame : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (R : Type) [CommRing R] (b : Base D R) (f : D.La →+ D.La) (c k N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R)
    (o : Obj b (N * k) s) (o₁ o₂ : Obj b N s) (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o.A ⟶ o₂.A), IsTranslA f c k N o o₁ ψ₁ → IsTranslA f c k N o o₂ ψ₂ →
    ∃ m : ObjMap o₁ o₂ (𝟙 S), ψ₁.left ≫ m.φ = ψ₂.left

def LevTr : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (R : Type) [CommRing R] (b : Base D R) (f : D.La →+ D.La) (c k N : ℕ) (𝔟 : Ideal (𝓞 D.F)), k.Coprime q → (∃ e : ℕ, ((q ^ e : ℕ) : 𝓞 D.F) ∈ 𝔟) →
    ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s) (o' : Obj b N s) (ψ : o.A ⟶ o'.A) (lv : D.La → (𝟙_ (Over S) ⟶ o.A)),
    IsTranslA f c k N o o' ψ → IsEtLev o 𝔟 1 lv → IsEtLev o' 𝔟 1 fun y => lv y ≫ ψ

def LevRe : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (β : D.La → D.La), 𝔟₁ ≤ 𝔟₂ → Reind D 𝔟₁ 𝔟₂ β →
    ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (lv : D.La → (𝟙_ (Over S) ⟶ o.A)), IsEtLev o 𝔟₁ 1 lv → IsEtLev o 𝔟₂ 1 fun y => lv (β y)

def BetaH : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (h : G.GAf) (κ n : ℕ), 0 < n → n.Coprime p → n.Coprime κ →
    Integ L h → (∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h v' = κ • v) →
    ∃ g : D.La →+ D.La, (∀ (a : D.O) x, ∃ z, g (a • x) = a • g x + n • z) ∧ (∀ x z, g x = n • z → ∃ v, x = n • v) ∧
      (∀ x, ∃ y z, g y = x + n • z) ∧ ∀ x, ∃ v ∈ LaHat D, L.actG h (inAf D (g x)) = inAf D x + n • v

def BetaLat : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (n m₁ : ℕ) (a₁ a₂ : 𝓞 D.F), 0 < n → 0 < m₁ → 𝔟₁ ≤ 𝔟₂ →
    IsGen a₁ (n * m₁) 𝔟₁ → IsGen a₂ n 𝔟₂ → ∀ g : D.La →+ D.La, (∀ (a : D.O) x, ∃ z, g (a • x) = a • g x + n • z) →
    (∀ x z, g x = n • z → ∃ v, x = n • v) → (∀ x, ∃ y z, g y = x + n • z) →
    ∃ β : D.La → D.La, Reind D 𝔟₁ 𝔟₂ β ∧ ∀ y, ∃ z, m₁ • g (algebraMap (𝓞 D.F) D.O a₂ • y) = algebraMap (𝓞 D.F) D.O a₁ • β y + (n * m₁) • z

def NumSplit : Prop :=
  ∀ (A : Type) [CommRing A] [IsDedekindDomain A] [CharZero A] (𝔟₁ 𝔟₂ : Ideal A) (M₁ M₂ Q : ℕ) (a₁ a₂ : A), 0 < M₁ → 0 < M₂ → 𝔟₁ ≤ 𝔟₂ →
    IsGen a₁ M₁ 𝔟₁ → IsGen a₂ M₂ 𝔟₂ → (Q : A) ∈ 𝔟₁ →
    ∃ (n m₁ m₂ : ℕ) (a : A), n ∣ Q ∧ M₁ = n * m₁ ∧ M₂ = n * m₂ ∧ a₂ = (m₂ : A) * a ∧ IsGen a n 𝔟₂

def CoreA : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (D : Datum q) (R R' : Type) [CommRing R] [CommRing R'] [Algebra ℚ R'] (b : Base D R) (gb : GBase D.toG R')
    (β : R →+* R') (hm : Match b gb β) (N κ c : ℕ) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (E₁ : EtModel b (N * κ) 𝔟₁ 1) (E₂ : EtModel b N 𝔟₂ 1),
    IsLocallyNoetherian E₁.X → 3 ≤ N → N.Coprime q → κ.Coprime q → c ∣ κ ^ 2 → 𝔟₁ ≤ 𝔟₂ → (∃ e : ℕ, ((q ^ e : ℕ) : 𝓞 D.F) ∈ 𝔟₁) →
    ∀ (f : ℕ → D.La →+ D.La) (u : ℕ → ℤ), Sys D.toG q f u c κ → ∀ ρ : D.La → D.La, Reind D 𝔟₁ 𝔟₂ ρ →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp R') (M₁ M₂ c₁ c₂ : ℕ) (a₁ a₂ : 𝓞 D.F) (e₁ : M₁ = N * κ * c₁) (e₂ : M₂ = N * c₂) (h₁ : 0 < M₁) (h₂ : 0 < M₂),
    IsGen a₂ M₂ 𝔟₂ → ∀ (o₁ : GObj gb M₁ s) (o₂ : GObj gb M₂ s) (ψ : o₁.A ⟶ o₂.A),
    IsTranslA (f (N * κ)) c κ N (ob hm o₁ (N * κ) c₁ e₁ h₁) (ob hm o₂ N c₂ e₂ h₂) ψ →
    (∀ y, o₁.eta (algebraMap (𝓞 D.F) D.O a₁ • ρ y) ≫ ψ = o₂.eta (algebraMap (𝓞 D.F) D.O a₂ • y)) →
    ∀ (C₁ : Cls E₁ β o₁ c₁ a₁) (C₂ : Cls E₂ β o₂ c₂ a₂),
    ∃ (t : E₁.X ⟶ E₂.X) (Φ : E₁.univ.A.left ⟶ E₂.univ.A.left), t ≫ E₂.s = E₁.s ∧ Φ ≫ E₂.univ.A.hom = E₁.univ.A.hom ≫ t ∧
      C₁.j ≫ t = C₂.j ∧ C₁.m.φ ≫ Φ = ψ.left ≫ C₂.m.φ

end UpperTheory.Gal.FiniteEtaleModels
