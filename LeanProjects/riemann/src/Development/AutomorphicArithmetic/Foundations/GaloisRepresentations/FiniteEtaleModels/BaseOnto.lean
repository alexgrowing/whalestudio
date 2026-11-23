import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsQuotTriv

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.crystallineComparison.Mod (Std)

namespace UpperTheory.Gal.FiniteEtaleModels

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {E : Type} [Field E] [NumberField E] {gb : GBase D.toG E}
  {w : HeightOneSpectrum (𝓞 E)} {q : ℕ} [Fact q.Prime] {r : ℤ} {𝔴 𝔫 : Ideal (𝓞 D.F)}

structure Ext (S : Site gb w q r 𝔴 𝔫) (N₁ : ℕ) (𝔟 : Ideal (𝓞 D.F)) : Type 1 where
  lev : LevAt D q r 𝔴 N₁ 𝔟
  M : Model S.b N₁
  Y : EtModel S.b N₁ 𝔟 1
  π : Y.X ⟶ M.X
  ov : π ≫ M.s = Y.s
  mπ : ObjMap Y.univ M.univ π
  fin : IsFinite π
  et : Etale π
  proj : ∀ k, IsProjOver ((GlobalTheory.KS.pow Y.univ.A k).hom ≫ Y.s)
  dim : ∀ k, ∃ d, SmoothOfRelativeDimension d ((GlobalTheory.KS.pow Y.univ.A k).hom ≫ Y.s)

abbrev Ext.site {S : Site gb w q r 𝔴 𝔫} {N₁ : ℕ} {𝔟 : Ideal (𝓞 D.F)} (X : Ext S N₁ 𝔟) :
    Site gb w q r 𝔴 (Ideal.span {(N₁ : 𝓞 D.F)} * 𝔟) where
  atq := S.atq
  sp := S.sp
  f := S.f
  b := S.b
  mat := S.mat
  N₀ := N₁
  𝔞 := 𝔟
  std := { S.std with three := X.lev.1, cop := X.lev.2.1 }
  qmem := S.qmem
  norm := S.norm
  cop := X.lev.2.2.1
  sup := X.lev.2.2.2.1
  upow := X.lev.2.2.2.2
  lev := rfl
  M := X.M
  Y := X.Y
  π := X.π
  ov := X.ov
  mπ := X.mπ
  fin := X.fin
  et := X.et
  proj := X.proj
  dim := X.dim

abbrev extSelf (S : Site gb w q r 𝔴 𝔫) : Ext S S.N₀ S.𝔞 where
  lev := ⟨S.std.three, S.std.cop, S.cop, S.sup, S.upow⟩
  M := S.M
  Y := S.Y
  π := S.π
  ov := S.ov
  mπ := S.mπ
  fin := S.fin
  et := S.et
  proj := S.proj
  dim := S.dim

variable {S : Site gb w q r 𝔴 𝔫} {N₁ N₂ : ℕ} {𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)}

structure Down (X₁ : Ext S N₁ 𝔟₁) (X₂ : Ext S N₂ 𝔟₂) : Type where
  t : X₁.Y.X ⟶ X₂.Y.X
  ov : t ≫ X₂.Y.s = X₁.Y.s
  Φ : X₁.Y.univ.A.left ⟶ X₂.Y.univ.A.left
  w : Φ ≫ X₂.Y.univ.A.hom = X₁.Y.univ.A.hom ≫ t

def Down.id (X₁ : Ext S N₁ 𝔟₁) : Down X₁ X₁ := ⟨𝟙 _, Category.id_comp _, 𝟙 _, by simp⟩

def Down.pw {X₁ : Ext S N₁ 𝔟₁} {X₂ : Ext S N₂ 𝔟₂} (d : Down X₁ X₂) (k : ℕ) :
    (GlobalTheory.KS.pow X₁.Y.univ.A k).left ⟶ (GlobalTheory.KS.pow X₂.Y.univ.A k).left := GlobalTheory.KS.powMap d.t d.Φ d.w k

def Down.Extends {X₁ : Ext S N₁ 𝔟₁} {X₂ : Ext S N₂ 𝔟₂} (d : Down X₁ X₂) {k : ℕ} {T : KS L gb k} {h : G.GAf} {M₁ M₂ : Lv p}
    (W : Wit T h M₁ M₂) {c₁ c₂ : ℕ} {a₁ a₂ : 𝓞 D.F} (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂) : Prop :=
  C₁.j ≫ d.t = W.π ≫ C₂.j ∧ C₁.m.φ ≫ d.Φ = W.ψ.left ≫ W.φ.φ ≫ C₂.m.φ

end

def StepA : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k)
    (N₀ κ : ℕ) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (X₁ : Ext S (N₀ * κ) 𝔟₁) (X₂ : Ext S N₀ 𝔟₂), 𝔟₁ ≤ 𝔟₂ → ∀ (h : G.GAf), Integ L h →
    (∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h v' = κ • v) → ∀ (M₁ M₂ : Lv p) (c₁ c₂ : ℕ) (a₁ a₂ : 𝓞 D.F),
    X₁.site.Num M₁.1 c₁ a₁ → X₂.site.Num M₂.1 c₂ a₂ →
    ∀ (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂) (W : Wit T h M₁ M₂),
      ∃ d : Down X₁ X₂, d.Extends W C₁ C₂

def StepF : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k)
    (N₀ κ : ℕ) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (X₁ : Ext S (N₀ * κ) 𝔟₁) (X₂ : Ext S N₀ 𝔟₂), 𝔟₁ ≤ 𝔟₂ →
    ∀ (M₁ M₂ : Lv p) (c₁ c₂ : ℕ) (a₁ a₂ : 𝓞 D.F), X₁.site.Num M₁.1 c₁ a₁ → X₂.site.Num M₂.1 c₂ a₂ → M₂.1 ∣ M₁.1 →
    ∀ (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂) (W : Wit T 1 M₁ M₂),
      ∃ d : Down X₁ X₂, d.Extends W C₁ C₂ ∧ IsFinite d.t ∧ Etale d.t ∧ IsPullback d.Φ X₁.Y.univ.A.hom X₂.Y.univ.A.hom d.t

def StepB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k)
    (N₀ : ℕ) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (X₁ : Ext S N₀ 𝔟₁) (X₂ : Ext S N₀ 𝔟₂) (𝔴' : Ideal (𝓞 D.F)) (i : ℕ), 𝔴'.IsMaximal → uId D q r ≤ 𝔴' →
    𝔟₁ ≤ 𝔟₂ * 𝔴' → i ≤ D.n → ∀ (h : G.GAf), Integ L h → IsTjElt L q r 𝔴' i h → ∀ (M₁ M₂ : Lv p) (c₁ c₂ : ℕ) (a₁ a₂ : 𝓞 D.F),
    X₁.site.Num M₁.1 c₁ a₁ → X₂.site.Num M₂.1 c₂ a₂ → Ideal.absNorm 𝔴' ^ i ∣ M₁.1 →
    ∀ (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂) (W : Wit T h M₁ M₂),
      ∃ d : Down X₁ X₂, d.Extends W C₁ C₂

def BaseFet : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k)
    (M : Lv p) (c : ℕ) (a : 𝓞 D.F), S.Num M.1 c a → ∀ C : S.Cl (T.M M).univ c a,
      IsFinite (pullback.lift C.j (T.M M).s C.ov) ∧ Etale (pullback.lift C.j (T.M M).s C.ov)

def BaseOnto : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k)
    (M : Lv p) (c : ℕ) (a : 𝓞 D.F), S.Num M.1 c a → ∀ (C : S.Cl (T.M M).univ c a) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
      (y : Sp Ω ⟶ S.Y.X) (σ : Sp Ω ⟶ Sp E), y ≫ S.Y.s = σ ≫ spMap (algebraMap (Ow w) E) → ∃ x, x ≫ C.j = y ∧ x ≫ (T.M M).s = σ

def LiftSys : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (D : Datum q), D.m = 1 → ∀ (r : ℤ), (q : ℤ) ∣ r ^ 2 - D.tr * r + D.nm → ∀ (𝔞 : Ideal (𝓞 D.F)) (N₀ : ℕ),
    (∃ e : ℕ, ES.uIdeal D r ^ e ≤ 𝔞) → N₀.Coprime q → ∀ g₀ : LevGrp D 𝔞 1, ∃ g : ℕ → D.La →+ D.La,
      (∀ n, 0 < n → ∀ (c : D.O) x, ∃ z, g n (c • x) = c • g n x + n • z) ∧ (∀ n, 0 < n → ∀ x, ∃ y z, g n y = x + n • z) ∧
      (∀ n, 0 < n → ∀ x z, g n x = n • z → ∃ v, x = n • v) ∧ (∀ n : ℕ, 0 < n → ∀ x y, (n : ℤ) ∣ D.EF (g n x) (g n y) - D.EF x y) ∧
      (∀ n m, 0 < n → 0 < m → ∀ x, ∃ z, g (n * m) x = g n x + n • z) ∧ (∀ x, ∃ z, g N₀ x = x + N₀ • z) ∧
      ∀ n, 0 < n → ((n : ℕ) : 𝓞 D.F) ∈ 𝔞 → ∀ x, (wSub D 𝔞 1).mkQ (g n x) = g₀ ((wSub D 𝔞 1).mkQ x)

def QuotOf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k)
    (K₀ : Subgroup G.GAf), IsLev L 𝔫 K₀ → ∀ (M : Lv p) (c : ℕ) (a : 𝓞 D.F), S.Num M.1 c a → ∀ C : S.Cl (T.M M).univ c a,
      IsQuot T.X (Ow w) K₀ (T.lev M) ((GlobalTheory.KS.pow S.Y.univ.A k).hom ≫ S.Y.s) (S.pi T C)

def ExtEx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫)
    (N₁ : ℕ) (𝔟 : Ideal (𝓞 D.F)), LevAt D q r 𝔴 N₁ 𝔟 → Nonempty (Ext S N₁ 𝔟)

def StepPow : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k)
    (N₁ N₂ : ℕ) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (X₁ : Ext S N₁ 𝔟₁) (X₂ : Ext S N₂ 𝔟₂) (h : G.GAf) (M₁ M₂ : Lv p) (c₁ c₂ : ℕ) (a₁ a₂ : 𝓞 D.F)
    (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂) (a b : _),
    (∀ W : Wit T h M₁ M₂, ∃ d : Down X₁ X₂, d.Extends W C₁ C₂) →
    ∃ t : (GlobalTheory.KS.pow X₁.Y.univ.A k).left ⟶ (GlobalTheory.KS.pow X₂.Y.univ.A k).left,
      t ≫ (GlobalTheory.KS.pow X₂.Y.univ.A k).hom ≫ X₂.Y.s = (GlobalTheory.KS.pow X₁.Y.univ.A k).hom ≫ X₁.Y.s ∧
      X₁.site.pi T C₁ ≫ t = T.X.tr (T.lev M₁) (T.lev M₂) h a b ≫ X₂.site.pi T C₂

end UpperTheory.Gal.FiniteEtaleModels
