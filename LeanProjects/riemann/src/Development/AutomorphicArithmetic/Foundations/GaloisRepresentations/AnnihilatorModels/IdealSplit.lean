import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PulledRead
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field

namespace UpperTheory.Gal.crystallineComparison.Mod

open GlobalTheory.UPel.HT.EtLev

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {M : Model b N} {r : ℤ}
  {w 𝔞 : Ideal (𝓞 D.F)} {j c ρ : ℕ}

structure TjE (E : EtModel b N 𝔞 ρ) {π : E.X ⟶ M.X} (mπ : ObjMap E.univ M.univ π) (T : TjD M r w j c) : Type 1 where
  Z : Scheme.{0}
  s : Z ⟶ E.X
  t : Z ⟶ E.X
  g : Z ⟶ T.Y
  pb : IsPullback s g π T.s
  tπ : t ≫ π = g ≫ T.t
  o : Obj b N (s ≫ E.s)
  o' : Obj b N (s ≫ E.s)
  ms : ObjMap o E.univ s
  mt : ObjMap o' E.univ t
  ψ : o.A ⟶ o'.A
  isog : IsPIsog c o o' ψ
  tj : IsTj r w j o o' ψ
  m₀ : ObjMap o T.o g
  m' : ObjMap o' T.o' g
  sq : m₀.φ ≫ T.ψ.left = ψ.left ≫ m'.φ
  tri : m₀.φ ≫ T.ms.φ = ms.φ ≫ mπ.φ
  tri' : m'.φ ≫ T.mt.φ = mt.φ ≫ mπ.φ
  lev : ∀ (y : D.La) (l : 𝟙_ (Over Z) ⟶ o.A), l.left ≫ ms.φ = s ≫ (E.lv y).left → (l ≫ ψ).left ≫ mt.φ = t ≫ (E.lv y).left

variable {E : EtModel b N 𝔞 ρ} {π : E.X ⟶ M.X} {mπ : ObjMap E.univ M.univ π} {T : TjD M r w j c}

def TjE.ksP (L : TjE E mπ T) (k : ℕ) : (GlobalTheory.KS.pow L.o.A k).left ⟶ (GlobalTheory.KS.pow E.univ.A k).left := GlobalTheory.KS.powMap L.s L.ms.φ L.ms.cart.1.w k

def TjE.ksR (L : TjE E mπ T) (k : ℕ) : (GlobalTheory.KS.pow L.o.A k).left ⟶ (GlobalTheory.KS.pow E.univ.A k).left :=
  (Limits.Pi.map fun _ : Fin k => L.ψ).left ≫ GlobalTheory.KS.powMap L.t L.mt.φ L.mt.cart.1.w k

structure KSOKE (L : TjE E mπ T) (k d : ℕ) : Prop where
  fin : IsFinite (L.ksP k)
  et : Etale (L.ksP k ∣_ (GlobalTheory.KS.pow E.univ.A k).left.basicOpen ((p : ℕ) : Γ((GlobalTheory.KS.pow E.univ.A k).left, ⊤)))
  deg : ∀ (K : Type) [Field K] [IsAlgClosed K], (p : K) ≠ 0 → ∀ y : Spec (CommRingCat.of K) ⟶ (GlobalTheory.KS.pow E.univ.A k).left,
    Nat.card {z : Spec (CommRingCat.of K) ⟶ (GlobalTheory.KS.pow L.o.A k).left // z ≫ L.ksP k = y} = d

def KSOKE.corr {L : TjE E mπ T} {k d : ℕ} (h : KSOKE L k d) : Corr p (GlobalTheory.KS.pow E.univ.A k).left :=
  ⟨(GlobalTheory.KS.pow L.o.A k).left, L.ksP k, L.ksR k, d, h.fin, h.et, h.deg⟩

end

def TjExF : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j : ℕ), j ≤ D.n → ∃ T : TjD M r w j (p ^ (f * j)), Flat (T.s ≫ M.s)

def TjEEx : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j c : ℕ) (T : TjD M r w j c), Flat (T.s ≫ M.s) → ∀ (𝔞 : Ideal (𝓞 D.F)) (ρ : ℕ), 𝔞 ⊔ w = ⊤ →
    (∃ e : ℕ, uIdeal D r ^ e ≤ 𝔞) → ∀ (E : EtModel b N 𝔞 ρ) (π : E.X ⟶ M.X), π ≫ M.s = E.s → ∀ mπ : ObjMap E.univ M.univ π,
    Nonempty (TjE E mπ T)

def OrdKSE : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (ϖ : O), Irreducible ϖ → ∀ (T : ∀ j : Fin (D.n + 1), TjD M r w j (p ^ (f * j)))
    (𝔞 : Ideal (𝓞 D.F)) (ρ : ℕ) (E : EtModel b N 𝔞 ρ) (π : E.X ⟶ M.X), π ≫ M.s = E.s → Flat π →
    ∀ (mπ : ObjMap E.univ M.univ π) (L : ∀ j, TjE E mπ (T j)) (k : ℕ),
    ∃ (d : Fin (D.n + 1) → ℕ) (h : ∀ j, KSOKE (L j) k (d j)),
      (∀ j, (h j).corr.r ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ E.s = (h j).corr.p ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ E.s) ∧
      OrdPt p (p ^ f) D.n (fn ((GlobalTheory.KS.pow E.univ.A k).hom ≫ E.s) ϖ) fun j => (h j).corr

def OrdEmb : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (ϖ : O), Irreducible ϖ → ∀ (T : ∀ j : Fin (D.n + 1), TjD M r w j (p ^ (f * j)))
    (Y : Scheme.{0}) (h : Y ⟶ M.X), Flat h → ∀ (I : Type) (a : I → (Y ⟶ M.univ.A.left)), (∀ i, a i ≫ M.univ.A.hom = h) →
    (∀ (X : Scheme.{0}) (u v : X ⟶ Y), u ≫ h = v ≫ h → (∀ i, u ≫ a i = v ≫ a i) → u = v) →
    ∀ (C : Fin (D.n + 1) → Corr p Y) (g : ∀ j, (C j).Z ⟶ (T j).Y), (∀ j, IsPullback (C j).p (g j) h (T j).s) →
    (∀ j, (C j).r ≫ h = g j ≫ (T j).t) → (∀ j i e, (C j).r ≫ a i = (T j).img (g j) ((C j).p ≫ a i) e) →
    OrdPt p (p ^ f) D.n (fn (h ≫ M.s) ϖ) C

def CorrBC : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j : ℕ), j ≤ D.n → ∀ (T : TjD M r w j (p ^ (f * j))) (Y Z : Scheme.{0}) (h : Y ⟶ M.X) (s : Z ⟶ Y)
    (g : Z ⟶ T.Y), IsPullback s g h T.s → IsFinite s ∧ Etale (s ∣_ Y.basicOpen ((p : ℕ) : Γ(Y, ⊤))) ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K], (p : K) ≠ 0 → ∀ y : Spec (CommRingCat.of K) ⟶ Y,
        Nat.card {z : Spec (CommRingCat.of K) ⟶ Z // z ≫ s = y} = Nat.card (Gr (𝓞 D.F ⧸ w) (Fin D.n → 𝓞 D.F ⧸ w) j)

def UKerW : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j c : ℕ) (T : TjD M r w j c), Flat (T.s ≫ M.s) →
    ∀ (X : Over T.Y) (g : X ⟶ T.o.A), UKer r T.o T.ψ X g → KilledBy T.o w g

def IdealSplit : Prop := ∀ (A : Type) [CommRing A] [IsDedekindDomain A] (𝔞 : Ideal A) (x : A), x ≠ 0 → ∀ ρ : ℕ,
    ∃ (m : ℕ) (α : A), α - 1 ∈ 𝔞 ^ ρ ∧ ∀ a ∈ 𝔞 ^ m, a * α ∈ Ideal.span {x}

def LevPull : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (f : S' ⟶ S) (o : Obj b N s) (o₁ : Obj b N s')
    (m : ObjMap o₁ o f) (𝔞 : Ideal (𝓞 D.F)) (ρ : ℕ) (lv : D.La → (𝟙_ (Over S) ⟶ o.A)), IsEtLev o 𝔞 ρ lv →
    ∃ l : D.La → (𝟙_ (Over S') ⟶ o₁.A), IsEtLev o₁ 𝔞 ρ l ∧ ∀ y, (l y).left ≫ m.φ = f ≫ (lv y).left

def LevPush : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (r : ℤ) (w 𝔞 : Ideal (𝓞 D.F)) (ρ : ℕ), 𝔞 ⊔ w = ⊤ → (∃ e : ℕ, uIdeal D r ^ e ≤ 𝔞) →
    ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (c : ℕ) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ →
    (∀ (X : Over S) (g : X ⟶ o.A), UKer r o ψ X g → KilledBy o w g) →
    ∀ lv : D.La → (𝟙_ (Over S) ⟶ o.A), IsEtLev o 𝔞 ρ lv → IsEtLev o' 𝔞 ρ fun y => lv y ≫ ψ

def EtInj : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (M : Model b N) (𝔞 : Ideal (𝓞 D.F)) (ρ : ℕ) (E : EtModel b N 𝔞 ρ) (π : E.X ⟶ M.X),
    π ≫ M.s = E.s → ∀ (mπ : ObjMap E.univ M.univ π) (X : Scheme.{0}) (u v : X ⟶ E.X), u ≫ π = v ≫ π →
    (∀ y, u ≫ (E.lv y).left ≫ mπ.φ = v ≫ (E.lv y).left ≫ mπ.φ) → u = v

end UpperTheory.Gal.crystallineComparison.Mod
