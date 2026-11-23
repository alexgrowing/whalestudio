import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field

namespace UpperTheory.Gal.crystallineComparison.Mod

def KerAt {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {M : Model b N} {r : ℤ}
    {w : Ideal (𝓞 D.F)} {j c : ℕ} (T : TjD M r w j c) {X : Scheme.{0}} (z : X ⟶ T.Y) (a : X ⟶ M.univ.A.left) : Prop :=
  ∀ a' : Over.mk z ⟶ T.o.A, a'.left ≫ T.ms.φ = a → a' ≫ T.ψ = 1

def TanAdd : Prop :=
  ∀ (κ : Type) [Field κ] (A : Over (Sp κ)) [GrpObj A] (v va vb vc : algPt κ (DualNumber κ) ⟶ A) (a b : κ),
    Inf (TrivSqZeroExt.fstHom κ κ κ) v → va.left = spMap (epsScale a) ≫ v.left → vb.left = spMap (epsScale b) ≫ v.left →
    vc.left = spMap (epsScale (a + b)) ≫ v.left → vc = va * vb

def PulledRead : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (M : Model b N) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) (T : TjD M r w j c)
    (S : Scheme.{0}) (x : S ⟶ M.X) (σ : S ⟶ Sp R) (o₁ : Obj b N σ) (m₁ : ObjMap o₁ M.univ x) (y : S ⟶ T.Y), y ≫ T.s = x →
    ∀ (P : Pulled T m₁ y) (a : 𝟙_ (Over S) ⟶ o₁.A), (a ≫ P.ψ = 1 ↔ KerAt T y (a.left ≫ m₁.φ)) ∧
      ∀ h, T.img y (a.left ≫ m₁.φ) h = (a ≫ P.ψ).left ≫ P.m'.φ ≫ T.mt.φ

def SecCard : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (M : Model b N) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) (T : TjD M r w j c), D.m = 1 →
    ∀ (K : Type) [Field K] [IsAlgClosed K], (p : K) ≠ 0 → ∀ (x : Sp K ⟶ M.X) (y : Sp K ⟶ T.Y), y ≫ T.s = x →
    Nat.card {g : Over.mk x ⟶ M.univ.A // KilledBy M.univ w g ∧ KerAt T y g.left} = Ideal.absNorm w ^ j

def SecInj : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j : ℕ), j ≤ D.n → ∀ (T : TjD M r w j (p ^ (f * j))) (K : Type) [Field K] [IsAlgClosed K], (p : K) ≠ 0 →
    ∀ (x : Sp K ⟶ M.X) (y y' : Sp K ⟶ T.Y), y ≫ T.s = x → y' ≫ T.s = x →
    (∀ g : Over.mk x ⟶ M.univ.A, KilledBy M.univ w g → (KerAt T y g.left ↔ KerAt T y' g.left)) → y = y'

def SecSurj : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j : ℕ), j ≤ D.n → ∀ (T : TjD M r w j (p ^ (f * j))) (K : Type) [Field K] [IsAlgClosed K], (p : K) ≠ 0 →
    ∀ (x : Sp K ⟶ M.X) (G : Subgroup (Over.mk x ⟶ M.univ.A)), (∀ g ∈ G, KilledBy M.univ w g) →
    (∀ g ∈ G, ∀ a : 𝓞 D.F, g ≫ M.univ.act.act (algebraMap (𝓞 D.F) D.O a) ∈ G) → Nat.card G = Ideal.absNorm w ^ j →
    ∃ y : Sp K ⟶ T.Y, y ≫ T.s = x ∧ ∀ g : Over.mk x ⟶ M.univ.A, KilledBy M.univ w g → (KerAt T y g.left ↔ g ∈ G)

def WVal : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (M : Model b N) (w : Ideal (𝓞 D.F)) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (x : Sp V ⟶ M.X),
    ∃ ρ : (Over.mk x ⟶ M.univ.A) ≃* (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ x) ⟶ M.univ.A),
      (∀ g, (ρ g).left = spMap (algebraMap V (FractionRing V)) ≫ g.left) ∧ (∀ g (a : M.univ.A ⟶ M.univ.A), ρ (g ≫ a) = ρ g ≫ a) ∧
      (∀ g, KilledBy M.univ w g ↔ KilledBy M.univ w (ρ g)) ∧
      ∀ (r : ℤ) (j c : ℕ) (T : TjD M r w j c) (z : Sp V ⟶ T.Y), z ≫ T.s = x → ∀ g,
        KerAt T z g.left ↔ KerAt T (spMap (algebraMap V (FractionRing V)) ≫ z) (ρ g).left

def RankN : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)], (p : V) ≠ 0 → ∀ (x : Sp V ⟶ M.X) (W : WMod M.univ w (Over.mk x)),
    Module.Finite (𝓞 D.F ⧸ w) W.H ∧ Module.finrank (𝓞 D.F ⧸ w) W.H = D.n

def LineC : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)] [IsAlgClosed (IsLocalRing.ResidueField V)], (p : V) ≠ 0 → ∀ (x : Sp V ⟶ M.X), IsWOrd M.univ w (resPt V ≫ x) →
    ∀ W : WMod M.univ w (Over.mk x), ∃ C : Submodule (𝓞 D.F ⧸ w) W.H, Module.finrank (𝓞 D.F ⧸ w) C = 1 ∧
      ∀ a a', resPt V ≫ (W.pt a).left = resPt V ≫ (W.pt a').left ↔ a - a' ∈ C

def SecEquiv : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j : ℕ), j ≤ D.n → ∀ (T : TjD M r w j (p ^ (f * j))) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)], (p : V) ≠ 0 →
    ∀ (x : Sp V ⟶ M.X) (W : WMod M.univ w (Over.mk x)), ∃ e : {z : Sp V ⟶ T.Y // z ≫ T.s = x} ≃ Gr (𝓞 D.F ⧸ w) W.H j,
      ∀ z h, h ∈ (e z).1 ↔ KerAt T z.1 (W.pt h).left

def KerRead : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j : ℕ) (T : TjD M r w j (p ^ (f * j))) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)], (p : V) ≠ 0 →
    ∀ (x : Sp V ⟶ M.X) (z : Sp V ⟶ T.Y), z ≫ T.s = x → ∀ (σ : Sp (IsLocalRing.ResidueField V) ⟶ Sp O) (o₁ : Obj b N σ)
      (m₁ : ObjMap o₁ M.univ (resPt V ≫ x)) (P : Pulled T m₁ (resPt V ≫ z)), RepAlg o₁.A (UKer r o₁ P.ψ) ((p ^ f) ^ j) ∧
      ∀ a : 𝟙_ (Over (Sp (IsLocalRing.ResidueField V))) ⟶ o₁.A, UKer r o₁ P.ψ _ a ↔
        ∃ g : Over.mk x ⟶ M.univ.A, KilledBy M.univ w g ∧ KerAt T z g.left ∧ a.left ≫ m₁.φ = resPt V ≫ g.left

def CaseE : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j c : ℕ) (T : TjD M r w j c) (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ M.X) (σ : Sp κ ⟶ Sp O),
    x ≫ M.s = σ → ∀ (o₁ : Obj b N σ) (m₁ : ObjMap o₁ M.univ x) (y y' : Sp κ ⟶ T.Y), y ≫ T.s = x → y' ≫ T.s = x →
    ∀ (P : Pulled T m₁ y) (P' : Pulled T m₁ y') (d : ℕ), RepAlg o₁.A (UKer r o₁ P.ψ) d → RepAlg o₁.A (UKer r o₁ P'.ψ) d →
    Nat.card {g : 𝟙_ (Over (Sp κ)) ⟶ o₁.A // UKer r o₁ P.ψ _ g} = d → (∀ g : 𝟙_ (Over (Sp κ)) ⟶ o₁.A, UKer r o₁ P.ψ _ g ↔ UKer r o₁ P'.ψ _ g) →
    y ≫ T.t = y' ≫ T.t ∧ ∀ a h h', T.img y a h = T.img y' a h'

def CaseW : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j : ℕ) (j₁ : ℕ), j₁ = j + 1 → ∀ (T : TjD M r w j₁ (p ^ (f * j₁))) (T' : TjD M r w j (p ^ (f * j)))
    (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p] (φ : κ →+* κ), (∀ a, φ a = a ^ p ^ f) → ∀ (x : Sp κ ⟶ M.X) (β : O →+* κ),
    x ≫ M.s = spMap β → (∀ a ∈ IsLocalRing.maximalIdeal O, β a = 0) → ∀ (o₁ : Obj b N (spMap β)) (m₁ : ObjMap o₁ M.univ x)
      (y : Sp κ ⟶ T.Y) (y' : Sp κ ⟶ T'.Y), y ≫ T.s = x → y' ≫ T'.s = x → ∀ (P : Pulled T m₁ y) (P' : Pulled T' m₁ y'),
    RepAlg o₁.A (UKer r o₁ P.ψ) ((p ^ f) ^ j₁) → RepAlg o₁.A (UKer r o₁ P'.ψ) ((p ^ f) ^ j) →
    Nat.card {g : 𝟙_ (Over (Sp κ)) ⟶ o₁.A // UKer r o₁ P'.ψ _ g} = (p ^ f) ^ j → (∀ g : 𝟙_ (Over (Sp κ)) ⟶ o₁.A, UKer r o₁ P.ψ _ g ↔ UKer r o₁ P'.ψ _ g) →
    y ≫ T.t = spMap φ ≫ y' ≫ T'.t ∧ ∀ a h h', T.img y a h = spMap φ ≫ T'.img y' a h'

def KSFin : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (M : Model b N) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) (T : TjD M r w j c) (k : ℕ),
    IsPullback (T.ksP k) (GlobalTheory.KS.pow T.o.A k).hom (GlobalTheory.KS.pow M.univ.A k).hom T.s ∧ IsFinite (T.ksP k) ∧
    Etale (T.ksP k ∣_ (GlobalTheory.KS.pow M.univ.A k).left.basicOpen ((p : ℕ) : Γ((GlobalTheory.KS.pow M.univ.A k).left, ⊤))) ∧
    T.ksR k ≫ (GlobalTheory.KS.pow M.univ.A k).hom = (GlobalTheory.KS.pow T.o.A k).hom ≫ T.t ∧
    ∀ (X : Scheme.{0}) (z : X ⟶ (GlobalTheory.KS.pow T.o.A k).left) (i : Fin k) h, z ≫ T.ksR k ≫ (GlobalTheory.KS.pr M.univ.A i).left =
      T.img (z ≫ (GlobalTheory.KS.pow T.o.A k).hom) (z ≫ T.ksP k ≫ (GlobalTheory.KS.pr M.univ.A i).left) h

def PowExt : Prop := ∀ (S : Scheme.{0}) (A : Over S) (k : ℕ), (Smooth A.hom → Flat (GlobalTheory.KS.pow A k).hom) ∧
    ∀ (X : Scheme.{0}) (u v : X ⟶ (GlobalTheory.KS.pow A k).left), u ≫ (GlobalTheory.KS.pow A k).hom = v ≫ (GlobalTheory.KS.pow A k).hom →
      (∀ i, u ≫ (GlobalTheory.KS.pr A i).left = v ≫ (GlobalTheory.KS.pr A i).left) → u = v

def KSDeg : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j : ℕ), j ≤ D.n → ∀ (T : TjD M r w j (p ^ (f * j))) (k : ℕ),
    KSOK T k (Nat.card (Gr (𝓞 D.F ⧸ w) (Fin D.n → 𝓞 D.F ⧸ w) j))

def OrdAt : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (ϖ : O), Irreducible ϖ → ∀ (k : ℕ) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)] [IsAlgClosed (IsLocalRing.ResidueField V)]
    (y : Sp V ⟶ (GlobalTheory.KS.pow M.univ.A k).left), GenPt (fn ((GlobalTheory.KS.pow M.univ.A k).hom ≫ M.s) ϖ) (y (IsLocalRing.closedPoint V)) →
    M.s ((y ≫ (GlobalTheory.KS.pow M.univ.A k).hom) (IsLocalRing.closedPoint V)) = IsLocalRing.closedPoint O ∧
      IsWOrd M.univ w (resPt V ≫ y ≫ (GlobalTheory.KS.pow M.univ.A k).hom)

end UpperTheory.Gal.crystallineComparison.Mod
