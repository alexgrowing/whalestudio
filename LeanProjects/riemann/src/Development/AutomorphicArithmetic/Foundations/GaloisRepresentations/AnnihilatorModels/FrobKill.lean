import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProd
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Definitions.Divisors.HxiTZeroComb
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
attribute [local instance] Ideal.Quotient.field

namespace UpperTheory.Gal.crystallineComparison.Mod

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

def Univ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) (M : Model b N) {Y : Scheme.{0}} (s : Y ⟶ M.X) (o o' : Obj b N (s ≫ M.s))
    (ψ : o.A ⟶ o'.A) : Prop :=
  ∀ (S : Scheme.{0}) (x : S ⟶ M.X) (o₁ o₁' : Obj b N (x ≫ M.s)) (_ : ObjMap o₁ M.univ x) (ψ₁ : o₁.A ⟶ o₁'.A),
    IsUnit ((p : ℕ) : Γ(S, ⊤)) → IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ →
    ∃! y : S ⟶ Y, y ≫ s = x ∧ ∃ (m₀ : ObjMap o₁ o y) (m₁ : ObjMap o₁' o' y), m₀.φ ≫ ψ.left = ψ₁.left ≫ m₁.φ

structure TjD (M : Model b N) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) : Type 1 where
  Y : Scheme.{0}
  s : Y ⟶ M.X
  t : Y ⟶ M.X
  st : s ≫ M.s = t ≫ M.s
  o : Obj b N (s ≫ M.s)
  o' : Obj b N (s ≫ M.s)
  ms : ObjMap o M.univ s
  mt : ObjMap o' M.univ t
  ψ : o.A ⟶ o'.A
  fin : IsFinite s
  et : Etale (s ∣_ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))
  isog : IsPIsog c o o' ψ
  tj : IsTj r w j o o' ψ
  univ : Univ r w j c M s o o' ψ

variable {M : Model b N} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ}

def TjD.ksP (T : TjD M r w j c) (k : ℕ) : (GlobalTheory.KS.pow T.o.A k).left ⟶ (GlobalTheory.KS.pow M.univ.A k).left :=
  GlobalTheory.KS.powMap T.s T.ms.φ T.ms.cart.1.w k

def TjD.ksR (T : TjD M r w j c) (k : ℕ) : (GlobalTheory.KS.pow T.o.A k).left ⟶ (GlobalTheory.KS.pow M.univ.A k).left :=
  (Limits.Pi.map fun _ : Fin k => T.ψ).left ≫ GlobalTheory.KS.powMap T.t T.mt.φ T.mt.cart.1.w k

structure KSOK (T : TjD M r w j c) (k d : ℕ) : Prop where
  fin : IsFinite (T.ksP k)
  et : Etale (T.ksP k ∣_ (GlobalTheory.KS.pow M.univ.A k).left.basicOpen ((p : ℕ) : Γ((GlobalTheory.KS.pow M.univ.A k).left, ⊤)))
  deg : ∀ (K : Type) [Field K] [IsAlgClosed K], (p : K) ≠ 0 → ∀ y : Spec (CommRingCat.of K) ⟶ (GlobalTheory.KS.pow M.univ.A k).left,
    Nat.card {z : Spec (CommRingCat.of K) ⟶ (GlobalTheory.KS.pow T.o.A k).left // z ≫ T.ksP k = y} = d

def KSOK.corr {T : TjD M r w j c} {k d : ℕ} (h : KSOK T k d) : Corr p (GlobalTheory.KS.pow M.univ.A k).left :=
  ⟨(GlobalTheory.KS.pow T.o.A k).left, T.ksP k, T.ksR k, d, h.fin, h.et, h.deg⟩

def TjD.img (T : TjD M r w j c) {X : Scheme.{0}} (z : X ⟶ T.Y) (a : X ⟶ M.univ.A.left) (h : a ≫ M.univ.A.hom = z ≫ T.s) :
    X ⟶ M.univ.A.left := T.ms.cart.1.lift a z h ≫ T.ψ.left ≫ T.mt.φ

structure Pulled (T : TjD M r w j c) {S : Scheme.{0}} {x : S ⟶ M.X} {σ : S ⟶ Sp R} {o₁ : Obj b N σ} (m₁ : ObjMap o₁ M.univ x)
    (y : S ⟶ T.Y) : Type 1 where
  o' : Obj b N σ
  ψ : o₁.A ⟶ o'.A
  m₀ : ObjMap o₁ T.o y
  m' : ObjMap o' T.o' y
  sq : m₀.φ ≫ T.ψ.left = ψ.left ≫ m'.φ
  tri : m₀.φ ≫ T.ms.φ = m₁.φ
  isog : IsPIsog c o₁ o' ψ
  tj : IsTj r w j o₁ o' ψ

def UKer (r : ℤ) {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) {A' : Over S} [GrpObj A'] (ψ : o.A ⟶ A') (T : Over S)
    (g : T ⟶ o.A) : Prop := g ≫ ψ = 1 ∧ ∃ e : ℕ, KilledBy o (uIdeal D r ^ e) g

structure WMod {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) (T : Over S) : Type 1 where
  H : Type
  [grp : AddCommGroup H]
  [md : Module (𝓞 D.F ⧸ w) H]
  pt : H → (T ⟶ o.A)
  inj : Function.Injective pt
  range : ∀ g, (∃ h, pt h = g) ↔ KilledBy o w g
  add : ∀ x y, pt (x + y) = pt x * pt y
  smul : ∀ (a : 𝓞 D.F) x, pt (Ideal.Quotient.mk w a • x) = pt x ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)

attribute [instance] WMod.grp WMod.md

end

structure Std {p : ℕ} [Fact p.Prime] {D : Datum p} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) : Prop where
  pmem : (p : O) ∈ IsLocalRing.maximalIdeal O
  card : Nat.card (IsLocalRing.ResidueField O) = p ^ f
  three : 3 ≤ N
  cop : N.Coprime p
  m1 : D.m = 1
  a1 : D.a = 1
  ule : uIdeal D r ≤ w
  norm : Ideal.absNorm w = p ^ f
  tw : ∀ i, ∀ x ∈ w, b.t i x ∈ IsLocalRing.maximalIdeal O

abbrev algPt (V B : Type) [CommRing V] [CommRing B] [Algebra V B] : Over (Sp V) := Over.mk (spMap (algebraMap V B))

def RepFF {S : Scheme.{0}} (A : Over S) (P : ∀ T : Over S, (T ⟶ A) → Prop) : Prop :=
  ∃ (K : Over S) (i : K ⟶ A), Mono i ∧ IsFinite K.hom ∧ Flat K.hom ∧ ∀ (T : Over S) (g : T ⟶ A), InSub i g ↔ P T g

def RepAlg {V : Type} [CommRing V] (A : Over (Sp V)) (P : ∀ T : Over (Sp V), (T ⟶ A) → Prop) (d : ℕ) : Prop :=
  ∃ (B : Type) (_ : CommRing B) (_ : Algebra V B), Module.Finite V B ∧ Module.Free V B ∧ Module.finrank V B = d ∧
    ∃ i : algPt V B ⟶ A, Mono i ∧ ∀ (T : Over (Sp V)) (g : T ⟶ A), InSub i g ↔ P T g

def IsSub {S : Scheme.{0}} (A : Over S) [GrpObj A] (P : ∀ T : Over S, (T ⟶ A) → Prop) : Prop :=
  ∀ T : Over S, P T 1 ∧ ∀ g h : T ⟶ A, P T g → P T h → P T (g * h⁻¹)

def Inf {κ Λ : Type} [Field κ] [CommRing Λ] [Algebra κ Λ] (ε : Λ →ₐ[κ] κ) {A : Over (Sp κ)} [GrpObj A] (g : algPt κ Λ ⟶ A) : Prop :=
  spMap ε.toRingHom ≫ g.left = (1 : 𝟙_ (Over (Sp κ)) ⟶ A).left

def FrobKill (p f : ℕ) (hp : p.Prime) {S : Scheme.{0}} {A T : Over S} [GrpObj A] (g : T ⟶ A) : Prop :=
  ∀ h : (p : Γ(T.left, ⊤)) = 0,
    GlobalTheory.SS.FrobField.absFrob T.left p f hp h ≫ g.left = GlobalTheory.SS.FrobField.absFrob T.left p f hp h ≫ (1 : T ⟶ A).left

def TanLe {κ : Type} [Field κ] (A : Over (Sp κ)) [GrpObj A] (P : ∀ T : Over (Sp κ), (T ⟶ A) → Prop) : Prop :=
  ∃ v₀ : algPt κ (DualNumber κ) ⟶ A, P _ v₀ ∧ Inf (TrivSqZeroExt.fstHom κ κ κ) v₀ ∧ ∀ v : algPt κ (DualNumber κ) ⟶ A, P _ v →
    Inf (TrivSqZeroExt.fstHom κ κ κ) v → ∃ c : κ, v.left = spMap (epsScale c) ≫ v₀.left

def EsNorm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∃ (Y : Scheme.{0}) (s t : Y ⟶ M.X) (o o' : Obj b N (s ≫ M.s)) (_ : ObjMap o M.univ s) (_ : ObjMap o' M.univ t) (ψ : o.A ⟶ o'.A), s ≫ M.s = t ≫ M.s ∧ IsFinite s ∧ IsFinite t ∧ (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧ Flat (s ≫ M.s) ∧ IsPIsog c o o' ψ ∧ IsTj r w j o o' ψ ∧ Univ r w j c M s o o' ψ

def EsGen : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∃ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (_ : ObjMap o₀ M.univ s₀) (_ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s ∧ gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ ∧ gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ ∧ IsFinite gs ∧ Etale gs ∧ IsFinite gt ∧ Etale gt ∧ IsPIsog c o₀ o₀' ψ₀ ∧ IsTj r w j o₀ o₀' ψ₀ ∧ Univ r w j c M s₀ o₀ o₀' ψ₀

def OrdGen : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → D.m = 1 → ∀ (i : Fin D.a) (w : Ideal (𝓞 D.F)), (IsLocalRing.maximalIdeal R).comap (b.t i) = w → ∀ (M : Model b N) (z : M.X), M.s.base z = IsLocalRing.closedPoint R → (∀ z' : M.X, M.s.base z' = IsLocalRing.closedPoint R → z' ⤳ z → z' = z) → ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ M.X), (∀ q, y.base q = z) → IsWOrd M.univ w y

def QuotObj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∀ (o : Obj b N s) (K : Over S) [GrpObj K] (i : K ⟶ o.A), IsMonHom i → Mono i → IsFinite K.hom → Etale K.hom → (∀ (T : Over S) (x : T ⟶ o.A), InSub i x → KilledBy o w x) → (∀ a : D.O, ∃ g : K ⟶ K, g ≫ i = i ≫ o.act.act a) → IsIsogDeg (toUnit K) (Ideal.absNorm w ^ j) → ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ ∧ IsTj r w j o o' ψ ∧ ∀ (T : Over S) (x : T ⟶ o.A), (x ≫ ψ = 1 ∧ ∃ e : ℕ, KilledBy o (uIdeal D r ^ e) x) ↔ InSub i x

def TjEx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (j : ℕ), j ≤ D.n →
    Nonempty (TjD M r w j (p ^ (f * j)))

def EW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N)
    (T : ∀ j : Fin (D.n + 1), TjD M r w j (p ^ (f * j)))
    (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)] [IsAlgClosed (IsLocalRing.ResidueField V)],
    (p : V) ≠ 0 → ∀ x : Sp V ⟶ M.X, M.s (x (IsLocalRing.closedPoint V)) = IsLocalRing.closedPoint O → IsWOrd M.univ w (resPt V ≫ x) →
    ∀ φ : IsLocalRing.ResidueField V →+* IsLocalRing.ResidueField V, (∀ a, φ a = a ^ p ^ f) →
    ∃ (H : Type) (_ : AddCommGroup H) (_ : Module (𝓞 D.F ⧸ w) H) (_ : Module.Finite (𝓞 D.F ⧸ w) H) (C : Submodule (𝓞 D.F ⧸ w) H)
      (e : ∀ j, {z : Sp V ⟶ (T j).Y // z ≫ (T j).s = x} ≃ Gr (𝓞 D.F ⧸ w) H j),
      Module.finrank (𝓞 D.F ⧸ w) H = D.n ∧ Module.finrank (𝓞 D.F ⧸ w) C = 1 ∧
      (∀ j z z', ¬ C ≤ (e j z).1 → ¬ C ≤ (e j z').1 → (e j z).1.map C.mkQ = (e j z').1.map C.mkQ →
        resPt V ≫ z.1 ≫ (T j).t = resPt V ≫ z'.1 ≫ (T j).t ∧
          ∀ a h h', (T j).img (resPt V ≫ z.1) a h = (T j).img (resPt V ≫ z'.1) a h') ∧
      ∀ (j j' : Fin (D.n + 1)) z z', (j : ℕ) = j' + 1 → C ≤ (e j z).1 → ¬ C ≤ (e j' z').1 → (e j z).1.map C.mkQ = (e j' z').1.map C.mkQ →
        resPt V ≫ z.1 ≫ (T j).t = spMap φ ≫ resPt V ≫ z'.1 ≫ (T j').t ∧
          ∀ a h h', (T j).img (resPt V ≫ z.1) a h = spMap φ ≫ (T j').img (resPt V ≫ z'.1) a h'

def OrdKS : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (ϖ : O),
    Irreducible ϖ → ∀ (f : ℕ) (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N)
    (T : ∀ j : Fin (D.n + 1), TjD M r w j (p ^ (f * j))) (k : ℕ),
    ∃ (d : Fin (D.n + 1) → ℕ) (h : ∀ j, KSOK (T j) k (d j)),
      (∀ j, (h j).corr.r ≫ (GlobalTheory.KS.pow M.univ.A k).hom ≫ M.s = (h j).corr.p ≫ (GlobalTheory.KS.pow M.univ.A k).hom ≫ M.s) ∧
      OrdPt p (p ^ f) D.n (fn ((GlobalTheory.KS.pow M.univ.A k).hom ≫ M.s) ϖ) fun j => (h j).corr

end UpperTheory.Gal.crystallineComparison.Mod
