import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EDual

def Base : Prop := A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ DivisorNaturality ∧ DivisorRingCompatibility ∧ DivisorSupportCondition ∧ DivisorAdditivity ∧ A7 ∧ A8 ∧ A9 ∧ A10 ∧ A11 ∧
  B1 ∧ B2 ∧ B3 ∧ B4 ∧ B5 ∧ DivisorPicardCompatibility ∧ B6h1 ∧ B7 ∧ C1 ∧ C2 ∧ C3 ∧ C4 ∧ C5 ∧ D1 ∧ E1 ∧ E2 ∧ E3 ∧ E4 ∧ E6

abbrev pt (k : Type) [Field k] : Scheme.{0} := Spec (CommRingCat.of k)

abbrev ptMap {k : Type} [Field k] (σ : k ≃+* k) : pt k ⟶ pt k := Spec.map (CommRingCat.ofHom σ.toRingHom)

def Deg {Y X : Scheme.{0}} (f : Y ⟶ X) (r : ℕ) : Prop :=
  ∃ V : X.Opens, Dense (V : Set X) ∧ Etale (f ∣_ V) ∧
    ∀ x : X, x ∈ V → IsClosed ({x} : Set X) → Nat.card (f ⁻¹' {x} : Set Y) = r

structure SP (k : Type) [Field k] (d : ℕ) where
  X : Scheme.{0}
  p : X ⟶ pt k
  proper : IsProper p
  smooth : SmoothOfRelativeDimension d p

structure Cpt (k : Type) [Field k] (d : ℕ) where
  X : Scheme.{0}
  Z : Scheme.{0}
  U : Scheme.{0}
  p : X ⟶ pt k
  ι : Z ⟶ X
  j : U ⟶ X
  proper : IsProper p
  closed : IsClosedImmersion ι
  opn : IsOpenImmersion j
  compl : IsCompl (Set.range ι) (Set.range j)
  smooth : SmoothOfRelativeDimension d (j ≫ p)

def Cpt.Q {k : Type} [Field k] {d : ℕ} (C : Cpt k d) : Spc := pushout (sch.map C.ι) (sch.map (C.ι ≫ C.p))

def Cpt.q {k : Type} [Field k] {d : ℕ} (C : Cpt k d) : C.Q ⟶ sch.obj (pt k) :=
  pushout.desc (sch.map C.p) (𝟙 _) (by rw [Category.comp_id, Functor.map_comp])

structure Cpt.Hom {k : Type} [Field k] {d : ℕ} (C' C : Cpt k d) where
  σ : k ≃+* k
  f : C'.X ⟶ C.X
  z : C'.Z ⟶ C.Z
  u : C'.U ⟶ C.U
  hp : f ≫ C.p = C'.p ≫ ptMap σ
  hz : C'.ι ≫ f = z ≫ C.ι
  hu : C'.j ≫ f = u ≫ C.j

def Cpt.Hom.Q {k : Type} [Field k] {d : ℕ} {C' C : Cpt k d} (φ : Cpt.Hom C' C) : C'.Q ⟶ C.Q :=
  pushout.map _ _ _ _ (sch.map φ.f) (sch.map (ptMap φ.σ)) (sch.map φ.z)
    (by rw [← Functor.map_comp, ← Functor.map_comp, φ.hz])
    (by rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, ← φ.hp, ← Category.assoc, φ.hz, Category.assoc])

def cupTop (q : ℕ) {E : Spc} (d : ℕ) {n i : ℤ} (a : Ht q E n i) (b : Ht q E (2 * d - n) (d - i)) : Ht q E (2 * d) d :=
  (cup q a b).cast (by ring) (by ring)

def lev {l : ℕ} [Fact l.Prime] {E : Spc} {n i : ℤ} (a : Hl l E n i) (m : ℕ) : Ht (l ^ m) E n i := a.1 m

def IsCupL {l : ℕ} [Fact l.Prime] {E : Spc} (d : ℕ) {n i : ℤ} (a : Hl l E n i) (b : Hl l E (2 * d - n) (d - i))
    (c : Hl l E (2 * d) d) : Prop :=
  ∀ m : ℕ, lev (E := E) (n := 2 * d) (i := d) c m =
    cupTop (l ^ m) (E := E) d (n := n) (i := i) (lev (E := E) a m) (lev (E := E) (n := 2 * d - n) (i := d - i) b m)

def toQ {l : ℕ} [Fact l.Prime] {E : Spc} {n i : ℤ} (a : Hl l E n i) : HQ l E n i := (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] a

def TorProper (k : Type) [Field k] : Prop := ∀ d : ℕ,
  ∃ tr : ∀ (q : ℕ) (X : SP k d), Ht q (sch.obj X.X) (2 * d) d →+ ZMod q,
    (∀ (q : ℕ) [NeZero q], IsUnit (q : k) → ∀ (X : SP k d) (n i : ℤ), Finite (Ht q (sch.obj X.X) n i) ∧
      ∀ φ : Ht q (sch.obj X.X) (2 * d - n) (d - i) →+ ZMod q,
        ∃! a : Ht q (sch.obj X.X) n i, ∀ b, φ b = tr q X (cupTop q d a b)) ∧
    (∀ (q : ℕ) [NeZero q], IsUnit (q : k) → ∀ (Y X : SP k d) (σ : k ≃+* k) (f : Y.X ⟶ X.X) (r : ℕ),
      f ≫ X.p = Y.p ≫ ptMap σ → Deg f r → ∀ a, tr q Y (pull _ (sch.map f) _ _ a) = r • tr q X a) ∧
    ∀ (Q q : ℕ) [NeZero Q] (h : q ∣ Q), IsUnit (Q : k) → ∀ (X : SP k d) (a : Ht Q (sch.obj X.X) (2 * d) d),
      tr q X (red Q q _ _ _ a) = ZMod.castHom h (ZMod q) (tr Q X a)

def AdicProper (k : Type) [Field k] : Prop := ∀ (l : ℕ) [Fact l.Prime], IsUnit (l : k) → ∀ d : ℕ,
  ∃ (tr : ∀ X : SP k d, HQ l (sch.obj X.X) (2 * d) d →ₗ[ℚ_[l]] ℚ_[l])
    (B : ∀ (X : SP k d) (n i : ℤ), HQ l (sch.obj X.X) n i →ₗ[ℚ_[l]] HQ l (sch.obj X.X) (2 * d - n) (d - i) →ₗ[ℚ_[l]] ℚ_[l]),
    (∀ (X : SP k d) (n i : ℤ), FiniteDimensional ℚ_[l] (HQ l (sch.obj X.X) n i) ∧ Function.Bijective (B X n i)) ∧
    (∀ (X : SP k d) (n i : ℤ) (a : Hl l (sch.obj X.X) n i) (b : Hl l (sch.obj X.X) (2 * d - n) (d - i)) (c : Hl l (sch.obj X.X) (2 * d) d),
      IsCupL d a b c → B X n i (toQ a) (toQ b) = tr X (toQ c)) ∧
    ∀ (Y X : SP k d) (σ : k ≃+* k) (f : Y.X ⟶ X.X) (r : ℕ), f ≫ X.p = Y.p ≫ ptMap σ → Deg f r →
      (∀ c, tr Y (pullHQ l (sch.map f) _ _ c) = r • tr X c) ∧
      ∀ n i a b, B Y n i (pullHQ l (sch.map f) _ _ a) (pullHQ l (sch.map f) _ _ b) = r • B X n i a b

def TorOpen (k : Type) [Field k] : Prop := ∀ d : ℕ,
  ∃ B : ∀ (q : ℕ) (C : Cpt k d) (n i : ℤ), Ht q C.Q n i →+ Ht q (sch.obj C.U) (2 * d - n) (d - i) →+ ZMod q,
    (∀ (q : ℕ) [NeZero q], IsUnit (q : k) → ∀ (C : Cpt k d) (n i : ℤ), Finite (Ht q C.Q n i) ∧ Finite (Ht q (sch.obj C.U) n i) ∧
      Function.Surjective (B q C n i) ∧ ∀ a, B q C n i a = 0 ↔ a ∈ Set.range (pull _ C.q (tw q i) n)) ∧
    (∀ (q : ℕ) [NeZero q], IsUnit (q : k) → ∀ (C' C : Cpt k d) (φ : Cpt.Hom C' C) (r : ℕ), Deg φ.u r → ∀ n i a b,
      B q C' n i (pull _ φ.Q _ _ a) (pull _ (sch.map φ.u) _ _ b) = r • B q C n i a b) ∧
    ∀ (Q q : ℕ) [NeZero Q] (h : q ∣ Q), IsUnit (Q : k) → ∀ (C : Cpt k d) (n i : ℤ) a b,
      B q C n i (red Q q _ _ _ a) (red Q q _ _ _ b) = ZMod.castHom h (ZMod q) (B Q C n i a b)

def AdicOpen (k : Type) [Field k] : Prop := ∀ (l : ℕ) [Fact l.Prime], IsUnit (l : k) → ∀ d : ℕ,
  ∃ B : ∀ (C : Cpt k d) (n i : ℤ), HQ l C.Q n i →ₗ[ℚ_[l]] HQ l (sch.obj C.U) (2 * d - n) (d - i) →ₗ[ℚ_[l]] ℚ_[l],
    (∀ C n i, FiniteDimensional ℚ_[l] (HQ l C.Q n i) ∧ FiniteDimensional ℚ_[l] (HQ l (sch.obj C.U) n i) ∧
      Function.Surjective (B C n i) ∧ LinearMap.ker (B C n i) = LinearMap.range (pullHQ l C.q n i)) ∧
    ∀ (C' C : Cpt k d) (φ : Cpt.Hom C' C) (r : ℕ), Deg φ.u r → ∀ n i a b,
      B C' n i (pullHQ l φ.Q _ _ a) (pullHQ l (sch.map φ.u) _ _ b) = r • B C n i a b

def GoalProper : Prop := Base → E8 → ∀ (k : Type) [Field k] [IsSepClosed k], AdicProper k

def GoalOpen : Prop := Base → ∀ (k : Type) [Field k] [IsSepClosed k], AdicOpen k

def Goal : Prop := GoalProper ∧ GoalOpen

def PointClasses (k : Type) [Field k] : Prop := ∀ d : ℕ,
  ∃ cl : ∀ (q : ℕ) (X : SP k d), X.X → Ht q (sch.obj X.X) (2 * d) d,
    (∀ (q : ℕ) [NeZero q], IsUnit (q : k) → ∀ (X : SP k d), IsIntegral X.X → ∀ x : X.X, IsClosed ({x} : Set X.X) →
      Function.Bijective (fun m : ZMod q => m • cl q X x) ∧ ∀ y : X.X, IsClosed ({y} : Set X.X) → cl q X y = cl q X x) ∧
    (∀ (q : ℕ) [NeZero q], IsUnit (q : k) → ∀ (Y X : SP k d) (σ : k ≃+* k) (f : Y.X ⟶ X.X), f ≫ X.p = Y.p ≫ ptMap σ →
      ∀ (V : X.X.Opens), Etale (f ∣_ V) → ∀ x : X.X, x ∈ V → IsClosed ({x} : Set X.X) → ∀ s : Finset Y.X,
        (s : Set Y.X) = f ⁻¹' {x} → pull _ (sch.map f) _ _ (cl q X x) = ∑ y ∈ s, cl q Y y) ∧
    ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → IsUnit (Q : k) → ∀ (X : SP k d) (x : X.X), IsClosed ({x} : Set X.X) →
      red Q q _ _ _ (cl Q X x) = cl q X x

def Insep : Prop := Base → ∀ (q : ℕ) {Y X : Scheme.{0}} (f : Y ⟶ X) [IsIntegralHom f] [Surjective f] [UniversallyInjective f],
  IsUnit (q : Γ(X, ⊤)) → ∀ i : ℤ, Eqv _ (sch.map f) (tw q i)

def ProperExc : Prop := Base → ∀ (k : Type) [Field k] (d q : ℕ) [NeZero q], IsUnit (q : k) → ∀ (C' C : Cpt k d)
  (φ : Cpt.Hom C' C), IsIso φ.u → ∀ i : ℤ, Eqv _ φ.Q (tw q i)

def FieldExt : Prop := Base → ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] (φ : k →+* K) (q : ℕ) [NeZero q],
  IsUnit (q : k) → ∀ {X : Scheme.{0}} (p : X ⟶ pt k) [IsProper p] [Smooth p] (i : ℤ),
  Eqv _ (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom φ)))) (tw q i)

def PointAlg : Prop := Base → E8 → ∀ (k : Type) [Field k] [IsAlgClosed k], PointClasses k

def TorAlg : Prop := Base → E8 → ∀ (k : Type) [Field k] [IsAlgClosed k], PointClasses k → TorProper k

def SepProper : Prop := Base → ∀ (k : Type) [Field k] [IsSepClosed k], TorProper (AlgebraicClosure k) → TorProper k

def SepOpen : Prop := Base → ∀ (k : Type) [Field k] [IsSepClosed k], TorOpen (AlgebraicClosure k) → TorOpen k

def AdicFin : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (i : ℤ), Inv l E → (∀ m n, Finite (Ht (l ^ m) E n i)) →
  ∀ n, Module.Finite ℤ_[l] (Hl l E n i) ∧ ∃ c : ℕ, ∀ (m : ℕ) (x : Ht (l ^ m) E n i), ∃ y : Hl l E n i, lev y m = l ^ c • x

def LimProper : Prop := Base → ∀ (k : Type) [Field k], TorProper k → AdicProper k

def LimOpen : Prop := Base → ∀ (k : Type) [Field k], TorOpen k → AdicOpen k

def OpenAlg : Prop := Base → ∀ (k : Type) [Field k] [IsAlgClosed k], TorOpen k

end LateralTheory.EDual
end
