import Mathlib

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

namespace UpperTheory.Gal.crystallineComparison

def GenericProd {K : Type} [CommMonoid K] {n : ℕ} (α : Fin n → K) : Prop :=
  ∀ m : Fin n → ℕ, ∑ i, m i = n → ∏ i, α i ^ m i = ∏ i, α i → ∀ i, m i = 1

def GenericMul {K : Type} [CommMonoid K] (s : Multiset K) : Prop :=
  ∀ t : Multiset K, t.card = s.card → (∀ x ∈ t, x ∈ s) → t.prod = s.prod → t = s

def rootPol {K : Type} [CommRing K] (s : Multiset K) : Polynomial K := (s.map fun a => Polynomial.X - Polynomial.C a).prod

def heckePol {K : Type} [CommRing K] (q n : ℕ) (θ : ℕ → K) : Polynomial K :=
  ∑ j ∈ Finset.range (n + 1), Polynomial.C ((-1) ^ j * (q : K) ^ (j.choose 2) * θ j) * Polynomial.X ^ (n - j)

def GenericMulOfProd : Prop :=
  ∀ (K : Type) [CommMonoid K] (n : ℕ) (α : Fin n → K), GenericProd α → GenericMul (Finset.univ.val.map α)

def CharOfAnn : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (M : Matrix (Fin n) (Fin n) K) (s : Multiset K), s.card = n → GenericMul s →
    Polynomial.aeval M (rootPol s) = 0 → M.det = s.prod → M.charpoly = rootPol s

def form {B ι : Type} [CommRing B] [Fintype ι] (c : ι → B) : Polynomial (MvPolynomial ι B) :=
  Polynomial.X - Polynomial.C (∑ k, MvPolynomial.C (c k) * MvPolynomial.X k)

def SameNorm {B ι : Type} [CommRing B] [Fintype ι] (u u' : Multiset (ι → B)) : Prop :=
  (u.map form).prod = (u'.map form).prod

def pts {J P : Type} [Fintype J] {I : J → Type} [∀ j, Fintype (I j)] (a : J → ℕ) (v : ∀ j, I j → P) : Multiset P :=
  ∑ j, a j • Finset.univ.val.map (v j)

def wEv (q : ℕ) {n : ℕ} (j : Fin (n + 1)) : ℕ := if Even (j : ℕ) then q ^ ((j : ℕ).choose 2) else 0

def wOd (q : ℕ) {n : ℕ} (j : Fin (n + 1)) : ℕ := if Even (j : ℕ) then 0 else q ^ ((j : ℕ).choose 2)

section Split
variable {R S B I : Type} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra R B]

def splitMap (z : I → (S →ₐ[R] B)) : B ⊗[R] S →ₐ[B] (I → B) :=
  Algebra.TensorProduct.lift (Algebra.ofId B (I → B)) (Pi.algHom R (fun _ => B) z) fun _ _ => Commute.all _ _

theorem splitMap_tmul (z : I → (S →ₐ[R] B)) (b : B) (s : S) (i : I) : splitMap z (b ⊗ₜ s) i = b * z i s := by
  simp [splitMap, Algebra.ofId_apply]

def Splits (z : I → (S →ₐ[R] B)) : Prop := Function.Bijective (splitMap z)

def SplitsAway (l : ℕ) (z : I → (S →ₐ[R] B)) : Prop :=
  Splits fun i => (IsScalarTower.toAlgHom R B (Localization.Away (l : B))).comp (z i)

end Split

structure EtAway (l d : ℕ) (R S : Type) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  fin : Module.Finite R S
  et : Algebra.Etale (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S)
  deg : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K], (l : K) ≠ 0 → Nat.card (S →ₐ[R] K) = d

structure BaseOK (l : ℕ) (R : Type) [CommRing R] (𝔞 : Ideal R) : Prop where
  nzd : (l : R) ∈ nonZeroDivisors R
  closed : ∀ c : Localization.Away (l : R), IsIntegral R c → ∃ r : R, algebraMap R _ r = c
  rad : 𝔞.IsRadical

def SameNormRing : Prop :=
  ∀ (l : ℕ) (R : Type) [CommRing R] (𝔞 : Ideal R), BaseOK l R 𝔞 →
  ∀ (J : Type) [Fintype J] (S : J → Type) [∀ j, CommRing (S j)] [∀ j, Algebra R (S j)] (d : J → ℕ), (∀ j, EtAway l (d j) R (S j)) →
  ∀ (a b : J → ℕ) (ι : Type) [Fintype ι] (s : ∀ j, ι → S j),
    (∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)] [Algebra R V], (l : V) ≠ 0 →
      (IsLocalRing.maximalIdeal V).comap (algebraMap R V) ∈ 𝔞.minimalPrimes →
      ∀ (I : J → Type) [∀ j, Fintype (I j)] (z : ∀ j, I j → (S j →ₐ[R] V)), (∀ j, Function.Bijective (z j)) →
        pts a (fun j i k => IsLocalRing.residue V (z j i (s j k))) = pts b (fun j i k => IsLocalRing.residue V (z j i (s j k)))) →
    ∀ (B : Type) [CommRing B] [Algebra R B], (l : B) ∈ nonZeroDivisors B →
    ∀ (I : J → Type) [∀ j, Fintype (I j)] (z : ∀ j, I j → (S j →ₐ[R] B)), (∀ j, SplitsAway l (z j)) →
    ∀ (B' : Type) [CommRing B'] (ρ : B →+* B'), (∀ x ∈ 𝔞, ρ (algebraMap R B x) = 0) →
      SameNorm (pts a fun j i k => ρ (z j i (s j k))) (pts b fun j i k => ρ (z j i (s j k)))

def redMod {B ι : Type} [CommRing B] (x : B) (u : Multiset (ι → B)) : Multiset (ι → B ⧸ Ideal.span {x}) :=
  u.map fun c k => Ideal.Quotient.mk _ (c k)

def Matching : Prop :=
  ∀ (B : Type) [CommRing B] (ϖ : B), ϖ ∈ nonZeroDivisors B → ¬ IsUnit ϖ →
  ∀ (ι : Type) [Fintype ι] (N : ℕ) (u u' : Multiset (ι → B)), u.card ≤ N → u'.card ≤ N →
    SameNorm (redMod (ϖ ^ (N + 1) ^ N) u) (redMod (ϖ ^ (N + 1) ^ N) u') →
    (∀ x ∈ u, ∀ y ∈ u', ∀ k k', x k - y k ∣ ϖ ^ (N + 1) ^ N → x k - y k ∣ x k' - y k' ∨ x k' - y k' ∣ x k - y k) →
    (∀ x ∈ u, ∀ y ∈ u', ∀ k, ∀ j ≤ N, x k - y k ∣ ϖ ^ (N + 1) ^ j ∨ ϖ ^ (N + 1) ^ j ∣ x k - y k) →
    redMod ϖ u = redMod ϖ u'

def ValLike {B : Type} [CommRing B] (ϖ : B) : Prop :=
  ∀ f g : B, (∃ m : ℕ, ϖ ^ m ∈ Ideal.span {f, g}) → ∃ e : B, IsIdempotentElem e ∧ g ∣ e * f ∧ f ∣ (1 - e) * g

def MatchingVal : Prop :=
  ∀ (B : Type) [CommRing B] (ϖ : B), ϖ ∈ nonZeroDivisors B → ValLike ϖ →
  ∀ (ι : Type) [Fintype ι] (I I' : Type) [Fintype I] [Fintype I'] [DecidableEq I] [DecidableEq I'] (N : ℕ),
    Fintype.card I = N → Fintype.card I' = N → ∀ (u : I → ι → B) (u' : I' → ι → B),
    SameNorm (redMod (ϖ ^ (N + 1) ^ N) (Finset.univ.val.map u)) (redMod (ϖ ^ (N + 1) ^ N) (Finset.univ.val.map u')) →
    ∃ e : (I ≃ I') → B, CompleteOrthogonalIdempotents e ∧ ∀ σ i k, ϖ ∣ e σ * (u i k - u' (σ i) k)

def Gr (k H : Type) [Field k] [AddCommGroup H] [Module k H] (j : ℕ) : Type := {D : Submodule k H // Module.finrank k D = j}

def OrdRead (q n : ℕ) {P : Type} (F : P → P) {I : Fin (n + 1) → Type} (v : ∀ j, I j → P) : Prop :=
  ∃ (k H : Type) (_ : Field k) (_ : Finite k) (_ : AddCommGroup H) (_ : Module k H) (_ : Module.Finite k H)
    (C : Submodule k H) (A : Submodule k (H ⧸ C) → P) (e : ∀ j, I j ≃ Gr k H j),
    Nat.card k = q ∧ Module.finrank k H = n ∧ Module.finrank k C = 1 ∧
    ∀ j i, (C ≤ (e j i).1 → v j i = F (A ((e j i).1.map C.mkQ))) ∧ (¬ C ≤ (e j i).1 → v j i = A ((e j i).1.map C.mkQ))

def AltId (q n : ℕ) {P : Type} (F : P → P) {I : Fin (n + 1) → Type} [∀ j, Fintype (I j)] (v : ∀ j, I j → P) : Prop :=
  pts (wEv q) (fun j i => F^[n - j] (v j i)) = pts (wOd q) (fun j i => F^[n - j] (v j i))

def OrdCount : Prop :=
  ∀ (q n : ℕ) (P : Type) (F : P → P) (I : Fin (n + 1) → Type) [∀ j, Fintype (I j)] (v : ∀ j, I j → P), OrdRead q n F v → AltId q n F v

structure Corr (l : ℕ) (Y : Scheme.{0}) : Type 1 where
  Z : Scheme.{0}
  p : Z ⟶ Y
  r : Z ⟶ Y
  d : ℕ
  fin : IsFinite p
  et : Etale (p ∣_ Y.basicOpen (l : Γ(Y, ⊤)))
  deg : ∀ (K : Type) [Field K] [IsAlgClosed K], (l : K) ≠ 0 → ∀ y : Spec (CommRingCat.of K) ⟶ Y,
    Nat.card {z : Spec (CommRingCat.of K) ⟶ Z // z ≫ p = y} = d

def Corr.graph (l : ℕ) {Y : Scheme.{0}} (z : Y ⟶ Y) : Corr l Y where
  Z := Y
  p := 𝟙 Y
  r := z
  d := 1
  fin := inferInstance
  et := inferInstance
  deg K _ _ _ y := by
    have : Unique {z : Spec (CommRingCat.of K) ⟶ Y // z ≫ 𝟙 Y = y} :=
      ⟨⟨⟨y, Category.comp_id y⟩⟩, fun a => Subtype.ext ((Category.comp_id a.1).symm.trans a.2)⟩
    exact Nat.card_unique

instance (l : ℕ) (Y : Scheme.{0}) : Inhabited (Corr l Y) := ⟨Corr.graph l (𝟙 Y)⟩

def Corr.Sec {l : ℕ} {Y : Scheme.{0}} (T : Corr l Y) {X : Scheme.{0}} (y : X ⟶ Y) : Type := {z : X ⟶ T.Z // z ≫ T.p = y}

def GenPt {Y : Scheme.{0}} (π : Γ(Y, ⊤)) (x : Y) : Prop :=
  x ∉ Y.basicOpen π ∧ ∀ x' : Y, x' ∉ Y.basicOpen π → x' ⤳ x → x' = x

def resPt (V : Type) [CommRing V] [IsLocalRing V] : Spec (CommRingCat.of (IsLocalRing.ResidueField V)) ⟶ Spec (CommRingCat.of V) :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue V))

def twist {κ : Type} [CommRing κ] (φ : κ →+* κ) (Y : Scheme.{0}) (x : Spec (CommRingCat.of κ) ⟶ Y) : Spec (CommRingCat.of κ) ⟶ Y :=
  Spec.map (CommRingCat.ofHom φ) ≫ x

def PtId (l q n : ℕ) {Y : Scheme.{0}} (π : Γ(Y, ⊤)) (T : Fin (n + 1) → Corr l Y) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)], (l : V) ≠ 0 →
    ∀ y : Spec (CommRingCat.of V) ⟶ Y, GenPt π (y (IsLocalRing.closedPoint V)) →
    ∀ φ : IsLocalRing.ResidueField V →+* IsLocalRing.ResidueField V, (∀ a, φ a = a ^ q) →
    ∀ (I : Fin (n + 1) → Type) [∀ j, Fintype (I j)] (z : ∀ j, I j → (T j).Sec y), (∀ j, Function.Bijective (z j)) →
      AltId q n (twist φ Y) fun j i => resPt V ≫ (z j i).1 ≫ (T j).r

def OrdPt (l q n : ℕ) {Y : Scheme.{0}} (π : Γ(Y, ⊤)) (T : Fin (n + 1) → Corr l Y) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)], (l : V) ≠ 0 →
    ∀ y : Spec (CommRingCat.of V) ⟶ Y, GenPt π (y (IsLocalRing.closedPoint V)) →
    ∀ φ : IsLocalRing.ResidueField V →+* IsLocalRing.ResidueField V, (∀ a, φ a = a ^ q) →
      OrdRead q n (twist φ Y) fun j (z : (T j).Sec y) => resPt V ≫ z.1 ≫ (T j).r

def PtIdOfOrd : Prop :=
  ∀ (l q n : ℕ) (Y : Scheme.{0}) (π : Γ(Y, ⊤)) (T : Fin (n + 1) → Corr l Y), OrdPt l q n π T → PtId l q n π T

def AffFin (Y : Scheme.{0}) : Prop := ∀ s : Finset Y, ∃ U : Y.Opens, IsAffineOpen U ∧ ∀ x ∈ s, x ∈ U

def ChartsExist : Prop :=
  ∀ (l : ℕ) (Y : Scheme.{0}), AffFin Y → ∀ (J : Type) [Finite J] (T : J → Corr l Y) (y : Y),
    ∃ U V : Y.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ y ∈ U ∧ ∀ j, (T j).p ⁻¹ᵁ U ≤ (T j).r ⁻¹ᵁ V

def fn {O : Type} [CommRing O] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of O)) (a : O) : Γ(Y, ⊤) :=
  f.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)

@[reducible] def Corr.alg {l : ℕ} {Y : Scheme.{0}} (T : Corr l Y) (U : Y.Opens) : Algebra Γ(Y, U) Γ(T.Z, T.p ⁻¹ᵁ U) :=
  (T.p.app U).hom.toAlgebra

def NormOn (l q n : ℕ) {Y : Scheme.{0}} (π : Γ(Y, ⊤)) (T : Fin (n + 1) → Corr l Y) (U V : Y.Opens)
    (h : ∀ j, (T j).p ⁻¹ᵁ U ≤ (T j).r ⁻¹ᵁ V) : Prop :=
  letI := fun j => (T j).alg U
  ∀ (B : Type) [CommRing B] [Algebra Γ(Y, U) B], (l : B) ∈ nonZeroDivisors B →
  ∀ (I : Fin (n + 1) → Type) [∀ j, Fintype (I j)] (z : ∀ j, I j → (Γ((T j).Z, (T j).p ⁻¹ᵁ U) →ₐ[Γ(Y, U)] B)),
    (∀ j, SplitsAway l (z j)) →
  ∀ (B' : Type) [CommRing B'] (ρ : B →+* B'), ρ (algebraMap Γ(Y, U) B (Y.presheaf.map (homOfLE le_top).op π)) = 0 →
  ∀ (ι : Type) [Fintype ι] (x : ι → Γ(Y, V)),
    SameNorm (pts (wEv q) fun j i k => ρ (z j i ((T j).r.appLE V _ (h j) (x k))) ^ q ^ (n - j))
      (pts (wOd q) fun j i k => ρ (z j i ((T j).r.appLE V _ (h j) (x k))) ^ q ^ (n - j))

def NormOfPt : Prop :=
  ∀ (l f n : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of O)), Smooth g →
    ∀ T : Fin (n + 1) → Corr l Y, PtId l (l ^ f) n (fn g ϖ) T →
    ∀ (U V : Y.Opens), IsAffineOpen U → IsAffineOpen V → ∀ h : ∀ j, (T j).p ⁻¹ᵁ U ≤ (T j).r ⁻¹ᵁ V,
      NormOn l (l ^ f) n (fn g ϖ) T U V h

end UpperTheory.Gal.crystallineComparison
