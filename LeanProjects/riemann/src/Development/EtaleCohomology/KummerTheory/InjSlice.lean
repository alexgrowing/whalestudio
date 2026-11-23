import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.KummerTheory

def IsoUpTo {A B : Type*} [AddCommGroup A] [AddCommGroup B] (N : ℕ) (f : A → B) : Prop :=
  (∀ a, f a = 0 → N • a = 0) ∧ ∀ b, ∃ a, f a = N • b

def ext (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ) (x : Ht q (sch.obj X) a i)
    (y : Ht q (sch.obj Y) (n - a) 0) : Ht q (sch.obj (pullback pX pY)) n i :=
  (cup q (pull _ (sch.map (pullback.fst pX pY)) _ _ x) (pull _ (sch.map (pullback.snd pX pY)) _ _ y)).cast
    (by ring) (by ring)

def lh (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (i : ℤ) (r : ℕ → ℕ)
    (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M : ℕ) (n : ℤ)
    (y : ∀ a : Fin (M + 1), Fin (r a) → Ht q (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) : Ht q (sch.obj (pullback pX pY)) n i :=
  ∑ a : Fin (M + 1), ∑ s : Fin (r a), ext q pX pY ((a : ℕ) : ℤ) n i (c a s) (y a s)

def comb (q : ℕ) {E : Spc} {n i : ℤ} {r : ℕ} (c : Fin r → Ht q E n i) (t : Fin r → ZMod q) : Ht q E n i := ∑ s, t s • c s

def lev (l : ℕ) [Fact l.Prime] {E : Spc} {n i : ℤ} (x : Hl l E n i) (k : ℕ) : Ht (l ^ k) E n i := x.1 k

def QBasis (l : ℕ) [Fact l.Prime] {E : Spc} {n i : ℤ} {r : ℕ} (c : Fin r → Hl l E n i) : Prop :=
  LinearIndependent ℚ_[l] (fun s => ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] c s : HQ l E n i)) ∧
    Submodule.span ℚ_[l] (Set.range fun s => ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] c s : HQ l E n i)) = ⊤

def KunIso (l : ℕ) [Fact l.Prime] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (n i : ℤ) : Prop :=
  ∃ κ : (⨁ a : ℤ, HQ l (sch.obj X) a i ⊗[ℚ_[l]] HQ l (sch.obj Y) (n - a) 0) ≃ₗ[ℚ_[l]] HQ l (sch.obj (pullback pX pY)) n i,
    ∀ (a : ℤ) (x : Hl l (sch.obj X) a i) (y : Hl l (sch.obj Y) (n - a) 0), ∃ z : Hl l (sch.obj (pullback pX pY)) n i,
      (∀ k, lev l z k = ext (l ^ k) pX pY a n i (lev l x k) (lev l y k)) ∧
      κ (DirectSum.lof ℚ_[l] ℤ (fun a : ℤ => HQ l (sch.obj X) a i ⊗[ℚ_[l]] HQ l (sch.obj Y) (n - a) 0) a
        (((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x) ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y))) = (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] z

def GOAL : Prop := A2 → DivisorNaturality → DivisorRingCompatibility → A7 → A8 → A9 → A10 → A11 → B1 → B2 → B3 → E2 → E3 → E4 →
  ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], IsUnit (l : k) → ∀ {X Y : Scheme.{0}}
    (pX : X ⟶ Spec (CommRingCat.of k)) (pY : Y ⟶ Spec (CommRingCat.of k)) [IsProper pX] [Smooth pX] [IsProper pY]
    (n i : ℤ), KunIso l pX pY n i

def IsCls {R : Type} [CommRing R] {X : Scheme.{0}} {I : Cx R} {n : ℤ}
    (x : CohomologyClass ((chains R).obj (sch.obj X)) I n) (a : Sec (I.X n) X) : Prop :=
  ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n, CohomologyClass.mk α = x ∧
    ev α.1 0 n (by simp) X (𝟙 X) = a ∧
    ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : Sx (sch.obj X) (p + 1) U), ev α.1 (p + 1) s h U y = 0

def tot {X S : Scheme.{0}} (p : X ⟶ S) : Over S ⥤ Scheme.{0} := Over.pullback p ⋙ Over.forget X

def bcMap {X : Scheme.{0}} {R A B : CommRingCat.{0}} (p : X ⟶ Spec R) (f : R ⟶ A) (g : R ⟶ B) (h : A ⟶ B) (e : f ≫ h = g) :
    pullback p (Spec.map g) ⟶ pullback p (Spec.map f) :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map h) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp, e])

def Dict : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) (X : Scheme.{0}) (n : ℤ),
  (∀ a : Sec (I.X n) X, Sec.map (I.d n (n + 1)) a = 0 → ∃ x, IsCls x a) ∧
  (∀ x : CohomologyClass ((chains R).obj (sch.obj X)) I n, ∃ a, IsCls x a) ∧
  (∀ x (a : Sec (I.X n) X), IsCls x a → Sec.map (I.d n (n + 1)) a = 0 ∧
    (x = 0 ↔ ∃ b : Sec (I.X (n - 1)) X, Sec.map (I.d (n - 1) n) b = a)) ∧
  (∀ x x' (a a' : Sec (I.X n) X), IsCls x a → IsCls x' a' → IsCls (x + x') (a + a') ∧ IsCls (-x) (-a)) ∧
  ∀ {Y : Scheme.{0}} (f : Y ⟶ X) x (a : Sec (I.X n) X), IsCls x a →
    IsCls (cpre (Cocycle.ofHom ((chains R).map (sch.map f))) I n n (zero_add n) x) (Sec.res f a)

def CupAW : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
  (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m),
  ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1 ∧
    μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

def CupSch : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (X : Scheme.{0}) {n m k : ℤ} (hk : n + m = k)
  x y (a : Sec (I.X n) X) (b : Sec (J.X m) X), IsCls x a → IsCls y b →
  IsCls (μ.cup (sch.obj X) hk x y) (μ.mul X n m k hk a b)

def Ghost : Prop := ∀ (A : Type 2) [Category.{1} A] [Abelian A] [EnoughInjectives A] (C : CochainComplex A ℤ)
  [C.IsStrictlyGE (-1)], (∀ j, Injective (C.X j)) → ∀ (N : ℕ) (m : ℕ), (∀ j : ℤ, j < m → N • 𝟙 (C.homology j) = 0) →
  ∀ j : ℤ, j < m → ∀ (P : A) (f : P ⟶ C.X j), f ≫ C.d j (j + 1) = 0 →
    ∃ g : P ⟶ C.X (j - 1), g ≫ C.d (j - 1) j = N ^ (m + 1) • f

def InjSlice : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) [Injective F] {X S : Scheme.{0}} (p : X ⟶ S),
  (∃ h : Presheaf.IsSheaf (Scheme.etaleTopology.over S) ((tot p).op ⋙ F.obj),
    Injective (⟨_, h⟩ : Sheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} R)))) ∧
  ∃ h : Presheaf.IsSheaf (Scheme.etaleTopology.over S) ((Over.forget S).op ⋙ F.obj),
    Injective (⟨_, h⟩ : Sheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} R)))

def StrictHenselization : Prop := ∀ (R : CommRingCat.{0}) (𝔭 : PrimeSpectrum R), ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J)
  (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (_ : IsColimit c) (u : (Functor.const J).obj R ⟶ D),
  SH c.pt ∧ ∀ j, (u.app j).hom.Etale ∧ ∃ 𝔮 : PrimeSpectrum (D.obj j), 𝔮.asIdeal.comap (u.app j).hom = 𝔭.asIdeal

def Cont : Prop := A2 → B1 → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} {R : CommRingCat.{0}} (p : X ⟶ Spec R) [QuasiCompact p]
  [IsSeparated p], IsUnit (q : R) → ∀ {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D),
  IsColimit c → ∀ (u : ∀ j, R ⟶ D.obj j) (hu : ∀ {j k} (f : j ⟶ k), u j ≫ D.map f = u k) (v : R ⟶ c.pt)
    (hv : ∀ j, u j ≫ c.ι.app j = v) (n i : ℤ),
  (∀ x : Ht q (sch.obj (pullback p (Spec.map v))) n i, ∃ j y, pull _ (sch.map (bcMap p (u j) v (c.ι.app j) (hv j))) _ _ y = x) ∧
  ∀ j (y : Ht q (sch.obj (pullback p (Spec.map (u j)))) n i),
    pull _ (sch.map (bcMap p (u j) v (c.ι.app j) (hv j))) _ _ y = 0 →
    ∃ (k : J) (f : j ⟶ k), pull _ (sch.map (bcMap p (u j) (u k) (D.map f) (hu f))) _ _ y = 0

def LH : Prop := A2 → DivisorNaturality → B1 → ∃ e : ℕ → ℕ, ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} {R : CommRingCat.{0}} (p : X ⟶ Spec R)
  [QuasiCompact p] [IsSeparated p], IsUnit (q : R) → ∀ (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i)
  (M N : ℕ), (∀ (A : CommRingCat.{0}) (s : R ⟶ A), SH A → ∀ n : ℤ, n ≤ M → IsoUpTo N (lh q p (Spec.map s) i r c M n)) →
  ∀ {Y : Scheme.{0}} (pY : Y ⟶ Spec R) (n : ℤ), n < M → IsoUpTo (N ^ e M) (lh q p pY i r c M n)

def TwSec : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
  Nonempty (Prim q Γ(Spec (CommRingCat.of A), ⊤)) ∧ ∀ (i : ℤ) (ζ : Prim q Γ(Spec (CommRingCat.of A), ⊤)),
    Function.Bijective fun t : ZMod q => (ULift.up t : ULift.{1} (ZMod q)) • twGen i ζ

def H0 : Prop := A9 → ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
  Function.Bijective fun t : ZMod q => t • one q (sp A)

def Place : Prop := ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] [Algebra k K],
  ∃ (T : ValuationSubring K) (σ : k →+* T), (∀ x, (σ x : K) = algebraMap k K x) ∧
    Function.Bijective ((IsLocalRing.residue T).comp σ) ∧ AIC T ∧ SH T

def AlgExt : Prop := E2 → E3 → ∀ (q : ℕ) [NeZero q] (k K : Type) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K]
  (f : k →+* K), IsUnit (q : k) → ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] [Smooth p] (i : ℤ),
  Eqv _ (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom f)))) (tw q i)

def SHInsep : Prop := ∀ (κ K A : Type) [Field κ] [Field K] [Algebra κ K] [IsPurelyInseparable κ K] [CommRing A] [Algebra κ A],
  SH A → SH (A ⊗[κ] K)

def Insep : Prop := A9 → B2 → B3 → ∀ (q : ℕ) [NeZero q] (κ K : Type) [Field κ] [Field K] [Algebra κ K]
  [IsPurelyInseparable κ K], IsUnit (q : κ) → ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of κ)) (i : ℤ),
  Eqv _ (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap κ K))))) (tw q i)

def SHInv : Prop := A9 → B2 → B3 → E2 → E3 → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] [Smooth p] (A : CommRingCat.{0})
    (s : CommRingCat.of k ⟶ A), SH A → ∀ i : ℤ, Eqv _ (sch.map (pullback.fst p (Spec.map s))) (tw q i)

def Stalk : Prop := DivisorNaturality → DivisorRingCompatibility → A9 → B2 → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} {R : CommRingCat.{0}} (p : X ⟶ Spec R)
  (A : CommRingCat.{0}) (s : R ⟶ A), SH A → IsUnit (q : R) → ∀ (i : ℤ) (r : ℕ → ℕ)
  (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M N : ℕ), Eqv _ (sch.map (pullback.fst p (Spec.map s))) (tw q i) →
  (∀ a ≤ M, IsoUpTo N (comb q (c a))) → ∀ n : ℤ, n ≤ M → IsoUpTo N (lh q p (Spec.map s) i r c M n)

def BockData (l b : ℕ) (E : Spc) (i : ℤ) : Prop :=
  ∃ (u : ∀ (a : ℕ) (n : ℤ), Ht (l ^ a) E n i →+ Ht (l ^ (b + a)) E n i)
    (d : ∀ (a : ℕ) (n : ℤ), Ht (l ^ b) E n i →+ Ht (l ^ a) E (n + 1) i), ∀ (a : ℕ) (n : ℤ),
    Function.Exact (u a n) (red (l ^ (b + a)) (l ^ b) E n i) ∧
    Function.Exact (red (l ^ (b + a)) (l ^ b) E n i) (d a n) ∧
    Function.Exact (d a n) (u a (n + 1)) ∧
    (∀ x, u a n (red (l ^ (b + a)) (l ^ a) E n i x) = l ^ b • x) ∧
    (∀ x, red (l ^ (a + 1)) (l ^ a) E (n + 1) i (d (a + 1) n x) = d a n x) ∧
    ∀ x, red (l ^ (b + (a + 1))) (l ^ (b + a)) E n i (u (a + 1) n x) = u a n (red (l ^ (a + 1)) (l ^ a) E n i x)

def Bock : Prop := A7 → A8 → A10 → A11 → ∀ (l : ℕ) [Fact l.Prime] (b : ℕ) (E : Spc) (i : ℤ), Inv l E → BockData l b E i

def AdicDeg : Prop := A11 → ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (i : ℤ), (∀ b, BockData l b E i) →
  (∀ (k : ℕ) (n : ℤ), Finite (Ht (l ^ k) E n i)) → ∀ n : ℤ, ∃ (r : ℕ) (c : Fin r → Hl l E n i) (N : ℕ), 0 < N ∧ QBasis l c ∧
    ∀ k, IsoUpTo N (comb (l ^ k) fun s => lev l (c s) k)

def Limit : Prop := A9 → A11 → ∀ (l : ℕ) [Fact l.Prime] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (n i : ℤ) (M N : ℕ)
  (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Hl l (sch.obj X) a i), n ≤ M → 0 < N → (∀ a ≤ M, QBasis l (c a)) →
  (∀ (k : ℕ) (m : ℤ), Finite (Ht (l ^ k) (sch.obj Y) m 0)) →
  (∀ k, IsoUpTo N (lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n)) → KunIso l pX pY n i

end LateralTheory.KummerTheory

end
