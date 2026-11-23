import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.EtaleCohomology.EtaleSheaves.EtaleChapterEThree

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.t_E3Cut

def Hyp : Prop := A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ A9 ∧ B1 ∧ B2 ∧ B4 ∧ C3 ∧ C4

def RE (q : ℕ) (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) : Prop := Eqv _ (sch.map (Spec.map f)) (tw q i)

def BC (q : ℕ) (i : ℤ) {A Y C : CommRingCat.{0}} (φ : A ⟶ Y) (c : A ⟶ C) : Prop :=
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : C ⟶ Y'), IsPushout φ c w φ' → RE q i φ'

def Et : MorphismProperty CommRingCat.{0} := fun _ _ f => f.hom.Etale

def IE : MorphismProperty CommRingCat.{0} := MorphismProperty.ind.{0} Et

def AlgRes : MorphismProperty CommRingCat.{0} := fun A C f =>
  ∀ Q : Ideal C, Q.IsPrime → ∀ c : C, ∃ p : Polynomial A, (∃ n, f.hom (p.coeff n) ∉ Q) ∧ p.eval₂ f.hom c ∈ Q

def SpS {A B : CommRingCat.{0}} (f : A ⟶ B) : Prop :=
  ∀ r : Ideal A, r.IsPrime → ∃ Q : Ideal B, Q.IsPrime ∧ Q.comap f.hom = r

abbrev pC (A : CommRingCat.{0}) : A ⟶ CommRingCat.of (Polynomial A) := CommRingCat.ofHom Polynomial.C

def Good (q : ℕ) (i : ℤ) {T K A : CommRingCat.{0}} (k : T ⟶ K) (t : T ⟶ A) : Prop :=
  ∀ (B : CommRingCat.{0}) (c : A ⟶ B), Et c → BC q i k (t ≫ c)

theorem RE.comp {q : ℕ} {i : ℤ} {A B C : CommRingCat.{0}} {f : A ⟶ B} {g : B ⟶ C} (hf : RE q i f) (hg : RE q i g) :
    RE q i (f ≫ g) := fun n => by
  have h : ⇑(pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) n) =
      pull _ (sch.map (Spec.map g)) (tw q i) n ∘ pull _ (sch.map (Spec.map f)) (tw q i) n := by
    funext x; rw [Spec.map_comp, Functor.map_comp, pull_comp]; rfl
  rw [h]; exact (hg n).comp (hf n)

theorem RE.of_comp_left {q : ℕ} {i : ℤ} {A B C : CommRingCat.{0}} {f : A ⟶ B} {g : B ⟶ C} (hf : RE q i f)
    (hfg : RE q i (f ≫ g)) : RE q i g := fun n => by
  have h : ⇑(pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) n) =
      pull _ (sch.map (Spec.map g)) (tw q i) n ∘ pull _ (sch.map (Spec.map f)) (tw q i) n := by
    funext x; rw [Spec.map_comp, Functor.map_comp, pull_comp]; rfl
  have := hfg n
  rw [h] at this; exact (Function.Bijective.of_comp_iff _ (hf n)).1 this

theorem RE.of_comp_right {q : ℕ} {i : ℤ} {A B C : CommRingCat.{0}} {f : A ⟶ B} {g : B ⟶ C} (hg : RE q i g)
    (hfg : RE q i (f ≫ g)) : RE q i f := fun n => by
  have h : ⇑(pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) n) =
      pull _ (sch.map (Spec.map g)) (tw q i) n ∘ pull _ (sch.map (Spec.map f)) (tw q i) n := by
    funext x; rw [Spec.map_comp, Functor.map_comp, pull_comp]; rfl
  have := hfg n
  rw [h] at this; exact (Function.Bijective.of_comp_iff' (hg n) _).1 this

theorem RE.id (q : ℕ) (i : ℤ) (A : CommRingCat.{0}) : RE q i (𝟙 A) := fun n => by
  have h : ⇑(pull _ (sch.map (Spec.map (𝟙 A))) (tw q i) n) = _root_.id := by
    funext x; rw [Spec.map_id, CategoryTheory.Functor.map_id, pull_id]; rfl
  rw [h]; exact Function.bijective_id

theorem RE.of_isIso (q : ℕ) (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) [IsIso f] : RE q i f := fun n => by
  have h1 : ∀ x, pull _ (sch.map (Spec.map (inv f))) (tw q i) n (pull _ (sch.map (Spec.map f)) (tw q i) n x) = x := fun x => by
    rw [← pull_comp, ← Functor.map_comp, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, CategoryTheory.Functor.map_id, pull_id]
  have h2 : ∀ x, pull _ (sch.map (Spec.map f)) (tw q i) n (pull _ (sch.map (Spec.map (inv f))) (tw q i) n x) = x := fun x => by
    rw [← pull_comp, ← Functor.map_comp, ← Spec.map_comp, IsIso.inv_hom_id, Spec.map_id, CategoryTheory.Functor.map_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem BC.of_one {q : ℕ} {i : ℤ} {A Y C Y' : CommRingCat.{0}} {φ : A ⟶ Y} {c : A ⟶ C} {w : Y ⟶ Y'} {φ' : C ⟶ Y'}
    (h : IsPushout φ c w φ') (hr : RE q i φ') : BC q i φ c := fun _ _ ψ h' => by
  rw [← h.inr_isoIsPushout_hom _ _ h']
  exact hr.comp (RE.of_isIso q i _)

def AlgResProps : Prop :=
  (∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), AlgRes f → AlgRes g → AlgRes (f ≫ g)) ∧
  (∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), AlgRes (f ≫ g) → AlgRes g) ∧
  (∀ {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D), IsPushout f g u v → AlgRes f → AlgRes v) ∧
  (∀ {A B : CommRingCat.{0}} (f : A ⟶ B), Et f → AlgRes f) ∧
  (∀ {A B : CommRingCat.{0}} (f : A ⟶ B), f.hom.IsIntegral → AlgRes f) ∧
  ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B],
    AlgRes (CommRingCat.ofHom (algebraMap A B))

def IEComp : Prop := ∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), IE f → IE g → IE (f ≫ g)

def LocIE : Prop := ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B],
  IE (CommRingCat.ofHom (algebraMap A B))

def SHExists : Prop := ∀ (A : CommRingCat.{0}) (r : Ideal A), r.IsPrime →
  ∃ (O : CommRingCat.{0}) (f : A ⟶ O), IE f ∧ SH O ∧ ∀ a : A, a ∈ r ↔ ¬ IsUnit (f.hom a)

def AICSH : Prop := ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → SH T

def AICExt : Prop := ∀ (C : CommRingCat.{0}), ∃ (D : CommRingCat.{0}) (g : C ⟶ D),
  g.hom.IsIntegral ∧ Function.Injective g.hom ∧ AIC D

def DomCover : Prop := ∀ (C : CommRingCat.{0}), AIC C → ∃ (D : CommRingCat.{0}) (g : C ⟶ D),
  g.hom.IsIntegral ∧ SpS g ∧ ∀ (r : Ideal D) [r.IsPrime], IsDomain (Localization.AtPrime r) ∧ AIC (Localization.AtPrime r)

def HensInt : Prop := ∀ (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] (f : A →+* B),
  f.IsIntegral → (∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) → Nonempty (HenselianLocalRing B)

def SHTensor : Prop := ∀ {A X B Z : CommRingCat.{0}} (x : A ⟶ X) (b : A ⟶ B) (u : X ⟶ Z) (v : B ⟶ Z), IsPushout x b u v →
  SH A → SH X → IsLocalHom x.hom → b.hom.IsIntegral → IsLocalRing B → SH Z

def IntClos : Prop := ∀ {A C : CommRingCat.{0}} (c : A ⟶ C) [IsDomain C], SH A → AIC C → AlgRes c →
  ∃ (B : CommRingCat.{0}) (b : A ⟶ B) (j : B ⟶ C), b ≫ j = c ∧ b.hom.IsIntegral ∧ Function.Injective j.hom ∧ IsLocalRing B ∧
    AIC B ∧ ∀ z : C, ∃ s y : B, s ≠ 0 ∧ j.hom s * z = j.hom y

def SHSection : Prop := ∀ (A : CommRingCat.{0}), SH A → ∀ {V : Scheme.{0}} (g : V ⟶ Spec A) [Etale g] [Surjective g],
  ∃ s : Spec A ⟶ V, s ≫ g = 𝟙 _

def Coprod : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {ι : Type} (X : ι → Scheme.{0}) (n : ℤ),
  Function.Bijective fun (x : H R (sch.obj (∐ X)) F n) (j : ι) => pull R (sch.map (Sigma.ι X j)) F n x

def ZarLocal : Prop := Hyp → ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (g : Y ⟶ X),
  (∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, IsAffineOpen V → V ≤ U → Eqv R (sch.map (g ∣_ V)) F) → Eqv R (sch.map g) F

def Limit : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  (∀ (C : CommRingCat.{0}) (c : A ⟶ C), Et c → BC q i φ c) → ∀ (C : CommRingCat.{0}) (c : A ⟶ C), IE c → BC q i φ c

def Stalk : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop,
  (∀ {C D E Z : CommRingCat.{0}} (c : A ⟶ C) (f : C ⟶ D) (g : C ⟶ E) (u : D ⟶ Z) (v : E ⟶ Z), IsPushout f g u v →
    P C c → P D (c ≫ f) → P E (c ≫ g) → P Z (c ≫ f ≫ u)) →
  (∀ {C D : CommRingCat.{0}} (c : A ⟶ C) (f : C ⟶ D), P C c → Et f → P D (c ≫ f)) →
  (∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → ∃ (D : CommRingCat.{0}) (g : C ⟶ D), g.hom.IsIntegral ∧ SpS g ∧ P D (c ≫ g) ∧
    ∀ r : Ideal D, r.IsPrime → ∃ (O : CommRingCat.{0}) (o : D ⟶ O) (Q : Ideal O), IE o ∧ Q.IsPrime ∧ Q.comap o.hom = r ∧
      BC q i φ (c ≫ g ≫ o)) →
  ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BC q i φ c

def SHEqv : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B), IsUnit (q : A) → SH A → SH B → RE q i f

def EtaleBaseChangeFractionFieldIndEtaleOverPolynomial : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) (T K : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [Field K] [Algebra T K]
  [IsFractionRing T K], AIC T → IsUnit (q : T) → ∀ (X : CommRingCat.{0}) (h : CommRingCat.of (Polynomial T) ⟶ X), IE h →
  BC q i (CommRingCat.ofHom (algebraMap T K)) (pC (CommRingCat.of T) ≫ h)

def ULAStalk : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A X : CommRingCat.{0}} (h : CommRingCat.of (Polynomial A) ⟶ X),
  IsUnit (q : A) → SH A → SH X → IE h → IsLocalHom (pC A ≫ h).hom →
  ∀ (C : CommRingCat.{0}) (c : A ⟶ C) [IsDomain C] [IsLocalRing C], AIC C → AlgRes c → BC q i (pC A ≫ h) c

def ULA : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A X : CommRingCat.{0}} (h : CommRingCat.of (Polynomial A) ⟶ X),
  IsUnit (q : A) → SH A → SH X → IE h → IsLocalHom (pC A ≫ h).hom →
  ∀ (C : CommRingCat.{0}) (c : A ⟶ C), AlgRes c → BC q i (pC A ≫ h) c

def Step : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {T K A : CommRingCat.{0}} (k : T ⟶ K) (t : T ⟶ A), IsUnit (q : T) →
  AlgRes k → Good q i k t → Good q i k (t ≫ pC A)

def Base : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
  Good q i (CommRingCat.ofHom (algebraMap T (FractionRing T))) (𝟙 _)

def Global : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) {T K : CommRingCat.{0}} (k : T ⟶ K),
  (∀ n : ℕ, Good q i k (CommRingCat.ofHom (MvPolynomial.C : T →+* MvPolynomial (Fin n) T))) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec T) [Smooth p], Eqv _ (sch.map (pullback.fst p (Spec.map k))) (tw q i)

theorem Good.of_equiv {q : ℕ} {i : ℤ} {T K A A' : CommRingCat.{0}} {k : T ⟶ K} {t : T ⟶ A} (h : Good q i k t)
    (e : A ≃+* A') (t' : T ⟶ A') (ht : t ≫ CommRingCat.ofHom e.toRingHom = t') : Good q i k t' := fun B c hc => by
  rw [← ht, Category.assoc]
  exact h B _ (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective e.bijective) hc)

theorem goal_of (h1 : AlgResProps) (h2 : Base) (h3 : Step) (h4 : Global) : LateralTheory.E.EtaleChapterEThree := by
  intro a1 a2 a3 a4 a5 _ _ a9 _ _ b1 b2 _ b4 _ _ _ _ c3 c4 _ _ _ _ _ _ q _ T _ _ _ hT hq X p _ i
  have H : Hyp := ⟨a1, a2, a3, a4, a5, a9, b1, b2, b4, c3, c4⟩
  refine h4 H q i _ (fun n => ?_) p
  induction n with
  | zero =>
    refine (h2 H q i T hT hq).of_equiv (MvPolynomial.isEmptyRingEquiv T (Fin 0)).symm _ ?_
    ext x; simp
  | succ n ih =>
    refine (h3 H q i _ _ hq (h1.2.2.2.2.2 T _ (nonZeroDivisors T)) ih).of_equiv
      (MvPolynomial.finSuccEquiv T n).symm.toRingEquiv _ ?_
    ext1
    exact RingHom.ext fun x => (MvPolynomial.finSuccEquiv T n).symm.commutes x

end LateralTheory.E.t_E3Cut

end
