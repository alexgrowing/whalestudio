import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.StalkCut

def RelZ (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) : Prop :=
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull _ (sch.map (Spec.map f)) (tw q i) m)) ∧
  Function.Injective (pull _ (sch.map (Spec.map f)) (tw q i) n)

def BCn (q : ℕ) (i n : ℤ) {A Y C : CommRingCat.{0}} (φ : A ⟶ Y) (c : A ⟶ C) : Prop :=
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : C ⟶ Y'), IsPushout φ c w φ' → RelZ q i n φ'

def PushClosed {A : CommRingCat.{0}} (P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop) : Prop :=
  ∀ {C D E Z : CommRingCat.{0}} (c : A ⟶ C) (f : C ⟶ D) (g : C ⟶ E) (u : D ⟶ Z) (v : E ⟶ Z), IsPushout f g u v →
    P C c → P D (c ≫ f) → P E (c ≫ g) → P Z (c ≫ f ≫ u)

def EtClosed {A : CommRingCat.{0}} (P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop) : Prop :=
  ∀ {C D : CommRingCat.{0}} (c : A ⟶ C) (f : C ⟶ D), P C c → Et f → P D (c ≫ f)

theorem relZ_neg (hH : Hyp) (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (hn : n < 0) : RelZ q i n f := by
  have hA9 := (hH.2.2.2.2.2.1 (ZMod q) (tw q i)).1
  refine ⟨fun m hm y => ?_, fun x y _ => ?_⟩
  · haveI := hA9 (sch.obj (Spec B)) m (by omega)
    exact ⟨0, Subsingleton.elim _ _⟩
  · haveI := hA9 (sch.obj (Spec A)) n hn
    exact Subsingleton.elim _ _

theorem re_of_relZ {q : ℕ} {i : ℤ} {A B : CommRingCat.{0}} {f : A ⟶ B} (h : ∀ n, RelZ q i n f) : RE q i f :=
  fun m => ⟨(h m).2, (h (m + 1)).1 m rfl⟩

def DescInt : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ {C D : CommRingCat.{0}} (c : A ⟶ C) (g : C ⟶ D), P C c → P D (c ≫ g) → g.hom.IsIntegral → SpS g →
  BCn q i n φ (c ≫ g) → BCn q i n φ c

def DescLoc : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  (∀ r : Ideal D, r.IsPrime → ∃ (O : CommRingCat.{0}) (o : D ⟶ O) (Q : Ideal O), IE o ∧ Q.IsPrime ∧ Q.comap o.hom = r ∧
    BC q i φ (d ≫ o)) →
  BCn q i n φ d

theorem goal_of (hInt : DescInt) (hLoc : DescLoc) : LateralTheory.E.t_E3Cut.Stalk := by
  intro hH q _ i A Y φ hq P hpush het hcov C c hC
  have key : ∀ k : ℕ, ∀ m : ℤ, m < k → ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c := by
    intro k
    induction k with
    | zero =>
      intro m hm C c _ Y' w φ' _
      exact relZ_neg hH q i m φ' (by exact_mod_cast hm)
    | succ k ih =>
      intro m hm C c hC
      have hm' : m ≤ (k : ℤ) := by push_cast at hm; omega
      rcases lt_or_eq_of_le hm' with h | h
      · exact ih m h C c hC
      · subst h
        obtain ⟨D, g, hgi, hgs, hD, hpts⟩ := hcov C c hC
        have hDl : BCn q i (k : ℤ) φ (c ≫ g) :=
          hLoc hH q i k φ hq P @hpush @het ih D (c ≫ g) hD (fun r hr => by
            obtain ⟨O, o, Q, h1, h2, h3, h4⟩ := hpts r hr
            exact ⟨O, o, Q, h1, h2, h3, by rwa [Category.assoc]⟩)
        exact hInt hH q i k φ hq P @hpush ih c g hC hD hgi hgs hDl
  intro Y' w φ' hpo
  refine re_of_relZ fun n => ?_
  exact key (n.toNat + 1) n (by omega) C c hC Y' w φ' hpo

end LateralTheory.E.StalkCut
