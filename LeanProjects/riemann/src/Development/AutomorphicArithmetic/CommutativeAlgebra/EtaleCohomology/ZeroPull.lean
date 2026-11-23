import Mathlib

noncomputable section

open CategoryTheory

namespace UpperTheory.Ru.crystallineComparison

variable {C : Type 1} [Category.{0} C]

structure Fam (A : C) : Type 1 where
  ι : Type
  [fin : Fintype ι]
  B : ι → C
  f : ∀ i, A ⟶ B i

attribute [instance] Fam.fin

variable (C) in

structure Parts where
  Cov : ∀ {A : C}, Fam A → Prop
  triv : ∀ A : C, Cov (⟨Unit, fun _ => A, fun _ => 𝟙 A⟩ : Fam A)
  pull : ∀ {A A' : C} (φ : A ⟶ A') (S : Fam A), Cov S → ∃ (B' : S.ι → C) (f' : ∀ i, A' ⟶ B' i) (ψ : ∀ i, S.B i ⟶ B' i),
    Cov (⟨S.ι, B', f'⟩ : Fam A') ∧ ∀ i, S.f i ≫ ψ i = φ ≫ f' i
  trans : ∀ {A : C} (S : Fam A) (T : ∀ i, Fam (S.B i)), Cov S → (∀ i, Cov (T i)) →
    Cov (⟨Σ i, (T i).ι, fun x => (T x.1).B x.2, fun x => S.f x.1 ≫ (T x.1).f x.2⟩ : Fam A)
  epi : ∀ {A : C} (S : Fam A), Cov S → ∀ i, Epi (S.f i)
  disj : ∀ {A : C} (S : Fam A), Cov S → ∀ {i j : S.ι}, i ≠ j → ∀ {X : C} (h : S.B i ⟶ X) (h' : S.B j ⟶ X),
    S.f i ≫ h = S.f j ≫ h' → Cov (⟨Empty, fun e => e.elim, fun e => e.elim⟩ : Fam X)

abbrev Coef (C : Type 1) [Category.{0} C] := C ⥤ AddCommGrpCat.{1}

def Parts.Add (Pa : Parts C) (F : Coef C) : Prop :=
  ∀ (A : C) (S : Fam A), Pa.Cov S → Function.Bijective fun (x : F.obj A) (i : S.ι) => (F.map (S.f i)).hom x

def Sec (P : C ⥤ Type) (F : Coef C) : AddSubgroup (∀ A : C, P.obj A → F.obj A) where
  carrier := {c | ∀ {A B : C} (φ : A ⟶ B) (y : P.obj A), (F.map φ).hom (c A y) = c B (P.map φ y)}
  zero_mem' := by intro A B φ y; simp
  add_mem' := by intro a b ha hb A B φ y; simp [ha φ y, hb φ y]
  neg_mem' := by intro a ha A B φ y; simp [ha φ y]

variable (C) in

structure Theory where
  H : (C ⥤ Type) → Coef C → ℕ → Type 1
  [ab : ∀ P F j, AddCommGroup (H P F j)]
  pull : ∀ {Q P : C ⥤ Type} (_ : Q ⟶ P) (F : Coef C) (j : ℕ), H P F j →+ H Q F j
  map : ∀ (P : C ⥤ Type) {F G : Coef C} (_ : F ⟶ G) (j : ℕ), H P F j →+ H P G j
  pull_map : ∀ {Q P : C ⥤ Type} (u : Q ⟶ P) {F G : Coef C} (α : F ⟶ G) (j : ℕ) (x : H P F j),
    pull u G j (map P α j x) = map Q α j (pull u F j x)
  δ : ∀ (P : C ⥤ Type) (S : ShortComplex (Coef C)), S.ShortExact → ∀ j : ℕ, H P S.X₃ j →+ H P S.X₁ (j + 1)
  pull_δ : ∀ {Q P : C ⥤ Type} (u : Q ⟶ P) (S : ShortComplex (Coef C)) (h : S.ShortExact) (j : ℕ) (x : H P S.X₃ j),
    pull u S.X₁ (j + 1) (δ P S h j x) = δ Q S h j (pull u S.X₃ j x)
  ex₃ : ∀ (P : C ⥤ Type) (S : ShortComplex (Coef C)) (h : S.ShortExact) (j : ℕ), Function.Exact (map P S.g j) (δ P S h j)
  ex₁ : ∀ (P : C ⥤ Type) (S : ShortComplex (Coef C)) (h : S.ShortExact) (j : ℕ), Function.Exact (δ P S h j) (map P S.f (j + 1))
  zero : ∀ (P : C ⥤ Type) (F : Coef C), H P F 0 ≃+ Sec P F
  zero_pull : ∀ {Q P : C ⥤ Type} (u : Q ⟶ P) (F : Coef C) (x : H P F 0) (A : C) (y : Q.obj A),
    (zero Q F (pull u F 0 x)).1 A y = (zero P F x).1 A (u.app A y)
  zero_map : ∀ (P : C ⥤ Type) {F G : Coef C} (α : F ⟶ G) (x : H P F 0) (A : C) (y : P.obj A),
    (zero P G (map P α 0 x)).1 A y = (α.app A).hom ((zero P F x).1 A y)
  inj : ∀ (P : C ⥤ Type) (K : Coef C), Injective K → ∀ j : ℕ, Subsingleton (H P K (j + 1))

attribute [instance] Theory.ab

def Parts.LocZero (Pa : Parts C) {Q P : C ⥤ Type} {I : Type} [Fintype I] (a : I → ℤ) (u : I → (Q ⟶ P)) : Prop :=
  ∀ (A : C) (y : Q.obj A), ∃ S : Fam A, Pa.Cov S ∧ ∀ s,
    ∑ i, Finsupp.single ((u i).app _ (Q.map (S.f s) y)) (a i) = 0 ∨ Pa.Cov (⟨Empty, fun e => e.elim, fun e => e.elim⟩ : Fam (S.B s))

def Parts.LocTrans (Pa : Parts C) {Q P : C ⥤ Type} (p : Q ⟶ P) {I : Type} [Fintype I] (g : I → (Q ⟶ Q)) : Prop :=
  (∀ i, g i ≫ p = p) ∧ (∀ A, Function.Surjective (p.app A)) ∧
  ∀ (A : C) (y y' : Q.obj A), p.app A y = p.app A y' → ∃ S : Fam A, Pa.Cov S ∧ ∀ s,
    (Finset.univ.val.map fun i => (g i).app _ (Q.map (S.f s) y)) = Finset.univ.val.map fun i => (g i).app _ (Q.map (S.f s) y')

def Emb : Prop := ∀ (C : Type 1) [Category.{0} C] (Pa : Parts C) (F : Coef C), Pa.Add F →
  ∃ (K : Coef C) (ι : F ⟶ K), Mono ι ∧ Injective K ∧ Pa.Add K

def QuotAdd : Prop := ∀ (C : Type 1) [Category.{0} C] (Pa : Parts C) (S : ShortComplex (Coef C)), S.ShortExact →
  Pa.Add S.X₁ → Pa.Add S.X₂ → Pa.Add S.X₃

def LocSum : Prop := ∀ (C : Type 1) [Category.{0} C] (Pa : Parts C) (T : Theory C) (F : Coef C), Pa.Add F →
  ∀ (Q P : C ⥤ Type) (I : Type) [Fintype I] (a : I → ℤ) (u : I → (Q ⟶ P)), Pa.LocZero a u →
  ∀ (j : ℕ) (x : T.H P F j), ∑ i, a i • T.pull (u i) F j x = 0

def LocAvg : Prop := ∀ (C : Type 1) [Category.{0} C] (Pa : Parts C) (T : Theory C) (F : Coef C), Pa.Add F →
  ∀ (Q P : C ⥤ Type) (p : Q ⟶ P) (I : Type) [Fintype I] (g : I → (Q ⟶ Q)), Pa.LocTrans p g →
  ∀ (j : ℕ) (x : T.H P F j), T.pull p F j x = 0 → Fintype.card I • x = 0

end UpperTheory.Ru.crystallineComparison
