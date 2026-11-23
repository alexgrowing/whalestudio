import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.ColimEx

variable {A : Type} [CommRing A] {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
  (f : ∀ n, G n →ₐ[A] G (n + 1))

def trA (i j : ℕ) (h : i ≤ j) : G i →ₐ[A] G j :=
  Nat.leRecOn (C := fun k => G i →ₐ[A] G k) h (fun {k} g => (f k).comp g) (AlgHom.id A (G i))

theorem trA_self (i : ℕ) (h : i ≤ i) : trA f i i h = AlgHom.id A (G i) :=
  Nat.leRecOn_self (C := fun k => G i →ₐ[A] G k) _

theorem trA_succ (i k : ℕ) (h : i ≤ k) (h2 : i ≤ k + 1) :
    trA f i (k + 1) h2 = (f k).comp (trA f i k h) :=
  Nat.leRecOn_succ (C := fun k => G i →ₐ[A] G k) h _

theorem trA_trans (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (x : G i) :
    trA f j k hjk (trA f i j hij x) = trA f i k (hij.trans hjk) x := by
  induction k, hjk using Nat.le_induction with
  | base => rw [trA_self]; rfl
  | succ k hjk ih =>
    rw [trA_succ f j k hjk, trA_succ f i k (hij.trans hjk)]
    simp only [AlgHom.comp_apply, ih]

theorem tr_eq_trA (n k : ℕ) (x : G n) : tr f n k x = trA f n (n + k) (Nat.le_add_right n k) x := by
  induction k with
  | zero =>
    show tr f n 0 x = trA f n n (Nat.le_refl n) x
    rw [trA_self]; rfl
  | succ k ih =>
    have h := trA_succ f n (n + k) (Nat.le_add_right n k) (Nat.le_add_right n (k + 1))
    show f (n + k) (tr f n k x) = trA f n (n + k + 1) (Nat.le_add_right n (k + 1)) x
    rw [h, AlgHom.comp_apply, ih]

def trR (i j : ℕ) (h : i ≤ j) : G i →+* G j := (trA f i j h).toRingHom

instance directedSystem_trR : DirectedSystem G fun i j h => trR f i j h where
  map_self i x := by simp [trR, trA_self]
  map_map k j i hij hjk x := trA_trans f i j k hij hjk x

abbrev Lim := Ring.DirectLimit G fun i j h => trR f i j h

instance : Algebra A (Lim f) :=
  ((Ring.DirectLimit.of G (fun i j h => trR f i j h) 0).comp (algebraMap A (G 0))).toAlgebra

def ι (n : ℕ) : G n →ₐ[A] Lim f :=
  { Ring.DirectLimit.of G (fun i j h => trR f i j h) n with
    commutes' := fun a => by
      show Ring.DirectLimit.of G (fun i j h => trR f i j h) n (algebraMap A (G n) a) =
        Ring.DirectLimit.of G (fun i j h => trR f i j h) 0 (algebraMap A (G 0) a)
      rw [← Ring.DirectLimit.of_f (G := G) (f := fun i j h => trR f i j h) (Nat.zero_le n)
        (algebraMap A (G 0) a)]
      simp [trR] }

theorem ι_apply (n : ℕ) (x : G n) :
    ι f n x = Ring.DirectLimit.of G (fun i j h => trR f i j h) n x := rfl

theorem ι_trA (i j : ℕ) (h : i ≤ j) (x : G i) : ι f j (trA f i j h x) = ι f i x := by
  rw [ι_apply, ι_apply]
  exact Ring.DirectLimit.of_f (G := G) (f := fun i j h => trR f i j h) h x

theorem ι_tr (n k : ℕ) (x : G n) : ι f (n + k) (tr f n k x) = ι f n x := by
  rw [tr_eq_trA, ι_trA]

theorem isColim : IsColim f (ι f) where
  comm n x := by
    have := ι_tr f n 1 x
    simpa [tr] using this
  surj m x := by
    choose n y hy using fun i => Ring.DirectLimit.exists_of (x i)
    refine ⟨Finset.univ.sup n, fun i => trA f (n i) _ (Finset.le_sup (Finset.mem_univ i)) (y i),
      fun i => ?_⟩
    rw [ι_trA, ι_apply, hy]
  ker n m y hy := by
    have h0 : ∀ i, ∃ j, ∃ hij : n ≤ j, trR f n j hij (y i) = 0 := fun i =>
      Ring.DirectLimit.of.zero_exact (f' := fun i j h => trR f i j h) (hy i)
    choose j hj hz using h0
    refine ⟨Finset.univ.sup fun i => j i - n, fun i => ?_⟩
    have hle : j i ≤ n + Finset.univ.sup fun i => j i - n := by
      have := Finset.le_sup (f := fun i => j i - n) (Finset.mem_univ i)
      omega
    rw [tr_eq_trA, ← trA_trans f n (j i) _ (hj i) hle]
    have : trA f n (j i) (hj i) (y i) = 0 := hz i
    rw [this, map_zero]

end GlobalTheory.CompanionTheory.ColimEx

theorem GlobalTheory.CompanionTheory.ColimEx.exists_isColim : ∀ (A : Type) [CommRing A](G : ℕ → Type) [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)] (f : ∀ n, G n →ₐ[A] G (n + 1)), ∃ (L : Type) (_ : CommRing L) (_ : Algebra A L), ∃ ι : ∀ n, G n →ₐ[A] L, IsColim f ι :=
  fun A _ G _ _ f => ⟨GlobalTheory.CompanionTheory.ColimEx.Lim f, inferInstance, inferInstance, GlobalTheory.CompanionTheory.ColimEx.ι f,
    GlobalTheory.CompanionTheory.ColimEx.isColim f⟩
