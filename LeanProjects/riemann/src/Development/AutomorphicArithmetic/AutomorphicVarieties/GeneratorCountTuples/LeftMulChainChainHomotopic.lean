import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LeftMultiplication.Lmul
open UpperTheory.V.ZK UpperTheory.V.ZK.PM

section
variable (A : Type) [CommRing A] {G : Type} [Group G]

private theorem lmul_single (h : G) (m : ℕ) (x : Fin m → G) (a : A) :
    lmul A h m (Finsupp.single x a) = Finsupp.single (fun i => h * x i) a := by
  simp [lmul]

private theorem lmul_cone (h a : G) (m : ℕ) (y : Ch A G m) :
    lmul A h (m + 1) (cone A a m y) = cone A (h * a) m (lmul A h m y) := by
  simp only [lmul, cone, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
  congr 1
  funext x i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

private theorem lmul_rmul (h k : G) (m : ℕ) (y : Ch A G m) :
    lmul A h m (rmul A k m y) = rmul A k m (lmul A h m y) := by
  simp only [lmul, rmul, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
  congr 1
  funext x i
  simp [mul_assoc]

private theorem pr_lmul (h : G) (m : ℕ) (y : Ch A G (m + 1)) :
    pr A G m (lmul A h (m + 1) y) = pr A G m y := by
  simp only [lmul, pr, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
  congr 1
  funext x i
  simp [mul_assoc]

private theorem lmul_hp (h k : G) : ∀ (m : ℕ) (y : Ch A G m),
    lmul A h (m + 1) (hp A k m y) = hp A k m (lmul A h m y)
  | 0, y => by simp [hp]
  | m + 1, y => by
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add, hf, hg]
    | single x a =>
      rw [lmul_single]
      simp only [hp, Finsupp.linearCombination_single, map_smul]
      rw [lmul_cone, map_sub, lmul_rmul, lmul_hp h k m, lmul_single, lmul_single]
      rfl

private theorem lmul_hd (h k k' : G) : ∀ (m : ℕ) (y : Ch A G m),
    lmul A h (m + 2) (hd A k k' m y) = hd A k k' m (lmul A h m y)
  | 0, y => by simp [hd]
  | m + 1, y => by
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add, hf, hg]
    | single x a =>
      rw [lmul_single]
      simp only [hd, Finsupp.linearCombination_single, map_smul]
      rw [lmul_cone, map_add, lmul_hp, lmul_rmul, lmul_hd h k k' m, lmul_single, lmul_single]
      rfl

end

theorem UpperTheory.leftMulChain_chainHomotopic :
    ∀ (A : Type) [CommRing A] (G : Type) [Group G] (k k' h : G) (m : ℕ) (z : Ch A G (m + 1)), pr A G (m + 2) (hd A k k' (m + 1) (lmul A h (m + 1) z)) = pr A G (m + 2) (hd A k k' (m + 1) z) := by
  intro A _ G _ k k' h m z
  rw [← lmul_hd]
  exact pr_lmul A h (m + 2) _
