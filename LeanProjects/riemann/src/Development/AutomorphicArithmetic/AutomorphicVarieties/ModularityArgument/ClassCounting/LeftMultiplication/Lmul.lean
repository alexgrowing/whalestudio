import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.HasVal

noncomputable section

namespace UpperTheory.V.ZK.PM

variable (A : Type) [CommRing A] {G : Type} [Group G]

def cone (a : G) (m : ℕ) : Ch A G m →ₗ[A] Ch A G (m + 1) :=
  Finsupp.lmapDomain A A fun x => Fin.cons (α := fun _ => G) a x

def rmul (k : G) (m : ℕ) : Ch A G m →ₗ[A] Ch A G m := Finsupp.lmapDomain A A fun x i => x i * k

def lmul (h : G) (m : ℕ) : Ch A G m →ₗ[A] Ch A G m := Finsupp.lmapDomain A A fun x i => h * x i

def hbd (G : Type) [Group G] : ∀ m : ℕ, Ch A G (m + 1) →ₗ[A] Ch A G m
  | 0 => Finsupp.linearCombination A fun x => Finsupp.single (Fin.tail (α := fun _ => G) x) 1
  | m + 1 => Finsupp.linearCombination A fun x => Finsupp.single (Fin.tail (α := fun _ => G) x) 1 -
      cone A (x 0) m (hbd G m (Finsupp.single (Fin.tail (α := fun _ => G) x) 1))

def hp (k : G) : ∀ m : ℕ, Ch A G m →ₗ[A] Ch A G (m + 1)
  | 0 => 0
  | m + 1 => Finsupp.linearCombination A fun x => cone A (x 0) (m + 1)
      (rmul A k (m + 1) (Finsupp.single x 1) - hp k m (Finsupp.single (Fin.tail (α := fun _ => G) x) 1))

def hd (k k' : G) : ∀ m : ℕ, Ch A G m →ₗ[A] Ch A G (m + 2)
  | 0 => 0
  | m + 1 => Finsupp.linearCombination A fun x => cone A (x 0) (m + 2)
      (hp A k' (m + 1) (rmul A k (m + 1) (Finsupp.single x 1)) +
        hd k k' m (Finsupp.single (Fin.tail (α := fun _ => G) x) 1))

def pr (G : Type) [Group G] (m : ℕ) : Ch A G (m + 1) →ₗ[A] Ch A G m :=
  Finsupp.lmapDomain A A fun x i => (x i.castSucc)⁻¹ * x i.succ

end UpperTheory.V.ZK.PM

end
