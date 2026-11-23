import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SumSplitsEvalTwoWord

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.G2

variable {k : Type} [CommRing k] {d : ℕ}

section Mon
variable (F : Fin d → PS k 2 d) {ι : Type} (u : ι → Fin d → k)

end Mon

section abelian₂
variable {ι : Type} [Fintype ι] [DecidableEq ι] (ψ : List ι → k)

def lamW (P : MvPolynomial ι k) : k :=
  (AddMonoidAlgebra.coeff P).sum (fun n a => a * ψ (word (Finset.univ : Finset ι).toList n))

theorem lamW_add (P Q : MvPolynomial ι k) : lamW ψ (P + Q) = lamW ψ P + lamW ψ Q := by
  show (AddMonoidAlgebra.coeff P + AddMonoidAlgebra.coeff Q).sum _ = _
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem lamW_monomial (n : ι →₀ ℕ) (a : k) :
    lamW ψ (MvPolynomial.monomial n a) = a * ψ (word (Finset.univ : Finset ι).toList n) := by
  show (Finsupp.single n a).sum _ = _
  exact Finsupp.sum_single_index (zero_mul _)

theorem lamW_sum (s : Finset ι) (f : ι → MvPolynomial ι k) :
    lamW ψ (∑ i ∈ s, f i) = ∑ i ∈ s, lamW ψ (f i) := by
  let L : MvPolynomial ι k →+ k :=
    { toFun := lamW ψ, map_zero' := by simpa using lamW_add ψ 0 0, map_add' := lamW_add ψ }
  exact map_sum L f s

def rW (c : ι → ι → k) (n : ι →₀ ℕ) : k :=
  ((Finset.univ : Finset ι).toList.map (fun x => ((Finset.univ : Finset ι).toList.map (fun y =>
    c x y * ((n y * (n - Finsupp.single y 1 : ι →₀ ℕ) x : ℕ) : k) *
      ψ (word (Finset.univ : Finset ι).toList (n - Finsupp.single y 1 - Finsupp.single x 1)))).sum)).sum

theorem secondOrder_add (c : ι → ι → k) (p q : MvPolynomial ι k) :
    secondOrder k c (p + q) = secondOrder k c p + secondOrder k c q := by
  unfold secondOrder
  simp only [map_add, mul_add, add_mul, Finset.sum_add_distrib]
  done

theorem lamW_secondOrder (c : ι → ι → k) (P : MvPolynomial ι k) :
    lamW ψ (secondOrder k c P) = (AddMonoidAlgebra.coeff P).sum (fun n a => a * rW ψ c n) := by
  refine MvPolynomial.induction_on' P (fun n a => ?_) (fun p q hp hq => ?_)
  · show lamW ψ (secondOrder k c (MvPolynomial.monomial n a)) =
      (Finsupp.single n a).sum fun m b => b * rW ψ c m
    have hL : ∀ g : ι → k, ((Finset.univ : Finset ι).toList.map g).sum = ∑ i, g i := by
      intro g
      first
        | exact Finset.sum_map_toList _ _
        | exact Finset.sum_toList _ _
        | rw [Finset.sum_eq_multiset_sum, ← Finset.coe_toList, Multiset.map_coe, Multiset.sum_coe]
    rw [Finsupp.sum_single_index (zero_mul _)]
    simp only [secondOrder, lamW_sum, MvPolynomial.pderiv_monomial, MvPolynomial.C_mul_monomial,
      lamW_monomial, rW, hL, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [Nat.cast_mul]
    ring
  · rw [secondOrder_add, lamW_add, hp, hq]
    show _ = (AddMonoidAlgebra.coeff p + AddMonoidAlgebra.coeff q).sum _
    rw [Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]

end abelian₂

end ReciprocityTheory.ChartRestriction.G.TB.G2
