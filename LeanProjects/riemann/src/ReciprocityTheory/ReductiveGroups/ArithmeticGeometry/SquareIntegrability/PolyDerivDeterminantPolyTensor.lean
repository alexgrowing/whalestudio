import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain

namespace ReciprocityTheory.ChartRestriction.G.I2

open MvPolynomial

noncomputable section

variable {E : Type} [Field E] [NumberField E] {n nb : ℕ} {dim : (E →+* ℂ) → ℕ}

section Expand
variable (bs : Fin nb → Block E n dim)

abbrev Choice := ∀ j : Fin nb, Fin (bs j).c → Equiv.Perm (Fin (bs j).i)

abbrev Slot := Σ j : Fin nb, Fin (bs j).c × Fin (bs j).i

def sgnT (T : Choice bs) : ℂ := ∏ j, ∏ r, ((Equiv.Perm.sign (T j r) : ℤ) : ℂ)

def letter (T : Choice bs) (t : Slot bs) : Letter n dim :=
  ((bs t.1).col t.2.2, ⟨(bs t.1).τ, Fin.castLE (bs t.1).hi (T t.1 t.2.1 t.2.2)⟩)

theorem block_poly_expand (B : Block E n dim) :
    B.poly = ∑ p : Fin B.c → Equiv.Perm (Fin B.i),
      (∏ r, ((Equiv.Perm.sign (p r) : ℤ) : MvPolynomial (Letter n dim) ℂ)) *
        ∏ r, ∏ b, X (B.col b, ⟨B.τ, Fin.castLE B.hi (p r b)⟩) := by
  rw [Block.poly, Matrix.det_apply', ← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.prod_mul_distrib]
  rfl

theorem determinantPoly_expand :
    P1 bs = ∑ T : Choice bs, sgnT bs T • ∏ t : Slot bs, X (letter bs T t) := by
  rw [P1]
  simp only [block_poly_expand]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_mul_distrib, MvPolynomial.smul_eq_C_mul]
  congr 1
  · simp only [sgnT, map_prod, map_intCast]
  · rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Fintype.prod_prod_type]
    rfl

end Expand

section PD
variable (X : PT E) (bs : Fin nb → Block E n X.dim)

open Classical in

def lst (T : Choice bs) : List (Fin n × Vsp X.dim) :=
  (Multiset.map (letter bs T) Finset.univ.val).toList.map
    (fun l => (l.1, EuclideanSpace.single l.2 (1 : ℂ)))

theorem prod_X_letter (T : Choice bs) :
    (∏ t : Slot bs, MvPolynomial.X (letter bs T t) : MvPolynomial (Letter n X.dim) ℂ) =
      monomial (∑ t : Slot bs, Finsupp.single (letter bs T t) 1) 1 := by
  rw [MvPolynomial.monomial_sum_one]
  rfl

theorem toMultiset_letters (T : Choice bs) :
    Finsupp.toMultiset (∑ t : Slot bs, Finsupp.single (letter bs T t) 1) =
      Multiset.map (letter bs T) Finset.univ.val := by
  rw [map_sum]
  simp only [Finsupp.toMultiset_single, one_nsmul]
  rw [Finset.sum_eq_multiset_sum]
  have h : ∀ (s : Multiset (Slot bs)),
      (s.map fun t => ({letter bs T t} : Multiset (Letter n X.dim))).sum = s.map (letter bs T) := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih => simp [ih]
  exact h _

theorem polyDeriv_determinantPoly_tensor (s : Fin n → (Fin 1 → Vsp X.dim) → ℂ)
    (hs : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (s k)) :
    polyDeriv (P1 bs) dir (tens X s) 0 =
      ∑ T : Choice bs, sgnT bs T * ∏ k, d1 (s k) (colL (lst X bs T) k).length
        (fun j => (colL (lst X bs T) k).get j) := by
  rw [determinantPoly_expand, jof_polyDeriv_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [polyDeriv_smul, prod_X_letter, polyDeriv_monomial_one, pdTerm_eq_itD, toMultiset_letters]
  congr 1
  have hl : (Multiset.map (letter bs T) Finset.univ.val).toList.map dir =
      (lst X bs T).map (fun p => Pi.single p.1 p.2) := by
    rw [lst, List.map_map]
    rfl
  rw [hl]
  have hg : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (fun z : Vsp X.dim => s k (fun _ => z)) := fun k =>
    (hs k).comp (contDiff_pi.2 fun _ => contDiff_id)
  have h1 := itD_prod hg (lst X bs T) 0
  rw [show tens X s = fun v : Fin n → Vsp X.dim => ∏ k, s k (fun _ => v k) from rfl, h1]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Pi.zero_apply, itD_col (hs k)]
  rfl

open Classical in

theorem colL_coe (T : Choice bs) (k : Fin n) :
    ((colL (lst X bs T) k : List (Vsp X.dim)) : Multiset (Vsp X.dim)) =
      ((Multiset.map (letter bs T) Finset.univ.val).filter (fun l => l.1 = k)).map
        (fun l => EuclideanSpace.single l.2 (1 : ℂ)) := by
  rw [colL, lst, List.filter_map, List.map_map, ← Multiset.map_coe]
  conv_rhs => rw [← Multiset.coe_toList (Multiset.map (letter bs T) Finset.univ.val),
    Multiset.filter_coe, Multiset.map_coe]
  rfl

end PD

end

end ReciprocityTheory.ChartRestriction.G.I2
