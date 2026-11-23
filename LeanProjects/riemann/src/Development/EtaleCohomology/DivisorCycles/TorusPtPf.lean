import Development.EtaleCohomology.DivisorCycles.OpenCoset

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.TorusPtPf
open LateralTheory.DivDb

variable {C : Type} [Field C] [CharZero C]

noncomputable def E (a : C) : PowerSeries C := PowerSeries.rescale a (PowerSeries.exp C)

lemma coeff_E (a : C) (k : ℕ) : PowerSeries.coeff k (E a) = a ^ k * (k.factorial : C)⁻¹ := by
  simp [E, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]

lemma E_add (a b : C) : E a * E b = E (a + b) := PowerSeries.exp_mul_exp_eq_exp_add a b

lemma E_zero : E (0 : C) = 1 := by
  ext k; rcases k with _ | k <;> simp [coeff_E, PowerSeries.coeff_one]

lemma E_prod {ι : Type} (s : Finset ι) (a : ι → C) : ∏ i ∈ s, E (a i) = E (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [E_zero]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, E_add]

lemma E_pow (a : C) (m : ℕ) : E a ^ m = E ((m : C) * a) := by
  induction m with
  | zero => simp [E_zero]
  | succ m ih => rw [pow_succ, ih, E_add]; congr 1; push_cast; ring

lemma E_ne (a b c : C) (h : E a - PowerSeries.C b * E c = 0) : b = 1 ∧ a = c := by
  have h0 := congrArg (PowerSeries.coeff 0) h
  have h1 := congrArg (PowerSeries.coeff 1) h
  simp only [map_sub, PowerSeries.coeff_C_mul, coeff_E, map_zero] at h0 h1
  simp at h0 h1
  have hb : b = 1 := by linear_combination -h0
  refine ⟨hb, ?_⟩
  rw [hb] at h1
  linear_combination h1

lemma pow_sys {N n : ℕ} {p : Fin n → Mat C N} (hp : Sys p) (e : Fin n → C) (k : ℕ) :
    (∑ i, e i • p i) ^ k = ∑ i, e i ^ k • p i := by
  induction k with
  | zero => simpa using hp.1.complete.symm
  | succ k ih =>
    rw [pow_succ, ih, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [smul_mul_smul_comm, (hp.1.idem i).eq, pow_succ]
    · intro j _ hji; rw [smul_mul_smul_comm, hp.1.ortho hji.symm, smul_zero]
    · simp

lemma entry_exp {N n : ℕ} {p : Fin n → Mat C N} (hp : Sys p) (e : Fin n → C) (a b : Fin N) :
    (PowerSeries.mk fun k => ((k.factorial : C)⁻¹ • (∑ i, e i • p i) ^ k) a b) =
      ∑ j, PowerSeries.C (p j a b) * E (e j) := by
  ext k
  simp only [PowerSeries.coeff_mk, map_sum, PowerSeries.coeff_C_mul, coeff_E, pow_sys hp, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

noncomputable def F {N n : ℕ} (p : Fin n → Mat C N) (f : MP C N) : MvPolynomial (Fin n) C :=
  MvPolynomial.bind₁ (fun ab : Fin N × Fin N => ∑ j, MvPolynomial.C (p j ab.1 ab.2) * MvPolynomial.X j) f

noncomputable def bin {n : ℕ} (q : Finset (Fin n) × Finset (Fin n) × C) : MvPolynomial (Fin n) C :=
  (∏ i ∈ q.1, MvPolynomial.X i) ^ q.2.1.card - MvPolynomial.C q.2.2 * (∏ i ∈ q.2.1, MvPolynomial.X i) ^ q.1.card

theorem TorusPt_of (hE : ExpVan) (hS : SpecPt) : TorusPt := by
  intro C _ _ _ N n S p e hp hlac hX B hB
  classical
  let x : Fin n → PowerSeries C := fun j => E (e j)
  let Q : Set (Finset (Fin n) × Finset (Fin n) × C) :=
    {q | q.1.Nonempty ∧ q.2.1.Nonempty ∧ Disjoint q.1 q.2.1 ∧ q.2.2 ∈ B}
  let G : Set (MvPolynomial (Fin n) C) := Set.range (fun j => MvPolynomial.X j) ∪ bin '' Q
  have hQ : Q.Finite := (Set.finite_univ.prod (Set.finite_univ.prod hB)).subset fun q hq => by
    simp only [Set.mem_prod, Set.mem_univ, true_and]; exact hq.2.2.2
  have hG : G.Finite := (Set.finite_range _).union (hQ.image _)
  have hxg : ∀ g ∈ G, MvPolynomial.aeval x g ≠ 0 := by
    rintro g (⟨j, rfl⟩ | ⟨q, ⟨h1, h2, h3, h4⟩, rfl⟩)
    · intro h0
      have := congrArg (PowerSeries.coeff 0) h0
      simp [x, coeff_E] at this
    · intro h0
      simp only [bin, map_sub, map_mul, map_pow, map_prod, MvPolynomial.aeval_X, MvPolynomial.aeval_C, x, E_prod,
        E_pow] at h0
      have h0' : E ((q.2.1.card : C) * ∑ i ∈ q.1, e i) - PowerSeries.C q.2.2 * E ((q.1.card : C) * ∑ i ∈ q.2.1, e i) = 0 := by
        simpa using h0
      exact hlac _ _ h1 h2 h3 (E_ne _ _ _ h0').2
  obtain ⟨y, hy1, hy2⟩ := hS C (PowerSeries C) (Fin n) x G hG hxg
  refine ⟨y, fun j => ?_, fun f hf => ?_, fun O O' hO hO' hd b hb => ?_⟩
  · have := hy2 _ (Or.inl ⟨j, rfl⟩); simpa using this
  · have h := hE C N S _ hX f hf
    have hent : (fun ab : Fin N × Fin N => PowerSeries.mk fun k =>
          ((k.factorial : C)⁻¹ • (∑ i, e i • p i) ^ k) ab.1 ab.2)
        = fun ab => MvPolynomial.aeval x (∑ j, MvPolynomial.C (p j ab.1 ab.2) * MvPolynomial.X j) := by
      funext ab; rw [entry_exp hp]; simp [x]
    rw [hent, ← MvPolynomial.aeval_bind₁] at h
    have h2 := hy1 _ h
    have h3 : MvPolynomial.aeval y
        ((MvPolynomial.bind₁ fun ab : Fin N × Fin N => ∑ j, MvPolynomial.C (p j ab.1 ab.2) * MvPolynomial.X j) f) = 0 := by
      exact h2
    rw [MvPolynomial.aeval_bind₁] at h3
    unfold ev
    rw [show (fun q : Fin N × Fin N => (∑ j, y j • p j) q.1 q.2) = fun ab =>
        MvPolynomial.aeval y (∑ j, MvPolynomial.C (p j ab.1 ab.2) * MvPolynomial.X j) from
      funext fun ab => by simp [Matrix.sum_apply, mul_comm]]
    exact h3
  · intro h
    apply hy2 _ (Or.inr ⟨(O, O', b), ⟨hO, hO', hd, hb⟩, rfl⟩)
    simp only [bin, map_sub, map_mul, map_pow, map_prod, MvPolynomial.eval_X, MvPolynomial.eval_C]
    rw [h]; ring
end LateralTheory.DivDb.TorusPtPf
