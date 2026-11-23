import Formalism.PieriBlockIdeals.IntegralQuotient
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InnerProductFormulaField

open Polynomial

namespace Formalism.CohomologicalDescent.Symmetrization

theorem commute_list_prod_of_commute_adjacent {B : Type*} [Ring B] (c : B) : ∀ (n : ℕ) (y : Fin n → B) (j : ℕ) (hj : j + 1 < n),
    Commute c (y ⟨j, by omega⟩ * y ⟨j + 1, hj⟩) →
    (∀ l : Fin n, l.val ≠ j → l.val ≠ j + 1 → Commute c (y l)) →
    Commute c (List.ofFn y).prod := by
  intro n
  induction n with
  | zero => intro y j hj; omega
  | succ n ih =>
    intro y j hj h1 h2
    rw [List.ofFn_succ, List.prod_cons]
    cases j with
    | zero =>
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [List.ofFn_succ, List.prod_cons, ← mul_assoc]
      refine Commute.mul_right h1 ?_
      apply Commute.list_prod_right
      intro b hb
      rw [List.mem_ofFn] at hb
      obtain ⟨i, rfl⟩ := hb
      exact h2 _ (by rw [Fin.val_succ, Fin.val_succ]; omega) (by rw [Fin.val_succ, Fin.val_succ]; omega)
    | succ j =>
      refine Commute.mul_right (h2 0 (by simp) (by simp)) ?_
      exact ih (fun i => y i.succ) j (by omega) h1
        (fun l hl1 hl2 => h2 l.succ (by rw [Fin.val_succ]; omega) (by rw [Fin.val_succ]; omega))

theorem symmetric_commute_abstract_holds : SymCommAbstract := by
  intro A _ n x s j hj hx hss hsa hfar
  have hCX : ∀ a : A, Commute s a → Commute (C s) (X - C a : A[X]) := fun a h =>
    ((commute_X (C s)).symm).sub_right (h.map C)
  refine commute_list_prod_of_commute_adjacent (C s) n (fun a => (X - C (x a) : A[X])) j.val hj ?_ ?_
  · obtain ⟨a, ha⟩ : ∃ a, a = x j := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = x ⟨j.val + 1, hj⟩ := ⟨_, rfl⟩
    have hab0 : Commute a b := by rw [ha, hb]; exact hx _ _
    rw [← ha, ← hb] at hsa
    have hsb : s * b = a * s + 1 := by
      have h1 : s * (s * a) * s = s * (b * s - 1) * s := by rw [hsa]
      have h2 : s * (s * a) * s = a * s := by rw [← mul_assoc, hss, one_mul]
      have h3 : s * (b * s - 1) * s = s * b - 1 := by
        rw [mul_sub, sub_mul, mul_one, hss, ← mul_assoc, mul_assoc (s * b), hss, mul_one]
      rw [h2, h3] at h1
      rw [h1]; abel
    show Commute (C s) ((X - C (x ⟨j.val, _⟩)) * (X - C (x ⟨j.val + 1, hj⟩)))
    have hj' : (⟨j.val, by omega⟩ : Fin n) = j := rfl
    rw [hj', ← ha, ← hb]
    have e1 : C s * (X - C a) = (X - C b) * C s + 1 := by
      rw [mul_sub, sub_mul, ← C_mul, hsa, C_sub, C_mul, C_1, X_mul_C]; abel
    have e2 : C s * (X - C b) = (X - C a) * C s - 1 := by
      rw [mul_sub, sub_mul, ← C_mul, hsb, C_add, C_mul, C_1, X_mul_C]; abel
    have hab : (X - C a) * (X - C b) = (X - C b) * (X - C a) :=
      (((Commute.refl (X : A[X])).sub_right (commute_X (C b))).sub_left
        (((commute_X (C a)).symm).sub_right (hab0.map C))).eq
    show C s * ((X - C a) * (X - C b)) = (X - C a) * (X - C b) * C s
    calc C s * ((X - C a) * (X - C b)) = (C s * (X - C a)) * (X - C b) := by rw [mul_assoc]
      _ = ((X - C b) * C s + 1) * (X - C b) := by rw [e1]
      _ = (X - C b) * (C s * (X - C b)) + (X - C b) := by rw [add_mul, one_mul, mul_assoc]
      _ = (X - C b) * ((X - C a) * C s - 1) + (X - C b) := by rw [e2]
      _ = (X - C b) * (X - C a) * C s := by rw [mul_sub, mul_one, mul_assoc]; abel
      _ = _ := by rw [← hab]
  · intro l hl1 hl2
    exact hCX _ (hfar l (fun h => hl1 (by rw [h])) (fun h => hl2 (by rw [h])))

section JM

variable {A R : Type*} [Ring A] [Fintype R] [DecidableEq R]

theorem casimir_pair_commute_sum (P Q : R → R → A) (hP : GlRel P) (hQ : GlRel Q) (hPQ : ∀ a b c d, Commute (P a b) (Q c d))
    (c d : R) : Commute (∑ b, ∑ b', P b b' * Q b' b) (P c d + Q c d) := by
  have key : ∀ b b', P b b' * Q b' b * (P c d + Q c d) - (P c d + Q c d) * (P b b' * Q b' b) =
      ((if b' = c then P b d else 0) - (if d = b then P c b' else 0)) * Q b' b +
        P b b' * ((if b = c then Q b' d else 0) - (if d = b' then Q c b else 0)) := by
    intro b b'
    rw [← hP b b' c d, ← hQ b' b c d]
    have h1 := (hPQ c d b' b).eq
    have h2 := (hPQ b b' c d).eq
    have e1 : P b b' * Q b' b * P c d = P b b' * P c d * Q b' b := by rw [mul_assoc, ← h1, mul_assoc]
    have e2 : Q c d * (P b b' * Q b' b) = P b b' * Q c d * Q b' b := by rw [← mul_assoc, ← h2]
    rw [mul_add, add_mul, e1, e2]
    noncomm_ring
  have hsum : (∑ b, ∑ b', P b b' * Q b' b) * (P c d + Q c d) - (P c d + Q c d) * (∑ b, ∑ b', P b b' * Q b' b) =
      ∑ b, ∑ b', (P b b' * Q b' b * (P c d + Q c d) - (P c d + Q c d) * (P b b' * Q b' b)) := by
    simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
  have S1 : ∑ b, ∑ b', (if b' = c then P b d else 0) * Q b' b = ∑ b, P b d * Q c b := by
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [ite_mul]
  have S2 : ∑ b, ∑ b', (if d = b then P c b' else 0) * Q b' b = ∑ b', P c b' * Q b' d := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => ?_
    simp [ite_mul]
  have S3 : ∑ b, ∑ b', P b b' * (if b = c then Q b' d else 0) = ∑ b', P c b' * Q b' d := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => ?_
    simp [mul_ite]
  have S4 : ∑ b, ∑ b', P b b' * (if d = b' then Q c b else 0) = ∑ b, P b d * Q c b := by
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [mul_ite]
  rw [commute_iff_eq, ← sub_eq_zero, hsum,
    Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun b' _ => key b b'))]
  simp only [sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [S1, S2, S3, S4]
  abel

def positionTransposition (ε : ℕ → R → R → A) (i j : ℕ) : A := ∑ b, ∑ b', ε i b b' * ε j b' b

variable (ε : ℕ → R → R → A) (H1 : ∀ j, GlRel (ε j))
  (H2 : ∀ i j, i ≠ j → ∀ a b c d, Commute (ε i a b) (ε j c d))

include H2 in
theorem transposition_commute_disjoint (i j l : ℕ) (hi : l ≠ i) (hj : l ≠ j) (c d : R) : Commute (positionTransposition ε i j) (ε l c d) := by
  unfold positionTransposition
  refine Commute.sum_left _ _ _ fun b _ => Commute.sum_left _ _ _ fun b' _ => ?_
  exact Commute.mul_left (H2 i l hi.symm _ _ _ _) (H2 j l hj.symm _ _ _ _)

include H2 in
theorem transposition_commute_disjoint_pair (i j l m : ℕ) (hli : l ≠ i) (hlj : l ≠ j) (hmi : m ≠ i) (hmj : m ≠ j) :
    Commute (positionTransposition ε i j) (positionTransposition ε l m) := by
  rw [positionTransposition.eq_1 ε l m]
  refine Commute.sum_right _ _ _ fun b _ => Commute.sum_right _ _ _ fun b' _ => ?_
  exact Commute.mul_right (transposition_commute_disjoint ε H2 i j l hli hlj _ _) (transposition_commute_disjoint ε H2 i j m hmi hmj _ _)

include H1 H2 in
theorem transposition_commute_sum_pair (i j : ℕ) (hij : i ≠ j) (c d : R) : Commute (positionTransposition ε i j) (ε i c d + ε j c d) :=
  casimir_pair_commute_sum (ε i) (ε j) (H1 i) (H1 j) (H2 i j hij) c d

include H1 H2 in
theorem transposition_commute_sum_shared (i j l : ℕ) (hij : i ≠ j) (hli : l ≠ i) (hlj : l ≠ j) :
    Commute (positionTransposition ε i j) (positionTransposition ε i l + positionTransposition ε j l) := by
  have h : positionTransposition ε i l + positionTransposition ε j l = ∑ c, ∑ d, (ε i c d + ε j c d) * ε l d c := by
    simp only [positionTransposition, add_mul, Finset.sum_add_distrib]
  rw [h]
  refine Commute.sum_right _ _ _ fun b _ => Commute.sum_right _ _ _ fun b' _ => ?_
  exact Commute.mul_right (transposition_commute_sum_pair ε H1 H2 i j hij _ _) (transposition_commute_disjoint ε H2 i j l hli hlj _ _)

omit [Fintype R] [DecidableEq R] in
theorem commute_sum_of_commute_pair_and_rest (c : A) (f : ℕ → A) (s : Finset ℕ) (a i : ℕ) (ha : a ∈ s) (hi : i ∈ s) (hai : a ≠ i)
    (h1 : Commute c (f a + f i)) (h2 : ∀ b ∈ s, b ≠ a → b ≠ i → Commute c (f b)) :
    Commute c (∑ b ∈ s, f b) := by
  rw [← Finset.add_sum_erase s f ha, ← Finset.add_sum_erase (s.erase a) f (Finset.mem_erase.2 ⟨hai.symm, hi⟩),
    ← add_assoc]
  refine h1.add_right (Commute.sum_right _ _ _ ?_)
  intro b hb
  simp only [Finset.mem_erase] at hb
  exact h2 b hb.2.2 hb.2.1 hb.1

include H1 H2 in
theorem commute_partial_jucysMurphy_sums (i j : ℕ) (hij : i < j) :
    Commute (∑ a ∈ Finset.range i, positionTransposition ε a i) (∑ a ∈ Finset.range j, positionTransposition ε a j) := by
  refine Commute.sum_left _ _ _ fun a ha => ?_
  have hai : a < i := Finset.mem_range.1 ha
  refine commute_sum_of_commute_pair_and_rest _ (fun b => positionTransposition ε b j) _ a i (Finset.mem_range.2 (by omega)) (Finset.mem_range.2 hij)
    (by omega) (transposition_commute_sum_shared ε H1 H2 a i j (by omega) (by omega) (by omega)) ?_
  intro b hb hba hbi
  have hbj : b < j := Finset.mem_range.1 hb
  exact transposition_commute_disjoint_pair ε H2 a i b j hba hbi (by omega) (by omega)

end JM

theorem jucys_murphy_commute_holds : JMCommAbstract := by
  intro A R _ _ _ ε H1 H2
  refine ⟨?_, ?_⟩
  · intro i j
    rcases lt_trichotomy i j with h | h | h
    · exact commute_partial_jucysMurphy_sums ε H1 H2 i j h
    · subst h; exact Commute.refl _
    · exact (commute_partial_jucysMurphy_sums ε H1 H2 j i h).symm
  · intro j m c d hjm
    refine Commute.sum_left _ _ _ fun a ha => ?_
    have haj : a < j := Finset.mem_range.1 ha
    refine commute_sum_of_commute_pair_and_rest _ (fun i => ε i c d) _ a j (Finset.mem_range.2 (by omega)) (Finset.mem_range.2 hjm)
      (by omega) (transposition_commute_sum_pair ε H1 H2 a j (by omega) c d) ?_
    intro b _ hba hbj
    exact transposition_commute_disjoint ε H2 a j b hba hbj c d

open scoped IsMulCommutative in
theorem exists_mvPolynomial_algHom_commuting {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M] {n : ℕ} (c : Fin n → Module.End O M)
    (hc : ∀ a b, Commute (c a) (c b)) :
    ∃ φ : MvPolynomial (Fin n) O →ₐ[O] Module.End O M,
      (∀ a, φ (MvPolynomial.X a) = c a) ∧ ∀ p, φ p ∈ Algebra.adjoin O (Set.range c) := by
  have : IsMulCommutative (Algebra.adjoin O (Set.range c)) := Algebra.isMulCommutative_adjoin O (by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact (hc a b).eq)
  let ψ := MvPolynomial.aeval (R := O) (S₁ := Algebra.adjoin O (Set.range c))
    fun a : Fin n => (⟨c a, Algebra.subset_adjoin ⟨a, rfl⟩⟩ : Algebra.adjoin O (Set.range c))
  refine ⟨(Algebra.adjoin O (Set.range c)).val.comp ψ, ?_, ?_⟩
  · intro a; simp [ψ]
  · intro p; exact (ψ p).2

theorem integral_quotient_holds : IntegralQuotient := by
  intro O K M I _ _ _ _ _ _ _ n c hc Mt χ hχ Dn hdiv w
  obtain ⟨φ, hφX, hφmem⟩ := exists_mvPolynomial_algHom_commuting c hc
  obtain ⟨AAp, hAAp⟩ : ∃ p : (MvPolynomial (Fin n) O)[X],
    p = X ^ n + ∑ a : Fin n, C (MvPolynomial.X a) * X ^ a.val := ⟨_, rfl⟩
  have hmon : AAp.Monic := by rw [hAAp]; exact monic_X_pow_add (degree_sum_fin_lt _)
  obtain ⟨DnA, hDnA⟩ : ∃ p : (MvPolynomial (Fin n) O)[X],
    p = Dn.map (algebraMap O (MvPolynomial (Fin n) O)) := ⟨_, rfl⟩
  let ψ : I → MvPolynomial (Fin n) O →+* K := fun τ => MvPolynomial.eval₂Hom (algebraMap O K) (χ τ)
  have hact : ∀ τ (p : MvPolynomial (Fin n) O), ∀ m ∈ Mt τ, φ p m = ψ τ p • m := by
    intro τ p
    induction p using MvPolynomial.induction_on with
    | C r =>
      intro m _
      have h1 : φ (MvPolynomial.C r) = algebraMap O (Module.End O M) r := φ.commutes r
      rw [h1, Module.algebraMap_end_apply]
      simp [ψ]
    | add p q hp hq =>
      intro m hm
      rw [map_add, map_add, LinearMap.add_apply, add_smul, hp m hm, hq m hm]
    | mul_X p a hp =>
      intro m hm
      rw [map_mul, map_mul, hφX, Module.End.mul_apply, hχ τ a m hm, hp _ ((Mt τ).smul_mem _ hm), smul_smul]
      simp [ψ]
  have hRem : ∀ τ, (DnA %ₘ AAp).map (ψ τ) = 0 := by
    intro τ
    rw [map_modByMonic _ hmon, modByMonic_eq_zero_iff_dvd (hmon.map _)]
    have e1 : DnA.map (ψ τ) = Dn.map (algebraMap O K) := by
      rw [hDnA, Polynomial.map_map]
      congr 1
      ext r
      simp [ψ, MvPolynomial.algebraMap_eq]
    have e2 : AAp.map (ψ τ) = X ^ n + ∑ a : Fin n, C (χ τ a) * X ^ a.val := by
      simp [hAAp, ψ, Polynomial.map_sum]
    rw [e1, e2]; exact hdiv τ
  obtain ⟨W0, hW0⟩ : ∃ p : MvPolynomial (Fin n) O, p = algebraMap O _ w := ⟨_, rfl⟩
  have hdivid : DnA.eval W0 = (DnA %ₘ AAp).eval W0 + AAp.eval W0 * (DnA /ₘ AAp).eval W0 := by
    conv_lhs => rw [← modByMonic_add_div DnA AAp]
    rw [eval_add, eval_mul]
  have hD : φ (DnA.eval W0) = algebraMap O (Module.End O M) (Dn.eval w) := by
    rw [hDnA, hW0, eval_map, eval₂_at_apply]; exact φ.commutes _
  have hA : φ (AAp.eval W0) = w ^ n • (1 : Module.End O M) + ∑ a : Fin n, w ^ a.val • c a := by
    have hW : φ W0 = algebraMap O (Module.End O M) w := by rw [hW0]; exact φ.commutes w
    simp only [hAAp, eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C, map_add, map_pow, map_sum,
      map_mul, hφX, hW]
    congr 1
    · rw [← map_pow, Algebra.algebraMap_eq_smul_one]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def]
  refine ⟨φ ((DnA /ₘ AAp).eval W0), hφmem _, ?_⟩
  intro m hm
  refine Submodule.iSup_induction Mt (motive := fun m => Dn.eval w • m =
    (w ^ n • (1 : Module.End O M) + ∑ a : Fin n, w ^ a.val • c a) (φ ((DnA /ₘ AAp).eval W0) m)) hm ?_ ?_ ?_
  · intro τ m hm
    have h0 : φ ((DnA %ₘ AAp).eval W0) m = 0 := by
      rw [hact τ _ m hm, ← eval₂_at_apply, ← eval_map, hRem τ, eval_zero, zero_smul]
    calc Dn.eval w • m = (algebraMap O (Module.End O M) (Dn.eval w)) m := by rw [Module.algebraMap_end_apply]
      _ = φ (DnA.eval W0) m := by rw [hD]
      _ = _ := by rw [hdivid, map_add, map_mul, LinearMap.add_apply, h0, zero_add, Module.End.mul_apply, hA]
  · simp
  · intro x y hx hy
    rw [smul_add, map_add, map_add, hx, hy]

end Formalism.CohomologicalDescent.Symmetrization

open Polynomial

namespace Formalism.CohomologicalDescent.Symmetrization

section B

variable (k : Type*) {R P M : Type*} [CommRing k] [AddCommGroup M] [Module k M] {n : ℕ}

theorem permTensor_apply_comp (σ : Equiv.Perm (Fin n)) (z : Tens R P M n) (g : Fin n → R × P) :
    perm k σ z g = z (g ∘ σ) := rfl

theorem permSecond_apply (σ : Equiv.Perm (Fin n)) (z : Tens R P M n) (g : Fin n → R × P) :
    permY k σ z g = z (fun s => ((g (σ s)).1, (g s).2)) := rfl

theorem permFirst_apply (σ : Equiv.Perm (Fin n)) (z : Tens R P M n) (g : Fin n → R × P) :
    permX k σ z g = z (fun s => ((g s).1, (g (σ s)).2)) := rfl

theorem onModule_apply (T : Module.End k M) (z : Tens R P M n) (g : Fin n → R × P) :
    onM k T z g = T (z g) := rfl

theorem permOnTensor_mul (σ τ : Equiv.Perm (Fin n)) :
    (permY k (σ * τ) : Module.End k (Tens R P M n)) = permY k σ * permY k τ :=
  LinearMap.ext fun _ => funext fun _ => rfl

theorem permSecond_one : (permY k (1 : Equiv.Perm (Fin n)) : Module.End k (Tens R P M n)) = 1 :=
  LinearMap.ext fun _ => funext fun _ => rfl

theorem permTensor_eq_permSecond_mul_permFirst (σ : Equiv.Perm (Fin n)) :
    (perm k σ : Module.End k (Tens R P M n)) = permY k σ * permX k σ :=
  LinearMap.ext fun _ => funext fun _ => rfl

theorem permSecond_commute_onModule (σ : Equiv.Perm (Fin n)) (T : Module.End k M) :
    Commute (permY k σ : Module.End k (Tens R P M n)) (onM k T) :=
  LinearMap.ext fun _ => funext fun _ => rfl

theorem permFirst_commute_onModule (σ : Equiv.Perm (Fin n)) (T : Module.End k M) :
    Commute (permX k σ : Module.End k (Tens R P M n)) (onM k T) :=
  LinearMap.ext fun _ => funext fun _ => rfl

theorem update_first_snd_eq [DecidableEq (Fin n)] (g : Fin n → R × P) (i : Fin n) (b : R) (s : Fin n) :
    (Function.update g i (b, (g i).2) s).2 = (g s).2 := by
  by_cases h : s = i
  · subst h; simp
  · rw [Function.update_of_ne h]

variable [DecidableEq R] [DecidableEq P]

theorem unitOnTensor_apply (j : Fin n) (a b : R) (z : Tens R P M n) (g : Fin n → R × P) :
    unitY k j a b z g = if (g j).1 = a then z (Function.update g j (b, (g j).2)) else 0 := by
  unfold unitY
  rw [LinearMap.pi_apply]
  split_ifs <;> rfl

theorem unitSecond_mul_unitSecond (j : Fin n) (a b c d : R) :
    (unitY k j a b * unitY k j c d : Module.End k (Tens R P M n)) = if b = c then unitY k j a d else 0 := by
  refine LinearMap.ext fun z => funext fun g => ?_
  simp only [Module.End.mul_apply, unitOnTensor_apply, Function.update_self, Function.update_idem]
  by_cases h : b = c
  · simp only [h, if_true, unitOnTensor_apply]
  · simp [h]

theorem unitSecond_commute_of_ne {i j : Fin n} (h : i ≠ j) (a b c d : R) :
    Commute (unitY k i a b : Module.End k (Tens R P M n)) (unitY k j c d) := by
  refine LinearMap.ext fun z => funext fun g => ?_
  simp only [Module.End.mul_apply, unitOnTensor_apply, Function.update_of_ne h, Function.update_of_ne h.symm]
  rw [Function.update_comm h]
  split_ifs <;> rfl

theorem onModule_commute_unitSecond (T : Module.End k M) (j : Fin n) (a b : R) :
    Commute (onM k T : Module.End k (Tens R P M n)) (unitY k j a b) := by
  refine LinearMap.ext fun z => funext fun g => ?_
  simp only [Module.End.mul_apply, unitOnTensor_apply, onModule_apply]
  split_ifs <;> simp

theorem onModule_gl_relations {EM : R → R → Module.End k M} (h : GlRel EM) :
    GlRel (fun a b => (onM k (EM a b) : Module.End k (Tens R P M n))) := by
  intro a b c d
  refine LinearMap.ext fun z => funext fun g => ?_
  have := LinearMap.congr_fun (h a b c d) (z g)
  by_cases h1 : b = c <;> by_cases h2 : d = a <;>
    simpa [h1, h2, onModule_apply, LinearMap.sub_apply, Module.End.mul_apply] using this

theorem permFirst_commute_unitSecond (σ : Equiv.Perm (Fin n)) (i : Fin n) (a b : R) :
    Commute (permX k σ : Module.End k (Tens R P M n)) (unitY k i a b) := by
  refine LinearMap.ext fun z => funext fun g => ?_
  simp only [Module.End.mul_apply, unitOnTensor_apply, permFirst_apply]
  split_ifs with h
  · congr 1
    funext s
    refine Prod.ext ?_ ?_
    · by_cases hs : s = i
      · subst hs; simp
      · simp [Function.update_of_ne hs]
    · by_cases hs : s = i
      · subst hs
        simp only [Function.update_self]
        exact (update_first_snd_eq g s b (σ s)).symm
      · simp only [Function.update_of_ne hs]
        exact (update_first_snd_eq g i b (σ s)).symm
  · rfl

theorem permSecond_mul_unitSecond (σ : Equiv.Perm (Fin n)) (i : Fin n) (a b : R) :
    (permY k σ * unitY k i a b : Module.End k (Tens R P M n)) = unitY k (σ i) a b * permY k σ := by
  refine LinearMap.ext fun z => funext fun g => ?_
  simp only [Module.End.mul_apply, unitOnTensor_apply, permSecond_apply]
  split_ifs with h
  · congr 1
    funext s
    refine Prod.ext ?_ ?_
    · by_cases hs : s = i
      · subst hs; simp
      · have h2 : σ s ≠ σ i := fun e => hs (σ.injective e)
        simp [Function.update_of_ne hs, Function.update_of_ne h2]
    · exact (update_first_snd_eq (fun s => ((g (σ s)).1, (g s).2)) i b s).trans
        (update_first_snd_eq g (σ i) b s).symm
  · rfl

variable [Fintype R]

theorem sum_unitSecond_products_eq_swap {i j : Fin n} (h : i ≠ j) :
    ∑ b, ∑ b', unitY k i b b' * unitY k j b' b = (permY k (Equiv.swap i j) : Module.End k (Tens R P M n)) := by
  refine LinearMap.ext fun z => funext fun g => ?_
  simp only [LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, unitOnTensor_apply,
    permSecond_apply, Function.update_of_ne h.symm]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  funext s
  by_cases hs : s = j
  · subst hs; simp [Equiv.swap_apply_right]
  · by_cases hi : s = i
    · subst hi; simp [Function.update_of_ne hs, Equiv.swap_apply_left]
    · simp [Function.update_of_ne hs, Function.update_of_ne hi, Equiv.swap_apply_of_ne_of_ne hi hs]

def factorGenerator (EM : R → R → Module.End k M) (n : ℕ) : ℕ → R → R → Module.End k (Tens R P M n)
  | 0, a, b => onM k (EM a b)
  | (j + 1), a, b => if h : j < n then unitY k ⟨j, h⟩ a b else 0

theorem glRel_factorGenerator {EM : R → R → Module.End k M} (h : GlRel EM) (j : ℕ) :
    GlRel (factorGenerator k EM n j : R → R → Module.End k (Tens R P M n)) := by
  cases j with
  | zero => exact onModule_gl_relations k h
  | succ j =>
    intro a b c d
    by_cases hj : j < n
    · simp only [factorGenerator, dif_pos hj]
      rw [unitSecond_mul_unitSecond, unitSecond_mul_unitSecond]
    · simp [factorGenerator, hj]

theorem factorGenerator_commute_of_ne (EM : R → R → Module.End k M) (i j : ℕ) (hij : i ≠ j) (a b c d : R) :
    Commute (factorGenerator k EM n i a b : Module.End k (Tens R P M n)) (factorGenerator k EM n j c d) := by
  cases i with
  | zero =>
    cases j with
    | zero => exact absurd rfl hij
    | succ j =>
      simp only [factorGenerator]
      split_ifs
      · exact onModule_commute_unitSecond k _ _ _ _
      · exact Commute.zero_right _
  | succ i =>
    cases j with
    | zero =>
      simp only [factorGenerator]
      split_ifs
      · exact (onModule_commute_unitSecond k _ _ _ _).symm
      · exact Commute.zero_left _
    | succ j =>
      simp only [factorGenerator]
      split_ifs
      · exact unitSecond_commute_of_ne k (fun e => hij (by simpa using congrArg Fin.val e)) _ _ _ _
      · exact Commute.zero_right _
      · exact Commute.zero_left _
      · exact Commute.zero_left _

theorem jucysMurphy_eq_sum_position_products (EM : R → R → Module.End k M) (j : Fin n) :
    (xJM k EM j : Module.End k (Tens R P M n)) =
      ∑ a ∈ Finset.range (j.val + 1), ∑ b, ∑ b', factorGenerator k EM n a b b' * factorGenerator k EM n (j.val + 1) b' b := by
  have h0 : (Om k EM j : Module.End k (Tens R P M n)) =
      ∑ b, ∑ b', factorGenerator k EM n 0 b b' * factorGenerator k EM n (j.val + 1) b' b := by
    simp only [factorGenerator, dif_pos j.2, Fin.eta]
    rw [Om, Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ =>
      (onModule_commute_unitSecond k _ _ _ _).eq.symm
  have hG : ∀ j' : Fin n, j' < j →
      ∑ b, ∑ b', factorGenerator k EM n (j'.val + 1) b b' * factorGenerator k EM n (j.val + 1) b' b =
        (permY k (Equiv.swap j' j) : Module.End k (Tens R P M n)) := by
    intro j' hj'
    simp only [factorGenerator, dif_pos j'.2, dif_pos j.2, Fin.eta]
    exact sum_unitSecond_products_eq_swap k (ne_of_lt hj')
  have h1 : ∑ j' ∈ Finset.univ.filter (· < j), (permY k (Equiv.swap j' j) : Module.End k (Tens R P M n)) =
      ∑ a ∈ Finset.range j.val, ∑ b, ∑ b', factorGenerator k EM n (a + 1) b b' * factorGenerator k EM n (j.val + 1) b' b := by
    refine Finset.sum_nbij (fun j' => j'.val) ?_ ?_ ?_ ?_
    · intro a ha
      exact Finset.mem_range.2 (Fin.lt_def.1 (Finset.mem_filter.1 ha).2)
    · intro a _ b _ hab
      exact Fin.ext hab
    · intro a ha
      have ha' : a < j.val := by simpa using ha
      exact ⟨⟨a, lt_trans ha' j.2⟩,
        Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.lt_def.2 ha'⟩), rfl⟩
    · intro a ha
      exact (hG a (by simpa using ha)).symm
  rw [Finset.sum_range_succ', ← h0, ← h1, xJM]
  exact add_comm _ _

theorem commute_positionGenerator_of_commute (EM : R → R → Module.End k M) (T : Module.End k (Tens R P M n))
    (h0 : ∀ a b, Commute T (onM k (EM a b))) (h1 : ∀ j a b, Commute T (unitY k j a b)) :
    ∀ a b c, Commute T (factorGenerator k EM n a b c)
  | 0, b, c => h0 b c
  | (a + 1), b, c => by
    simp only [factorGenerator]
    split_ifs
    · exact h1 _ _ _
    · exact Commute.zero_right _

theorem commute_jucysMurphy_of_commute (EM : R → R → Module.End k M) (T : Module.End k (Tens R P M n))
    (h0 : ∀ a b, Commute T (onM k (EM a b))) (h1 : ∀ j a b, Commute T (unitY k j a b)) (j : Fin n) :
    Commute T (xJM k EM j) := by
  have hT := commute_positionGenerator_of_commute k EM T h0 h1
  rw [jucysMurphy_eq_sum_position_products]
  exact Commute.sum_right _ _ _ fun a _ => Commute.sum_right _ _ _ fun b _ =>
    Commute.sum_right _ _ _ fun b' _ => (hT _ _ _).mul_right (hT _ _ _)

theorem permSecond_mul_positionCasimir (EM : R → R → Module.End k M) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (permY k σ * Om k EM i : Module.End k (Tens R P M n)) = Om k EM (σ i) * permY k σ := by
  simp only [Om, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  rw [← mul_assoc, permSecond_mul_unitSecond, mul_assoc, (permSecond_commute_onModule k σ _).eq, ← mul_assoc]

theorem permOnTensor_mul_swap (σ : Equiv.Perm (Fin n)) (a b : Fin n) :
    (permY k σ * permY k (Equiv.swap a b) : Module.End k (Tens R P M n)) =
      permY k (Equiv.swap (σ a) (σ b)) * permY k σ := by
  rw [← permOnTensor_mul, ← permOnTensor_mul, Equiv.mul_swap_eq_swap_mul]

theorem permSecond_mul_jucysMurphy (EM : R → R → Module.End k M) (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    (permY k σ * xJM k EM j : Module.End k (Tens R P M n)) =
      (Om k EM (σ j) + ∑ j' ∈ Finset.univ.filter (· < j), permY k (Equiv.swap (σ j') (σ j))) * permY k σ := by
  rw [xJM, mul_add, add_mul, permSecond_mul_positionCasimir, Finset.mul_sum, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun j' _ => permOnTensor_mul_swap k σ j' j

theorem swap_mul_jucysMurphy_eq_sub_one (EM : R → R → Module.End k M) (j : Fin n) (hj : j.val + 1 < n) :
    (permY k (Equiv.swap j ⟨j.val + 1, hj⟩) * xJM k EM j : Module.End k (Tens R P M n)) =
        xJM k EM ⟨j.val + 1, hj⟩ * permY k (Equiv.swap j ⟨j.val + 1, hj⟩) - 1 := by
  have hss : (permY k (Equiv.swap j ⟨j.val + 1, hj⟩) * permY k (Equiv.swap j ⟨j.val + 1, hj⟩) :
      Module.End k (Tens R P M n)) = 1 := by
    rw [← permOnTensor_mul, Equiv.swap_mul_self, permSecond_one]
  have hfil : (Finset.univ.filter (· < (⟨j.val + 1, hj⟩ : Fin n))) = insert j (Finset.univ.filter (· < j)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.lt_def, Fin.ext_iff]
    omega
  have hsum : ∑ j' ∈ Finset.univ.filter (· < j),
      (permY k (Equiv.swap (Equiv.swap j ⟨j.val + 1, hj⟩ j') (Equiv.swap j ⟨j.val + 1, hj⟩ j)) :
        Module.End k (Tens R P M n)) =
      ∑ j' ∈ Finset.univ.filter (· < j), permY k (Equiv.swap j' ⟨j.val + 1, hj⟩) := by
    refine Finset.sum_congr rfl fun j' hj' => ?_
    have h1 : j'.val < j.val := Fin.lt_def.1 (Finset.mem_filter.1 hj').2
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne]
    · intro e; rw [e] at h1; exact lt_irrefl _ h1
    · intro e; rw [e] at h1; simp at h1
  rw [permSecond_mul_jucysMurphy, hsum, Equiv.swap_apply_left, xJM, hfil, Finset.sum_insert (by simp)]
  rw [add_mul, add_mul, add_mul, hss]
  abel

theorem swap_adjacent_commute_jucysMurphy_far (EM : R → R → Module.End k M) (j : Fin n) (hj : j.val + 1 < n) (l : Fin n)
    (h1 : l ≠ j) (h2 : l ≠ ⟨j.val + 1, hj⟩) :
    Commute (permY k (Equiv.swap j ⟨j.val + 1, hj⟩) : Module.End k (Tens R P M n)) (xJM k EM l) := by
  have h1' : l.val ≠ j.val := fun e => h1 (Fin.ext e)
  have h2' : l.val ≠ j.val + 1 := fun e => h2 (Fin.ext e)
  show _ * _ = _ * _
  rw [permSecond_mul_jucysMurphy, Equiv.swap_apply_of_ne_of_ne h1 h2, xJM]
  congr 2
  refine Finset.sum_equiv (Equiv.swap j ⟨j.val + 1, hj⟩) ?_ (fun _ _ => rfl)
  intro a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
  by_cases ha : a = j
  · subst ha; rw [Equiv.swap_apply_left]; simp only; omega
  · by_cases hb : a = ⟨j.val + 1, hj⟩
    · subst hb; rw [Equiv.swap_apply_right]; simp only; omega
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

theorem commute_C_jucysMurphyPoly (EM : R → R → Module.End k M) (T : Module.End k (Tens R P M n))
    (h : ∀ j, Commute T (xJM k EM j)) : Commute (C T) (AApoly k EM n) := by
  unfold AApoly
  refine Commute.list_prod_right _ _ fun x hx => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  exact ((Polynomial.commute_X _).symm).sub_right ((h i).map C)

noncomputable def evalAtCentral (t : k) : (Module.End k (Tens R P M n))[X] →+* Module.End k (Tens R P M n) :=
  Polynomial.eval₂RingHom' (RingHom.id _) (t • 1) (fun a => by
    show a * (t • (1 : Module.End k (Tens R P M n))) = (t • (1 : Module.End k (Tens R P M n))) * a
    simp)

theorem eval_jucysMurphyPoly_eq_product (EM : R → R → Module.End k M) (t : k) :
    evalAtCentral k t (AApoly k EM n) = (AA k EM n t : Module.End k (Tens R P M n)) := by
  unfold AApoly AA
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext j
  simp [evalAtCentral]

theorem evalAtCentral_C (t : k) (T : Module.End k (Tens R P M n)) : evalAtCentral k t (C T) = T := by
  simp [evalAtCentral]

end B

theorem hecke_relations_hold : HeckeRel := by
  intro k R P M _ _ _ _ _ _ EM n j hj
  exact ⟨swap_mul_jucysMurphy_eq_sub_one k EM j hj, fun l h1 h2 => swap_adjacent_commute_jucysMurphy_far k EM j hj l h1 h2⟩

theorem XComm_of (h : JMCommAbstract) : XComm := by
  intro k R P M _ _ _ _ _ _ EM hEM n i j
  rw [jucysMurphy_eq_sum_position_products, jucysMurphy_eq_sum_position_products]
  exact (h (Module.End k (Tens R P M n)) R (factorGenerator k EM n) (glRel_factorGenerator k hEM)
    (factorGenerator_commute_of_ne k EM)).1 (i.val + 1) (j.val + 1)

theorem commute_C_permSecond_jucysMurphyPoly (h1 : SymCommAbstract) (h2 : JMCommAbstract) (k R P M : Type) [CommRing k] [AddCommGroup M]
    [Module k M] [DecidableEq R] [DecidableEq P] [Fintype R] (EM : R → R → Module.End k M) (hEM : GlRel EM)
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Commute (C (permY k σ)) (AApoly k EM n : (Module.End k (Tens R P M n))[X]) := by
  cases n with
  | zero =>
    have : σ = 1 := Subsingleton.elim _ _
    subst this
    rw [permSecond_one, C_1]
    exact Commute.one_left _
  | succ m =>
    induction σ using Submonoid.dense_induction (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ)
      (Equiv.Perm.mclosure_swap_castSucc_succ m) with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have hj : i.castSucc.val + 1 < m + 1 := by simp
      have hs : i.succ = ⟨i.castSucc.val + 1, hj⟩ := Fin.ext (by simp)
      show Commute (C (permY k (Equiv.swap i.castSucc i.succ))) _
      rw [hs]
      exact h1 _ (m + 1) (xJM k EM) _ i.castSucc hj (XComm_of h2 k R P M EM hEM (m + 1))
        (by rw [← permOnTensor_mul, Equiv.swap_mul_self, permSecond_one])
        (swap_mul_jucysMurphy_eq_sub_one k EM _ hj) (fun l a b => swap_adjacent_commute_jucysMurphy_far k EM _ hj l a b)
    | one =>
      rw [permSecond_one, C_1]
      exact Commute.one_left _
    | mul x y hx hy =>
      rw [permOnTensor_mul, C_mul]
      exact hx.mul_left hy

theorem AAComm_of (h1 : SymCommAbstract) (h2 : JMCommAbstract) : AAComm := by
  intro k R P M _ _ _ _ _ _ EM hEM n σ
  have hY := commute_C_permSecond_jucysMurphyPoly h1 h2 k R P M EM hEM n σ
  have hX : Commute (C (permX k σ)) (AApoly k EM n : (Module.End k (Tens R P M n))[X]) :=
    commute_C_jucysMurphyPoly k EM _ (commute_jucysMurphy_of_commute k EM _ (fun a b => permFirst_commute_onModule k σ _)
      (fun j a b => permFirst_commute_unitSecond k σ j a b))
  have hP : Commute (C (perm k σ)) (AApoly k EM n : (Module.End k (Tens R P M n))[X]) := by
    rw [permTensor_eq_permSecond_mul_permFirst, C_mul]
    exact hY.mul_left hX
  refine ⟨hY, hP, fun t => ⟨?_, ?_⟩⟩
  · have := hY.map (evalAtCentral k t)
    rwa [evalAtCentral_C, eval_jucysMurphyPoly_eq_product] at this
  · have := hP.map (evalAtCentral k t)
    rwa [evalAtCentral_C, eval_jucysMurphyPoly_eq_product] at this

end Formalism.CohomologicalDescent.Symmetrization

open Polynomial

namespace Formalism.CohomologicalDescent.Symmetrization

section Ops

variable (k : Type*) {R P M : Type*} [CommRing k] [AddCommGroup M] [Module k M] {n : ℕ}

theorem perm_tensor_apply (σ : Equiv.Perm (Fin n)) (z : Tens R P M n) (g : Fin n → R × P) :
    perm k σ z g = z (g ∘ σ) := rfl

theorem permSecond_apply_comp (σ : Equiv.Perm (Fin n)) (z : Tens R P M n) (g : Fin n → R × P) :
    permY k σ z g = z (fun s => ((g (σ s)).1, (g s).2)) := rfl

theorem contract_apply_insertNth (j : Fin (n + 1)) (v : R × P) (z : Tens R P M (n + 1)) (g : Fin n → R × P) :
    contr k j v z g = z (j.insertNth v g) := rfl

theorem contract_zero_apply_cons (v : R × P) (z : Tens R P M (n + 1)) (g : Fin n → R × P) :
    contr k 0 v z g = z (Fin.cons v g) := by
  rw [contract_apply_insertNth, Fin.insertNth_zero']

theorem onModule_apply_eval (T : Module.End k M) (z : Tens R P M n) (g : Fin n → R × P) :
    onM k T z g = T (z g) := rfl

variable [DecidableEq R] [DecidableEq P]

theorem unitSecond_apply_formula (j : Fin n) (a b : R) (z : Tens R P M n) (g : Fin n → R × P) :
    unitY k j a b z g = if (g j).1 = a then z (Function.update g j (b, (g j).2)) else 0 := by
  unfold unitY
  rw [LinearMap.pi_apply]
  split_ifs <;> rfl

theorem unitFirst_apply_formula (j : Fin n) (a b : P) (z : Tens R P M n) (g : Fin n → R × P) :
    unitX k j a b z g = if (g j).2 = a then z (Function.update g j ((g j).1, b)) else 0 := by
  unfold unitX
  rw [LinearMap.pi_apply]
  split_ifs <;> rfl

theorem mixedCasimir_apply_sum [Fintype R] (EM : R → R → Module.End k M) (j : Fin n) (z : Tens R P M n)
    (g : Fin n → R × P) :
    Om k EM j z g = ∑ b', EM b' (g j).1 (z (Function.update g j (b', (g j).2))) := by
  unfold Om
  simp only [LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, unitSecond_apply_formula,
    onModule_apply_eval]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [Finset.sum_ite_eq]
  simp

theorem swap_insertNth_eq_update (s : Fin (n + 1)) (t : Fin n) (v : R × P) (g : Fin n → R × P) :
    (fun x => (((s.insertNth v g : Fin (n + 1) → R × P) (Equiv.swap (s.succAbove t) s x)).1,
      ((s.insertNth v g : Fin (n + 1) → R × P) x).2)) =
      (s.insertNth ((g t).1, v.2) (Function.update g t (v.1, (g t).2)) : Fin (n + 1) → R × P) := by
  funext x
  rcases Fin.eq_self_or_eq_succAbove s x with h | ⟨y, h⟩
  · rw [h]
    simp
  · rw [h]
    by_cases hy : y = t
    · rw [hy]
      simp
    · have h1 : s.succAbove y ≠ s.succAbove t := fun e => hy (Fin.succAbove_right_injective e)
      have h2 : s.succAbove y ≠ s := Fin.succAbove_ne s y
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      simp [hy]

theorem apply_insertNth_eq_of_perm_invariant (z : Tens R P M (n + 1)) (hz : ∀ σ, perm k σ z = z) (j j' : Fin (n + 1))
    (x : R × P) (g : Fin n → R × P) : z (j.insertNth x g) = z (j'.insertNth x g) := by
  have h : (j'.insertNth x g : Fin (n + 1) → R × P) ∘
      ((finSuccEquiv' j).trans (finSuccEquiv' j').symm) = j.insertNth x g := by
    funext s
    rcases Fin.eq_self_or_eq_succAbove j s with h | ⟨t, h⟩
    · rw [h]; simp
    · rw [h]; simp
  have h2 := congrFun (hz ((finSuccEquiv' j).trans (finSuccEquiv' j').symm)) (j'.insertNth x g)
  rw [perm_tensor_apply, h] at h2
  exact h2

end Ops

theorem sum_pairs_split_first_index {G : Type*} [AddCommGroup G] (n : ℕ) (A : Fin (n + 1) → G)
    (B : Fin (n + 1) → Fin (n + 1) → G) :
    ∑ j, A j - ∑ j, ∑ l ∈ Finset.univ.filter (j < ·), B j l =
      (A 0 - ∑ t : Fin n, B 0 t.succ) +
        (∑ j : Fin n, A j.succ - ∑ j : Fin n, ∑ l ∈ Finset.univ.filter (j < ·), B j.succ l.succ) := by
  simp only [Finset.sum_filter, Fin.sum_univ_succ, Fin.succ_lt_succ_iff, Fin.succ_pos,
    if_true, if_false, Fin.not_lt_zero, zero_add]
  abel

theorem sum_ordered_pairs_eq_sum_succAbove {G : Type*} [AddCommGroup G] (n : ℕ) (φ : Fin (n + 1) → Fin (n + 1) → G) :
    ∑ j, ∑ l ∈ Finset.univ.filter (j < ·), (φ j l + φ l j) = ∑ s, ∑ t : Fin n, φ s (s.succAbove t) := by
  have h1 : ∀ s, ∑ t : Fin n, φ s (s.succAbove t) =
      ∑ t', (if s < t' then φ s t' else 0) + ∑ t', (if t' < s then φ s t' else 0) := by
    intro s
    rw [← Finset.sum_add_distrib, Fin.sum_univ_succAbove _ s]
    simp only [lt_self_iff_false, if_false, add_zero, zero_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases lt_or_gt_of_ne (Fin.succAbove_ne s t) with h | h
    · simp [h, not_lt_of_gt h]
    · simp [h, not_lt_of_gt h]
  simp_rw [h1, Finset.sum_add_distrib, Finset.sum_filter]
  congr 1
  rw [Finset.sum_comm]

theorem list_prod_map_eq_of_perm_pairwise_commute {A ι : Type*} [Monoid A] (φ : ι → A) (hφ : ∀ a b, Commute (φ a) (φ b))
    {l₁ l₂ : List ι} (h : l₁.Perm l₂) : (l₁.map φ).prod = (l₂.map φ).prod :=
  (h.map φ).prod_eq' (List.pairwise_of_forall_mem_list (fun a ha b hb => by
    obtain ⟨x, _, rfl⟩ := List.mem_map.1 ha
    obtain ⟨y, _, rfl⟩ := List.mem_map.1 hb
    exact hφ x y))

theorem content_toList_perm_ofFn {ι : Type*} {n : ℕ} (g : Fin n → ι) : (cont g).1.toList.Perm (List.ofFn g) := by
  rw [← Multiset.coe_eq_coe, Multiset.coe_toList]
  simp [cont]

theorem content_comp_perm {ι : Type*} {n : ℕ} (g : Fin n → ι) (σ : Equiv.Perm (Fin n)) :
    cont (g ∘ σ) = cont g := by
  apply Subtype.ext
  simp only [cont]
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv]

section Set1

variable {k V P R : Type*} [CommRing k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
  (S : HidaSetting k V P R)

theorem lowering_operators_commute_pair (u v : R × P) : S.f u * S.f v = S.f v * S.f u := by
  have h := S.comm (Sum.inr u.1) (Sum.inl u.2) (Sum.inr v.1) (Sum.inl v.2)
  simp only [reduceCtorEq, if_false, sub_zero] at h
  exact sub_eq_zero.mp h

theorem raising_operators_commute (u v : R × P) : S.e u * S.e v = S.e v * S.e u := by
  have h := S.comm (Sum.inl u.2) (Sum.inr u.1) (Sum.inl v.2) (Sum.inr v.1)
  simp only [reduceCtorEq, if_false, sub_zero] at h
  exact sub_eq_zero.mp h

theorem raising_lowering_commutator (v0 v : R × P) (x : V) : S.e v0 (S.f v x) = S.f v (S.e v0 x) +
    ((if v0.1 = v.1 then S.E (Sum.inl v0.2) (Sum.inl v.2) x else 0) -
      (if v.2 = v0.2 then S.E (Sum.inr v.1) (Sum.inr v0.1) x else 0)) := by
  have h := S.comm (Sum.inl v0.2) (Sum.inr v0.1) (Sum.inr v.1) (Sum.inl v.2)
  simp only [Sum.inr.injEq, Sum.inl.injEq] at h
  have h2 := congrArg (fun T : Module.End k V => T x) h
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h2
  have h3 : S.e v0 (S.f v x) = S.f v (S.e v0 x) + (S.e v0 (S.f v x) - S.f v (S.e v0 x)) := by abel
  rw [h3]
  congr 1
  unfold HidaSetting.e HidaSetting.f
  rw [h2]
  split_ifs <;> simp

theorem diagSecond_lowering_commutator (c d : R) (v : R × P) (x : V) : S.E (Sum.inr c) (Sum.inr d) (S.f v x) =
    S.f v (S.E (Sum.inr c) (Sum.inr d) x) + (if d = v.1 then S.f (c, v.2) x else 0) := by
  have h := S.comm (Sum.inr c) (Sum.inr d) (Sum.inr v.1) (Sum.inl v.2)
  simp only [Sum.inr.injEq, reduceCtorEq, if_false, sub_zero] at h
  have h2 := congrArg (fun T : Module.End k V => T x) h
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h2
  have h3 : S.E (Sum.inr c) (Sum.inr d) (S.f v x) = S.f v (S.E (Sum.inr c) (Sum.inr d) x) +
    (S.E (Sum.inr c) (Sum.inr d) (S.f v x) - S.f v (S.E (Sum.inr c) (Sum.inr d) x)) := by abel
  rw [h3]
  congr 1
  unfold HidaSetting.f
  rw [h2]
  split_ifs <;> simp

theorem diagFirst_lowering_commutator (α β : P) (v : R × P) (x : V) : S.E (Sum.inl α) (Sum.inl β) (S.f v x) =
    S.f v (S.E (Sum.inl α) (Sum.inl β) x) - (if v.2 = α then S.f (v.1, β) x else 0) := by
  have h := S.comm (Sum.inl α) (Sum.inl β) (Sum.inr v.1) (Sum.inl v.2)
  simp only [Sum.inl.injEq, reduceCtorEq, if_false, zero_sub] at h
  have h2 := congrArg (fun T : Module.End k V => T x) h
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h2
  have h3 : S.E (Sum.inl α) (Sum.inl β) (S.f v x) = S.f v (S.E (Sum.inl α) (Sum.inl β) x) +
    (S.E (Sum.inl α) (Sum.inl β) (S.f v x) - S.f v (S.E (Sum.inl α) (Sum.inl β) x)) := by abel
  have h4 : S.E (Sum.inl α) (Sum.inl β) (S.f v x) - S.f v (S.E (Sum.inl α) (Sum.inl β) x) =
      -(if v.2 = α then S.f (v.1, β) x else 0) := by
    unfold HidaSetting.f
    rw [h2]
    split_ifs <;> simp
  rw [h3, h4, sub_eq_add_neg]

theorem wordProduct_cons {n : ℕ} (v : R × P) (g : Fin n → R × P) :
    S.Fw (Fin.cons v g : Fin (n + 1) → R × P) = S.f v * S.Fw g := by
  simp [HidaSetting.Fw, List.ofFn_succ]

theorem wordProduct_insertNth : ∀ (n : ℕ) (j : Fin (n + 1)) (v : R × P) (g : Fin n → R × P),
    S.Fw (j.insertNth v g : Fin (n + 1) → R × P) = S.f v * S.Fw g := by
  intro n
  induction n with
  | zero =>
    intro j v g
    refine Fin.cases ?_ (fun i => i.elim0) j
    rw [Fin.insertNth_zero', wordProduct_cons]
  | succ n ih =>
    intro j v g
    refine Fin.cases ?_ (fun i => ?_) j
    · rw [Fin.insertNth_zero', wordProduct_cons]
    · obtain ⟨a, p, rfl⟩ : ∃ a p, g = Fin.cons a p := ⟨g 0, Fin.tail g, (Fin.cons_self_tail g).symm⟩
      rw [Fin.insertNth_succ_cons, wordProduct_cons, ih, wordProduct_cons, ← mul_assoc, ← mul_assoc,
        lowering_operators_commute_pair]

theorem word_products_of_content {n : ℕ} (g : Fin n → R × P) : S.Fs (cont g) = S.Fw g ∧ S.Es (cont g) = S.Ew g := by
  constructor
  · unfold HidaSetting.Fs HidaSetting.Fw
    rw [list_prod_map_eq_of_perm_pairwise_commute S.f (fun a b => lowering_operators_commute_pair S a b) (content_toList_perm_ofFn g), List.map_ofFn]
    rfl
  · unfold HidaSetting.Es HidaSetting.Ew
    rw [list_prod_map_eq_of_perm_pairwise_commute S.e (fun a b => raising_operators_commute S a b) (content_toList_perm_ofFn g), List.map_ofFn]
    rfl

theorem wordProduct_comp_perm {n : ℕ} (g : Fin n → R × P) (σ : Equiv.Perm (Fin n)) : S.Fw (g ∘ σ) = S.Fw g := by
  rw [← (word_products_of_content S g).1, ← (word_products_of_content S (g ∘ σ)).1, content_comp_perm]

variable [Fintype P] [Fintype R]

theorem symMap_apply_sum_words (n : ℕ) (z : Tens R P S.W n) : S.mu n z = ∑ g, S.Fw g (z g : V) := by
  simp [HidaSetting.mu, LinearMap.sum_apply]

theorem symMap_zero_eq_default (z : Tens R P S.W 0) : S.mu 0 z = (z default : V) := by
  rw [symMap_apply_sum_words, Fintype.sum_unique]
  simp [HidaSetting.Fw]

theorem symMap_succ_eq_sum_contract (n : ℕ) (j : Fin (n + 1)) (z : Tens R P S.W (n + 1)) :
    S.mu (n + 1) z = ∑ v, S.f v (S.mu n (contr k j v z)) := by
  simp only [symMap_apply_sum_words, map_sum, contract_apply_insertNth]
  rw [← (Fin.insertNthEquiv (fun _ => R × P) j).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun g _ => ?_
  have h : (Fin.insertNthEquiv (fun _ => R × P) j) (v, g) = j.insertNth v g := rfl
  rw [h, wordProduct_insertNth]
  rfl

theorem symMap_perm_invariant (n : ℕ) (σ : Equiv.Perm (Fin n)) (z : Tens R P S.W n) :
    S.mu n (perm k σ z) = S.mu n z := by
  simp only [symMap_apply_sum_words, perm_tensor_apply]
  rw [← (Equiv.arrowCongr σ (Equiv.refl (R × P))).sum_comp]
  refine Finset.sum_congr rfl fun g _ => ?_
  have h : (Equiv.arrowCongr σ (Equiv.refl (R × P))) g = g ∘ σ.symm := rfl
  have h2 : (g ∘ σ.symm) ∘ σ = g := by
    funext s
    simp
  rw [h, wordProduct_comp_perm, h2]

end Set1

section Set2

variable {k V P R : Type*} [CommRing k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
  [Fintype P] [Fintype R] (S : HidaSetting k V P R)

theorem contract_zero_diagSecond (n : ℕ) (c d : R) (v : R × P) (z : Tens R P S.W (n + 1)) :
    contr k 0 v (diagY k S.EW c d z) =
      diagY k S.EW c d (contr k 0 v z) + (if v.1 = c then contr k 0 (d, v.2) z else 0) := by
  funext g
  simp only [contract_zero_apply_cons, diagY, LinearMap.add_apply, Pi.add_apply, LinearMap.sum_apply,
    Finset.sum_apply, onModule_apply_eval, unitSecond_apply_formula, Fin.sum_univ_succ, Fin.cons_zero,
    Fin.cons_succ, Fin.update_cons_zero, ← Fin.cons_update]
  by_cases hc : v.1 = c
  · simp only [hc, if_true, contract_zero_apply_cons]
    abel
  · simp only [hc, if_false, Pi.zero_apply]
    abel

theorem contract_zero_diagFirst (n : ℕ) (w : k) (α β : P) (v : R × P) (z : Tens R P S.W (n + 1)) :
    contr k 0 v (diagX k w α β z) =
      diagX k w α β (contr k 0 v z) - (if v.2 = β then contr k 0 (v.1, α) z else 0) := by
  funext g
  simp only [contract_zero_apply_cons, diagX, LinearMap.sub_apply, Pi.sub_apply, LinearMap.sum_apply,
    LinearMap.add_apply, Pi.add_apply, Finset.sum_apply, unitFirst_apply_formula, Fin.sum_univ_succ, Fin.cons_zero,
    Fin.cons_succ, Fin.update_cons_zero, ← Fin.cons_update]
  have h1 : ((if α = β then w • (1 : Module.End k (Tens R P S.W (n + 1))) else 0) z) (Fin.cons v g) =
      ((if α = β then w • (1 : Module.End k (Tens R P S.W n)) else 0) (contr k 0 v z)) g := by
    split_ifs
    · simp [contract_zero_apply_cons]
    · simp
  rw [h1]
  by_cases hc : v.2 = β
  · simp only [hc, if_true, contract_zero_apply_cons]
    abel
  · simp only [hc, if_false, Pi.zero_apply]
    abel

theorem symMap_diagSecond_intertwines : ∀ (n : ℕ) (c d : R) (z : Tens R P S.W n),
    S.E (Sum.inr c) (Sum.inr d) (S.mu n z) = S.mu n (diagY k S.EW c d z) := by
  intro n
  induction n with
  | zero =>
    intro c d z
    rw [symMap_zero_eq_default, symMap_zero_eq_default]
    simp [diagY, onModule_apply_eval, HidaSetting.EW]
  | succ n ih =>
    intro c d z
    rw [symMap_succ_eq_sum_contract S n 0 z, symMap_succ_eq_sum_contract S n 0 (diagY k S.EW c d z), map_sum]
    have hv : ∀ v : R × P, S.f v (S.mu n (contr k 0 v (diagY k S.EW c d z))) =
        S.f v (S.mu n (diagY k S.EW c d (contr k 0 v z))) +
          (if v.1 = c then S.f v (S.mu n (contr k 0 (d, v.2) z)) else 0) := by
      intro v
      rw [contract_zero_diagSecond]
      split_ifs <;> simp
    simp_rw [diagSecond_lowering_commutator, ih, hv, Finset.sum_add_distrib]
    congr 1
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm,
      Finset.sum_comm (f := fun (x : R) (y : P) => if (x, y).1 = c then _ else _)]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp

theorem symMap_diagFirst_intertwines : ∀ (n : ℕ) (α β : P) (z : Tens R P S.W n),
    S.E (Sum.inl α) (Sum.inl β) (S.mu n z) = S.mu n (diagX k S.w α β z) := by
  intro n
  induction n with
  | zero =>
    intro α β z
    rw [symMap_zero_eq_default, symMap_zero_eq_default, S.scal α β _ (z default).2]
    by_cases h : α = β <;> simp [diagX, h]
  | succ n ih =>
    intro α β z
    rw [symMap_succ_eq_sum_contract S n 0 z, symMap_succ_eq_sum_contract S n 0 (diagX k S.w α β z), map_sum]
    have hv : ∀ v : R × P, S.f v (S.mu n (contr k 0 v (diagX k S.w α β z))) =
        S.f v (S.mu n (diagX k S.w α β (contr k 0 v z))) -
          (if v.2 = β then S.f v (S.mu n (contr k 0 (v.1, α) z)) else 0) := by
      intro v
      rw [contract_zero_diagFirst]
      split_ifs <;> simp
    simp_rw [diagFirst_lowering_commutator, ih, hv, Finset.sum_sub_distrib]
    congr 1
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp

end Set2

section Set3

variable {k V P R : Type*} [CommRing k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
  [Fintype P] [Fintype R] (S : HidaSetting k V P R)

def leviRemainder (n : ℕ) (v0 : R × P) (z : Tens R P S.W (n + 1)) : Tens R P S.W n :=
  ∑ β, diagX k S.w v0.2 β (contr k 0 (v0.1, β) z) - ∑ b, diagY k S.EW b v0.1 (contr k 0 (b, v0.2) z)

theorem raising_symMap_succ_eq (n : ℕ) (v0 : R × P) (z : Tens R P S.W (n + 1)) :
    S.e v0 (S.mu (n + 1) z) =
      ∑ v, S.f v (S.e v0 (S.mu n (contr k 0 v z))) + S.mu n (leviRemainder S n v0 z) := by
  rw [symMap_succ_eq_sum_contract S n 0 z, map_sum]
  simp_rw [raising_lowering_commutator, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  congr 1
  unfold leviRemainder
  rw [map_sub, map_sum, map_sum]
  congr 1
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp [symMap_diagFirst_intertwines]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [symMap_diagSecond_intertwines]

def raisingRemainder (n : ℕ) (v : R × P) (z : Tens R P S.W (n + 1)) : Tens R P S.W n :=
  ∑ j, contr k j v (S.w • z - Om k S.EW j z) -
    ∑ j, ∑ l ∈ Finset.univ.filter (j < ·),
      (contr k j v (permY k (Equiv.swap j l) z) + contr k l v (permY k (Equiv.swap j l) z))

def firstPositionRemainder (n : ℕ) (v : R × P) (z : Tens R P S.W (n + 1)) : Tens R P S.W n :=
  contr k 0 v (S.w • z - Om k S.EW 0 z) -
    ∑ t : Fin n, (contr k 0 v (permY k (Equiv.swap 0 t.succ) z) +
      contr k t.succ v (permY k (Equiv.swap 0 t.succ) z))

def tailRemainder (n : ℕ) (v : R × P) (z : Tens R P S.W (n + 1)) : Tens R P S.W n :=
  ∑ j : Fin n, contr k j.succ v (S.w • z - Om k S.EW j.succ z) -
    ∑ j : Fin n, ∑ l ∈ Finset.univ.filter (j < ·),
      (contr k j.succ v (permY k (Equiv.swap j.succ l.succ) z) +
        contr k l.succ v (permY k (Equiv.swap j.succ l.succ) z))

theorem raisingRemainder_eq_first_add_tail (n : ℕ) (v : R × P) (z : Tens R P S.W (n + 1)) :
    raisingRemainder S n v z = firstPositionRemainder S n v z + tailRemainder S n v z :=
  sum_pairs_split_first_index n (fun j => contr k j v (S.w • z - Om k S.EW j z))
    (fun j l => contr k j v (permY k (Equiv.swap j l) z) + contr k l v (permY k (Equiv.swap j l) z))

def flippedLetterTerm (n : ℕ) (v0 : R × P) (z : Tens R P S.W (n + 1)) (t : Fin n) : Tens R P S.W n :=
  fun g => z (Fin.cons (v0.1, (g t).2) (Function.update g t ((g t).1, v0.2)))

theorem contract_zero_swap_succ_apply (n : ℕ) (v0 : R × P) (z : Tens R P S.W (n + 1)) (t : Fin n) (g : Fin n → R × P) :
    contr k 0 v0 (permY k (Equiv.swap 0 t.succ) z) g =
      z (Fin.cons ((g t).1, v0.2) (Function.update g t (v0.1, (g t).2))) := by
  rw [contract_apply_insertNth, permSecond_apply_comp, Equiv.swap_comm]
  have h := swap_insertNth_eq_update (0 : Fin (n + 1)) t v0 g
  rw [Fin.zero_succAbove] at h
  rw [h, Fin.insertNth_zero']

theorem contraction_remainder_eq (n : ℕ) (v0 : R × P) (z : Tens R P S.W (n + 1)) :
    leviRemainder S n v0 z = contr k 0 v0 (S.w • z - Om k S.EW 0 z) - ∑ t : Fin n, flippedLetterTerm S n v0 z t -
      ∑ t : Fin n, contr k 0 v0 (permY k (Equiv.swap 0 t.succ) z) := by
  funext g
  have hX : ∀ β : P, (diagX k S.w v0.2 β (contr k 0 (v0.1, β) z)) g =
      (if v0.2 = β then S.w • z (Fin.cons (v0.1, β) g) else 0) -
        ∑ j, (if (g j).2 = β then z (Fin.cons (v0.1, β) (Function.update g j ((g j).1, v0.2))) else 0) := by
    intro β
    simp only [diagX, LinearMap.sub_apply, Pi.sub_apply, LinearMap.sum_apply, Finset.sum_apply,
      unitFirst_apply_formula, contract_zero_apply_cons]
    congr 1
    split_ifs
    · simp [contract_zero_apply_cons]
    · simp
  have hY : ∀ b : R, (diagY k S.EW b v0.1 (contr k 0 (b, v0.2) z)) g =
      S.EW b v0.1 (z (Fin.cons (b, v0.2) g)) +
        ∑ j, (if (g j).1 = b then z (Fin.cons (b, v0.2) (Function.update g j (v0.1, (g j).2))) else 0) := by
    intro b
    simp only [diagY, LinearMap.add_apply, Pi.add_apply, LinearMap.sum_apply, Finset.sum_apply,
      unitSecond_apply_formula, contract_zero_apply_cons, onModule_apply_eval]
  simp only [leviRemainder, Pi.sub_apply, Finset.sum_apply, hX, hY, contract_zero_swap_succ_apply, flippedLetterTerm]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, contract_zero_apply_cons, Pi.smul_apply,
    Pi.sub_apply, mixedCasimir_apply_sum, Fin.cons_zero, Fin.update_cons_zero]
  rw [Finset.sum_comm (s := (Finset.univ : Finset P)), Finset.sum_comm (s := (Finset.univ : Finset R))]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  abel

theorem symMap_swap_contraction_eq (m : ℕ) (v0 : R × P) (z : Tens R P S.W (m + 2)) (t : Fin (m + 1)) :
    S.mu (m + 1) (flippedLetterTerm S (m + 1) v0 z t) =
      S.mu (m + 1) (contr k t.succ v0 (permY k (Equiv.swap 0 t.succ) z)) := by
  rw [symMap_succ_eq_sum_contract S m t, symMap_succ_eq_sum_contract S m 0]
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 2
  funext g
  rw [contract_apply_insertNth, contract_zero_apply_cons, contract_apply_insertNth, permSecond_apply_comp]
  have h := swap_insertNth_eq_update t.succ (0 : Fin (m + 1)) v0 (Fin.cons v g)
  rw [Fin.succ_succAbove_zero] at h
  rw [h]
  simp only [flippedLetterTerm, Fin.insertNth_apply_same, Fin.update_insertNth, Fin.cons_zero,
    Fin.update_cons_zero, Fin.insertNth_succ_cons]

theorem symMap_firstPositionRemainder_eq (n : ℕ) (v0 : R × P) (z : Tens R P S.W (n + 1)) :
    S.mu n (firstPositionRemainder S n v0 z) = S.mu n (leviRemainder S n v0 z) := by
  rw [contraction_remainder_eq]
  unfold firstPositionRemainder
  simp only [map_sub, map_sum, map_add, Finset.sum_add_distrib]
  have h : ∀ t : Fin n, S.mu n (flippedLetterTerm S n v0 z t) =
      S.mu n (contr k t.succ v0 (permY k (Equiv.swap 0 t.succ) z)) := by
    cases n with
    | zero => intro t; exact t.elim0
    | succ m => intro t; exact symMap_swap_contraction_eq S m v0 z t
  simp_rw [h]
  abel

theorem contract_zero_contract_succ_comm (m : ℕ) (j : Fin (m + 1)) (v v0 : R × P) (z : Tens R P S.W (m + 2)) :
    contr k 0 v (contr k j.succ v0 z) = contr k j v0 (contr k 0 v z) := by
  funext g
  rw [contract_zero_apply_cons, contract_apply_insertNth, contract_apply_insertNth, contract_zero_apply_cons,
    Fin.insertNth_succ_cons]

theorem contract_zero_positionCasimir_succ (m : ℕ) (j : Fin m) (v : R × P) (z : Tens R P S.W (m + 1)) :
    contr k 0 v (Om k S.EW j.succ z) = Om k S.EW j (contr k 0 v z) := by
  funext g
  simp only [contract_zero_apply_cons, mixedCasimir_apply_sum, Fin.cons_succ, ← Fin.cons_update]

theorem contract_zero_permSecond_swap_succ (m : ℕ) (j l : Fin m) (v : R × P) (z : Tens R P S.W (m + 1)) :
    contr k 0 v (permY k (Equiv.swap j.succ l.succ) z) = permY k (Equiv.swap j l) (contr k 0 v z) := by
  funext g
  rw [contract_zero_apply_cons, permSecond_apply_comp, permSecond_apply_comp, contract_zero_apply_cons]
  congr 1
  funext s
  refine Fin.cases ?_ (fun t => ?_) s
  · rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero j).symm (Fin.succ_ne_zero l).symm]
    simp
  · rw [(Fin.succ_injective m).swap_apply]
    simp

theorem contract_zero_tailRemainder (m : ℕ) (v v0 : R × P) (z : Tens R P S.W (m + 2)) :
    contr k 0 v (tailRemainder S (m + 1) v0 z) = raisingRemainder S m v0 (contr k 0 v z) := by
  unfold tailRemainder raisingRemainder
  simp only [map_sub, map_sum, map_add, map_smul, contract_zero_contract_succ_comm, contract_zero_positionCasimir_succ,
    contract_zero_permSecond_swap_succ]

theorem raising_symMap_eq_one_level_down : ∀ (n : ℕ) (v0 : R × P) (z : Tens R P S.W (n + 1)),
    S.e v0 (S.mu (n + 1) z) = S.mu n (raisingRemainder S n v0 z) := by
  intro n
  induction n with
  | zero =>
    intro v0 z
    rw [raising_symMap_succ_eq, raisingRemainder_eq_first_add_tail, map_add, symMap_firstPositionRemainder_eq, add_comm]
    congr 1
    have h1 : tailRemainder S 0 v0 z = 0 := by simp [tailRemainder]
    rw [h1, map_zero]
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [symMap_zero_eq_default]
    have h2 := S.kill v0.2 v0.1 _ ((contr k 0 v z) default).2
    unfold HidaSetting.e
    rw [h2, map_zero]
  | succ m ih =>
    intro v0 z
    rw [raising_symMap_succ_eq, raisingRemainder_eq_first_add_tail, map_add, symMap_firstPositionRemainder_eq, add_comm]
    congr 1
    rw [symMap_succ_eq_sum_contract S m 0]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [ih, contract_zero_tailRemainder]

end Set3

section Set4

variable {k V P R : Type*} [CommRing k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
  [Fintype P] [Fintype R] (S : HidaSetting k V P R)

theorem jucysMurphy_last_eq (n : ℕ) (z : Tens R P S.W (n + 1)) :
    xJM k S.EW (Fin.last n) z = Om k S.EW (Fin.last n) z +
      ∑ t : Fin n, permY k (Equiv.swap t.castSucc (Fin.last n)) z := by
  unfold xJM
  rw [LinearMap.add_apply, LinearMap.sum_apply, Finset.sum_filter, Fin.sum_univ_castSucc]
  simp [Fin.castSucc_lt_last]

theorem raisingRemainder_of_perm_invariant (n : ℕ) (v : R × P) (z : Tens R P S.W (n + 1)) (hz : ∀ σ, perm k σ z = z) :
    raisingRemainder S n v z = (n + 1) • contr k (Fin.last n) v (S.w • z - xJM k S.EW (Fin.last n) z) := by
  have hA : ∀ j, contr k j v (S.w • z - Om k S.EW j z) =
      contr k (Fin.last n) v (S.w • z - Om k S.EW (Fin.last n) z) := by
    intro j
    funext g
    simp only [contract_apply_insertNth, Pi.sub_apply, Pi.smul_apply, mixedCasimir_apply_sum,
      Fin.insertNth_apply_same, Fin.update_insertNth]
    rw [apply_insertNth_eq_of_perm_invariant k z hz j (Fin.last n)]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [apply_insertNth_eq_of_perm_invariant k z hz j (Fin.last n)]
  have hC : ∀ (s : Fin (n + 1)) (t : Fin n), contr k s v (permY k (Equiv.swap (s.succAbove t) s) z) =
      contr k (Fin.last n) v (permY k (Equiv.swap t.castSucc (Fin.last n)) z) := by
    intro s t
    funext g
    rw [contract_apply_insertNth, permSecond_apply_comp, swap_insertNth_eq_update, contract_apply_insertNth, permSecond_apply_comp]
    have h := swap_insertNth_eq_update (Fin.last n) t v g
    rw [Fin.succAbove_last] at h
    rw [h]
    exact apply_insertNth_eq_of_perm_invariant k z hz s (Fin.last n) _ _
  have hB : ∑ j, ∑ l ∈ Finset.univ.filter (j < ·),
      (contr k j v (permY k (Equiv.swap j l) z) + contr k l v (permY k (Equiv.swap j l) z)) =
      (n + 1) • ∑ t : Fin n, contr k (Fin.last n) v (permY k (Equiv.swap t.castSucc (Fin.last n)) z) := by
    have h1 := sum_ordered_pairs_eq_sum_succAbove n (fun s t => contr k s v (permY k (Equiv.swap t s) z))
    simp only [hC] at h1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [Equiv.swap_comm l j]
  unfold raisingRemainder
  rw [hB]
  simp only [hA]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, jucysMurphy_last_eq, ← smul_sub]
  congr 1
  simp only [map_sub, map_add, map_sum]
  abel

end Set4

theorem word_specification_holds : WordSpec := by
  intro k V P R _ _ _ _ _ S n g
  exact word_products_of_content S g

theorem symMap_equivariant_holds : MuEquivariant := by
  intro k V P R _ _ _ _ _ _ _ S n z
  exact ⟨fun c d => symMap_diagSecond_intertwines S n c d z, fun α β => symMap_diagFirst_intertwines S n α β z,
    fun σ => symMap_perm_invariant S n σ z⟩

theorem one_step_invariance_holds : OneStepInv := by
  intro k V P R _ _ _ _ _ _ _ S n v z hz
  rw [raising_symMap_eq_one_level_down, raisingRemainder_of_perm_invariant S n v z hz, map_nsmul]

end Formalism.CohomologicalDescent.Symmetrization

open Polynomial

namespace Formalism.CohomologicalDescent.Symmetrization

section
variable {k R P M : Type*} [CommRing k] [AddCommGroup M] [Module k M] {n : ℕ}

theorem permOnTensor_apply (σ : Equiv.Perm (Fin n)) (z : Tens R P M n) (g) : perm k σ z g = z (g ∘ σ) := rfl
theorem permSecond_apply_formula (σ : Equiv.Perm (Fin n)) (z : Tens R P M n) (g) :
    permY k σ z g = z (fun s => ((g (σ s)).1, (g s).2)) := rfl
theorem contract_apply_eq_insertNth (j : Fin (n + 1)) (v : R × P) (z : Tens R P M (n + 1)) (g) :
    contr k j v z g = z (j.insertNth v g) := rfl
theorem contract_last_apply_snoc (v : R × P) (z : Tens R P M (n + 1)) (g) :
    contr k (Fin.last n) v z g = z (Fin.snoc g v) := by
  rw [contract_apply_eq_insertNth, Fin.insertNth_last']
theorem onFactor_apply (T : Module.End k M) (z : Tens R P M n) (g) : onM k T z g = T (z g) := rfl

variable [DecidableEq R] [DecidableEq P]

theorem unitSecond_apply (j : Fin n) (a b : R) (z : Tens R P M n) (g) :
    unitY k j a b z g = if (g j).1 = a then z (Function.update g j (b, (g j).2)) else 0 := by
  unfold unitY
  rw [LinearMap.pi_apply]
  split_ifs <;> rfl

variable [Fintype R]

theorem mixedCasimir_apply (EM : R → R → Module.End k M) (j : Fin n) (z : Tens R P M n) (g) :
    Om k EM j z g = ∑ b', EM b' (g j).1 (z (Function.update g j (b', (g j).2))) := by
  unfold Om
  simp only [LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, unitSecond_apply, onFactor_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [Finset.sum_ite_eq]
  simp

theorem jucysMurphy_apply (EM : R → R → Module.End k M) (j : Fin n) (z : Tens R P M n) (g) :
    xJM k EM j z g = ∑ b', EM b' (g j).1 (z (Function.update g j (b', (g j).2))) +
      ∑ j' ∈ Finset.univ.filter (· < j), z (fun s => ((g (Equiv.swap j' j s)).1, (g s).2)) := by
  unfold xJM
  simp only [LinearMap.add_apply, LinearMap.sum_apply, Pi.add_apply, Finset.sum_apply, mixedCasimir_apply,
    permSecond_apply_formula]

theorem filter_lt_castSucc_eq_map (j : Fin n) :
    (Finset.univ.filter (· < j.castSucc) : Finset (Fin (n + 1))) =
      (Finset.univ.filter (· < j)).map Fin.castSuccEmb := by
  ext x
  refine Fin.lastCases ?_ (fun t => ?_) x
  · simp [Fin.le_last]
  · simp

theorem contract_last_jucysMurphy_castSucc (EM : R → R → Module.End k M) (j : Fin n) (v : R × P) (z : Tens R P M (n + 1)) :
    contr k (Fin.last n) v (xJM k EM j.castSucc z) = xJM k EM j (contr k (Fin.last n) v z) := by
  funext g
  rw [contract_last_apply_snoc, jucysMurphy_apply, jucysMurphy_apply, filter_lt_castSucc_eq_map, Finset.sum_map]
  congr 1
  · refine Finset.sum_congr rfl fun b' _ => ?_
    rw [contract_last_apply_snoc, Fin.snoc_castSucc, Fin.snoc_update]
  · refine Finset.sum_congr rfl fun j' _ => ?_
    rw [contract_last_apply_snoc]
    congr 1
    funext s
    refine Fin.lastCases ?_ (fun t => ?_) s
    · rw [Equiv.swap_apply_of_ne_of_ne]
      · simp
      · exact (Fin.castSucc_lt_last j').ne'
      · exact (Fin.castSucc_lt_last j).ne'
    · have : Equiv.swap (Fin.castSuccEmb j') j.castSucc t.castSucc = (Equiv.swap j' j t).castSucc :=
        ((Fin.castSucc_injective n).map_swap j' j t).symm
      rw [this]
      simp

theorem intertwine_list_prod {X Y : Type*} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    (φ : X →ₗ[k] Y) : ∀ (m : ℕ) (a : Fin m → Module.End k X) (b : Fin m → Module.End k Y),
    (∀ j x, φ (a j x) = b j (φ x)) → ∀ x, φ ((List.ofFn a).prod x) = (List.ofFn b).prod (φ x) := by
  intro m
  induction m with
  | zero => intro a b _ x; simp
  | succ m ih =>
    intro a b h x
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply, Module.End.mul_apply, h,
      ih _ _ (fun j x => h j.succ x)]

theorem jucysMurphyProduct_succ (EM : R → R → Module.End k M) (t : k) :
    (AA k EM (n + 1) t : Module.End k (Tens R P M (n + 1))) =
      (List.ofFn fun j : Fin n => t • (1 : Module.End k (Tens R P M (n + 1))) - xJM k EM j.castSucc).prod *
        (t • 1 - xJM k EM (Fin.last n)) := by
  unfold AA
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]

theorem jucysMurphyProduct_contract_last (EM : R → R → Module.End k M) (t : k) (v : R × P) (z : Tens R P M (n + 1)) :
    AA k EM n t (contr k (Fin.last n) v (t • z - xJM k EM (Fin.last n) z)) =
      contr k (Fin.last n) v (AA k EM (n + 1) t z) := by
  rw [jucysMurphyProduct_succ, Module.End.mul_apply]
  unfold AA
  have key := intertwine_list_prod (contr k (Fin.last n) v : Tens R P M (n + 1) →ₗ[k] Tens R P M n) n
    (fun j : Fin n => t • (1 : Module.End k (Tens R P M (n + 1))) - xJM k EM j.castSucc)
    (fun j : Fin n => t • (1 : Module.End k (Tens R P M n)) - xJM k EM j)
    (by intro j x; simp [contract_last_jucysMurphy_castSucc]) ((t • 1 - xJM k EM (Fin.last n)) z)
  rw [key]
  simp

end

def permExtendLast {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  finSuccEquivLast.trans ((Equiv.optionCongr σ).trans finSuccEquivLast.symm)

theorem snoc_comp_eq_comp_permExtendLast {n : ℕ} {α : Type*} (σ : Equiv.Perm (Fin n)) (g : Fin n → α) (v : α) :
    (Fin.snoc (g ∘ σ) v : Fin (n + 1) → α) = (Fin.snoc g v : Fin (n + 1) → α) ∘ permExtendLast σ := by
  funext s
  refine Fin.lastCases ?_ (fun t => ?_) s
  · simp [permExtendLast]
  · simp [permExtendLast]

theorem contract_last_perm_invariant {k R P M : Type*} [CommRing k] [AddCommGroup M] [Module k M] {n : ℕ} (v : R × P)
    (X : Tens R P M (n + 1)) (hX : ∀ σ, perm k σ X = X) (σ : Equiv.Perm (Fin n)) :
    perm k σ (contr k (Fin.last n) v X) = contr k (Fin.last n) v X := by
  funext g
  rw [permOnTensor_apply, contract_last_apply_snoc, contract_last_apply_snoc, snoc_comp_eq_comp_permExtendLast]
  exact congrFun (hX (permExtendLast σ)) (Fin.snoc g v)

theorem generators_satisfy_gl_relations {k V P R : Type*} [CommRing k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
    (S : HidaSetting k V P R) : GlRel S.EW := by
  intro a b c d
  ext u
  have h := congrArg (fun T : Module.End k V => T (u : V)) (S.comm (Sum.inr a) (Sum.inr b) (Sum.inr c) (Sum.inr d))
  simp only [Sum.inr.injEq] at h
  have e1 : (((S.EW a b * S.EW c d - S.EW c d * S.EW a b) u : S.W) : V) =
      (S.E (Sum.inr a) (Sum.inr b) * S.E (Sum.inr c) (Sum.inr d) - S.E (Sum.inr c) (Sum.inr d) * S.E (Sum.inr a) (Sum.inr b)) (u : V) := rfl
  rw [e1, h]
  by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2, HidaSetting.EW]

theorem perm_sum_over_perms_eq {k R P M : Type*} [CommRing k] [AddCommGroup M] [Module k M] {n : ℕ}
    (z : Tens R P M n) (τ : Equiv.Perm (Fin n)) :
    perm k τ (∑ σ : Equiv.Perm (Fin n), perm k σ z) = ∑ σ : Equiv.Perm (Fin n), perm k σ z := by
  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
  funext g
  simp [permOnTensor_apply, Function.comp_assoc, Equiv.Perm.coe_mul]

theorem Iteration_of (h1 : OneStepInv) (h2 : AAComm) (h3 : MuEquivariant) : Iteration := by
  intro k V P R _ _ _ _ _ _ _ _ S n
  induction n with
  | zero =>
    intro h z _
    simp only [HidaSetting.Ew, HidaSetting.mu, AA, List.ofFn_zero, List.prod_nil, Nat.factorial_zero, one_smul,
      Module.End.one_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, HidaSetting.Fw,
      Submodule.subtype_apply]
    rw [Fintype.sum_unique]
    congr 2
    exact Subsingleton.elim _ _
  | succ n ih =>
    intro h z hz
    set v := h (Fin.last n) with hv
    set h' : Fin n → R × P := fun s => h s.castSucc with hh'
    have hEw : S.Ew h = S.Ew h' * S.e v := by
      unfold HidaSetting.Ew
      rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
    set Rr := contr k (Fin.last n) v (S.w • z - xJM k S.EW (Fin.last n) z) with hRr
    set X := AA k S.EW (n + 1) S.w z with hX
    have hXinv : ∀ σ, perm k σ X = X := by
      intro σ
      have := ((h2 k R P S.W S.EW (generators_satisfy_gl_relations S) (n + 1) σ).2.2 S.w).2
      have h4 := congrArg (fun T : Module.End k (Tens R P S.W (n + 1)) => T z) this.eq
      simp only [Module.End.mul_apply] at h4
      rw [hX, h4, hz]
    have hAR : AA k S.EW n S.w Rr = contr k (Fin.last n) v X := jucysMurphyProduct_contract_last S.EW S.w v z
    set Y := ∑ σ : Equiv.Perm (Fin n), perm k σ Rr with hY
    have hmuY : S.mu n Y = n.factorial • S.mu n Rr := by
      rw [hY, map_sum, Finset.sum_congr rfl (fun σ _ => (h3 k V P R S n Rr).2.2 σ)]
      simp [Fintype.card_perm]
    have hAY : AA k S.EW n S.w Y = n.factorial • contr k (Fin.last n) v X := by
      rw [hY, map_sum]
      have : ∀ σ : Equiv.Perm (Fin n), AA k S.EW n S.w (perm k σ Rr) = contr k (Fin.last n) v X := by
        intro σ
        have := ((h2 k R P S.W S.EW (generators_satisfy_gl_relations S) n σ).2.2 S.w).2
        have h4 := congrArg (fun T : Module.End k (Tens R P S.W n) => T Rr) this.eq
        simp only [Module.End.mul_apply] at h4
        rw [← h4, hAR, contract_last_perm_invariant v X hXinv]
      rw [Finset.sum_congr rfl (fun σ _ => this σ)]
      simp [Fintype.card_perm]
    have hIH := ih h' Y (perm_sum_over_perms_eq Rr)
    have hval : (contr k (Fin.last n) v X) h' = X h := by
      rw [contract_last_apply_snoc]
      congr 1
      exact Fin.snoc_init_self h
    rw [hmuY, hAY, map_nsmul] at hIH
    have hc : S.Ew h' (S.mu n Rr) = n.factorial • ((X h : S.W) : V) := by
      apply nsmul_right_injective (Nat.factorial_ne_zero n)
      simp only
      rw [hIH, Pi.smul_apply, hval]
      simp
    rw [hEw, Module.End.mul_apply, h1 k V P R S n v z hz, map_nsmul, hc, Nat.factorial_succ, mul_smul]

end Formalism.CohomologicalDescent.Symmetrization

open Polynomial

namespace Formalism.CohomologicalDescent.Symmetrization

section Comb
variable {ι : Type*} {n : ℕ}

theorem content_comp_perm_eq (g : Fin n → ι) (σ : Equiv.Perm (Fin n)) : cont (g ∘ σ) = cont g := by
  apply Subtype.ext
  change Finset.univ.val.map (g ∘ σ) = Finset.univ.val.map g
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv]

theorem content_surjective : Function.Surjective (cont : (Fin n → ι) → Sym ι n) := by
  rintro ⟨m, hm⟩
  induction m using Quotient.inductionOn with
  | h l =>
    have hl : l.length = n := by simpa using hm
    subst hl
    refine ⟨l.get, Subtype.ext ?_⟩
    change Finset.univ.val.map l.get = _
    rw [Fin.univ_val_map, List.ofFn_get]
    rfl

variable [DecidableEq ι]

theorem count_content_eq_card_fiber (g : Fin n → ι) (v : ι) :
    Multiset.count v (cont g).1 = Fintype.card {a // g a = v} := by
  change Multiset.count v (Finset.univ.val.map g) = _
  rw [Multiset.count_map, Fintype.card_subtype]
  simp only [eq_comm (a := v)]
  rfl

theorem exists_perm_of_content_eq (g g' : Fin n → ι) (h : cont g = cont g') : ∃ σ : Equiv.Perm (Fin n), g ∘ σ = g' := by
  have hc : ∀ v, Fintype.card {a // g' a = v} = Fintype.card {a // g a = v} := by
    intro v; rw [← count_content_eq_card_fiber, ← count_content_eq_card_fiber, h]
  let ev : ∀ v, {a // g' a = v} ≃ {a // g a = v} := fun v => Fintype.equivOfCardEq (hc v)
  refine ⟨(Equiv.sigmaFiberEquiv g').symm.trans ((Equiv.sigmaCongrRight ev).trans (Equiv.sigmaFiberEquiv g)), ?_⟩
  funext a
  simp only [Function.comp_apply, Equiv.trans_apply, Equiv.sigmaCongrRight_apply, Equiv.sigmaFiberEquiv_apply]
  exact (ev (g' a) _).2

variable [Fintype ι]

theorem card_perms_matching_content_eq_mfact (g g' : Fin n → ι) (h : cont g = cont g') :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => g ∘ σ = g').card = mfact (cont g) := by
  obtain ⟨σ0, h0⟩ := exists_perm_of_content_eq g g' h
  have h1 : (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => g ∘ σ = g').card =
      (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => g ∘ σ = g).card := by
    refine Finset.card_bij (fun σ _ => σ * σ0⁻¹) ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hσ, ← h0, Function.comp_assoc]
      funext a; simp
    · intro a _ b _ hab
      exact mul_right_cancel hab
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
      refine ⟨τ * σ0, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hτ, h0]
  rw [h1, ← Fintype.card_subtype, DomMulAct.stabilizer_card]
  unfold mfact
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [count_content_eq_card_fiber]

end Comb

section Lin
variable {k R P M : Type*} [CommRing k] [AddCommGroup M] [Module k M] [DecidableEq R] [DecidableEq P] [Fintype R]
  [Fintype P] {n : ℕ}

theorem toSym_apply_sum_fiber (z : Tens R P M n) (m : Sym (R × P) n) :
    toSym k z m = ∑ g ∈ Finset.univ.filter (fun g : Fin n → R × P => cont g = m), z g := by
  unfold toSym
  simp [LinearMap.pi_apply, LinearMap.sum_apply]

theorem norm_apply_eq_mfact_smul (y : Sym (R × P) n → M) (g : Fin n → R × P) :
    NmS k y g = mfact (cont g) • y (cont g) := by
  unfold NmS
  simp [LinearMap.pi_apply, Nat.cast_smul_eq_nsmul]

theorem norm_toSym_eq_sum_perm (z : Tens R P M n) : NmS k (toSym k z) = ∑ σ : Equiv.Perm (Fin n), perm k σ z := by
  funext g
  rw [norm_apply_eq_mfact_smul, toSym_apply_sum_fiber, Finset.sum_apply]
  simp only [permOnTensor_apply]
  rw [Finset.sum_comp z (fun σ : Equiv.Perm (Fin n) => g ∘ σ), Finset.smul_sum]
  have himg : (Finset.univ.image fun σ : Equiv.Perm (Fin n) => g ∘ σ) =
      Finset.univ.filter (fun g' : Fin n → R × P => cont g' = cont g) := by
    ext g'
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨σ, rfl⟩; exact content_comp_perm_eq g σ
    · intro h; exact exists_perm_of_content_eq g g' h.symm
  rw [himg]
  refine Finset.sum_congr rfl fun g' hg' => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg'
  rw [card_perms_matching_content_eq_mfact g g' hg'.symm]

theorem toSym_perm_eq (z : Tens R P M n) (σ : Equiv.Perm (Fin n)) : toSym k (perm k σ z) = toSym k z := by
  funext m
  rw [toSym_apply_sum_fiber, toSym_apply_sum_fiber]
  simp only [permOnTensor_apply]
  refine Finset.sum_bij (fun g _ => g ∘ σ) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    rw [content_comp_perm_eq, hg]
  · intro a _ b _ hab
    funext s
    have := congrFun hab (σ⁻¹ s)
    simpa using this
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    refine ⟨g ∘ (σ⁻¹ : Equiv.Perm (Fin n)), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [content_comp_perm_eq, hg]
    · funext s; simp
  · intro g _; rfl

theorem toSym_single_eq_single_content (g : Fin n → R × P) (u : M) :
    toSym k (Pi.single g u : Tens R P M n) = Pi.single (cont g) u := by
  funext m
  rw [toSym_apply_sum_fiber]
  by_cases h : cont g = m
  · subst h
    rw [Pi.single_eq_same, Finset.sum_eq_single g]
    · simp
    · intro b _ hb; simp [hb]
    · intro hg; simp at hg
  · rw [Pi.single_apply, if_neg (fun h' => h h'.symm)]
    refine Finset.sum_eq_zero fun b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    rw [Pi.single_apply, if_neg]
    rintro rfl; exact h hb

theorem toSym_surjective : Function.Surjective (toSym k : Tens R P M n →ₗ[k] (Sym (R × P) n → M)) := by
  intro y
  refine ⟨∑ m, Pi.single (Function.surjInv content_surjective m) (y m), ?_⟩
  rw [map_sum]
  simp only [toSym_single_eq_single_content, Function.surjInv_eq]
  funext m
  simp [Finset.sum_apply, Pi.single_apply]

end Lin

section Fld
variable {k V P R : Type} [Field k] [CharZero k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
  [Fintype P] [Fintype R]

theorem isAddTorsionFree_of_charZero_module (k : Type) {V : Type} [Field k] [CharZero k] [AddCommGroup V] [Module k V] : IsAddTorsionFree V :=
  ⟨fun n hn a b hab => by
    simp only [← Nat.cast_smul_eq_nsmul k] at hab
    exact smul_right_injective V (Nat.cast_ne_zero.2 hn : (n : k) ≠ 0) hab⟩

theorem symMap_norm_toSym_eq_factorial_smul (h3 : MuEquivariant) (S : HidaSetting k V P R) (n : ℕ) (z : Tens R P S.W n) :
    S.mu n (NmS k (toSym k z)) = n.factorial • S.mu n z := by
  rw [norm_toSym_eq_sum_perm, map_sum, Finset.sum_congr rfl (fun σ _ => (h3 k V P R S n z).2.2 σ)]
  simp [Fintype.card_perm]

theorem symmetric_action_eq_symMap (h3 : MuEquivariant) (S : HidaSetting k V P R) (n : ℕ) (z : Tens R P S.W n) :
    S.act n (toSym k z) = S.mu n z := by
  unfold HidaSetting.act
  rw [symMap_norm_toSym_eq_factorial_smul h3, ← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀, one_smul]
  exact Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)

theorem symMap_single_eq_wordProduct (S : HidaSetting k V P R) (n : ℕ) (g : Fin n → R × P) (u : S.W) :
    S.mu n (Pi.single g u) = S.Fw g (u : V) := by
  unfold HidaSetting.mu
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply]
  rw [Finset.sum_eq_single g]
  · simp
  · intro b _ hb; simp [hb]
  · intro hg; simp at hg

theorem ActSpec_of (h3 : MuEquivariant) (h4 : WordSpec) : ActSpec := by
  intro k V P R _ _ _ _ _ _ _ _ S n
  refine ⟨fun m u => ?_, fun z => symmetric_action_eq_symMap h3 S n z⟩
  obtain ⟨g, rfl⟩ := content_surjective m
  rw [← toSym_single_eq_single_content (k := k), symmetric_action_eq_symMap h3, symMap_single_eq_wordProduct, (h4 k V P R S n g).1]

theorem jucysMurphyProduct_norm_toSym_comm (h2 : AAComm) (S : HidaSetting k V P R) (n : ℕ) (z : Tens R P S.W n) :
    AA k S.EW n S.w (NmS k (toSym k z)) = NmS k (toSym k (AA k S.EW n S.w z)) := by
  rw [norm_toSym_eq_sum_perm, norm_toSym_eq_sum_perm, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have := ((h2 k R P S.W S.EW (generators_satisfy_gl_relations S) n σ).2.2 S.w).2
  have h4 := congrArg (fun T : Module.End k (Tens R P S.W n) => T z) this.eq
  simp only [Module.End.mul_apply] at h4
  exact h4.symm

theorem IotaMu_of (h2 : AAComm) (h3 : MuEquivariant) (h4 : WordSpec) (h5 : Iteration) : IotaMu := by
  intro k V P R _ _ _ _ _ _ _ _ S n z m
  have := isAddTorsionFree_of_charZero_module k (V := V)
  obtain ⟨h, rfl⟩ := content_surjective m
  unfold HidaSetting.iota
  rw [(h4 k V P R S n h).2]
  have hinv : ∀ σ, perm k σ (NmS k (toSym k z)) = NmS k (toSym k z) := by
    intro σ; rw [norm_toSym_eq_sum_perm]; exact perm_sum_over_perms_eq z σ
  have h6 := h5 k V P R S n h (NmS k (toSym k z)) hinv
  rw [symMap_norm_toSym_eq_factorial_smul h3, map_nsmul, jucysMurphyProduct_norm_toSym_comm h2, norm_apply_eq_mfact_smul] at h6
  have h7 := nsmul_right_injective (Nat.factorial_ne_zero n) h6
  rw [h7, Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀, one_smul]
  unfold mfact
  exact Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun v _ => Nat.factorial_ne_zero _)

end Fld

end Formalism.CohomologicalDescent.Symmetrization

open Polynomial

namespace Formalism.CohomologicalDescent.Symmetrization

theorem commute_coeff_of_commute_C {A : Type*} [Ring A] (s : A) (p : A[X]) (h : Commute (C s) p) (a : ℕ) :
    Commute s (p.coeff a) := by
  have := congrArg (fun q : A[X] => q.coeff a) h.eq
  simp only [coeff_C_mul, coeff_mul_C] at this
  exact this

theorem coeff_succ_X_sub_C_mul_alt {A : Type*} [Ring A] (x0 : A) (q : A[X]) (a : ℕ) :
    ((X - C x0) * q).coeff (a + 1) = q.coeff a - x0 * q.coeff (a + 1) := by
  rw [sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul]

theorem coeff_zero_X_sub_C_mul_alt {A : Type*} [Ring A] (x0 : A) (q : A[X]) :
    ((X - C x0) * q).coeff 0 = -(x0 * q.coeff 0) := by
  rw [sub_mul, coeff_sub, coeff_X_mul_zero, coeff_C_mul, zero_sub]

theorem prod_X_sub_C_coeff_top {A : Type*} [Ring A] : ∀ (n : ℕ) (x : Fin n → A),
    (List.ofFn fun j => (X - C (x j) : A[X])).prod.coeff n = 1 ∧
      ∀ a, n < a → (List.ofFn fun j => (X - C (x j) : A[X])).prod.coeff a = 0 := by
  intro n
  induction n with
  | zero =>
    intro x
    refine ⟨by simp, fun a ha => ?_⟩
    rw [List.ofFn_zero, List.prod_nil, coeff_one, if_neg (by omega)]
  | succ n ih =>
    intro x
    rw [List.ofFn_succ, List.prod_cons]
    have h := ih (fun j => x j.succ)
    refine ⟨?_, fun a ha => ?_⟩
    · rw [coeff_succ_X_sub_C_mul_alt, h.1, h.2 (n + 1) (Nat.lt_succ_self n), mul_zero, sub_zero]
    · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      rw [coeff_succ_X_sub_C_mul_alt, h.2 b (by omega), h.2 (b + 1) (by omega), mul_zero, sub_zero]

theorem coeff_prod_X_sub_C_mem_subring {A : Type*} [Ring A] (Sr : Subring A) : ∀ (n : ℕ) (x : Fin n → A), (∀ j, x j ∈ Sr) →
    ∀ a, (List.ofFn fun j => (X - C (x j) : A[X])).prod.coeff a ∈ Sr := by
  intro n
  induction n with
  | zero =>
    intro x _ a
    rw [List.ofFn_zero, List.prod_nil, coeff_one]
    split_ifs
    · exact Sr.one_mem
    · exact Sr.zero_mem
  | succ n ih =>
    intro x hx a
    rw [List.ofFn_succ, List.prod_cons]
    have h := ih (fun j => x j.succ) (fun j => hx j.succ)
    cases a with
    | zero => rw [coeff_zero_X_sub_C_mul_alt]; exact Sr.neg_mem (Sr.mul_mem (hx 0) (h 0))
    | succ a => rw [coeff_succ_X_sub_C_mul_alt]; exact Sr.sub_mem (h a) (Sr.mul_mem (hx 0) (h (a + 1)))

def stabilizerSubring {K Y : Type*} [CommRing K] [AddCommGroup Y] [Module K Y] (abelian₂ : AddSubgroup Y) :
    Subring (Module.End K Y) where
  carrier := {T | ∀ z ∈ abelian₂, T z ∈ abelian₂}
  mul_mem' := fun ha hb z hz => ha _ (hb z hz)
  one_mem' := fun _ hz => hz
  add_mem' := fun ha hb z hz => abelian₂.add_mem (ha z hz) (hb z hz)
  zero_mem' := fun _ _ => abelian₂.zero_mem
  neg_mem' := fun ha z hz => abelian₂.neg_mem (ha z hz)

section
variable {K R P M : Type*} [CommRing K] [AddCommGroup M] [Module K M] [DecidableEq R] [DecidableEq P] [Fintype R]
  {n : ℕ}

theorem jucysMurphyProduct_expand_coeff (EM : R → R → Module.End K M) (t : K) :
    (AA K EM n t : Module.End K (Tens R P M n)) =
      t ^ n • (1 : Module.End K (Tens R P M n)) + ∑ a : Fin n, t ^ a.val • (AApoly K EM n).coeff a.val := by
  have htop := prod_X_sub_C_coeff_top n (fun j => (xJM K EM j : Module.End K (Tens R P M n)))
  have hdeg : (AApoly K EM n : (Module.End K (Tens R P M n))[X]).natDegree < n + 1 :=
    Nat.lt_succ_of_le (natDegree_le_iff_coeff_eq_zero.2 htop.2)
  have hn : (AApoly K EM n : (Module.End K (Tens R P M n))[X]).coeff n = 1 := htop.1
  have hev : evalAtCentral K t (AApoly K EM n : (Module.End K (Tens R P M n))[X]) =
      eval₂ (RingHom.id _) (t • 1) (AApoly K EM n : (Module.End K (Tens R P M n))[X]) := rfl
  rw [← eval_jucysMurphyPoly_eq_product, hev, eval₂_eq_sum_range' _ hdeg, Finset.sum_range_succ, Finset.sum_range, add_comm, hn]
  congr 1
  · simp [_root_.smul_pow]
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp [_root_.smul_pow]

end

section
variable {K R P M : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M] [DecidableEq R] [DecidableEq P]
  [Fintype R] [Fintype P] {n : ℕ}

noncomputable def descendToCoinvariants (T : Module.End K (Tens R P M n)) : Module.End K (Sym (R × P) n → M) :=
  ((n.factorial : K)⁻¹) • (toSym K ∘ₗ T ∘ₗ NmS K)

theorem descendToCoinvariants_toSym (T : Module.End K (Tens R P M n)) (hT : ∀ σ, Commute (perm K σ) T) (z : Tens R P M n) :
    descendToCoinvariants T (toSym K z) = toSym K (T z) := by
  have hn : ((n.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  unfold descendToCoinvariants
  rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply, norm_toSym_eq_sum_perm, map_sum, map_sum]
  have : ∀ σ : Equiv.Perm (Fin n), toSym K (T (perm K σ z)) = toSym K (T z) := by
    intro σ
    have h4 := congrArg (fun U : Module.End K (Tens R P M n) => U z) (hT σ).eq
    simp only [Module.End.mul_apply] at h4
    rw [← h4, toSym_perm_eq]
  rw [Finset.sum_congr rfl (fun σ _ => this σ)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hn, one_smul]

end

theorem coefficient_operators_hold : CoeffOps := by
  intro O K R P M _ _ _ _ _ _ _ _ _ _ _ _ EM hEM n
  have hAA := AAComm_of symmetric_commute_abstract_holds jucys_murphy_commute_holds K R P M EM hEM n
  have hX := XComm_of jucys_murphy_commute_holds K R P M EM hEM n
  set p := (AApoly K EM n : (Module.End K (Tens R P M n))[X]) with hp
  have hperm : ∀ (a : ℕ) (σ : Equiv.Perm (Fin n)), Commute (perm K σ) (p.coeff a) :=
    fun a σ => commute_coeff_of_commute_C _ _ (hAA σ).2.1 a
  have hxc : ∀ (a : ℕ) (j : Fin n), Commute (p.coeff a) (xJM K EM j) := fun a j =>
    (commute_coeff_of_commute_C _ _ (commute_C_jucysMurphyPoly K EM _ (fun i => hX j i)) a).symm
  have hcc : ∀ a b : ℕ, Commute (p.coeff a) (p.coeff b) := fun a b =>
    commute_coeff_of_commute_C _ _ (commute_C_jucysMurphyPoly K EM _ (hxc a)) b
  have h1 : ∀ (a : ℕ) (z : Tens R P M n), descendToCoinvariants (p.coeff a) (toSym K z) = toSym K (p.coeff a z) :=
    fun a z => descendToCoinvariants_toSym _ (hperm a) z
  refine ⟨fun a => descendToCoinvariants (p.coeff a.val), fun a z => h1 a.val z, ?_, ?_, ?_⟩
  · intro a b
    refine LinearMap.ext fun y => ?_
    obtain ⟨z, rfl⟩ := toSym_surjective (k := K) y
    simp only [Module.End.mul_apply]
    rw [h1, h1, h1, h1]
    have := congrArg (fun U : Module.End K (Tens R P M n) => U z) (hcc a.val b.val).eq
    simp only [Module.End.mul_apply] at this
    rw [this]
  · intro t z
    rw [jucysMurphyProduct_expand_coeff]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, LinearMap.sum_apply, map_add,
      map_smul, map_sum, h1, ← hp]
  · intro L hL a y hy m
    let abelian₂ : AddSubgroup (Tens R P M n) :=
      { carrier := {z | ∀ g, z g ∈ L (cont g)}
        add_mem' := fun ha hb g => (L _).add_mem (ha g) (hb g)
        zero_mem' := fun g => (L _).zero_mem
        neg_mem' := fun ha g => (L _).neg_mem (ha g) }
    have hmem : p.coeff a.val ∈ stabilizerSubring (K := K) abelian₂ :=
      coeff_prod_X_sub_C_mem_subring (stabilizerSubring (K := K) abelian₂) n (fun j => xJM K EM j) (fun j z hz => hL j z hz) a.val
    let rep : Sym (R × P) n → (Fin n → R × P) := Function.surjInv content_surjective
    have hrep : ∀ m, cont (rep m) = m := Function.surjInv_eq _
    let z : Tens R P M n := fun g => if g = rep (cont g) then y (cont g) else 0
    have hz : ∀ g, z g ∈ L (cont g) := by
      intro g
      simp only [z]
      split_ifs
      · exact hy _
      · exact (L _).zero_mem
    have hzy : toSym K z = y := by
      funext m'
      rw [toSym_apply_sum_fiber, Finset.sum_eq_single (rep m')]
      · simp only [z, hrep, if_true]
      · intro g hg hne
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
        simp only [z, hg, if_neg hne]
      · intro h
        exact absurd (by simp [hrep]) h
    have hcy : descendToCoinvariants (p.coeff a.val) y = toSym K (p.coeff a.val z) := by rw [← h1, hzy]
    show descendToCoinvariants (p.coeff a.val) y m ∈ L m
    rw [hcy, toSym_apply_sum_fiber]
    refine Submodule.sum_mem _ fun g hg => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    have := hmem z hz g
    rwa [hg] at this

end Formalism.CohomologicalDescent.Symmetrization

open Polynomial

namespace Formalism.CohomologicalDescent.Symmetrization

theorem x_lattice_holds : XLattice := by
  intro O K R P M _ _ _ _ _ _ _ _ _ _ EM L hL n j z hz g
  rw [jucysMurphy_apply]
  exact L.add_mem (L.sum_mem fun b' _ => hL _ _ _ (hz _)) (L.sum_mem fun j' _ => hz _)

section Beta
variable {R P : Type*} [DecidableEq R] [DecidableEq P]

def letterRoot (v : R × P) : P ⊕ R → ℤ := Pi.single (Sum.inl v.2) 1 - Pi.single (Sum.inr v.1) 1

def weightOfMultiset (s : Multiset (R × P)) : P ⊕ R → ℤ :=
  Sum.elim (fun α => (Multiset.countP (fun v : R × P => v.2 = α) s : ℤ))
    (fun b => -(Multiset.countP (fun v : R × P => v.1 = b) s : ℤ))

theorem weightOfMultiset_cons (v : R × P) (s : Multiset (R × P)) :
    weightOfMultiset (v ::ₘ s) = letterRoot v + weightOfMultiset s := by
  funext a
  rcases a with α | b
  · by_cases h : v.2 = α
    · subst h
      simp [weightOfMultiset, letterRoot, Multiset.countP_cons, add_comm]
    · have h' : ¬ α = v.2 := fun e => h e.symm
      simp [weightOfMultiset, letterRoot, Multiset.countP_cons, h, h']
  · by_cases h : v.1 = b
    · subst h
      simp [weightOfMultiset, letterRoot, Multiset.countP_cons, add_comm]
    · have h' : ¬ b = v.1 := fun e => h e.symm
      simp [weightOfMultiset, letterRoot, Multiset.countP_cons, h, h']

theorem weightOfMultiset_eq_sum_roots (s : Multiset (R × P)) : weightOfMultiset s = (s.map letterRoot).sum := by
  induction s using Multiset.induction_on with
  | empty => funext a; rcases a with a | a <;> simp [weightOfMultiset]
  | cons v s ih => rw [weightOfMultiset_cons, Multiset.map_cons, Multiset.sum_cons, ih]

theorem weight_content_eq_sum_roots {n : ℕ} (g : Fin n → R × P) : beta (cont g) = ∑ s, letterRoot (g s) := by
  change weightOfMultiset (Finset.univ.val.map g) = _
  rw [weightOfMultiset_eq_sum_roots, Multiset.map_map]
  rfl

theorem weight_content_update {n : ℕ} (g : Fin n → R × P) (j : Fin n) (b' : R) :
    beta (cont (Function.update g j (b', (g j).2))) + Pi.single (Sum.inr b') 1 - Pi.single (Sum.inr (g j).1) 1 =
      beta (cont g) := by
  rw [weight_content_eq_sum_roots, weight_content_eq_sum_roots,
    ← Finset.add_sum_erase Finset.univ (fun s => letterRoot (Function.update g j (b', (g j).2) s)) (Finset.mem_univ j),
    ← Finset.add_sum_erase Finset.univ (fun s => letterRoot (g s)) (Finset.mem_univ j)]
  have h : ∑ s ∈ Finset.univ.erase j, letterRoot (Function.update g j (b', (g j).2) s) =
      ∑ s ∈ Finset.univ.erase j, letterRoot (g s) :=
    Finset.sum_congr rfl fun s hs => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
  rw [h, Function.update_self]
  unfold letterRoot
  simp only
  abel

theorem weight_content_swap_invariant {n : ℕ} (g : Fin n → R × P) (σ : Equiv.Perm (Fin n)) :
    beta (cont (fun s => ((g (σ s)).1, (g s).2))) = beta (cont g) := by
  rw [weight_content_eq_sum_roots, weight_content_eq_sum_roots]
  unfold letterRoot
  simp only [Finset.sum_sub_distrib]
  congr 1
  exact Equiv.sum_comp σ (fun s => (Pi.single (Sum.inr (g s).1) (1 : ℤ) : P ⊕ R → ℤ))

end Beta

theorem beta_dominant_holds : BetaDominant := by
  intro P R _ _ xi h n m
  rw [show beta m = weightOfMultiset m.1 from rfl, weightOfMultiset_eq_sum_roots, map_multiset_sum, Multiset.map_map]
  apply Multiset.sum_nonneg
  intro x hx
  obtain ⟨v, _, rfl⟩ := Multiset.mem_map.1 hx
  exact h v.2 v.1

section Wt
variable {k V P R : Type*} [CommRing k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]

theorem mem_weightSpace_iff_alt (S : HidaSetting k V P R) (κ : P ⊕ R → ℤ) (v : V) :
    v ∈ S.wt κ ↔ ∀ a, S.E a a v = (κ a : k) • v := by
  simp [HidaSetting.wt, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem gl_generator_shifts_weight (S : HidaSetting k V P R) (κ : P ⊕ R → ℤ) (a' b' : P ⊕ R) (u : V) (hu : u ∈ S.wt κ) :
    S.E a' b' u ∈ S.wt (κ + Pi.single a' 1 - Pi.single b' 1) := by
  rw [mem_weightSpace_iff_alt] at hu ⊢
  intro a
  have h := congrArg (fun T : Module.End k V => T u) (S.comm a a a' b')
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [hu a, map_smul] at h
  have key : S.E a a (S.E a' b' u) = (κ a : k) • S.E a' b' u +
      ((if a = a' then S.E a b' else 0 : Module.End k V) u - (if b' = a then S.E a' a else 0 : Module.End k V) u) := by
    rw [← h]; abel
  rw [key]
  by_cases h1 : a = a' <;> by_cases h2 : a = b'
  · subst h1; subst h2; simp
  · subst h1
    have h2' : ¬ b' = a := fun e => h2 e.symm
    simp [h2, h2', add_smul]
  · subst h2
    simp [h1, sub_eq_add_neg, add_smul]
  · have h2' : ¬ b' = a := fun e => h2 e.symm
    simp [h1, h2, h2']

theorem list_raising_mem_weightSpace (S : HidaSetting k V P R) (l : List (R × P)) (ν : P ⊕ R → ℤ) (v : V) (hv : v ∈ S.wt ν) :
    (l.map S.e).prod v ∈ S.wt (ν + weightOfMultiset (l : Multiset (R × P))) := by
  induction l with
  | nil => simpa [weightOfMultiset_eq_sum_roots] using hv
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ← Multiset.cons_coe, weightOfMultiset_cons]
    have h := gl_generator_shifts_weight S _ (Sum.inl x.2) (Sum.inr x.1) _ ih
    have e : ν + (letterRoot x + weightOfMultiset (l : Multiset (R × P))) =
        ν + weightOfMultiset (l : Multiset (R × P)) + Pi.single (Sum.inl x.2) 1 - Pi.single (Sum.inr x.1) 1 := by
      unfold letterRoot; abel
    rw [e]
    exact h

end Wt

theorem iota_weight_holds : IotaWeight := by
  intro k V P R _ _ _ _ _ _ _ S n ν v m hv
  unfold HidaSetting.iota
  refine Submodule.smul_mem _ _ ?_
  have h := list_raising_mem_weightSpace S m.1.toList ν v hv
  rw [Multiset.coe_toList] at h
  exact h

theorem x_weight_holds : XWeight := by
  intro k V P R _ _ _ _ _ _ _ S n ν j z hz g
  rw [jucysMurphy_apply, Submodule.coe_add, AddSubmonoidClass.coe_finsetSum, AddSubmonoidClass.coe_finsetSum]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun b' _ => ?_) (Submodule.sum_mem _ fun j' _ => ?_)
  · have h := gl_generator_shifts_weight S _ (Sum.inr b') (Sum.inr (g j).1) _ (hz (Function.update g j (b', (g j).2)))
    have e : ν + beta (cont (Function.update g j (b', (g j).2))) + Pi.single (Sum.inr b') 1 -
        Pi.single (Sum.inr (g j).1) 1 = ν + beta (cont g) := by
      rw [← weight_content_update g j b']; abel
    rw [e] at h
    exact h
  · have h := hz (fun s => ((g (Equiv.swap j' j s)).1, (g s).2))
    rw [weight_content_swap_invariant] at h
    exact h

theorem ActLattice_of (h3 : MuEquivariant) (h4 : WordSpec) : ActLattice := by
  intro O K V P R _ _ _ _ _ _ _ _ _ _ _ _ S n DelL y hy
  have hA := (ActSpec_of h3 h4 K V P R S n).1
  have hadd : S.act n (∑ m, Pi.single m (y m)) = ∑ m, S.act n (Pi.single m (y m)) := by
    unfold HidaSetting.act
    rw [map_sum, map_sum, Finset.smul_sum]
  have hy' : S.act n y = ∑ m, S.act n (Pi.single m (y m)) := by
    rw [← hadd, Finset.univ_sum_single]
  rw [hy']
  refine Submodule.sum_mem _ fun m _ => ?_
  rw [hA]
  have hne : ((mfact m : ℕ) : K) ≠ 0 := by
    unfold mfact
    exact Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun v _ => Nat.factorial_ne_zero _)
  have e : S.Fs m ((y m : S.W) : V) = (mfact m) • (((mfact m : K)⁻¹) • S.Fs m ((y m : S.W) : V)) := by
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul, mul_inv_cancel₀ hne, one_smul]
  rw [e]
  have hm : ((mfact m : K)⁻¹) • S.Fs m ((y m : S.W) : V) ∈ S.DeltaN n DelL :=
    Submodule.subset_span ⟨m, y m, hy m, rfl⟩
  exact nsmul_mem hm _

end Formalism.CohomologicalDescent.Symmetrization

open Polynomial

namespace Formalism.CohomologicalDescent.Symmetrization

theorem casimir_recursion_holds : CasimirStep := by
  intro A R _ _ ε hcomm j
  have h1 : ∀ b b' : R, (∑ i ∈ Finset.range (j + 1), ε i b b') * (∑ i ∈ Finset.range (j + 1), ε i b' b) =
      (∑ i ∈ Finset.range j, ε i b b') * (∑ i ∈ Finset.range j, ε i b' b) +
        (∑ a ∈ Finset.range j, ε a b b' * ε j b' b) + (∑ a ∈ Finset.range j, ε a b' b * ε j b b') +
        ε j b b' * ε j b' b := by
    intro b b'
    have e1 : (∑ i ∈ Finset.range j, ε i b b') * ε j b' b = ∑ a ∈ Finset.range j, ε a b b' * ε j b' b :=
      Finset.sum_mul _ _ _
    have e2 : ε j b b' * ∑ i ∈ Finset.range j, ε i b' b = ∑ a ∈ Finset.range j, ε a b' b * ε j b b' := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i hi => (hcomm j i (Finset.mem_range.1 hi).ne' _ _ _ _).eq
    rw [Finset.sum_range_succ, Finset.sum_range_succ, add_mul, mul_add, mul_add, e1, e2]
    abel
  have h2 : ∀ F : R → R → ℕ → A, ∑ b, ∑ b', ∑ a ∈ Finset.range j, F b b' a =
      ∑ a ∈ Finset.range j, ∑ b, ∑ b', F b b' a := by
    intro F
    calc _ = ∑ b, ∑ a ∈ Finset.range j, ∑ b', F b b' a := Finset.sum_congr rfl (fun b _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  have h3 : ∑ b, ∑ b', ∑ a ∈ Finset.range j, ε a b' b * ε j b b' =
      ∑ a ∈ Finset.range j, ∑ b, ∑ b', ε a b b' * ε j b' b := by
    rw [Finset.sum_comm, h2]
  simp only [h1, Finset.sum_add_distrib]
  rw [h2, h3, two_nsmul]
  abel

theorem casimir_on_tensor_holds : CasimirY := by
  intro k R P M _ _ _ _ _ _ n j
  refine LinearMap.ext fun z => ?_
  funext g
  simp only [LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, unitSecond_apply, Function.update_self,
    Function.update_idem, if_true, LinearMap.smul_apply, Module.End.one_apply, Pi.smul_apply]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Prod.mk.eta, Function.update_eq_self, Finset.sum_const,
    Finset.card_univ]

theorem casimir_content_holds : CasimirContent := by
  intro r κ ρ
  rw [← Finset.sum_sub_distrib]
  have : ∀ b : Fin r, (κ b + if b = ρ then 1 else 0) * ((κ b + if b = ρ then 1 else 0) + (r : ℤ) - 1 - 2 * (b.val : ℤ)) -
      κ b * (κ b + (r : ℤ) - 1 - 2 * (b.val : ℤ)) = if b = ρ then 2 * κ ρ + (r : ℤ) - 2 * (ρ.val : ℤ) else 0 := by
    intro b
    by_cases h : b = ρ
    · subst h; simp; ring
    · simp [h]
  rw [Finset.sum_congr rfl (fun b _ => this b), Finset.sum_ite_eq' ]
  simp
  ring

end Formalism.CohomologicalDescent.Symmetrization

open Polynomial

namespace Formalism.CohomologicalDescent.Symmetrization

theorem iota_sub_smul {k V P R : Type} [Field k] [AddCommGroup V] [Module k V] [DecidableEq P] [DecidableEq R]
    [Fintype P] [Fintype R] (S : HidaSetting k V P R) (n : ℕ) (v1 v2 : V) (r : k) (m : Sym (R × P) n) :
    S.iota n (v1 - r • v2) m = S.iota n v1 m - r • S.iota n v2 m := by
  unfold HidaSetting.iota
  rw [map_sub, map_smul, smul_sub, smul_comm]

theorem LemmaDSkeleton_of (hCo : CoeffOps) (hXL : XLattice) (hXW : XWeight) (hIW : IotaWeight) (hBD : BetaDominant)
    (hAL : ActLattice) (hIQ : IntegralQuotient) (hIM : IotaMu) (hAS : ActSpec) : LemmaDSkeleton := by
  intro O K V P R I _ _ _ _ _ _ _ _ _ _ _ _ S n wO nabL DelL Mt χ Dn xi lam l e i' hw hstab hinj h3a hdiv h3b hdom heL
    ν hν z hzν hznab
  obtain ⟨c, hc1, hc2, hc3, hc4⟩ := hCo O K R P S.W S.EW (generators_satisfy_gl_relations S) n
  set c' : Fin n → Module.End O (Sym (R × P) n → S.W) := fun a => (c a).restrictScalars O with hc'
  have hcomm : ∀ a b, Commute (c' a) (c' b) := by
    intro a b
    refine LinearMap.ext fun y => ?_
    exact congrArg (fun T : Module.End K (Sym (R × P) n → S.W) => T y) (hc2 a b).eq
  have hχ : ∀ τ a, ∀ y ∈ Mt τ, c' a y = χ τ a • y := by
    intro τ a y hy
    obtain ⟨z', rfl⟩ := toSym_surjective (k := K) y
    change c a (toSym K z') = _
    rw [hc1, h3a τ a z' hy]
  obtain ⟨Q, hQ, hQD⟩ := hIQ O K (Sym (R × P) n → S.W) I n c' hcomm Mt χ hχ Dn hdiv wO
  set AAS : Module.End K (Sym (R × P) n → S.W) :=
    S.w ^ n • (1 : Module.End K (Sym (R × P) n → S.W)) + ∑ a : Fin n, S.w ^ a.val • c a with hAAS
  have hid : ∀ y, (wO ^ n • (1 : Module.End O (Sym (R × P) n → S.W)) + ∑ a : Fin n, wO ^ a.val • c' a) y = AAS y := by
    intro y
    simp only [hAAS, hc', LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, LinearMap.sum_apply,
      LinearMap.coe_restrictScalars, hw, ← map_pow, algebraMap_smul]
  set y0 := toSym K (AA K S.EW n S.w z) with hy0
  have hy0i : ∀ m, S.iota n (S.mu n z) m = ((y0 m : S.W) : V) := fun m => hIM K V P R S n z m
  let L : Sym (R × P) n → Submodule O S.W := fun m =>
    nabL ⊓ ((S.wt (ν + beta m)).comap S.W.subtype).restrictScalars O
  have hLmem : ∀ m (u : S.W), u ∈ L m ↔ u ∈ nabL ∧ (u : V) ∈ S.wt (ν + beta m) := by
    intro m u
    simp [L]
  have hy0L : ∀ m, y0 m ∈ L m := by
    intro m
    rw [hLmem]
    constructor
    · obtain ⟨u, hu, hu'⟩ := hznab m
      rw [hy0i] at hu'
      rw [Subtype.ext hu']; exact hu
    · rw [← hy0i]; exact hIW K V P R S n ν _ m hzν
  have hLx : ∀ (j : Fin n) (z' : Tens R P S.W n), (∀ g, z' g ∈ L (cont g)) → ∀ g, xJM K S.EW j z' g ∈ L (cont g) := by
    intro j z' hz' g
    rw [hLmem]
    exact ⟨hXL O K R P S.W S.EW nabL hstab n j z' (fun g => ((hLmem _ _).1 (hz' g)).1) g,
      hXW K V P R S n ν j z' (fun g => ((hLmem _ _).1 (hz' g)).2) g⟩
  have hQL : ∀ y : Sym (R × P) n → S.W, (∀ m, y m ∈ L m) → ∀ m, Q y m ∈ L m := by
    refine Algebra.adjoin_induction (p := fun T _ => ∀ y : Sym (R × P) n → S.W, (∀ m, y m ∈ L m) → ∀ m, T y m ∈ L m)
      ?_ ?_ ?_ ?_ hQ
    · rintro _ ⟨a, rfl⟩ y hy m
      exact hc4 L hLx a y hy m
    · intro r y hy m
      rw [Module.algebraMap_end_apply]
      exact (L m).smul_mem r (hy m)
    · intro T1 T2 _ _ h1 h2 y hy m
      exact (L m).add_mem (h1 y hy m) (h2 y hy m)
    · intro T1 T2 _ _ h1 h2 y hy m
      exact h1 (T2 y) (h2 y hy) m
  set y1 := Q y0 with hy1
  have hy1L := hQL y0 hy0L
  have hy2 : ∀ m, (l ^ e • y1) m ∈ DelL := by
    intro m
    obtain ⟨ha, hb⟩ := (hLmem _ _).1 (hy1L m)
    refine heL (ν + beta m) ?_ (y1 m) ha hb
    have h0 := hBD P R xi hdom n m
    have : lam - (ν + beta m) = (lam - ν) - beta m := by abel
    rw [this, map_sub]
    linarith
  obtain ⟨z1, hz1⟩ := toSym_surjective (k := K) (l ^ e • y1)
  have hmem : S.mu n z1 ∈ S.DeltaN n DelL := by
    rw [← (hAS K V P R S n).2 z1, hz1]
    exact hAL O K V P R S n DelL _ hy2
  set r : K := algebraMap O K (l ^ e * Dn.eval wO) with hr
  have hAy : AAS (l ^ e • y1) = r • y0 := by
    rw [← algebraMap_smul K (l ^ e) y1, map_smul, ← hid y1, ← hQD y0 (h3b z), ← algebraMap_smul K (Dn.eval wO) y0,
      smul_smul, hr, map_mul]
  have hzero : S.mu n (z1 - r • z) = 0 := by
    apply hinj
    intro m
    rw [map_sub, map_smul, iota_sub_smul, hIM K V P R S n z1 m, hc3, hz1, hAy, hy0i]
    simp
  rw [map_sub, map_smul, sub_eq_zero] at hzero
  rw [← algebraMap_smul K, ← hr, ← hzero]
  exact hmem

end Formalism.CohomologicalDescent.Symmetrization

open Polynomial

namespace Formalism.CohomologicalDescent.Symmetrization

theorem polynomial_evaluation_holds : DnPolyEval := by
  intro p w i q lam2
  unfold DnPoly LD.Dn
  rw [eval_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp

theorem shape_bounds_of_mem_shapes {p w i q : ℕ} {lam2 tau : Fin q → ℕ} (h : tau ∈ LD.shapes p w i lam2) :
    (∀ a, lam2 a ≤ tau a ∧ tau a ≤ lam2 a + i) ∧ ∑ a, tau a = ∑ a, lam2 a + i := by
  unfold LD.shapes at h
  rw [Finset.mem_filter, Fintype.mem_piFinset] at h
  exact ⟨fun a => Finset.mem_Icc.1 (h.1 a), h.2.2.1⟩

theorem shape_divisibility_holds : ShapeDvd := by
  intro p w i q lam2 hw tau htau
  obtain ⟨hb, hsum⟩ := shape_bounds_of_mem_shapes htau
  refine ⟨?_, ?_, ?_⟩
  · unfold shapePoly
    exact monic_prod_of_monic _ _ fun a _ => monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _
  · unfold shapePoly
    rw [natDegree_prod_of_monic _ _ fun a _ => monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _]
    have : ∀ a : Fin q, (∏ j ∈ Finset.Ico (lam2 a) (tau a), (X - C ((j : ℤ) - (a.val : ℤ)) : ℤ[X])).natDegree =
        tau a - lam2 a := by
      intro a
      rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _,
        Finset.sum_congr rfl fun j _ => natDegree_X_sub_C _]
      simp
    rw [Finset.sum_congr rfl fun a _ => this a]
    have h2 : ∑ a, (tau a - lam2 a) + ∑ a, lam2 a = ∑ a, tau a := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => Nat.sub_add_cancel (hb a).1
    omega
  · unfold shapePoly DnPoly
    rw [Finset.prod_sigma']
    set s : Finset (Σ _ : Fin q, ℕ) := Finset.univ.sigma fun a => Finset.Ico (lam2 a) (tau a) with hs
    have hmaps : ∀ x ∈ s, x.2 + q - x.1.val ∈ Finset.range (q + w + i) := by
      intro x hx
      rw [hs, Finset.mem_sigma, Finset.mem_Ico] at hx
      have h1 := (hb x.1).2
      have h2 := hw x.1
      have h3 := x.1.isLt
      rw [Finset.mem_range]
      omega
    rw [← Finset.prod_fiberwise_of_maps_to hmaps]
    refine Finset.prod_dvd_prod_of_dvd _ _ fun k _ => ?_
    have hfib : ∏ x ∈ s with x.2 + q - x.1.val = k, (X - C ((x.2 : ℤ) - (x.1.val : ℤ)) : ℤ[X]) =
        (X - C ((k : ℤ) - (q : ℤ))) ^ (s.filter fun x => x.2 + q - x.1.val = k).card := by
      rw [Finset.prod_congr rfl (g := fun _ => (X - C ((k : ℤ) - (q : ℤ)) : ℤ[X])), Finset.prod_const]
      intro x hx
      rw [Finset.mem_filter] at hx
      have h3 := x.1.isLt
      have : (x.2 : ℤ) - (x.1.val : ℤ) = (k : ℤ) - (q : ℤ) := by omega
      rw [this]
    rw [hfib]
    apply pow_dvd_pow
    calc (s.filter fun x => x.2 + q - x.1.val = k).card
        ≤ LD.boxesOfContent lam2 tau ((k : ℤ) - (q : ℤ)) := by
          unfold LD.boxesOfContent
          refine Finset.card_le_card_of_injOn (fun x => x.1) ?_ ?_
          · intro x hx
            rw [Finset.mem_coe, Finset.mem_filter, hs, Finset.mem_sigma, Finset.mem_Ico] at hx
            have h3 := x.1.isLt
            rw [Finset.mem_coe, Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_, ?_⟩ <;> dsimp only <;> omega
          · intro x hx y hy hxy
            rw [Finset.mem_coe, Finset.mem_filter] at hx hy
            have h3 := x.1.isLt
            have h4 := y.1.isLt
            obtain ⟨x1, x2⟩ := x
            obtain ⟨y1, y2⟩ := y
            simp only at hxy hx hy h3 h4
            subst hxy
            have : x2 = y2 := by omega
            rw [this]
      _ ≤ LD.mu p w i lam2 ((k : ℤ) - (q : ℤ)) := by
          unfold LD.mu
          exact Finset.le_sup (f := fun tau => LD.boxesOfContent lam2 tau ((k : ℤ) - (q : ℤ))) htau

end Formalism.CohomologicalDescent.Symmetrization

namespace Formalism.CohomologicalDescent.Symmetrization

theorem lowering_operators_commute : AAComm := AAComm_of symmetric_commute_abstract_holds jucys_murphy_commute_holds
theorem iteration_holds : Iteration := Iteration_of one_step_invariance_holds lowering_operators_commute symMap_equivariant_holds
theorem action_on_symmetric_holds : ActSpec := ActSpec_of symMap_equivariant_holds word_specification_holds
theorem iota_symMap_holds : IotaMu := IotaMu_of lowering_operators_commute symMap_equivariant_holds word_specification_holds iteration_holds
theorem action_lattice_holds : ActLattice := ActLattice_of symMap_equivariant_holds word_specification_holds
theorem lemma_d_skeleton_holds : LemmaDSkeleton :=
  LemmaDSkeleton_of coefficient_operators_hold x_lattice_holds x_weight_holds iota_weight_holds beta_dominant_holds action_lattice_holds
    integral_quotient_holds iota_symMap_holds action_on_symmetric_holds

end Formalism.CohomologicalDescent.Symmetrization
