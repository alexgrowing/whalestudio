import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem corner_eq {R : Type} [CommRing R] {n : ℕ} {E : Type} [Ring E] [Algebra R E] {τ : E →ₗ[R] R}
    {e : Fin n → E} (h : IsTrGMA τ e) (i : Fin n) (z : E) (hz : e i * z * e i = z) : z = τ z • e i := by
  have hidem : e i * e i = e i := (h.idem.idem i).eq
  have h1 : e i * z = z := by
    calc e i * z = e i * (e i * z * e i) := by rw [hz]
      _ = e i * z * e i := by rw [← mul_assoc, ← mul_assoc, hidem]
      _ = z := hz
  calc z = e i * z * e i := hz.symm
    _ = τ (e i * z) • e i := h.corner i z
    _ = τ z • e i := by rw [h1]

private theorem tr_single {O : Type} [CommRing O] {n : ℕ} (o i j : Fin n) (c : O) (A : Matrix (Fin n) (Fin n) O) :
    ((c • Matrix.single o i (1 : O)) * A * (c • Matrix.single j o (1 : O))).trace = c ^ 2 * A i j := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.single_mul_mul_single]
  simp [Matrix.trace_smul, pow_two, mul_assoc]

theorem UpperTheory.V.Th.Coc.smat :
    ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {n : ℕ} {E : Type} [Ring E] [Algebra R E] (x : R →ₐ[O] O) (ρ : E →+* Matrix (Fin n) (Fin n) O) (τ : E →ₗ[R] R) (e : Fin n → E) (c : O), 1 ≤ n → IsTrGMA τ e → (∀ i, ρ (e i) = Matrix.single i i 1) → (∀ a, (ρ a).trace = x (τ a)) → (∀ Z, ∃ a, ρ a = c • Z) → ∃ (s : E →ₗ[R] Matrix (Fin n) (Fin n) R) (β : R), x β = c ^ (2 * n) ∧ (∀ a b, s a * s b = β • s (a * b)) ∧ (∀ a, (s a).map x = c ^ (2 * n) • ρ a) ∧ ∀ a, (s a).trace = β * τ a := by
  intro O R _ _ _ n E _ _ x ρ τ e c hn hT hρe htr hsurj
  classical
  obtain ⟨o, -⟩ : ∃ o : Fin n, True := ⟨⟨0, hn⟩, trivial⟩
  have hidem : ∀ i, e i * e i = e i := fun i => (hT.idem.idem i).eq
  have hρE : ∀ (i j : Fin n) (r : O), Matrix.single i i (1 : O) * (r • Matrix.single i j (1 : O)) *
      Matrix.single j j (1 : O) = r • Matrix.single i j (1 : O) := by
    intro i j r
    ext u v
    simp only [Matrix.single_mul_mul_single, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs <;> simp_all
  choose hh hhρ using fun i : Fin n => hsurj (Matrix.single o i (1 : O))
  choose kk kkρ using fun j : Fin n => hsurj (Matrix.single j o (1 : O))
  obtain ⟨p, hp⟩ : ∃ p : Fin n → E, ∀ i, p i = e o * hh i * e i := ⟨_, fun _ => rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : Fin n → E, ∀ j, q j = e j * kk j * e o := ⟨_, fun _ => rfl⟩
  have ρp : ∀ i, ρ (p i) = c • Matrix.single o i (1 : O) := by
    intro i
    simp only [hp, map_mul, hρe, hhρ]
    exact hρE o i c
  have ρq : ∀ j, ρ (q j) = c • Matrix.single j o (1 : O) := by
    intro j
    simp only [hq, map_mul, hρe, kkρ]
    exact hρE j o c
  have hpl : ∀ i, e o * p i = p i := by
    intro i
    simp only [hp, ← mul_assoc, hidem]
  have hpr : ∀ i, p i * e i = p i := by
    intro i
    simp only [hp, mul_assoc, hidem]
  have hql : ∀ j, e j * q j = q j := by
    intro j
    simp only [hq, ← mul_assoc, hidem]
  have hqr : ∀ j, q j * e o = q j := by
    intro j
    simp only [hq, mul_assoc, hidem]
  have hcorner : ∀ i z, e i * z * e i = z → z = τ z • e i := fun i z hz => corner_eq hT i z hz
  obtain ⟨γ, hγ⟩ : ∃ γ : Fin n → R, ∀ j, γ j = τ (q j * p j) := ⟨_, fun _ => rfl⟩
  have hqp : ∀ j, q j * p j = γ j • e j := by
    intro j
    rw [hγ]
    apply hcorner
    rw [← mul_assoc, hql, mul_assoc, hpr]
  have hxγ : ∀ j, x (γ j) = c ^ 2 := by
    intro j
    rw [hγ, ← htr, map_mul, ρq, ρp]
    have h := tr_single j o o c (1 : Matrix (Fin n) (Fin n) O)
    rw [Matrix.mul_one, Matrix.one_apply_eq, mul_one] at h
    exact h
  have hρs : ∀ r : R, ρ (r • e o) = Matrix.single o o (x r) := by
    intro r
    have hz : e o * (r • e o) * e o = r • e o := by
      rw [mul_smul_comm, smul_mul_assoc, hidem, hidem]
    have h1 : ρ (r • e o) = Matrix.single o o ((ρ (r • e o)) o o) := by
      conv_lhs => rw [← hz]
      rw [map_mul, map_mul, hρe, Matrix.single_mul_mul_single, one_mul, mul_one]
    have h2 : (ρ (r • e o)).trace = x r := by
      rw [htr, map_smul, hT.one, smul_eq_mul, mul_one]
    rw [h1] at h2 ⊢
    congr 1
    simpa [Matrix.trace, Matrix.single_apply] using h2
  obtain ⟨Γj, hΓj⟩ : ∃ Γj : Fin n → R, ∀ j, Γj j = ∏ l ∈ Finset.univ.erase j, γ l := ⟨_, fun _ => rfl⟩
  obtain ⟨q', hq'⟩ : ∃ q' : Fin n → E, ∀ j, q' j = q j * (Γj j • e o) := ⟨_, fun _ => rfl⟩
  have hq'p : ∀ j, q' j * p j = (∏ l, γ l) • e j := by
    intro j
    rw [hq', mul_smul_comm, smul_mul_assoc, hqr, hqp, smul_smul, hΓj,
      Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  have hsum : ∑ j, q' j * p j = (∏ l, γ l) • (1 : E) := by
    simp_rw [hq'p]
    rw [← Finset.smul_sum, hT.idem.complete]
  have hq'r : ∀ j, q' j * e o = q' j := by
    intro j
    rw [hq', mul_assoc, smul_mul_assoc, hidem]
  have hX : ∀ i j a, p i * a * q' j = τ (p i * a * q' j) • e o := by
    intro i j a
    apply hcorner
    have h : e o * (p i * a * q' j) * e o = (e o * p i) * a * (q' j * e o) := by simp only [mul_assoc]
    rw [h, hpl, hq'r]
  have hτmul : ∀ i k j a b, τ (p i * a * q' k) * τ (p k * b * q' j) =
      τ (p i * a * q' k * (p k * b * q' j)) := by
    intro i k j a b
    have hl : e o * (p k * b * q' j) = p k * b * q' j := by simp only [← mul_assoc, hpl]
    conv_rhs => rw [hX i k a, smul_mul_assoc, hl, map_smul, smul_eq_mul]
  have hρq' : ∀ j, ρ (q' j) = x (Γj j) • (c • Matrix.single j o (1 : O)) := by
    intro j
    rw [hq', map_mul, ρq, hρs]
    ext u v
    simp only [Matrix.smul_mul, Matrix.single_mul_single_same, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs <;> ring
  have hxΓj : ∀ j, x (Γj j) = (c ^ 2) ^ (n - 1) := by
    intro j
    rw [hΓj, map_prod]
    simp_rw [hxγ]
    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  let s : E →ₗ[R] Matrix (Fin n) (Fin n) R :=
    { toFun := fun a => Matrix.of fun i j => τ (p i * a * q' j)
      map_add' := by
        intro a b
        ext i j
        simp only [Matrix.of_apply, Matrix.add_apply, mul_add, add_mul, map_add]
      map_smul' := by
        intro r a
        ext i j
        simp only [Matrix.of_apply, Matrix.smul_apply, mul_smul_comm, smul_mul_assoc, map_smul,
          RingHom.id_apply] }
  have hs : ∀ a i j, s a i j = τ (p i * a * q' j) := fun _ _ _ => rfl
  refine ⟨s, ∏ l, γ l, ?_, ?_, ?_, ?_⟩
  · rw [map_prod]
    simp_rw [hxγ]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  · intro a b
    ext i j
    rw [Matrix.mul_apply, Matrix.smul_apply, hs, smul_eq_mul]
    simp_rw [hs, hτmul]
    rw [← map_sum]
    have hrw : ∑ k, p i * a * q' k * (p k * b * q' j) = p i * a * (∑ k, q' k * p k) * b * q' j := by
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by simp only [mul_assoc]
    rw [hrw, hsum, mul_smul_comm, mul_one, smul_mul_assoc, smul_mul_assoc, map_smul, smul_eq_mul,
      mul_assoc (p i) a b]
  · intro a
    ext i j
    rw [Matrix.map_apply, hs, Matrix.smul_apply, smul_eq_mul, ← htr, map_mul, map_mul, ρp, hρq',
      Matrix.mul_smul, Matrix.trace_smul, tr_single, smul_eq_mul, hxΓj, ← mul_assoc, ← pow_succ,
      ← pow_mul, Nat.sub_add_cancel hn]
  · intro a
    have hc : ∀ i, τ (p i * a * q' i) = τ (a * (q' i * p i)) := by
      intro i
      rw [mul_assoc, hT.comm, mul_assoc]
    simp only [Matrix.trace, Matrix.diag_apply, hs, hc]
    rw [← map_sum, ← Finset.mul_sum, hsum, mul_smul_comm, mul_one, map_smul, smul_eq_mul]
