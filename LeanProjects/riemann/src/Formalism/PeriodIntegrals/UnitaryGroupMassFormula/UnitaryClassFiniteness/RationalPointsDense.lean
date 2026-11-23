import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.IsIntegralOfIntOE

noncomputable section

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

namespace PI.UnitaryGroupMassFormula.UJClassFin

open PI.UJClassFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}

theorem single_tmul (l : Fin M) (a : Af F) (t : E) :
    Pi.single l (a ⊗ₜ[F] t) = fun i => a ⊗ₜ[F] ((Pi.single l t : Fin M → E) i) := by
  funext i
  by_cases h : i = l
  · subst h
    simp
  · simp [Pi.single_apply, h]

theorem nsmul_tmul_F (N : ℕ) (a : Af F) (e : E) : N • (a ⊗ₜ[F] e) = a ⊗ₜ[F] ((N : F) • e) := by
  first
  | (rw [Nat.cast_smul_eq_nsmul, TensorProduct.tmul_smul])
  | (induction N with
      | zero => simp
      | succ n ih => simp [succ_nsmul, ih, add_smul, TensorProduct.tmul_add])

theorem mulVec_single' (g : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) (j : Fin M) (x : Af F ⊗[F] E) :
    g.mulVec (Pi.single j x) = fun l => g l j * x := by
  funext l
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem latHat_smul (L : Set (Fin M → E)) {a : Af F} (ha : a ∈ intAf F) {y : Fin M → Af F ⊗[F] E}
    (hy : y ∈ latHat F E L) : (a ⊗ₜ[F] (1 : E)) • y ∈ latHat F E L := by
  unfold latHat at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    have hmul : a * a' ∈ intAf F := by
      unfold intAf at ha ha' ⊢
      intro v
      rw [map_mul]
      exact mul_mem (ha v) (ha' v)
    refine ⟨a * a', hmul, x, hx, ?_⟩
    funext i
    simp [Pi.smul_apply, Algebra.TensorProduct.tmul_mul_tmul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y1 y2 _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg y _ h => rw [smul_neg]; exact neg_mem h

theorem single_mem (L : Set (Fin M → E)) {k : ℕ}
    (hk : ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ L)
    {p : Af F ⊗[F] E} (hp : p ∈ Oh F E) (l : Fin M) : Pi.single l (k • p) ∈ latHat F E L := by
  let S' : AddSubgroup (Af F ⊗[F] E) :=
    { carrier := {q | Pi.single l (k • q) ∈ latHat F E L}
      add_mem' := fun {a b} ha hb => by
        show Pi.single l (k • (a + b)) ∈ latHat F E L
        rw [smul_add, Pi.single_add]
        exact add_mem ha hb
      zero_mem' := by
        show Pi.single l (k • (0 : Af F ⊗[F] E)) ∈ latHat F E L
        rw [smul_zero, Pi.single_zero]
        exact zero_mem _
      neg_mem' := fun {a} ha => by
        show Pi.single l (k • (-a)) ∈ latHat F E L
        rw [smul_neg, Pi.single_neg]
        exact neg_mem ha }
  have hsub : {r : Af F ⊗[F] E | ∃ a ∈ intAf F, ∃ e : E, IsIntegral ℤ e ∧ r = a ⊗ₜ[F] e} ⊆
      (S' : Set _) := by
    rintro r ⟨a, ha, e, he, rfl⟩
    show Pi.single l (k • (a ⊗ₜ[F] e)) ∈ latHat F E L
    rw [nsmul_tmul_F, single_tmul]
    unfold latHat
    exact AddSubgroup.subset_closure ⟨a, ha, Pi.single l ((k : F) • e), hk l e he, rfl⟩
  exact (AddSubgroup.closure_le S').mpr hsub hp

theorem rational_points_dense : RatDense := by
  intro F E _ _ _ _ _ σ M J L _h4 h5 h y
  classical
  obtain ⟨k, hk, hkL⟩ := low_nat L h5
  set g' := finMat σ J h⁻¹ with hg'
  have hden : ∃ m : ℕ, 0 < m ∧ ∀ l j, m • g' l j ∈ Oh F E := by
    choose mf hmf hmO using fun p : Fin M × Fin M => den (g' p.1 p.2)
    refine ⟨∏ p, mf p, Finset.prod_pos (fun p _ => hmf p), fun l j => ?_⟩
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem mf (Finset.mem_univ (l, j))
    rw [hq, mul_comm, mul_smul]
    exact AddSubgroup.nsmul_mem _ (hmO (l, j)) _
  obtain ⟨m, hm, hmO⟩ := hden
  have K1 : ∀ o ∈ Oh F E, ∀ j, g'.mulVec (Pi.single j ((k * m) • o)) ∈ latHat F E L := by
    intro o ho j
    rw [mulVec_single']
    have : (fun l => g' l j * ((k * m) • o)) = ∑ l, Pi.single l (k • ((m • g' l j) * o)) := by
      rw [Finset.univ_sum_single (fun l => k • ((m • g' l j) * o))]
      funext l
      rw [mul_smul_comm, smul_mul_assoc, smul_smul]
    rw [this]
    exact AddSubgroup.sum_mem _ (fun l _ => single_mem L hkL (Oh_mul (hmO l j) ho) l)
  have SL : ∀ p ∈ Oh F E, ∀ j, Pi.single j ((k * m) • p) ∈ latHat F E (abelian₂ σ J L h) := by
    intro p hp j
    induction hp using AddSubgroup.closure_induction with
    | mem p hp =>
      obtain ⟨a, ha, e, he, rfl⟩ := hp
      rw [nsmul_tmul_F, single_tmul]
      refine AddSubgroup.subset_closure ⟨a, ha, _, ?_, rfl⟩
      show g'.mulVec (vinc (Pi.single j (((k * m : ℕ) : F) • e))) ∈ latHat F E L
      have hv : vinc (F := F) (Pi.single j (((k * m : ℕ) : F) • e)) = Pi.single j ((k * m) • ((1 : Af F) ⊗ₜ[F] e)) := by
        rw [nsmul_tmul_F, single_tmul]
        rfl
      rw [hv]
      exact K1 _ (tmul_mem_Oh intAf_one he) j
    | zero => rw [smul_zero, Pi.single_zero]; exact zero_mem _
    | add p q _ _ h1 h2 => rw [smul_add, Pi.single_add]; exact add_mem h1 h2
    | neg p _ h1 => rw [smul_neg, Pi.single_neg]; exact neg_mem h1
  constructor
  · intro hy
    choose e o ho hyo using fun j => approx (F := F) (k * m) (Nat.mul_pos hk hm) (y j)
    have hyw : y = vinc (F := F) e + ∑ j, Pi.single j ((k * m) • o j) := by
      rw [Finset.univ_sum_single (fun j => (k * m) • o j)]
      funext j
      exact hyo j
    have hwsum : g'.mulVec (∑ j, Pi.single j ((k * m) • o j)) ∈ latHat F E L := by
      rw [Matrix.mulVec_sum]
      exact AddSubgroup.sum_mem _ (fun j _ => K1 _ (ho j) j)
    have he : e ∈ abelian₂ σ J L h := by
      show g'.mulVec (vinc e) ∈ latHat F E L
      have : vinc (F := F) e = y - ∑ j, Pi.single j ((k * m) • o j) := by
        conv_rhs => rw [hyw]
        abel
      rw [this, Matrix.mulVec_sub]
      exact sub_mem hy hwsum
    rw [hyw]
    refine add_mem (AddSubgroup.subset_closure ⟨1, intAf_one, e, he, rfl⟩) ?_
    exact AddSubgroup.sum_mem _ (fun j _ => SL _ (ho j) j)
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      have hx' : g'.mulVec (vinc x) ∈ latHat F E L := hx
      have : (fun i => a ⊗ₜ[F] x i) = (a ⊗ₜ[F] (1 : E)) • vinc (F := F) x := by
        funext i
        simp [vinc, inclR, Algebra.TensorProduct.tmul_mul_tmul]
      rw [this, Matrix.mulVec_smul]
      exact latHat_smul L ha hx'
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add y z _ _ h1 h2 => rw [Matrix.mulVec_add]; exact add_mem h1 h2
    | neg y _ h1 => rw [Matrix.mulVec_neg]; exact neg_mem h1

end PI.UnitaryGroupMassFormula.UJClassFin
