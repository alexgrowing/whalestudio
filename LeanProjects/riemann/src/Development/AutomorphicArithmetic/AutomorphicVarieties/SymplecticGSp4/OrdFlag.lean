import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OrderedFlagDiagonal
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem UpperTheory.V.GradeZeroInterpolatingElement.ordFlag_diag {K : Type} [Field K] (c : Fin 4 → K) (hc : Function.Injective c) (X : M4 K)
    (h : X.charpoly = ∏ j, (Polynomial.X - Polynomial.C (c j))) :
    ∃ P : (M4 K)ˣ, X * (P : M4 K) = (P : M4 K) * Matrix.diagonal c :=
  _root_.UpperTheory.Reformulated.B.OrderedFlagDiagonal.ordFlag_diag c hc X h

private theorem UpperTheory.V.GradeZeroInterpolatingElement.ordFlag_aeval {K : Type} [Field K] (c : Fin 4 → K) (X P : M4 K)
    (h : X * P = P * Matrix.diagonal c) (p : Polynomial K) :
    Polynomial.aeval X p * P = P * Matrix.diagonal fun k => p.eval (c k) := by
  induction p using Polynomial.induction_on with
  | C a =>
    ext i j
    simp [Matrix.mul_diagonal, Algebra.algebraMap_eq_smul_one, mul_comm]
  | add p q hp hq =>
    rw [map_add, add_mul, hp, hq, ← mul_add, Matrix.diagonal_add]
    simp
  | monomial n a hn =>
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, mul_assoc, h, ← mul_assoc, hn, mul_assoc,
      Matrix.diagonal_mul_diagonal]
    simp

theorem UpperTheory.V.GradeZeroInterpolatingElement.ordFlag :
    ∀ {H : Type} [Group H] (I : Subgroup H) (K : Type) [Field K] (ps : Fin 4 → H → K) (s₀ : H) (r : H →* M4 K), Function.Injective (fun i => ps i s₀) → Ord I ps s₀ r → ∃ (u : (M4 K)ˣ) (κ : Fin 4 → H →* Kˣ), (∀ g i j, j < i → ((u : M4 K) * r g * (u⁻¹ : (M4 K)ˣ)) i j = 0) ∧ (∀ g i, ((u : M4 K) * r g * (u⁻¹ : (M4 K)ˣ)) i i = κ i g) ∧ (∀ i, ∀ s ∈ I, (κ i s : K) = ps i s) ∧ ∀ i g, (∏ j ∈ Finset.univ.erase i, (ps i s₀ - ps j s₀)) * (κ i g : K) = (prj (fun a => ps a s₀) (r s₀) i * r g).trace := by
  intro H _ I K _ ps s₀ r hc ho
  obtain ⟨P, hP⟩ := ordFlag_diag _ hc (r s₀) ho.charpoly
  set d : Fin 4 → K := fun i => ∏ j ∈ Finset.univ.erase i, (ps i s₀ - ps j s₀) with hd
  have hd0 : ∀ i, d i ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr fun e => (Finset.mem_erase.mp hj).1 (hc e).symm
  have hprj : ∀ i, prj (fun a => ps a s₀) (r s₀) i
      = (P : M4 K) * Matrix.diagonal (Pi.single i (d i)) * ((P⁻¹ : (M4 K)ˣ) : M4 K) := by
    intro i
    rw [Units.eq_mul_inv_iff_mul_eq, prj, ordFlag_aeval _ _ _ hP]
    congr 2
    funext k
    rw [Polynomial.eval_prod]
    by_cases hk : k = i
    · subst hk; simp [hd]
    · rw [Pi.single_eq_of_ne hk]
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩) (by simp)
  have key : ∀ (Y : M4 K) i j, prj (fun a => ps a s₀) (r s₀) i * Y * prj (fun a => ps a s₀) (r s₀) j = 0 →
      (((P⁻¹ : (M4 K)ˣ) : M4 K) * Y * (P : M4 K)) i j = 0 := by
    intro Y i j h
    have h2 : Matrix.diagonal (Pi.single i (d i)) * (((P⁻¹ : (M4 K)ˣ) : M4 K) * Y * (P : M4 K)) *
        Matrix.diagonal (Pi.single j (d j)) = 0 := by
      have := congrArg (fun Z : M4 K => ((P⁻¹ : (M4 K)ˣ) : M4 K) * Z * (P : M4 K)) h
      simpa [hprj, mul_assoc] using this
    have h3 := congrFun (congrFun h2 i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h3
    simpa [hd0] using h3
  set M : H → M4 K := fun g => ((P⁻¹ : (M4 K)ˣ) : M4 K) * r g * (P : M4 K) with hM
  have htri : ∀ g i j, j < i → M g i j = 0 := fun g i j hij => key _ i j (ho.stable g j i hij)
  have hmul : ∀ g h, M (g * h) = M g * M h := by
    intro g h
    simp [hM, mul_assoc]
  let κ₀ : Fin 4 → H →* K := fun i =>
    { toFun := fun g => M g i i
      map_one' := by simp [hM]
      map_mul' := by
        intro g h
        rw [hmul, Matrix.mul_apply]
        refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
        rcases lt_or_gt_of_ne hk with hk | hk
        · rw [htri g i k hk, zero_mul]
        · rw [htri h k i hk, mul_zero] }
  refine ⟨P⁻¹, fun i => (κ₀ i).toHomUnits, ?_, ?_, ?_, ?_⟩
  · intro g i j hij
    rw [inv_inv]
    exact htri g i j hij
  · intro g i
    rw [inv_inv]
    rfl
  · intro i s hs
    have h1 := key _ i i (ho.inert s hs i)
    rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, Units.inv_mul, Matrix.sub_apply, sub_eq_zero] at h1
    show M s i i = _
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h1
    exact h1
  · intro i g
    show d i * M g i i = _
    rw [hprj, mul_assoc, mul_assoc, Matrix.trace_mul_comm, mul_assoc]
    show _ = (Matrix.diagonal (Pi.single i (d i)) * M g).trace
    simp [Matrix.trace, Matrix.diagonal_mul, Pi.single_apply]
