import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.OddDiag
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UpperTriangularMul
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem lower_entries_zero_of_commuting_triangular {K ι : Type} [Field K] {n : ℕ} (T : ι → Matrix (Fin n) (Fin n) K)
    (Y : Matrix (Fin n) (Fin n) K) (hT : ∀ g i j, j < i → T g i j = 0)
    (hd : ∀ i j, i ≠ j → ∃ g, T g i i ≠ T g j j)
    (hc : ∀ g i j, j < i → (T g * Y) i j = (Y * T g) i j) :
    ∀ (m : ℕ) (i j : Fin n), (n - (i : ℕ)) + (j : ℕ) = m → j < i → Y i j = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i j hm hji
    obtain ⟨g, hg⟩ := hd i j (ne_of_gt hji)
    have h1 : (T g * Y) i j = T g i i * Y i j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with h | h
        · rw [hT g i k h, zero_mul]
        · have hk' : (i : ℕ) < k := h
          have := k.2
          rw [ih ((n - (k : ℕ)) + (j : ℕ)) (by omega) k j rfl (hji.trans h), mul_zero]
      · simp
    have h2 : (Y * T g) i j = Y i j * T g j j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single j]
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with h | h
        · have hk' : (k : ℕ) < j := h
          rw [ih ((n - (i : ℕ)) + (k : ℕ)) (by omega) i k rfl (h.trans hji), zero_mul]
        · rw [hT g k j h, mul_zero]
      · simp
    have h3 := hc g i j hji
    rw [h1, h2] at h3
    have h4 : (T g i i - T g j j) * Y i j = 0 := by linear_combination h3
    exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 hg)

private theorem upper_triangular_mul {K : Type} [Field K] {n : ℕ} (U T : Matrix (Fin n) (Fin n) K)
    (hU : ∀ i j, j < i → U i j = 0) (hT : ∀ i j, j < i → T i j = 0) :
    ∀ i j, j < i → (U * T) i j = 0 :=
  _root_.UpperTheory.Reformulated.B.Qe38.upper_triangular_mul U T hU hT

private theorem conjugate_commutator_identity {K : Type} [Field K] {n : ℕ} (w wi r r' Y : Matrix (Fin n) (Fin n) K)
    (h1 : w * wi = 1) (h2 : r' * r = 1) :
    (wi * (r * Y * r' - Y) * w) * (wi * r * w) =
      (wi * r * w) * (wi * Y * w) - (wi * Y * w) * (wi * r * w) := by
  have e1 : ∀ M : Matrix (Fin n) (Fin n) K, w * (wi * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have e2 : ∀ M : Matrix (Fin n) (Fin n) K, r' * (r * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, e1, e2]

theorem UpperTheory.V.Pa.localInvariants_eq_zero :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (v : L.Vl) (Y : Matrix (Fin n) (Fin n) x.Fr), (∀ g i j, j < i → (x.wiX x.Fr v * dY G0.frame (x.ρX x.Fr) Y (G0.φ v g) * x.wX x.Fr v) i j = 0) → ∀ i j, j < i → (x.wiX x.Fr v * Y * x.wX x.Fr v) i j = 0 := by
  intro l _ L G G0 h n x v Y H i j hij
  obtain ⟨h1, -, -, h4, h5, h6, -, -⟩ := UpperTheory.V.Pa.oddDiag l L G G0 h n x x.Fr v
  refine lower_entries_zero_of_commuting_triangular (fun g : L.Gv v => x.wiX x.Fr v * x.ρX x.Fr (G0.φ v g) * x.wX x.Fr v)
    (x.wiX x.Fr v * Y * x.wX x.Fr v) (fun g => (h4 g).1) ?_ ?_ _ i j rfl hij
  · intro a b hab
    by_contra hcon
    push Not at hcon
    refine (x.N1 v).1 a b hab (MonoidHom.ext fun g => Units.ext ?_)
    have := hcon g
    rw [(h4 g).2 a, (h4 g).2 b] at this
    exact IsFractionRing.injective x.A x.Fr this
  · intro g a b hab
    have hinv : x.ρX x.Fr (G0.φ v g)⁻¹ * x.ρX x.Fr (G0.φ v g) = 1 := by
      rw [← h5, inv_mul_cancel, h6]
    have e := conjugate_commutator_identity (x.wX x.Fr v) (x.wiX x.Fr v) _ _ Y h1 hinv
    have z := upper_triangular_mul _ _ (H g) (h4 g).1 a b hab
    unfold dY at z
    rw [e, Matrix.sub_apply] at z
    exact sub_eq_zero.1 z
