import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableComb
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.AdaptedBasis

theorem exists_denominator {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] (κ : ι → K) :
    ∃ R : ℕ, 0 < R ∧ ∃ a : ι → 𝓞 K, ∀ i, (a i : K) = (R : K) * κ i := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := K) (Finset.univ.image κ)
  have h' : ∀ i, IsIntegral ℤ (((y.natAbs : ℕ) : K) * κ i) := by
    intro i
    have hi := h (κ i) (Finset.mem_image_of_mem κ (Finset.mem_univ i))
    rw [zsmul_eq_mul] at hi
    rcases Int.natAbs_eq y with e | e
    · have : ((y.natAbs : ℕ) : K) = (y : K) := by
        conv_rhs => rw [e]
        simp only [Int.cast_natCast]
      rw [this]; exact hi
    · have : ((y.natAbs : ℕ) : K) = -(y : K) := by
        conv_rhs => rw [e]
        simp only [Int.cast_neg, Int.cast_natCast, neg_neg]
      rw [this, neg_mul]; exact hi.neg
  exact ⟨y.natAbs, Int.natAbs_pos.2 hy, fun i => ⟨_, h' i⟩, fun i => rfl⟩

theorem embV_sum (D : D7) (T : Tor D) (h0 : ∀ τ, T.emb τ 0 = 0)
    (hadd : ∀ τ x y, T.emb τ (x + y) = T.emb τ x + T.emb τ y)
    (hmul : ∀ τ (a : D.host.K) y, T.emb τ ((a : D.host.E) * y) = D.host.φ₀ (a : D.host.E) * T.emb τ y)
    {N N' r : ℕ} (B : Fin r → Matrix (Fin N') (Fin N) D.host.E) (κ : Fin r → D.host.K) :
    embV D T (∑ i, κ i • B i) = ∑ i, D.host.φ₀ (κ i : D.host.E) • embV D T (B i) := by
  funext τ p q
  let f : D.host.E →+ ℂ := ⟨⟨T.emb τ, h0 τ⟩, hadd τ⟩
  have e : (∑ i, κ i • B i) p q = ∑ i, (κ i : D.host.E) * B i p q := by
    rw [Matrix.sum_apply]
    rfl
  have e2 : T.emb τ (∑ i, (κ i : D.host.E) * B i p q) = ∑ i, T.emb τ ((κ i : D.host.E) * B i p q) :=
    map_sum f _ _
  simp only [embV, e, e2, hmul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem liftM_of_mem (M : IntermediateField ℚ ℂ) {x : ℂ} (h : x ∈ M) : liftM M x = ⟨x, h⟩ := dif_pos h

theorem sum_smul_comm {V : Type*} [AddCommGroup V] [Module ℂ V] {r s : ℕ} (c : Fin s → ℂ) (k : Fin s → Fin r → ℂ)
    (v : Fin r → V) : ∑ j, c j • ∑ i, k j i • v i = ∑ i, (∑ j, k j i * c j) • v i := by
  simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem rationalLatticePoint_add {Λ : AddSubgroup ℂ} {x y : ℂ} (hx : InRationalLattice Λ x) (hy : InRationalLattice Λ y) : InRationalLattice Λ (x + y) := by
  obtain ⟨m, hm, hx⟩ := hx
  obtain ⟨n, hn, hy⟩ := hy
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  have : ((m * n : ℕ) : ℂ) * (x + y) = n • ((m : ℂ) * x) + m • ((n : ℂ) * y) := by
    simp only [nsmul_eq_mul]; push_cast; ring
  rw [this]
  exact Λ.add_mem (Λ.nsmul_mem hx n) (Λ.nsmul_mem hy m)

theorem adpB_of_family : ∀ (D : D7), admG1 D → galStar D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), FixK D M ρ → DataIn D (tor0 D cc δ) M → ∀ (N N' r s : ℕ) (B : Fin r → Matrix (Fin N') (Fin N) D.host.E) (b : Fin s → Matrix (Fin N') (Fin N) D.host.E), OnB D B → ∃ R : ℕ, 0 < R ∧ ∀ (n : ℕ) (c c' : Fin s → ℂ), 0 < n → (∀ j, InRationalLattice (lamOf D cc δ) (c j)) → (∀ j, Adp1 M ρ (lamOf D cc δ) (n * R) (c j) (c' j)) → AdpB D (tor0 D cc δ) M ρ B n (∑ j, c j • embV D (tor0 D cc δ) (b j)) (∑ j, c' j • embV D (torConj D (tor0 D cc δ) M ρ) (b j)) := by
  intro D hG hS cc δ hC M ρ hF hD N N' r s B b hB
  have hspan : ∀ j, ∃ κ : Fin r → D.host.K, ∑ i, κ i • B i = b j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun D.host.K).1 (by rw [hB.2]; trivial)
  choose κ hκ using hspan
  obtain ⟨R, hR, a, ha⟩ := exists_denominator (fun p : Fin s × Fin r => κ p.1 p.2)
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have haφ : ∀ j i, D.host.φ₀ (((a (j, i) : D.host.K) : D.host.E)) = R * D.host.φ₀ (κ j i : D.host.E) := by
    intro j i
    rw [ha]
    push_cast
    rw [map_mul, map_natCast]
  have hΛ := (GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hC).2.2.2.2
  obtain ⟨-, -, -, hadd, hmul, -⟩ := hS cc δ hC M ρ hF hD.2.1 hD.2.2
  have hM : ∀ τ x, embT D τ x ∈ M := hD.1
  have hψ := hG.1
  have e1 : ∀ j, embV D (tor0 D cc δ) (b j) =
      ∑ i, D.host.φ₀ (κ j i : D.host.E) • embV D (tor0 D cc δ) (B i) := by
    intro j
    rw [← hκ j]
    refine embV_sum D _ (fun τ => map_zero (embT D τ)) (fun τ => map_add (embT D τ)) (fun τ k y => ?_) B _
    show embT D τ _ = _ * embT D τ y
    rw [map_mul, hψ]
  have e2 : ∀ j, embV D (torConj D (tor0 D cc δ) M ρ) (b j) =
      ∑ i, D.host.φ₀ (κ j i : D.host.E) • embV D (torConj D (tor0 D cc δ) M ρ) (B i) := by
    intro j
    rw [← hκ j]
    refine embV_sum D _ (fun τ => ?_) (fun τ x y => ?_) (fun τ k y => ?_) B _
    · show ρ (liftM M (embT D τ 0)) = 0
      rw [map_zero, liftM_of_mem M (zero_mem M)]
      exact map_zero ρ
    · show ρ (liftM M (embT D τ (x + y))) = ρ (liftM M (embT D τ x)) + ρ (liftM M (embT D τ y))
      rw [liftM_of_mem M (hM τ _), liftM_of_mem M (hM τ _), liftM_of_mem M (hM τ _), ← map_add ρ]
      congr 1
      exact Subtype.ext (map_add (embT D τ) x y)
    · show ρ (liftM M (embT D τ (_ * y))) = _ * ρ (liftM M (embT D τ y))
      rw [← (hF k).2, cj, liftM_of_mem M (hM τ _), liftM_of_mem M (hM τ _), liftM_of_mem M (hF k).1, ← map_mul ρ]
      congr 1
      apply Subtype.ext
      show embT D τ (_ * y) = D.host.φ₀ _ * embT D τ y
      rw [map_mul, hψ]
  refine ⟨R, hR, fun n c c' hn hc hA => ⟨fun i => ∑ j, D.host.φ₀ (κ j i : D.host.E) * c j,
    fun i => ∑ j, D.host.φ₀ (κ j i : D.host.E) * c' j, fun i => ?_, ?_, ?_, fun i => ?_⟩⟩
  · refine Finset.sum_induction _ (InRationalLattice (lamOf D cc δ)) (fun x y => rationalLatticePoint_add)
      ⟨1, one_pos, by simp⟩ (fun j _ => ?_)
    obtain ⟨m, hm, hj⟩ := hc j
    refine ⟨R * m, Nat.mul_pos hR hm, ?_⟩
    have := hΛ (a (j, i)) _ hj
    rw [haφ] at this
    convert this using 1
    push_cast; ring
  · simp only [e1]; exact sum_smul_comm _ _ _
  · simp only [e2]; exact sum_smul_comm _ _ _
  · have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have key : ∀ t : Finset (Fin s), StarPt M ρ (lamOf D cc δ)
        ((∑ j ∈ t, D.host.φ₀ (κ j i : D.host.E) * c j) / n) ((∑ j ∈ t, D.host.φ₀ (κ j i : D.host.E) * c' j) / n) := by
      intro t
      induction t using Finset.induction_on with
      | empty => left; simp
      | insert j t hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj, add_div, add_div]
        refine hadd _ _ _ _ ?_ ih
        have := hmul (a (j, i)) _ _ (hA j)
        rw [haφ] at this
        convert this using 1 <;> (push_cast; field_simp)
    exact key Finset.univ

end GlobalTheory.AdaptedBasis
