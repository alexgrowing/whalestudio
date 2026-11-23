import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlIntertwinerOfResidualSpanEqTop

namespace GlobalTheory.TraceConj

open IsLocalRing

theorem ker_le_ker_of_trace_eq {Γ R : Type} [Monoid Γ] [CommRing R] {n : ℕ}
    (M N : Γ →* Matrix (Fin n) (Fin n) R) (h : ∀ g, (M g).trace = (N g).trace)
    (hN : Submodule.span R (Set.range N) = ⊤) :
    LinearMap.ker (Finsupp.linearCombination R (fun g => M g)) ≤
      LinearMap.ker (Finsupp.linearCombination R (fun g => N g)) := by
  classical
  set a := Finsupp.linearCombination R (fun g => M g) with ha
  set b := Finsupp.linearCombination R (fun g => N g) with hb
  have hab : ∀ c g, (a c * M g).trace = (b c * N g).trace := by
    intro c g
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, add_mul, add_mul, Matrix.trace_add, Matrix.trace_add, hx, hy]
    | single x c =>
      simp only [ha, hb, Finsupp.linearCombination_single, Matrix.smul_mul, Matrix.trace_smul, ← map_mul, h]
  intro c hc
  rw [LinearMap.mem_ker] at hc ⊢
  have h1 : ∀ Y ∈ Submodule.span R (Set.range N), (b c * Y).trace = 0 := by
    intro Y hY
    induction hY using Submodule.span_induction with
    | mem Y hY => obtain ⟨g, rfl⟩ := hY; rw [← hab, hc]; simp
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, Matrix.trace_add, hx, hy, add_zero]
    | smul t x _ hx => rw [Matrix.mul_smul, Matrix.trace_smul, hx, smul_zero]
  ext p q
  have := h1 (Matrix.single q p 1) (hN ▸ Submodule.mem_top)
  rw [Matrix.trace_mul_single] at this
  simpa using this

theorem span_top_of_trace_eq {Γ K : Type} [Monoid Γ] [Field K] {n : ℕ}
    (M N : Γ →* Matrix (Fin n) (Fin n) K) (h : ∀ g, (M g).trace = (N g).trace)
    (hN : Submodule.span K (Set.range N) = ⊤) : Submodule.span K (Set.range M) = ⊤ := by
  classical
  let a := Finsupp.linearCombination K (fun g => M g)
  let b := Finsupp.linearCombination K (fun g => N g)
  have hker : LinearMap.ker a ≤ LinearMap.ker b := ker_le_ker_of_trace_eq M N h hN
  have hb : LinearMap.range b = ⊤ := by rw [Finsupp.range_linearCombination]; exact hN
  let f : LinearMap.range a →ₗ[K] Matrix (Fin n) (Fin n) K :=
    ((LinearMap.ker a).liftQ b hker).comp a.quotKerEquivRange.symm.toLinearMap
  have hf : Function.Surjective f := by
    intro Y
    obtain ⟨c, rfl⟩ := LinearMap.range_eq_top.1 hb Y
    refine ⟨a.quotKerEquivRange (Submodule.Quotient.mk c), ?_⟩
    simp [f]
  have hle := LinearMap.finrank_le_finrank_of_surjective hf
  have := Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) hle)
  rwa [Finsupp.range_linearCombination] at this

theorem span_top_of_residual {Γ O : Type} [CommRing O] [IsLocalRing O] {n : ℕ}
    (M : Γ → Matrix (Fin n) (Fin n) O)
    (h : Submodule.span (ResidueField O) (Set.range fun g => (M g).map (residue O)) = ⊤) :
    Submodule.span O (Set.range M) = ⊤ := by
  classical
  have lift : ∀ Z ∈ Submodule.span (ResidueField O) (Set.range fun g => (M g).map (residue O)),
      ∃ Y ∈ Submodule.span O (Set.range M), Y.map (residue O) = Z := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem Z hZ => obtain ⟨g, rfl⟩ := hZ; exact ⟨M g, Submodule.subset_span ⟨g, rfl⟩, rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hy
      exact ⟨x + y, Submodule.add_mem _ hx hy, by ext; simp⟩
    | smul t x _ hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨t, rfl⟩ := residue_surjective t
      exact ⟨t • x, Submodule.smul_mem _ _ hx, by ext; simp⟩
  rw [eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal O) Module.Finite.fg_top
    (maximalIdeal_le_jacobson _) fun X _ => ?_
  obtain ⟨Y, hY, hYX⟩ := lift (X.map (residue O)) (h ▸ Submodule.mem_top)
  rw [← add_sub_cancel Y X]
  refine Submodule.add_mem_sup hY ?_
  rw [Matrix.matrix_eq_sum_single (X - Y)]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have e : Matrix.single i j ((X - Y) i j) = (X - Y) i j • Matrix.single i j (1 : O) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e]
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  rw [← residue_eq_zero_iff, Matrix.sub_apply, map_sub, sub_eq_zero]
  exact (congrFun (congrFun hYX i) j).symm

theorem exists_linearMap_of_trace_eq {Γ R : Type} [Monoid Γ] [CommRing R] {n : ℕ}
    (M N : Γ →* Matrix (Fin n) (Fin n) R) (h : ∀ g, (M g).trace = (N g).trace)
    (hM : Submodule.span R (Set.range M) = ⊤) (hN : Submodule.span R (Set.range N) = ⊤) :
    ∃ φ : Matrix (Fin n) (Fin n) R →ₗ[R] Matrix (Fin n) (Fin n) R, φ 1 = 1 ∧ ∀ g X, φ (M g * X) = N g * φ X := by
  classical
  let a := Finsupp.linearCombination R (fun g => M g)
  let b := Finsupp.linearCombination R (fun g => N g)
  have hker : LinearMap.ker a ≤ LinearMap.ker b := ker_le_ker_of_trace_eq M N h hN
  have ha : Function.Surjective a := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]; exact hM
  let φ : Matrix (Fin n) (Fin n) R →ₗ[R] Matrix (Fin n) (Fin n) R :=
    ((LinearMap.ker a).liftQ b hker).comp (a.quotKerEquivOfSurjective ha).symm.toLinearMap
  have hφ : ∀ c, φ (a c) = b c := fun c => by
    have : a c = a.quotKerEquivOfSurjective ha (Submodule.Quotient.mk c) := rfl
    rw [this]
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  have hφg : ∀ g, φ (M g) = N g := fun g => by
    simpa [a, b] using hφ (Finsupp.single g 1)
  refine ⟨φ, by simpa using hφg 1, fun g X => ?_⟩
  have hX : X ∈ Submodule.span R (Set.range M) := hM ▸ Submodule.mem_top
  induction hX using Submodule.span_induction with
  | mem X hX => obtain ⟨g', rfl⟩ := hX; rw [← map_mul, hφg, hφg, map_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add, map_add, map_add, mul_add, hx, hy]
  | smul t x _ hx => rw [Matrix.mul_smul, map_smul, map_smul, Matrix.mul_smul, hx]

theorem exists_gl_conj_of_trace_eq :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (Γ : Type) [Group Γ] (r : ℕ) (ρ ρ' : Γ →* GL (Fin r) O), Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g => ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) = ⊤ → (∀ g, ((ρ' g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).trace = ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).trace) → ∃ U : GL (Fin r) O, ∀ g, ρ' g * U = U * ρ g := by
  intro O _ _ _ _ Γ _ r ρ ρ' hspan htr
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨1, fun g => Units.ext (Subsingleton.elim _ _)⟩
  let M : Γ →* Matrix (Fin r) (Fin r) O := (Units.coeHom _).comp ρ
  let N : Γ →* Matrix (Fin r) (Fin r) O := (Units.coeHom _).comp ρ'
  let π : Matrix (Fin r) (Fin r) O →* Matrix (Fin r) (Fin r) (ResidueField O) := (residue O).mapMatrix.toMonoidHom
  have hN' : Submodule.span (ResidueField O) (Set.range (π.comp N)) = ⊤ :=
    span_top_of_trace_eq (π.comp N) (π.comp M) (fun g => by
      change ((N g).map (residue O)).trace = ((M g).map (residue O)).trace
      rw [← AddMonoidHom.map_trace, ← AddMonoidHom.map_trace]
      exact congrArg _ (htr g)) hspan
  obtain ⟨φ, h1, hφ⟩ := exists_linearMap_of_trace_eq M N (fun g => (htr g).symm)
    (span_top_of_residual _ hspan) (span_top_of_residual _ hN')
  let k : Fin r := ⟨0, hr⟩
  obtain ⟨j, hj⟩ : ∃ j, residue O (φ (Matrix.single j j 1) k k) ≠ 0 := by
    by_contra hc
    push Not at hc
    have e : (1 : Matrix (Fin r) (Fin r) O) = ∑ j, Matrix.single j j 1 := (Matrix.sum_single_one).symm
    have := congrArg (fun X : Matrix (Fin r) (Fin r) O => residue O (X k k)) h1
    rw [e, map_sum, ← e] at this
    simp [Matrix.sum_apply, hc] at this
  let A : Matrix (Fin r) (Fin r) O := Matrix.of fun p q => φ (Matrix.single q j 1) p k
  have hA : ∀ g, N g * A = A * M g := by
    intro g
    ext p q
    have e : M g * Matrix.single q j 1 = ∑ t, M g t q • Matrix.single t j (1 : O) := by
      ext a b
      by_cases hb : j = b
      · subst hb; simp [Matrix.sum_apply, Matrix.single_apply]
      · simp [Matrix.sum_apply, Matrix.single_apply, Matrix.mul_apply, hb]
    have := congrFun (congrFun (hφ g (Matrix.single q j 1)) p) k
    rw [e, map_sum] at this
    simp only [map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] at this
    simp only [Matrix.mul_apply, A, Matrix.of_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _
  refine GlobalTheory.exists_gl_intertwiner_of_residual_span_eq_top O Γ r ρ ρ' hspan ⟨A, fun h0 => ?_, hA⟩
  refine GlobalTheory.det_ne_zero_of_intertwines_of_span_eq_top _ (fun g => (N g).map (residue O)) hspan
    (A.map (residue O)) k j hj (fun g => ?_) ?_
  · rw [← Matrix.map_mul, hA, Matrix.map_mul]; rfl
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

end GlobalTheory.TraceConj
