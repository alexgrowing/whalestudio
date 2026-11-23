import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory.LogDR.StabTheta

variable {K : Type} [Field K]

theorem smul_mem_spanForms (M M' : Set K) (H : Set Ω[K⁄ℤ]) (a : ℕ) (c : K)
    (h : ∀ m ∈ M, c * m ∈ M') {η : abelian₂ K} (hη : η ∈ spanForms M H a) :
    c • η ∈ spanForms M' H a := by
  have key : spanForms M H a ≤
      (spanForms M' H a).comap (DistribMulAction.toAddMonoidHom (abelian₂ K) c) := by
    unfold spanForms
    rw [AddSubgroup.closure_le]
    rintro _ ⟨m, hm, v, hv, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    show c • (m • ExteriorAlgebra.ιMulti K a v) ∈ AddSubgroup.closure _
    rw [smul_smul]
    exact AddSubgroup.subset_closure ⟨c * m, h m hm, v, hv, rfl⟩
  exact key hη

theorem iota_mul_mem_spanForms (M : Set K) (H : Set Ω[K⁄ℤ]) (q : ℕ) (w : Ω[K⁄ℤ]) (hw : w ∈ H)
    {η : abelian₂ K} (hη : η ∈ spanForms M H q) :
    ExteriorAlgebra.ι K w * η ∈ spanForms M H (q + 1) := by
  have key : spanForms M H q ≤
      (spanForms M H (q + 1)).comap (AddMonoidHom.mulLeft (ExteriorAlgebra.ι K w)) := by
    unfold spanForms
    rw [AddSubgroup.closure_le]
    rintro _ ⟨m, hm, v, hv, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    show ExteriorAlgebra.ι K w * (m • ExteriorAlgebra.ιMulti K q v) ∈ AddSubgroup.closure _
    rw [mul_smul_comm]
    refine AddSubgroup.subset_closure ⟨m, hm, Fin.cons w v, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using hw
      · simpa using hv k
    · rw [ExteriorAlgebra.ιMulti_succ_apply]
      simp [Matrix.vecTail]
  exact key hη

theorem theta_dlog {n : ℕ} (x : Fin n → Kˣ) (i : Fin n) (θ : abelian₂ K →ₗ[K] abelian₂ K)
    (hθ : IsEulerContraction x i θ) (j : Fin n) :
    θ (ExteriorAlgebra.ι K (dlog (x j))) = algebraMap K (abelian₂ K) (if j = i then 1 else 0) := by
  rw [hθ.2.2 j]
  split_ifs <;> simp

theorem theta_frame (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n)
    (θ : abelian₂ K →ₗ[K] abelian₂ K) (hx : ∀ j, (x j : K) ∈ A) (hθ : IsEulerContraction x i θ) (j : Fin n) :
    ∃ a ∈ A, θ (ExteriorAlgebra.ι K (frame x J j)) = algebraMap K (abelian₂ K) a := by
  have hif : (if j = i then (1 : K) else 0) ∈ A := by split_ifs <;> simp
  unfold frame
  split_ifs with hj
  · exact ⟨_, hif, theta_dlog x i θ hθ j⟩
  · have hd : dK (x j : K) = (x j : K) • dlog (x j) := by
      unfold dlog
      rw [smul_smul]
      simp
    refine ⟨(x j : K) * (if j = i then 1 else 0), A.mul_mem (hx j) hif, ?_⟩
    rw [hd, map_smul, map_smul, theta_dlog x i θ hθ j, Algebra.smul_def, ← map_mul]

theorem theta_iotaMulti (A : Subring K) {n : ℕ} (x : Fin n → Kˣ) (J : Finset (Fin n)) (i : Fin n)
    (θ : abelian₂ K →ₗ[K] abelian₂ K) (hx : ∀ j, (x j : K) ∈ A) (hθ : IsEulerContraction x i θ) :
    ∀ (q : ℕ) (v : Fin (q + 1) → Ω[K⁄ℤ]), (∀ k, v k ∈ Set.range (frame x J)) →
      θ (ExteriorAlgebra.ιMulti K (q + 1) v) ∈ spanForms (A : Set K) (Set.range (frame x J)) q := by
  intro q
  induction q with
  | zero =>
    intro v hv
    rw [ExteriorAlgebra.ιMulti_succ_apply, hθ.2.1, ExteriorAlgebra.ιMulti_zero_apply, hθ.1,
      mul_zero, sub_zero, mul_one]
    obtain ⟨j, hj⟩ := hv 0
    obtain ⟨a, ha, he⟩ := theta_frame A x J i θ hx hθ j
    rw [← hj, he, Algebra.algebraMap_eq_smul_one]
    refine AddSubgroup.subset_closure ⟨a, ha, Matrix.vecTail v, fun k => k.elim0, ?_⟩
    rw [ExteriorAlgebra.ιMulti_zero_apply]
  | succ q ih =>
    intro v hv
    rw [ExteriorAlgebra.ιMulti_succ_apply, hθ.2.1]
    obtain ⟨j, hj⟩ := hv 0
    obtain ⟨a, ha, he⟩ := theta_frame A x J i θ hx hθ j
    have htail : ∀ k, Matrix.vecTail v k ∈ Set.range (frame x J) := fun k => hv k.succ
    refine AddSubgroup.sub_mem _ ?_ ?_
    · rw [← hj, he, ← Algebra.smul_def]
      exact AddSubgroup.subset_closure ⟨a, ha, Matrix.vecTail v, htail, rfl⟩
    · exact iota_mul_mem_spanForms _ _ q _ (hv 0) (ih _ htail)

end GlobalTheory.LogDR.StabTheta

open GlobalTheory.LogDR.StabTheta in
theorem GlobalTheory.LogDR.chartForms_stable_euler :
    ∀ (K : Type) [Field K] (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (i : Fin n) (θ : abelian₂ K →ₗ[K] abelian₂ K), (∀ j, (x j : K) ∈ A) → IsEulerContraction x i θ → (∀ q, ∀ η ∈ chartForms A x J t (q + 1), θ η ∈ chartForms A x J t q) ∧ ∀ η ∈ chartForms A x J t 0, θ η = 0 := by
  intro K _ A n x J t i θ hx hθ
  constructor
  · intro q η hη
    have key : chartForms A x J t (q + 1) ≤ (chartForms A x J t q).comap θ.toAddMonoidHom := by
      unfold chartForms spanForms
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, v, hv, rfl⟩
      rw [SetLike.mem_coe, AddSubgroup.mem_comap]
      show θ (c • ExteriorAlgebra.ιMulti K (q + 1) v) ∈ spanForms _ _ q
      rw [map_smul]
      refine smul_mem_spanForms (A : Set K) _ _ q c ?_ (theta_iotaMulti A x J i θ hx hθ q v hv)
      intro m hm
      show c * m * (t : K) ∈ A
      rw [mul_right_comm]
      exact A.mul_mem hc hm
    exact key hη
  · intro η hη
    have key : chartForms A x J t 0 ≤ θ.toAddMonoidHom.ker := by
      unfold chartForms spanForms
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, v, hv, rfl⟩
      rw [SetLike.mem_coe, AddMonoidHom.mem_ker]
      show θ (c • ExteriorAlgebra.ιMulti K 0 v) = 0
      rw [map_smul, ExteriorAlgebra.ιMulti_zero_apply, hθ.1, smul_zero]
    exact key hη
