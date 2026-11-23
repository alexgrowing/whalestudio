import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.IsChain

noncomputable section

open Matrix Submodule

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

variable {k : Type} [Field k] {n : ℕ}

def gradeColMat (b : Module.Basis (Fin n) k (Fin n → k)) : Matrix (Fin n) (Fin n) k :=
  (Pi.basisFun k (Fin n)).toMatrix b

def gradeRowMat (b : Module.Basis (Fin n) k (Fin n → k)) : Matrix (Fin n) (Fin n) k :=
  b.toMatrix (Pi.basisFun k (Fin n))

def gradeBasisGL (b : Module.Basis (Fin n) k (Fin n → k)) : GL (Fin n) k :=
  ⟨gradeColMat b, gradeRowMat b, Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩

theorem gradeColMat_mulVec (b : Module.Basis (Fin n) k (Fin n → k)) (u : Fin n → k) :
    gradeColMat b *ᵥ u = ∑ i, u i • b i := by
  ext r
  simp [gradeColMat, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, Finset.sum_apply, mul_comm]

theorem grade_mat_ext {ι : Type} (b : Module.Basis ι k (Fin n → k)) (X Y : Matrix (Fin n) (Fin n) k)
    (h : ∀ i, X *ᵥ b i = Y *ᵥ b i) : X = Y := by
  apply Matrix.toLin'.injective
  exact b.ext fun i => by simpa [Matrix.toLin'_apply] using h i

theorem grade_eig {ι : Type} (b : Module.Basis ι k (Fin n → k)) (g : Matrix (Fin n) (Fin n) k) (d : ι → k)
    (hg : ∀ i, g *ᵥ b i = d i • b i) (S : Set ι) (c : k) (hS : ∀ i ∈ S, d i = c) (y : Fin n → k)
    (hy : y ∈ span k (b '' S)) : g *ᵥ y = c • y := by
  let f : (Fin n → k) →ₗ[k] (Fin n → k) := Matrix.toLin' g - c • LinearMap.id
  have hle : span k (b '' S) ≤ LinearMap.ker f := by
    rw [span_le]
    rintro _ ⟨i, hi, rfl⟩
    simp [f, Matrix.toLin'_apply, hg, hS i hi]
  have := hle hy
  simp only [LinearMap.mem_ker, f, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    Matrix.toLin'_apply] at this
  exact sub_eq_zero.mp this

theorem grade_fin (b : Module.Basis (Fin n) k (Fin n → k)) (w : Fin n → ℤ)
    (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (N : Matrix (Fin n) (Fin n) k) (v : Fin n → k)
    (hZ : ∀ z ∈ Z, ∀ j, z *ᵥ b j ∈ span k (b '' {j' | w j' = w j}))
    (hN : ∀ j, N *ᵥ b j ∈ span k (b '' {j' | w j' = w j + 1}))
    (hv : v ∈ span k (b '' {j | w j = 0}))
    (hA : ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * N = N * a →
      ∀ j, w j < 0 → b.repr (a *ᵥ v) j = 0) :
    (∀ t : kˣ,
        let g : Matrix (Fin n) (Fin n) k :=
          (gradeBasisGL b).val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * (gradeBasisGL b)⁻¹.val
        (∀ a ∈ Z, a * g = g * a) ∧ g * N = (t : k) • (N * g) ∧ g *ᵥ v = v) ∧
      ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * N = N * a →
        ∃ u : Fin n → k, a *ᵥ v = (gradeBasisGL b).val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0 := by
  classical
  refine ⟨fun t => ?_, fun a ha haN => ?_⟩
  · intro g
    have hrow : ∀ j, gradeRowMat b *ᵥ b j = Pi.single j 1 := by
      intro j
      have h1 : gradeColMat b *ᵥ Pi.single j 1 = b j := by
        rw [gradeColMat_mulVec]
        simp [Pi.single_apply]
      rw [← h1, Matrix.mulVec_mulVec]
      show (b.toMatrix (Pi.basisFun k (Fin n)) * (Pi.basisFun k (Fin n)).toMatrix b) *ᵥ _ = _
      rw [Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.one_mulVec]
    have hgdef : g = gradeColMat b * diagonal (fun i => ((t ^ w i : kˣ) : k)) * gradeRowMat b := rfl
    clear_value g
    have hg : ∀ j, g *ᵥ b j = ((t ^ w j : kˣ) : k) • b j := by
      intro j
      rw [hgdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hrow, gradeColMat_mulVec]
      simp [Matrix.mulVec_diagonal, Pi.single_apply]
    refine ⟨fun a ha => ?_, ?_, ?_⟩
    · apply grade_mat_ext b
      intro j
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg, Matrix.mulVec_smul]
      rw [grade_eig b g (fun i => ((t ^ w i : kˣ) : k)) hg {j' | w j' = w j} _ (fun i hi => by rw [hi]) _ (hZ a ha j)]
    · apply grade_mat_ext b
      intro j
      rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hg, Matrix.mulVec_smul,
        grade_eig b g (fun i => ((t ^ w i : kˣ) : k)) hg {j' | w j' = w j + 1} (((t ^ (w j + 1) : kˣ) : k))
          (fun i hi => by rw [hi]) _ (hN j), smul_smul, _root_.zpow_add_one, Units.val_mul, Units.val_zpow_eq_zpow_val,
        mul_comm]
    · rw [grade_eig b g (fun i => ((t ^ w i : kˣ) : k)) hg {j | w j = 0} 1 (fun i hi => by rw [hi]; simp) v hv, one_smul]
  · refine ⟨⇑(b.repr (a *ᵥ v)), ?_, fun i hi => hA a ha haN i hi⟩
    simp only [gradeBasisGL]
    rw [gradeColMat_mulVec, b.sum_repr]

theorem grade_of_basis {κ : Type} [Fintype κ] (β : Module.Basis κ k (Fin n → k)) (ω : κ → ℤ)
    (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (N : Matrix (Fin n) (Fin n) k) (v : Fin n → k)
    (hZ : ∀ z ∈ Z, ∀ j, z *ᵥ β j ∈ span k (β '' {j' | ω j' = ω j}))
    (hN : ∀ j, N *ᵥ β j ∈ span k (β '' {j' | ω j' = ω j + 1}))
    (hv : v ∈ span k (β '' {j | ω j = 0}))
    (hA : ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * N = N * a →
      ∀ j, ω j < 0 → β.repr (a *ᵥ v) j = 0) :
    ∃ (P : GL (Fin n) k) (w : Fin n → ℤ), (∀ t : kˣ,
        let g : Matrix (Fin n) (Fin n) k := P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val
        (∀ a ∈ Z, a * g = g * a) ∧ g * N = (t : k) • (N * g) ∧ g *ᵥ v = v) ∧
      ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * N = N * a →
        ∃ u : Fin n → k, a *ᵥ v = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0 := by
  have hcard : Fintype.card κ = n := by
    rw [← Module.finrank_eq_card_basis β, Module.finrank_fin_fun]
  let e : κ ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let b := β.reindex e
  let w : Fin n → ℤ := fun i => ω (e.symm i)
  have hb : ∀ j, β j = b (e j) := fun j => by simp [b]
  have himg : ∀ c : ℤ, β '' {j | ω j = c} = b '' {i | w i = c} := by
    intro c
    ext y
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨e j, by simpa [w] using hj, (hb j).symm⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨e.symm i, hi, by simp [b]⟩
  refine ⟨gradeBasisGL b, w, grade_fin b w Z N v ?_ ?_ ?_ ?_⟩
  · intro z hz i
    have := hZ z hz (e.symm i)
    rw [himg] at this
    simpa [b, w] using this
  · intro i
    have := hN (e.symm i)
    rw [himg] at this
    simpa [b, w] using this
  · rw [← himg]; exact hv
  · intro a ha haN i hi
    have := hA a ha haN (e.symm i) hi
    simpa [b] using this

theorem grade_of_frame {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {M : Type} [Fintype M] {L : M → Type}
    [∀ m, Fintype (L m)] {R : Z → (m : M) → L m → L m → k} {o : (m : M) → L m → k}
    {N : Matrix (Fin n) (Fin n) k} {v : Fin n → k} (F : Frame Z M L R o N v) :
    ∃ (P : GL (Fin n) k) (w : Fin n → ℤ), (∀ t : kˣ,
        let g : Matrix (Fin n) (Fin n) k := P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val
        (∀ a ∈ Z, a * g = g * a) ∧ g * N = (t : k) • (N * g) ∧ g *ᵥ v = v) ∧
      ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * N = N * a →
        ∃ u : Fin n → k, a *ᵥ v = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0 := by
  let ω : (Σ m, L m × (Σ a : F.ι m, Fin (F.l m a))) → ℤ := fun j => ((j.2.2.2 : ℕ) : ℤ) - (F.s j.1 j.2.2.1 : ℤ)
  apply grade_of_basis F.β ω Z N v
  · rintro z hz ⟨m, p, jj⟩
    rw [show (z : Matrix (Fin n) (Fin n) k) = ((⟨z, hz⟩ : Z) : Matrix (Fin n) (Fin n) k) from rfl, F.hZ]
    refine sum_mem fun q _ => smul_mem _ _ (subset_span ⟨⟨m, q, jj⟩, rfl, rfl⟩)
  · rintro ⟨m, p, a, i⟩
    rw [F.hN]
    split_ifs with h
    · exact subset_span ⟨_, by simp only [Set.mem_ofPred_eq, ω]; push_cast; ring, rfl⟩
    · exact zero_mem _
  · suffices h : (∑ m, ∑ p, ∑ a, if h : F.s m a < F.l m a then o m p • F.β ⟨m, (p, ⟨a, ⟨F.s m a, h⟩⟩)⟩ else 0) ∈
        span k (F.β '' {j | ω j = 0}) by rw [← F.hv] at h; exact h
    refine sum_mem fun m _ => sum_mem fun p _ => sum_mem fun a _ => ?_
    split_ifs with h
    · exact smul_mem _ _ (subset_span ⟨_, by simp [ω], rfl⟩)
    · exact zero_mem _
  · rintro A hA hAN ⟨m, p, a, i⟩ hi
    exact F.hA A hA hAN m p a i (by simp only [ω] at hi; omega)

end PositivityTheory.RgUd.T.Nil.Orb.BReps
