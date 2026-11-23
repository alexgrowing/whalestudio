import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.PolarJmConjTranspose

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

namespace UnitaryGroupOfForm

variable {n : ℕ}

lemma jj (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

lemma jH (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

lemma jj_mul (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) : Jm ε * (Jm ε * A) = A := by
  rw [← Matrix.mul_assoc, jj, Matrix.one_mul]

lemma inv_mem_UJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ∃ g' ∈ UJset ε, g * g' = 1 := by
  have h : gᴴ * Jm ε * g = Jm ε := hg
  have hg' : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    calc (Jm ε * gᴴ * Jm ε) * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, jj]
  have hgg : g * (Jm ε * gᴴ * Jm ε) = 1 := mul_eq_one_comm.mp hg'
  have e1 : g * (Jm ε * gᴴ * Jm ε) * Jm ε = g * Jm ε * gᴴ := by
    simp only [Matrix.mul_assoc, jj, Matrix.mul_one]
  have hgJ : g * Jm ε * gᴴ = Jm ε := by rw [← e1, hgg, Matrix.one_mul]
  refine ⟨Jm ε * gᴴ * Jm ε, ?_, hgg⟩
  show (Jm ε * gᴴ * Jm ε)ᴴ * Jm ε * (Jm ε * gᴴ * Jm ε) = Jm ε
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, jH, Matrix.conjTranspose_conjTranspose]
  have h2 : g * (Jm ε * (gᴴ * Jm ε)) = 1 := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hgJ, jj]
  simp only [Matrix.mul_assoc, jj_mul, h2, Matrix.mul_one]

lemma K_mem_UJ {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    k ∈ UJset ε := by
  obtain ⟨hu, hc⟩ := hk
  show kᴴ * Jm ε * k = Jm ε
  have h1 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, h1, Matrix.one_mul]

lemma K_inv {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ ∈ Kset ε ∧ k * kᴴ = 1 := by
  obtain ⟨hu, hc⟩ := hk
  refine ⟨⟨?_, ?_⟩, Matrix.mem_unitaryGroup_iff.mp hu⟩
  · first
    | exact Unitary.star_mem hu
    | exact unitary.star_mem hu
  · have h := congrArg Matrix.conjTranspose hc
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, jH] at h
    exact h.symm

lemma inG_sub (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (M - Jm ε * Mᴴ * Jm ε) := by
  unfold inG
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, jH,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, jj, jj_mul, Matrix.mul_one]
  abel

lemma inG_add (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (Complex.I • (M + Jm ε * Mᴴ * Jm ε)) := by
  unfold inG
  have hY : (M + Jm ε * Mᴴ * Jm ε)ᴴ * Jm ε = Jm ε * (M + Jm ε * Mᴴ * Jm ε) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, jH,
      Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, jj, jj_mul, Matrix.mul_one]
    abel
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_I, Matrix.smul_mul, hY, Matrix.mul_smul,
    neg_smul, neg_add_cancel]

section Alg
variable {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)

lemma actM_add (X Y : Matrix (Fin n) (Fin n) ℂ) : actM E (X + Y) = actM E X + actM E Y := by
  simp only [actM, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

lemma actM_smul (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : actM E (c • X) = c • actM E X := by
  simp only [actM, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

lemma actM_sub (X Y : Matrix (Fin n) (Fin n) ℂ) : actM E (X - Y) = actM E X - actM E Y := by
  simp only [actM, Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]

lemma actM_single (a b : Fin n) : actM E (Matrix.single a b 1) = E a b := by
  simp only [actM, Matrix.single_apply, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [Ne.symm hi]
  · simp

lemma E_eq (ε : Fin n → Bool) (a b : Fin n) :
    E a b = (1 / 2 : ℂ) • (actM E (Matrix.single a b 1 - Jm ε * (Matrix.single a b 1)ᴴ * Jm ε) -
      Complex.I • actM E (Complex.I • (Matrix.single a b 1 + Jm ε * (Matrix.single a b 1)ᴴ * Jm ε))) := by
  rw [actM_sub, actM_smul, actM_add, actM_single, smul_smul, Complex.I_mul_I, neg_one_smul]
  have h2 : ∀ A B : Module.End ℂ M, A - B - -(A + B) = (2 : ℂ) • A := fun A B => by
    rw [two_smul]
    abel
  rw [h2, smul_smul]
  norm_num

end Alg

section Rep
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

lemma inner_map_map' (hσ : IsURepOn (UJset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε)
    (x y : H) : inner ℂ (σ g x) (σ g y) = inner ℂ x y :=
  (⟨(σ g : H →ₗ[ℂ] H), hσ.2.1 g hg⟩ : H →ₗᵢ[ℂ] H).inner_map_map x y

lemma orth_stable (hσ : IsURepOn (UJset ε) σ) {g g' : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε)
    (hg' : g' ∈ UJset ε) (hgg : g * g' = 1) (T : Submodule ℂ H) (hT : ∀ x ∈ T, σ g' x ∈ T) :
    ∀ x ∈ Tᗮ, σ g x ∈ Tᗮ := by
  intro x hx
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro y hy
  have hy' : σ g (σ g' y) = y := by
    have h := hσ.1.2 g hg g' hg'
    rw [hgg, hσ.1.1] at h
    have h' := congrArg (fun f : H →L[ℂ] H => f y) h
    simpa using h'.symm
  rw [← hy', inner_map_map' hσ hg]
  exact hx _ (hT y hy)

lemma proj_comm (T : Submodule ℂ H) [T.HasOrthogonalProjection] (A : H →L[ℂ] H)
    (h1 : ∀ x ∈ T, A x ∈ T) (h2 : ∀ x ∈ Tᗮ, A x ∈ Tᗮ) (x : H) :
    T.starProjection (A x) = A (T.starProjection x) := by
  have hx := Submodule.sub_starProjection_mem_orthogonal (K := T) x
  have e : A x = A (T.starProjection x) + A (x - T.starProjection x) := by
    rw [← map_add, add_sub_cancel]
  rw [e, map_add, Submodule.starProjection_eq_self_iff.mpr (h1 _ (T.starProjection_apply_mem x)),
    (Submodule.starProjection_apply_eq_zero_iff T).mpr (h2 _ hx), add_zero]

variable {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

lemma actM_mem (hD : IsDerivedOn ε σ D E) (T : Submodule ℂ H) (hTc : IsClosed (T : Set H))
    (hTG : ∀ g ∈ UJset ε, ∀ x ∈ T, σ g x ∈ T) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    (v : D) (hv : (v : H) ∈ T) : ((actM E X v : D) : H) ∈ T := by
  have hXh : Xᴴ = -(Jm ε * X * Jm ε) := by
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, jj, Matrix.mul_one]
      _ = -(Jm ε * X) * Jm ε := by rw [eq_neg_of_add_eq_zero_left hX]
      _ = -(Jm ε * X * Jm ε) := by rw [Matrix.neg_mul]
  have hexp : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε := by
    intro t
    have hg : (NormedSpace.exp ((t : ℂ) • X))ᴴ = Jm ε * NormedSpace.exp (-((t : ℂ) • X)) * Jm ε := by
      rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hXh, ← PolarDecomposition.polar_exp_Jconj]
      congr 1
      rw [Complex.star_def, Complex.conj_ofReal]
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]
    show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Jm ε * NormedSpace.exp ((t : ℂ) • X) = Jm ε
    rw [hg]
    simp only [Matrix.mul_assoc]
    rw [jj_mul, PolarDecomposition.polar_exp_neg_mul, Matrix.mul_one]
  have hlim := (hD.deriv X hX v).tendsto_slope_zero
  refine hTc.mem_of_tendsto hlim (Filter.Eventually.of_forall fun t => ?_)
  exact T.smul_of_tower_mem _ (T.sub_mem (hTG _ (hexp _) _ hv) (hTG _ (hexp _) _ hv))

lemma E_mem (hD : IsDerivedOn ε σ D E) (T : Submodule ℂ H) (hTc : IsClosed (T : Set H))
    (hTG : ∀ g ∈ UJset ε, ∀ x ∈ T, σ g x ∈ T) (a b : Fin n) (v : D) (hv : (v : H) ∈ T) :
    ((E a b v : D) : H) ∈ T := by
  have h := E_eq E ε a b
  have e : ((E a b v : D) : H) = (1 / 2 : ℂ) • (((actM E (Matrix.single a b 1 - Jm ε * (Matrix.single a b 1)ᴴ * Jm ε) v : D) : H) -
      Complex.I • ((actM E (Complex.I • (Matrix.single a b 1 + Jm ε * (Matrix.single a b 1)ᴴ * Jm ε)) v : D) : H)) := by
    rw [h]
    simp
  rw [e]
  exact T.smul_mem _ (T.sub_mem (actM_mem hD T hTc hTG (inG_sub ε _) v hv)
    (T.smul_mem _ (actM_mem hD T hTc hTG (inG_add ε _) v hv)))

lemma closGen_le (hD : IsDerivedOn ε σ D E) (T : Submodule ℂ H) (hTc : IsClosed (T : Set H))
    (hTG : ∀ g ∈ UJset ε, ∀ x ∈ T, σ g x ∈ T) (V : Submodule ℂ D) (hV : ∀ v ∈ V, (v : H) ∈ T) :
    ((genSub E V).map D.subtype).topologicalClosure ≤ T := by
  refine Submodule.topologicalClosure_minimal _ ?_ hTc
  have hle : genSub E V ≤ T.comap D.subtype :=
    sInf_le ⟨fun v hv => hV v hv, fun a b v hv => E_mem hD T hTc hTG a b v hv⟩
  rintro _ ⟨v, hv, rfl⟩
  exact hle hv

lemma mem_closGen (V : Submodule ℂ D) (v : D) (hv : v ∈ V) : (v : H) ∈ ((genSub E V).map D.subtype).topologicalClosure := by
  have h1 : v ∈ genSub E V := (le_sInf fun T hT => hT.1 : V ≤ genSub E V) hv
  exact Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem h1)

end Rep

end UnitaryGroupOfForm

end ReciprocityTheory.ChartRestriction.DS
