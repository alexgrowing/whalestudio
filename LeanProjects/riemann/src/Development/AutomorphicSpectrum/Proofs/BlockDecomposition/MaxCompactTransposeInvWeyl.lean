import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CstD
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.UnfoldingAlt.TiK

open GroundTheory.Automorphic.Reduction (archCompact euclidNorm infAt_apply finAt_apply infAt_inv finAt_inv)

section Arch

variable {E : Type*} [NormedField E] {n : ℕ}

theorem mul_transpose_eq_one_of_norm {M : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ z : Fin n → ℝ, euclidNorm (z ᵥ* M) = euclidNorm z) : M * Mᵀ = 1 := by
  have hsq : ∀ z : Fin n → ℝ, (z ᵥ* M) ⬝ᵥ (z ᵥ* M) = z ⬝ᵥ z := by
    intro z
    have h1 := h z
    have key : ∀ y : Fin n → ℝ, euclidNorm y ^ 2 = y ⬝ᵥ y := by
      intro y
      rw [euclidNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
      simp [dotProduct, sq]
    rw [← key, ← key, h1]
  have hpol : ∀ x y : Fin n → ℝ, (x ᵥ* M) ⬝ᵥ (y ᵥ* M) = x ⬝ᵥ y := by
    intro x y
    have h1 := hsq (x + y)
    have h2 := hsq x
    have h3 := hsq y
    simp only [Matrix.add_vecMul, add_dotProduct, dotProduct_add] at h1
    rw [dotProduct_comm (y ᵥ* M) (x ᵥ* M), dotProduct_comm y x] at h1
    linarith
  ext i j
  have h1 := hpol (Pi.single i 1) (Pi.single j 1)
  rw [single_one_vecMul, single_one_vecMul] at h1
  rw [Matrix.mul_apply', Matrix.one_apply]
  have h2 : (Pi.single i (1 : ℝ) : Fin n → ℝ) ⬝ᵥ Pi.single j 1 = if i = j then 1 else 0 := by
    simp [Pi.single_apply, eq_comm]
  rw [← h2, ← h1]
  rfl

theorem norm_preserving_iff (φ : E ≃+* ℝ) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (k : Matrix (Fin n) (Fin n) E) :
    (∀ y : Fin n → E, euclidNorm (y ᵥ* k) = euclidNorm y) ↔ k * kᵀ = 1 := by
  have hmap : ∀ y : Fin n → E, (fun i => φ.toRingHom ((y ᵥ* k) i)) =
      (fun i => φ.toRingHom (y i)) ᵥ* (k.map φ) := by
    intro y
    ext j
    simp [vecMul, dotProduct, map_sum, map_mul]
  constructor
  · intro h
    have hM : (k.map φ) * (k.map φ)ᵀ = 1 := by
      apply mul_transpose_eq_one_of_norm
      intro z
      have h1 := h (fun i => φ.symm (z i))
      rw [← Reduction.euclidNorm_map φ.toRingHom hφ, ← Reduction.euclidNorm_map φ.toRingHom hφ (fun i => φ.symm (z i)), hmap] at h1
      simpa using h1
    ext i j
    apply φ.injective
    have h1 := congrFun (congrFun hM i) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply] at h1
    simp only [Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_mul]
    rw [h1, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · intro h y
    have hU : (k.map φ) ∈ unitaryGroup (Fin n) ℝ := by
      rw [mem_unitaryGroup_iff]
      have : (k.map φ) * star (k.map φ) = (k * kᵀ).map φ := by
        ext i j
        simp [Matrix.mul_apply, Matrix.star_eq_conjTranspose, map_sum, map_mul]
      rw [this, h]
      ext i j
      simp [Matrix.one_apply]
    rw [← Reduction.euclidNorm_map φ.toRingHom hφ, hmap, Reduction.euclidNorm_vecMul_unitary hU,
      Reduction.euclidNorm_map φ.toRingHom hφ]

end Arch

section Adelic

variable {n : ℕ}

theorem infAt_ti (w : InfinitePlace ℚ) (k : AdelicGLn.AdelicGL ℚ n) :
    infAt w (ti k) = ti (infAt w k) := by
  apply Units.ext
  refine Matrix.ext fun a b => ?_
  change ((k⁻¹ : AdelicGLn.AdelicGL ℚ n) b a).1 w = ((infAt w k)⁻¹ : GL (Fin n) w.Completion) b a
  rw [← infAt_inv]
  rfl

theorem finAt_ti (v : HeightOneSpectrum (𝓞 ℚ)) (k : AdelicGLn.AdelicGL ℚ n) :
    finAt v (ti k) = ti (finAt v k) := by
  apply Units.ext
  refine Matrix.ext fun a b => ?_
  change ((k⁻¹ : AdelicGLn.AdelicGL ℚ n) b a).2 v = ((finAt v k)⁻¹ : GL (Fin n) (v.adicCompletion ℚ)) b a
  rw [← finAt_inv]
  rfl

theorem mem_archCompact_iff (w : InfinitePlace ℚ) (k : GL (Fin n) w.Completion) :
    k ∈ archCompact w ↔ k.val * k.valᵀ = 1 := by
  have hw : w.IsReal := RationalIdeles.isReal_infinitePlace w
  rw [Reduction.mem_archCompact]
  exact norm_preserving_iff (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
    (fun x => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) x) k.val

theorem ti_eq_self_of_orthogonal {R : Type*} [CommRing R] (k : GL (Fin n) R)
    (h : k.val * k.valᵀ = 1) : ti k = k := by
  apply Units.ext
  change k.inv.transpose = k.val
  have h1 : k.inv = k.valᵀ := by
    calc k.inv = k.inv * (k.val * k.valᵀ) := by rw [h, mul_one]
      _ = k.valᵀ := by rw [← mul_assoc, k.inv_val, one_mul]
  rw [h1, Matrix.transpose_transpose]

theorem ti_mem_maxCompact {k : AdelicGLn.AdelicGL ℚ n}
    (hk : k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL ℚ n))) :
    ti k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL ℚ n)) := by
  obtain ⟨h1, h2⟩ := Reduction.mem_maxCompact.1 hk
  refine Reduction.mem_maxCompact.2 ⟨fun w => ?_, fun v => ?_⟩
  · rw [infAt_ti, ti_eq_self_of_orthogonal _ ((mem_archCompact_iff w _).1 (h1 w))]
    exact h1 w
  · rw [finAt_ti]
    obtain ⟨ha, hb⟩ := (GLnLocal.mem_integralGL_iff _ _).1 (h2 v)
    exact (GLnLocal.mem_integralGL_iff _ _).2 ⟨fun i j => hb j i, fun i j => ha j i⟩

theorem diagonal_mem_maxCompact (γ : GL (Fin n) ℚ)
    (h1 : ∀ i j, γ.val i j = 0 ∨ γ.val i j = 1 ∨ γ.val i j = -1) (h2 : γ.inv = γ.valᵀ) :
    AdelicGLn.diagonal ℚ n γ ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL ℚ n)) := by
  have hinv : ∀ i j, (γ⁻¹ : GL (Fin n) ℚ).val i j = γ.val j i := fun i j => by
    change γ.inv i j = _
    rw [h2]
    rfl
  refine Reduction.mem_maxCompact.2 ⟨fun w => ?_, fun v => ?_⟩
  · rw [mem_archCompact_iff]
    have hT : (infAt w (AdelicGLn.diagonal ℚ n γ)).valᵀ = (infAt w (AdelicGLn.diagonal ℚ n γ)).inv := by
      refine Matrix.ext fun a b => ?_
      change _ = ((infAt w (AdelicGLn.diagonal ℚ n γ))⁻¹ : GL (Fin n) w.Completion) a b
      rw [← infAt_inv, ← map_inv]
      change (algebraMap ℚ 𝔸[ℚ] (γ.val b a)).1 w = (algebraMap ℚ 𝔸[ℚ] ((γ⁻¹ : GL (Fin n) ℚ).val a b)).1 w
      rw [hinv]
    rw [hT]
    exact Units.val_inv _
  · have hent : ∀ q : ℚ, (q = 0 ∨ q = 1 ∨ q = -1) →
        (algebraMap ℚ 𝔸[ℚ] q).2 v ∈ (ValuativeRel.valuation (v.adicCompletion ℚ)).integer := by
      rintro q (rfl | rfl | rfl)
      · rw [map_zero]
        exact zero_mem (ValuativeRel.valuation (v.adicCompletion ℚ)).integer
      · simp
      · rw [map_neg, map_one]
        exact neg_mem (one_mem (ValuativeRel.valuation (v.adicCompletion ℚ)).integer)
    refine (GLnLocal.mem_integralGL_iff _ _).2 ⟨fun i j => hent _ (h1 i j), fun i j => ?_⟩
    rw [← finAt_inv, ← map_inv]
    change (algebraMap ℚ 𝔸[ℚ] ((γ⁻¹ : GL (Fin n) ℚ).val i j)).2 v ∈ _
    rw [hinv]
    exact hent _ (h1 j i)

end Adelic

theorem weyl_eq_rational_GL3 : (w3 : G3) = dia w3 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w3]

theorem weyl_eq_rational_GL2 : (w2 : G2) = dia2 w2 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w2]

theorem rational_weyl_mem_maxCompact_GL3 : dia w3 ∈ (maxCompact : Subgroup G3) := by
  refine diagonal_mem_maxCompact _ (fun i j => ?_) ?_
  · fin_cases i <;> fin_cases j <;> simp [w3]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [w3]

theorem rational_weyl_mem_maxCompact_GL2 : dia2 w2 ∈ (maxCompact : Subgroup G2) := by
  refine diagonal_mem_maxCompact _ (fun i j => ?_) ?_
  · fin_cases i <;> fin_cases j <;> simp [w2]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [w2]

theorem rational_sign_mem_maxCompact_GL3 : dia dl3 ∈ (maxCompact : Subgroup G3) := by
  refine diagonal_mem_maxCompact _ (fun i j => ?_) ?_
  · fin_cases i <;> fin_cases j <;> simp [dl3, dg]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [dl3, dg]

theorem rational_sign_mem_maxCompact_GL2 : dia2 dl2 ∈ (maxCompact : Subgroup G2) := by
  refine diagonal_mem_maxCompact _ (fun i j => ?_) ?_
  · fin_cases i <;> fin_cases j <;> simp [dl2, dg2]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [dl2, dg2]

theorem weyl_delta_ti_maxCompact : (w3 : G3) ∈ (maxCompact : Subgroup G3) ∧ dia dl3 ∈ (maxCompact : Subgroup G3) ∧
    (w2 : G2) ∈ (maxCompact : Subgroup G2) ∧ dia2 dl2 ∈ (maxCompact : Subgroup G2) ∧
    (∀ k ∈ (maxCompact : Subgroup G3), ti k ∈ (maxCompact : Subgroup G3)) ∧
    (∀ k ∈ (maxCompact : Subgroup G2), ti k ∈ (maxCompact : Subgroup G2)) ∧
    (w3 : G3) = dia w3 ∧ (w2 : G2) = dia2 w2 :=
  ⟨weyl_eq_rational_GL3 ▸ rational_weyl_mem_maxCompact_GL3, rational_sign_mem_maxCompact_GL3, weyl_eq_rational_GL2 ▸ rational_weyl_mem_maxCompact_GL2, rational_sign_mem_maxCompact_GL2,
    fun _ hk => ti_mem_maxCompact hk, fun _ hk => ti_mem_maxCompact hk, weyl_eq_rational_GL3, weyl_eq_rational_GL2⟩

end GlobalTheory.CompanionTheory.UnfoldingAlt.TiK
