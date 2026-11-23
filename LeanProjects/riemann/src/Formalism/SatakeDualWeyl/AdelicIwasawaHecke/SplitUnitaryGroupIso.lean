import Formalism.SatakeDualWeyl.Statement

noncomputable section

open Matrix

namespace Formalism.UG.P

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem split_mat_ext {M N : Matrix n n (R × R)} (h1 : M.map Prod.fst = N.map Prod.fst)
    (h2 : M.map Prod.snd = N.map Prod.snd) : M = N := by
  ext i j
  · simpa using congrFun (congrFun h1 i) j
  · simpa using congrFun (congrFun h2 i) j

theorem split_map_fst_mul (M N : Matrix n n (R × R)) :
    (M * N).map Prod.fst = M.map Prod.fst * N.map Prod.fst := by
  ext i j
  simp [Matrix.mul_apply, Prod.fst_sum]

theorem split_map_snd_mul (M N : Matrix n n (R × R)) :
    (M * N).map Prod.snd = M.map Prod.snd * N.map Prod.snd := by
  ext i j
  simp [Matrix.mul_apply, Prod.snd_sum]

theorem split_cT_fst (g : Matrix n n (R × R)) :
    (cT (swapR R) g).map Prod.fst = (g.map Prod.snd)ᵀ := by
  ext i j
  rfl

theorem split_cT_snd (g : Matrix n n (R × R)) :
    (cT (swapR R) g).map Prod.snd = (g.map Prod.fst)ᵀ := by
  ext i j
  rfl

theorem splitJ_fst (J₁ : Matrix n n R) : (splitJ J₁).map Prod.fst = J₁ := by
  ext i j
  rfl

theorem splitJ_snd (J₁ : Matrix n n R) : (splitJ J₁).map Prod.snd = J₁ᵀ := by
  ext i j
  rfl

theorem split_mem_iff (J₁ : Matrix n n R) (g : GL n (R × R)) :
    g ∈ UJ (swapR R) (splitJ J₁) ↔
      ((g : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ * (g : Matrix n n (R × R)).map Prod.fst
        = J₁ := by
  constructor
  · intro h
    have h' := congrArg (fun M : Matrix n n (R × R) => M.map Prod.fst)
      (show cT (swapR R) (g : Matrix n n (R × R)) * splitJ J₁ * (g : Matrix n n (R × R)) = splitJ J₁ from h)
    simpa only [split_map_fst_mul, split_cT_fst, splitJ_fst] using h'
  · intro h
    show cT (swapR R) (g : Matrix n n (R × R)) * splitJ J₁ * (g : Matrix n n (R × R)) = splitJ J₁
    apply split_mat_ext
    · rw [split_map_fst_mul, split_map_fst_mul, split_cT_fst, splitJ_fst, h]
    · rw [split_map_snd_mul, split_map_snd_mul, split_cT_snd, splitJ_snd]
      have h' := congrArg Matrix.transpose h
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at h'
      rw [← Matrix.mul_assoc] at h'
      exact h'

theorem split_conj_mul (J₁ : Matrix n n R) (hJ : IsUnit J₁.det) {P Q : Matrix n n R}
    (hPQ : P * Q = 1) : (J₁ * P * J₁⁻¹) * (J₁ * Q * J₁⁻¹) = 1 := by
  have h1 : J₁⁻¹ * J₁ = 1 := Matrix.nonsing_inv_mul _ hJ
  have h2 : J₁ * J₁⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJ
  calc (J₁ * P * J₁⁻¹) * (J₁ * Q * J₁⁻¹) = J₁ * (P * (J₁⁻¹ * J₁) * Q) * J₁⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_one, hPQ, Matrix.mul_one, h2]

def pairMat (X Y : Matrix n n R) : Matrix n n (R × R) := fun i j => (X i j, Y i j)

theorem pairMat_fst (X Y : Matrix n n R) : (pairMat X Y).map Prod.fst = X := by
  ext i j
  rfl

theorem pairMat_snd (X Y : Matrix n n R) : (pairMat X Y).map Prod.snd = Y := by
  ext i j
  rfl

theorem pairMat_mul_eq_one {X Y X' Y' : Matrix n n R} (h1 : X * X' = 1) (h2 : Y * Y' = 1) :
    pairMat X Y * pairMat X' Y' = 1 := by
  apply split_mat_ext
  · rw [split_map_fst_mul, pairMat_fst, pairMat_fst, h1]
    exact (Matrix.map_one _ rfl rfl).symm
  · rw [split_map_snd_mul, pairMat_snd, pairMat_snd, h2]
    exact (Matrix.map_one _ rfl rfl).symm

theorem split_injective (J₁ : Matrix n n R) (hJ : IsUnit J₁.det) (g g' : GL n (R × R))
    (hg : g ∈ UJ (swapR R) (splitJ J₁)) (hg' : g' ∈ UJ (swapR R) (splitJ J₁))
    (h : (g : Matrix n n (R × R)).map Prod.fst = (g' : Matrix n n (R × R)).map Prod.fst) :
    g = g' := by
  have hF : (g : Matrix n n (R × R)).map Prod.fst * ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst = 1 := by
    rw [← split_map_fst_mul, Units.mul_inv]
    exact Matrix.map_one _ rfl rfl
  have e1 := (split_mem_iff J₁ g).mp hg
  have e2 := (split_mem_iff J₁ g').mp hg'
  rw [← h] at e2
  have k1 : ((g : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ =
      J₁ * ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst := by
    calc ((g : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁
        = ((g : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ * ((g : Matrix n n (R × R)).map Prod.fst *
            ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst) := by rw [hF, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, e1]
  have k2 : ((g' : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ =
      J₁ * ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst := by
    calc ((g' : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁
        = ((g' : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ * ((g : Matrix n n (R × R)).map Prod.fst *
            ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst) := by rw [hF, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, e2]
  have k3 : ((g : Matrix n n (R × R)).map Prod.snd)ᵀ = ((g' : Matrix n n (R × R)).map Prod.snd)ᵀ := by
    have h3 := congrArg (fun M : Matrix n n R => M * J₁⁻¹) (k1.trans k2.symm)
    simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ, Matrix.mul_one] using h3
  have k4 := congrArg Matrix.transpose k3
  rw [Matrix.transpose_transpose, Matrix.transpose_transpose] at k4
  exact Units.ext (split_mat_ext h k4)

theorem split_surjective (J₁ : Matrix n n R) (hJ : IsUnit J₁.det) (h : GL n R) :
    ∃ g : GL n (R × R), g ∈ UJ (swapR R) (splitJ J₁) ∧ bc (RingHom.fst R R) g = h := by
  have hS : (J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ * (J₁ * (h : Matrix n n R) * J₁⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, split_conj_mul J₁ hJ (Units.mul_inv h), Matrix.transpose_one]
  have hSi : (J₁ * (h : Matrix n n R) * J₁⁻¹)ᵀ * (J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, split_conj_mul J₁ hJ (Units.inv_mul h), Matrix.transpose_one]
  refine ⟨⟨pairMat (h : Matrix n n R) (J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ,
    pairMat ((h⁻¹ : GL n R) : Matrix n n R) (J₁ * (h : Matrix n n R) * J₁⁻¹)ᵀ,
    pairMat_mul_eq_one (Units.mul_inv h) hS, pairMat_mul_eq_one (Units.inv_mul h) hSi⟩, ?_, ?_⟩
  · apply (split_mem_iff J₁ _).mpr
    show ((pairMat (h : Matrix n n R) (J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ).map Prod.snd)ᵀ * J₁ *
      (pairMat (h : Matrix n n R) (J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ).map Prod.fst = J₁
    rw [pairMat_snd, pairMat_fst, Matrix.transpose_transpose]
    calc J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹ * J₁ * (h : Matrix n n R)
        = J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * (J₁⁻¹ * J₁) * (h : Matrix n n R) := by
          simp only [Matrix.mul_assoc]
      _ = J₁ := by
          rw [Matrix.nonsing_inv_mul _ hJ, Matrix.mul_one, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  · exact Units.ext (pairMat_fst (h : Matrix n n R) (J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ)

theorem split_unitary_group_iso : Formalism.UG.SplitIso := by
  intro R _ n _ _ J₁ hJ
  refine ⟨MulEquiv.ofBijective ((bc (RingHom.fst R R)).comp (UJ (swapR R) (splitJ J₁)).subtype) ⟨?_, ?_⟩,
    fun g => rfl⟩
  · intro a b hab
    apply Subtype.ext
    apply split_injective J₁ hJ a b a.2 b.2
    exact congrArg (fun u : GL n R => (u : Matrix n n R)) hab
  · intro h
    obtain ⟨g, hg, he⟩ := split_surjective J₁ hJ h
    exact ⟨⟨g, hg⟩, he⟩

end Formalism.UG.P
