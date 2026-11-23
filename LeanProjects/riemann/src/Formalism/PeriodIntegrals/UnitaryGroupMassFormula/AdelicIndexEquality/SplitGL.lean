import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Commensurated

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL

open Matrix

variable {R k : Type} [CommRing R] [Field k] {n : Type} [Fintype n] [DecidableEq n]

def p1 (π : R ≃+* k × k) : R →+* k := (RingHom.fst k k).comp π.toRingHom

def p2 (π : R ≃+* k × k) : R →+* k := (RingHom.snd k k).comp π.toRingHom

theorem ext_p (π : R ≃+* k × k) {r s : R} (h1 : p1 π r = p1 π s) (h2 : p2 π r = p2 π s) : r = s := by
  apply π.injective
  exact Prod.ext h1 h2

theorem mat_ext_p (π : R ≃+* k × k) {M N : Matrix n n R} (h1 : M.map (p1 π) = N.map (p1 π))
    (h2 : M.map (p2 π) = N.map (p2 π)) : M = N := by
  ext i j
  exact ext_p π (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

variable (σ : R →+* R) (π : R ≃+* k × k) (hπ : ∀ r, π (σ r) = (π r).swap)
include hπ

theorem p1_sigma_eq_p2 (r : R) : p1 π (σ r) = p2 π r := by
  show (π (σ r)).1 = (π r).2
  rw [hπ]
  rfl

theorem snd_conj (r : R) : p2 π (σ r) = p1 π r := by
  show (π (σ r)).2 = (π r).1
  rw [hπ]
  rfl

theorem map_conjTranspose_fst (M : Matrix n n R) : (Formalism.UG.cT σ M).map (p1 π) = (M.map (p2 π))ᵀ := by
  ext i j
  exact p1_sigma_eq_p2 σ π hπ (M j i)

theorem map_conjTranspose_snd (M : Matrix n n R) : (Formalism.UG.cT σ M).map (p2 π) = (M.map (p1 π))ᵀ := by
  ext i j
  exact snd_conj σ π hπ (M j i)

theorem unitary_iff (J M : Matrix n n R) :
    Formalism.UG.cT σ M * J * M = J ↔
      (M.map (p2 π))ᵀ * J.map (p1 π) * M.map (p1 π) = J.map (p1 π) ∧
      (M.map (p1 π))ᵀ * J.map (p2 π) * M.map (p2 π) = J.map (p2 π) := by
  have e1 : (Formalism.UG.cT σ M * J * M).map (p1 π) = (M.map (p2 π))ᵀ * J.map (p1 π) * M.map (p1 π) := by
    rw [Matrix.map_mul, Matrix.map_mul, map_conjTranspose_fst σ π hπ]
  have e2 : (Formalism.UG.cT σ M * J * M).map (p2 π) = (M.map (p1 π))ᵀ * J.map (p2 π) * M.map (p2 π) := by
    rw [Matrix.map_mul, Matrix.map_mul, map_conjTranspose_snd σ π hπ]
  constructor
  · intro h
    rw [← e1, ← e2, h]
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    exact mat_ext_p π (by rw [e1, h1]) (by rw [e2, h2])

theorem hermitian_map_snd (J : Matrix n n R) (hJ : Formalism.UG.cT σ J = J) : J.map (p2 π) = (J.map (p1 π))ᵀ := by
  have h := map_conjTranspose_fst σ π hπ J
  rw [hJ] at h
  rw [h, Matrix.transpose_transpose]

omit hπ in

def proj (J : Matrix n n R) : Formalism.UG.UJ σ J →* GL n k :=
  (Units.map ((p1 π).mapMatrix : Matrix n n R →+* Matrix n n k).toMonoidHom).comp (Formalism.UG.UJ σ J).subtype

theorem proj_bijective (J : Matrix n n R) (hJ : Formalism.UG.cT σ J = J) (hdet : IsUnit J.det) :
    Function.Bijective (proj σ π J) := by
  have hJ1 : IsUnit (J.map (p1 π)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hdet.map _
  have hunit : ∀ x : Formalism.UG.UJ σ J,
      (((x : GL n R) : Matrix n n R).map (p2 π))ᵀ * J.map (p1 π) * ((x : GL n R) : Matrix n n R).map (p1 π) =
        J.map (p1 π) :=
    fun x => ((unitary_iff σ π hπ J ((x : GL n R) : Matrix n n R)).1 x.2).1
  have hinv1 : ∀ x : GL n R,
      (x : Matrix n n R).map (p1 π) * ((x⁻¹ : GL n R) : Matrix n n R).map (p1 π) = 1 := by
    intro x
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  constructor
  · intro g h hgh
    have h1 : ((g : GL n R) : Matrix n n R).map (p1 π) = ((h : GL n R) : Matrix n n R).map (p1 π) :=
      congrArg (fun u : GL n k => (u : Matrix n n k)) hgh
    have h2 : ((g : GL n R) : Matrix n n R).map (p2 π) = ((h : GL n R) : Matrix n n R).map (p2 π) := by
      have hg := hunit g
      have hh := hunit h
      rw [h1] at hg
      have e : (((g : GL n R) : Matrix n n R).map (p2 π))ᵀ * J.map (p1 π) =
          (((h : GL n R) : Matrix n n R).map (p2 π))ᵀ * J.map (p1 π) := by
        have := congrArg (fun X => X * (((h : GL n R)⁻¹ : GL n R) : Matrix n n R).map (p1 π)) (hg.trans hh.symm)
        simp only [Matrix.mul_assoc, hinv1, Matrix.mul_one] at this
        simpa only [Matrix.mul_assoc] using this
      have e' := congrArg (fun X => X * (J.map (p1 π))⁻¹) e
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ1, Matrix.mul_one] at e'
      have := congrArg Matrix.transpose e'
      simpa only [Matrix.transpose_transpose] using this
    exact Subtype.ext (Units.ext (mat_ext_p π h1 h2))
  · intro A
    let J1 : Matrix n n k := J.map (p1 π)
    let A1 : Matrix n n k := (A : Matrix n n k)
    let B : Matrix n n k := (J1 * ((A⁻¹ : GL n k) : Matrix n n k) * J1⁻¹)ᵀ
    let M : Matrix n n R := Matrix.of fun i j => π.symm (A1 i j, B i j)
    have hM1 : M.map (p1 π) = A1 := by
      ext i j
      simp [M, p1]
    have hM2 : M.map (p2 π) = B := by
      ext i j
      simp [M, p2]
    have hJ1' : IsUnit J1.det := hJ1
    have key : Bᵀ * J1 * A1 = J1 := by
      simp only [B, Matrix.transpose_transpose, Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul_cancel_left _ _ hJ1', Units.inv_mul, Matrix.mul_one]
    have hU : Formalism.UG.cT σ M * J * M = J := by
      rw [unitary_iff σ π hπ J M, hM1, hM2, hermitian_map_snd σ π hπ J hJ]
      refine ⟨key, ?_⟩
      have := congrArg Matrix.transpose key
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at this
      exact this
    have hdetM : IsUnit M.det := by
      have h := congrArg Matrix.det hU
      rw [Matrix.det_mul, Matrix.det_mul] at h
      have h' : IsUnit ((Formalism.UG.cT σ M).det * J.det * M.det) := by rw [h]; exact hdet
      exact isUnit_of_mul_isUnit_right h'
    refine ⟨⟨((Matrix.isUnit_iff_isUnit_det M).2 hdetM).unit, hU⟩, ?_⟩
    exact Units.ext hM1

end PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL

end
