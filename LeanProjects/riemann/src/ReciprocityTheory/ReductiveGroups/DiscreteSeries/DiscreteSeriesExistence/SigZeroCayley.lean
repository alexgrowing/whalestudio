import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroCayleyA

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

theorem exists_cayley_unitary (k r : ℕ) (hk : 1 ≤ k) :
    ∃ P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Formalism.MainNotions.S.IsCayleyU k r (Formalism.MainNotions.CayleySignature.eps48 k r) P := by
  obtain ⟨π, hπ⟩ := szc_exists_perm k r hk
  have hCC := szc_CC k r
  have hCs := szc_Cstar k r
  have hCHC := szc_CHC k r
  set C := szcMk (szcTau k r) (szcC k r) (szcO k r) with hCdef
  have hPs : (C.submatrix π id)ᴴ = C.submatrix id π := by
    rw [Matrix.conjTranspose_submatrix, hCs]
  have hPP : C.submatrix π id * (C.submatrix π id)ᴴ = 1 := by
    rw [hPs, ← Matrix.submatrix_mul C C (⇑π) id (⇑π) Function.bijective_id, hCC,
      Matrix.submatrix_one_equiv]
  have hPsP : (C.submatrix π id)ᴴ * C.submatrix π id = 1 := mul_eq_one_comm.mp hPP
  have hJ : Formalism.REAL.Jm (Formalism.MainNotions.CayleySignature.eps48 k r) =
      C.submatrix π id * Formalism.QuantumDeterminants.Hpk k r * (C.submatrix π id)ᴴ := by
    have e1 : C.submatrix π id * Formalism.QuantumDeterminants.Hpk k r * (C.submatrix π id)ᴴ =
        (C * Formalism.QuantumDeterminants.Hpk k r * C).submatrix π π := by
      rw [hPs, Matrix.submatrix_mul (C * Formalism.QuantumDeterminants.Hpk k r) C (⇑π) id (⇑π) Function.bijective_id,
        Matrix.submatrix_mul C (Formalism.QuantumDeterminants.Hpk k r) (⇑π) id id Function.bijective_id,
        Matrix.submatrix_id_id]
    rw [e1, hCHC, Matrix.submatrix_diagonal_equiv]
    unfold Formalism.REAL.Jm
    congr 1
    funext i
    have h := hπ i
    simp only [Function.comp_apply, szcD]
    cases he : Formalism.MainNotions.CayleySignature.eps48 k r i
    · have h' : r + k ≤ (π i).val := h.mp he
      simp [not_lt.mpr h']
    · have h' : (π i).val < r + k := by
        by_contra hh
        have := h.mpr (not_lt.mp hh)
        rw [he] at this
        exact Bool.noConfusion this
      simp [h']
  refine ⟨C.submatrix π id, ?_⟩
  unfold Formalism.MainNotions.S.IsCayleyU Formalism.MainNotions.S.IsCayley
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse hPP)
  · rw [hJ]
    calc (C.submatrix π id)ᴴ * (C.submatrix π id * Formalism.QuantumDeterminants.Hpk k r * (C.submatrix π id)ᴴ) *
          C.submatrix π id
        = ((C.submatrix π id)ᴴ * C.submatrix π id) * Formalism.QuantumDeterminants.Hpk k r *
            ((C.submatrix π id)ᴴ * C.submatrix π id) := by simp only [Matrix.mul_assoc]
      _ = Formalism.QuantumDeterminants.Hpk k r := by rw [hPsP, Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    exact hPP

section BlockSumPreservesCone

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem szc_Kset_UJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) :
    g ∈ Formalism.MainNotions.S.UJset ε := by
  obtain ⟨hu, hJ⟩ := hg
  have h1 : gᴴ * g = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 hu
  show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  rw [Matrix.mul_assoc, ← hJ, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem szc_Kset_mul {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε)
    (hh : h ∈ Formalism.REAL.Kset ε) : g * h ∈ Formalism.REAL.Kset ε := by
  refine ⟨Submonoid.mul_mem _ hg.1 hh.1, ?_⟩
  rw [Matrix.mul_assoc, hh.2, ← Matrix.mul_assoc, hg.2, Matrix.mul_assoc]

variable {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
  {U V : Matrix (Fin n) (Fin n) ℂ}

theorem szc_stab_iff (hU : U ∈ Formalism.REAL.Kset ε) (hV : V ∈ Formalism.REAL.Kset ε) (hUV : U * V = 1)
    (S' : Submodule ℂ H) :
    Formalism.MainNotions.S.IsKStableOn ε (fun g => σ (U * g * V)) S' ↔ Formalism.MainNotions.S.IsKStableOn ε σ S' := by
  constructor
  · intro h g hg v hv
    have e : U * (V * g * U) * V = g := by
      calc U * (V * g * U) * V = (U * V) * g * (U * V) := by simp only [Matrix.mul_assoc]
        _ = g := by rw [hUV, Matrix.one_mul, Matrix.mul_one]
    have := h (V * g * U) (szc_Kset_mul (szc_Kset_mul hV hg) hU) v hv
    simpa only [e] using this
  · intro h g hg v hv
    exact h (U * g * V) (szc_Kset_mul (szc_Kset_mul hU hg) hV) v hv

theorem szc_conj_V (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (hU : U ∈ Formalism.REAL.Kset ε)
    (hV : V ∈ Formalism.REAL.Kset ε) (hVU : V * U = 1) {t : Matrix (Fin n) (Fin n) ℂ}
    (ht : t ∈ Formalism.REAL.Kset ε) (v : H) : σ t (σ V v) = σ V (σ (U * t * V) v) := by
  have hUtV : U * t * V ∈ Formalism.REAL.Kset ε := szc_Kset_mul (szc_Kset_mul hU ht) hV
  have e : t * V = V * (U * t * V) := by
    calc t * V = (V * U) * t * V := by rw [hVU, Matrix.one_mul]
      _ = V * (U * t * V) := by simp only [Matrix.mul_assoc]
  calc σ t (σ V v) = σ (t * V) v := by
        rw [hσ.1.2 t (szc_Kset_UJ ht) V (szc_Kset_UJ hV), ContinuousLinearMap.comp_apply]
    _ = σ V (σ (U * t * V) v) := by
        rw [e, hσ.1.2 V (szc_Kset_UJ hV) _ (szc_Kset_UJ hUtV), ContinuousLinearMap.comp_apply]

theorem szc_conj_U (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (hU : U ∈ Formalism.REAL.Kset ε)
    (hV : V ∈ Formalism.REAL.Kset ε) (hVU : V * U = 1) {t : Matrix (Fin n) (Fin n) ℂ}
    (ht : t ∈ Formalism.REAL.Kset ε) (v : H) : σ (U * t * V) (σ U v) = σ U (σ t v) := by
  have hUtV : U * t * V ∈ Formalism.REAL.Kset ε := szc_Kset_mul (szc_Kset_mul hU ht) hV
  have e : U * t * V * U = U * t := by rw [Matrix.mul_assoc (U * t), hVU, Matrix.mul_one]
  calc σ (U * t * V) (σ U v) = σ (U * t * V * U) v := by
        rw [hσ.1.2 _ (szc_Kset_UJ hUtV) U (szc_Kset_UJ hU), ContinuousLinearMap.comp_apply]
    _ = σ (U * t) v := by rw [e]
    _ = σ U (σ t v) := by
        rw [hσ.1.2 U (szc_Kset_UJ hU) t (szc_Kset_UJ ht), ContinuousLinearMap.comp_apply]

theorem szc_kType_conj (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (hU : U ∈ Formalism.REAL.Kset ε)
    (hV : V ∈ Formalism.REAL.Kset ε) (hUV : U * V = 1) (hVU : V * U = 1)
    {Λ : Fin n → ℝ} {S : Submodule ℂ H}
    (hS : Formalism.MainNotions.S.IsKTypeOf ε (fun g => σ (U * g * V)) Λ S) : Formalism.MainNotions.S.IsKTypeOf ε σ Λ S := by
  obtain ⟨hfd, hst, hirr, ⟨v, hvS, hv0, hvw⟩, hdom⟩ := hS
  have hst' := (szc_stab_iff hU hV hUV S).mp hst
  refine ⟨hfd, hst', ?_, ?_, ?_⟩
  · intro S' hle hS'
    exact hirr S' hle ((szc_stab_iff hU hV hUV S').mpr hS')
  · refine ⟨σ V v, hst' V hV v hvS, ?_, ?_⟩
    · intro h0
      apply hv0
      have := hσ.2.1 V (szc_Kset_UJ hV) v
      rw [h0, norm_zero] at this
      exact norm_eq_zero.mp this.symm
    · intro θ hθ
      have h1 : σ (U * _ * V) v = _ := hvw θ hθ
      rw [szc_conj_V hσ hU hV hVU hθ, h1, map_smul]
  · intro μ w hw hw0 hww
    refine hdom μ (σ U w) (hst' U hU w hw) ?_ ?_
    · intro h0
      apply hw0
      have := hσ.2.1 U (szc_Kset_UJ hU) w
      rw [h0, norm_zero] at this
      exact norm_eq_zero.mp this.symm
    · intro θ hθ
      show σ (U * _ * V) (σ U w) = _
      rw [szc_conj_U hσ hU hV hVU hθ, hww θ hθ, map_smul]

theorem szc_lowKSub_le (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (hU : U ∈ Formalism.REAL.Kset ε)
    (hV : V ∈ Formalism.REAL.Kset ε) (hUV : U * V = 1) (hVU : V * U = 1) (lam : Fin n → ℝ) :
    Formalism.MainNotions.S.lowKSub ε lam (fun g => σ (U * g * V)) ≤ Formalism.MainNotions.S.lowKSub ε lam σ := by
  unfold Formalism.MainNotions.S.lowKSub
  exact sSup_le_sSup (fun S hS => szc_kType_conj hσ hU hV hUV hVU hS)

end BlockSumPreservesCone

section CayleyFacts

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem szc_unit_facts {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) : Pᴴ * P = 1 ∧ P * Pᴴ = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp hP.2
  rw [Matrix.star_eq_conjTranspose] at h
  exact ⟨mul_eq_one_comm.mp h, h⟩

theorem szc_J_eq {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) : Formalism.REAL.Jm ε = P * Formalism.QuantumDeterminants.Hpk k r * Pᴴ := by
  obtain ⟨_, h2⟩ := szc_unit_facts hP
  rw [← hP.1.2]
  calc Formalism.REAL.Jm ε = (P * Pᴴ) * Formalism.REAL.Jm ε * (P * Pᴴ) := by
        rw [h2, Matrix.one_mul, Matrix.mul_one]
    _ = P * (Pᴴ * Formalism.REAL.Jm ε * P) * Pᴴ := by simp only [Matrix.mul_assoc]

theorem szc_K_mem {P Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (hQ : Formalism.MainNotions.S.IsCayleyU k r ε Q) :
    P * Qᴴ ∈ Formalism.REAL.Kset ε := by
  obtain ⟨hP1, hP2⟩ := szc_unit_facts hP
  obtain ⟨hQ1, _⟩ := szc_unit_facts hQ
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    calc P * Qᴴ * (Q * Pᴴ) = P * (Qᴴ * Q) * Pᴴ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQ1, Matrix.mul_one, hP2]
  · have eP := szc_J_eq hP
    have eQ := szc_J_eq hQ
    calc P * Qᴴ * Formalism.REAL.Jm ε = P * Qᴴ * (Q * Formalism.QuantumDeterminants.Hpk k r * Qᴴ) := by rw [← eQ]
      _ = P * (Qᴴ * Q) * Formalism.QuantumDeterminants.Hpk k r * Qᴴ := by simp only [Matrix.mul_assoc]
      _ = (P * Formalism.QuantumDeterminants.Hpk k r * Pᴴ) * (P * Qᴴ) := by
          rw [hQ1, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Pᴴ P, hP1, Matrix.one_mul]
      _ = Formalism.REAL.Jm ε * (P * Qᴴ) := by rw [← eP]

end CayleyFacts

section Transport

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
  {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem isDSHpk_of_isDS (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (hDS : Formalism.MainNotions.S.IsDS ε lam σ) :
    Formalism.MainNotions.S.IsDSHpk k r ε lam (fun g => σ (P * g * P⁻¹)) := by
  refine ⟨P, hP, ?_⟩
  have hdet := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  have key : ∀ g, P * (P⁻¹ * g * P) * P⁻¹ = g := by
    intro g
    calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [Matrix.mul_nonsing_inv P hdet, Matrix.one_mul, Matrix.mul_one]
  simp only [key]
  exact hDS

theorem isURepOn_UH_of (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) :
    Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (fun g => σ (P * g * P⁻¹)) := by
  obtain ⟨hP1, _⟩ := szc_unit_facts hP
  have hPi : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv hP1
  have hJ := szc_J_eq hP
  have hmap : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), P * g * P⁻¹ ∈ Formalism.MainNotions.S.UJset ε := by
    intro g hg
    have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
    rw [hPi]
    show (P * g * Pᴴ)ᴴ * Formalism.REAL.Jm ε * (P * g * Pᴴ) = Formalism.REAL.Jm ε
    rw [hJ]
    calc (P * g * Pᴴ)ᴴ * (P * Formalism.QuantumDeterminants.Hpk k r * Pᴴ) * (P * g * Pᴴ)
        = P * (gᴴ * (Pᴴ * P) * Formalism.QuantumDeterminants.Hpk k r * (Pᴴ * P) * g) * Pᴴ := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = P * Formalism.QuantumDeterminants.Hpk k r * Pᴴ := by simp only [hP1, Matrix.mul_one, hg']
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · show σ (P * 1 * P⁻¹) = 1
    rw [Matrix.mul_one, Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hP.1.1)]
    exact hσ.1.1
  · intro a ha b hb
    show σ (P * (a * b) * P⁻¹) = (σ (P * a * P⁻¹)).comp (σ (P * b * P⁻¹))
    rw [← hσ.1.2 _ (hmap a ha) _ (hmap b hb)]
    congr 1
    rw [hPi]
    calc P * (a * b) * Pᴴ = P * a * (Pᴴ * P) * b * Pᴴ := by
          rw [hP1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = P * a * Pᴴ * (P * b * Pᴴ) := by simp only [Matrix.mul_assoc]
  · intro g hg v
    exact hσ.2.1 _ (hmap g hg) v
  · intro v
    have hc : Continuous
        (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => P * g * P⁻¹) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact (hσ.2.2 v).comp hc.continuousOn (fun g hg => hmap g hg)

theorem isLowUnit_of_isLowUnitH (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (hDS : Formalism.MainNotions.S.IsDS ε lam σ) {w : H}
    (hw : Formalism.MainNotions.S.IsLowUnitH k r ε lam (fun g => σ (P * g * P⁻¹)) w) : Formalism.MainNotions.S.IsLowUnit ε lam σ w := by
  obtain ⟨P', hP', hw1, hw2⟩ := hw
  have hU : P * P'ᴴ ∈ Formalism.REAL.Kset ε := szc_K_mem hP hP'
  have hV : P' * Pᴴ ∈ Formalism.REAL.Kset ε := szc_K_mem hP' hP
  obtain ⟨hP1, hP2⟩ := szc_unit_facts hP
  obtain ⟨hQ1, hQ2⟩ := szc_unit_facts hP'
  have hPi : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv hP1
  have hQi : P'⁻¹ = P'ᴴ := Matrix.inv_eq_left_inv hQ1
  have hUV : P * P'ᴴ * (P' * Pᴴ) = 1 := by
    calc P * P'ᴴ * (P' * Pᴴ) = P * (P'ᴴ * P') * Pᴴ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQ1, Matrix.mul_one, hP2]
  have hVU : P' * Pᴴ * (P * P'ᴴ) = 1 := by
    calc P' * Pᴴ * (P * P'ᴴ) = P' * (Pᴴ * P) * P'ᴴ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hP1, Matrix.mul_one, hQ2]
  have key : ∀ g, P * (P'⁻¹ * g * P') * P⁻¹ = P * P'ᴴ * g * (P' * Pᴴ) := by
    intro g
    rw [hPi, hQi]
    simp only [Matrix.mul_assoc]
  have hw2' : w ∈ Formalism.MainNotions.S.lowKSub ε lam (fun g => σ (P * (P'⁻¹ * g * P') * P⁻¹)) := hw2
  simp only [key] at hw2'
  exact ⟨hw1, szc_lowKSub_le hDS.2.2.1 hU hV hUV hVU lam hw2'⟩

end Transport

end ReciprocityTheory.ChartRestriction.DS
