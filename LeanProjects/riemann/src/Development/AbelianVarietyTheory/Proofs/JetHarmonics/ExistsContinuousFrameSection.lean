import Mathlib
import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DensityConstantOfParts

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate

set_option linter.unusedSimpArgs false

noncomputable section

namespace GlobalTheory.FrameSection

def secDiag (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Equiv.Perm (Fin (r + 1))) (d0 : Fin (r + 1) → ℂ) :
    Fin (r + 1) → ℂ :=
  fun b => if π b = Fin.last r then ((Real.sqrt (Tz k r z' / Tz k r z) : ℝ) : ℂ) * d0 b else d0 b

def secKappa (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Equiv.Perm (Fin (r + 1))) (d0 : Fin (r + 1) → ℂ) : ℝ :=
  Real.sqrt (1 / Real.sqrt (Tz k r z') ^ 2 -
    Real.sqrt (Tz k r z') ^ 2 / Complex.normSq (secDiag k r z z' π d0 (Fin.last r)))

def secMat (k r : ℕ) (z z' ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (π : Equiv.Perm (Fin (r + 1)))
    (d0 : Fin (r + 1) → ℂ) : B.Mat k r :=
  m₀ * smat (Hpk k r) (uB z' ν') (wB z' ν' (Real.sqrt (Tz k r z')))
    (YB π (secDiag k r z z' π d0) z' ν' (Real.sqrt (Tz k r z')) (secKappa k r z z' π d0))

variable {k r : ℕ}

theorem sec_spec {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (hbase : Formalism.FourierDecayAlt.D.IsBaseFrame S ν' m₀) (π : Equiv.Perm (Fin (r + 1))) (d0 : Fin (r + 1) → ℂ)
    (hd0 : ∀ a, d0 a ≠ 0) (hB : π (Fin.last r) = Fin.last r)
    (hG : Tz k r S.z * Tz k r S.z' < Complex.normSq (d0 (Fin.last r))) :
    secMat k r S.z S.z' ν' m₀ π d0 ∈ B.GV k r ∧ Zhat k r S.z S.z' (secMat k r S.z S.z' ν' m₀ π d0) = C2.monoP π d0 ∧
      Formalism.FourierDecayAlt.D.IsDFrame S ν' m₀ (secMat k r S.z S.z' ν' m₀ π d0) := by
  obtain ⟨hν, hνz, hνν, ⟨hmU, hmfix⟩, hmz⟩ := hbase
  have hme : ∀ a : Fin r, m₀ *ᵥ ee k r a = ee k r a := fun a => (hmfix a a.isLt).1
  have hms : ∀ a : Fin r, m₀ *ᵥ es k r a = es k r a := fun a => (hmfix a a.isLt).2
  have hz := S.z_mem
  have hz' := S.z'_mem
  have hT := S.T_pos
  have hT' := S.T'_pos
  set s := Real.sqrt (Tz k r S.z') with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hT'
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hs2 : s ^ 2 = Tz k r S.z' := Real.sq_sqrt hT'.le
  have hzz : herm (Hpk k r) S.z' S.z' = -((s : ℂ) ^ 2) := by
    rw [herm_self_alt]; congr 1; exact_mod_cast hs2.symm
  have hzz0 : herm (Hpk k r) S.z' S.z' ≠ 0 := by rw [hzz]; simpa using hs'
  set μ := Real.sqrt (Tz k r S.z' / Tz k r S.z) with hμdef
  have hμ : 0 < μ := Real.sqrt_pos.2 (div_pos hT' hT)
  have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  have hμ2 : μ ^ 2 = Tz k r S.z' / Tz k r S.z := Real.sq_sqrt (div_pos hT' hT).le
  set d' : Fin (r + 1) → ℂ := fun b => if π b = Fin.last r then (μ : ℂ) * d0 b else d0 b with hd'def
  have hd' : ∀ b, d' b ≠ 0 := by
    intro b; simp only [hd'def]; split_ifs
    · exact mul_ne_zero hμ' (hd0 b)
    · exact hd0 b
  have hne : ∀ b : Fin r, π b.castSucc ≠ Fin.last r := by
    intro b h; rw [← hB] at h; exact Fin.castSucc_ne_last b (π.injective h)
  have hdl : d' (Fin.last r) = (μ : ℂ) * d0 (Fin.last r) := by simp [hd'def, hB]
  have hdb : ∀ b : Fin r, d' b.castSucc = d0 b.castSucc := by
    intro b; simp only [hd'def]; rw [if_neg (hne b)]

  set N := Complex.normSq (d' (Fin.last r)) with hNdef
  have hN : s ^ 4 < N := by
    rw [hNdef, hdl, Complex.normSq_mul, Complex.normSq_ofReal]
    have : s ^ 4 = μ * μ * (Tz k r S.z * Tz k r S.z') := by
      have e1 : μ * μ = μ ^ 2 := by ring
      rw [e1, hμ2, show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2]; field_simp

    rw [this]; exact mul_lt_mul_of_pos_left hG (by positivity)
  have hN0 : 0 < N := lt_trans (by positivity) hN
  set κ := Real.sqrt (1 / s ^ 2 - s ^ 2 / N) with hκdef
  have hκarg : 0 < 1 / s ^ 2 - s ^ 2 / N := by
    rw [sub_pos, div_lt_div_iff₀ hN0 (by positivity)]; nlinarith [hN]
  have hκ0 : 0 < κ := Real.sqrt_pos.2 hκarg
  have hκ2 : κ ^ 2 = 1 / s ^ 2 - s ^ 2 / N := Real.sq_sqrt hκarg.le
  have hκr : κ ^ 2 * s ^ 2 * N = N - s ^ 4 := by rw [hκ2]; field_simp
  have hDD : d' (Fin.last r) * conj (d' (Fin.last r)) = ((N : ℝ) : ℂ) := by rw [hNdef, Complex.mul_conj]
  have hκ : (κ : ℂ) ^ 2 * (s : ℂ) ^ 2 * (d' (Fin.last r) * conj (d' (Fin.last r))) =
      d' (Fin.last r) * conj (d' (Fin.last r)) - (s : ℂ) ^ 4 := by
    rw [hDD]; exact_mod_cast hκr
  set Y := YB π d' S.z' ν' s κ with hYdef
  set σ := smat (Hpk k r) (uB S.z' ν') (wB S.z' ν' s) Y with hσdef
  have hσU : σ ∈ UH (Hpk k r) :=
    sig_UH Y hz' hν hs hzz hνz hνν (YB_gram π d' hz' hν hs hzz hνz hνν hd' κ hκ hB)
      (fun x hx i => YB_perp π d' κ x hx i)
  have hσu : ∀ i, σ *ᵥ uB S.z' ν' i = Y i := sig_u Y hz' hν hs hzz hνz hνν
  have hγ : m₀ * σ ∈ UH (Hpk k r) := mul_UH hmU hσU
  have hzν := herm_zν hνz
  have hσe : ∀ b : Fin r, σ *ᵥ ee k r b = Y (Sum.inl (Sum.inl b)) := fun b => hσu (Sum.inl (Sum.inl b))
  have hσz : σ *ᵥ S.z' = Y (Sum.inr 0) := hσu (Sum.inr 0)
  have hσn : σ *ᵥ ν' = Y (Sum.inr 1) := hσu (Sum.inr 1)
  have hZ : Zhat k r S.z S.z' (m₀ * σ) = C2.monoP π d0 := by
    ext a b
    rw [reduced_matrix_of_stabilizer m₀ σ hmU hme μ hμ.ne' hmz]
    rcases cast_or_last b with hbl | ⟨b', rfl⟩ <;> rcases cast_or_last a with hal | ⟨a', rfl⟩
    · subst hbl hal
      rw [fvec_lastI, fvec_lastI, hσz]
      simp [hYdef, YB, C2.monoP, hB, hdl, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz', h_w_ee hν, h_w_es hz', h_w_es hν, h_ee_w hz', h_ee_w hν, h_es_w hz', h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]
      field_simp
    · subst hbl
      rw [fvec_lastI, fvec_cs, hσz]
      have h1 : ¬ (a'.castSucc = π (Fin.last r)) := by rw [hB]; exact Fin.castSucc_ne_last a'
      simp [hYdef, YB, C2.monoP, h1, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz', h_w_ee hν, h_w_es hz', h_w_es hν, h_ee_w hz', h_ee_w hν, h_es_w hz', h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]
    · subst hal
      rw [fvec_lastI, fvec_cs, hσe]
      have h1 : ¬ (Fin.last r = π b'.castSucc) := fun h => hne b' h.symm
      simp [hYdef, YB, C2.monoP, h1, B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz', h_w_ee hν, h_w_es hz', h_w_es hν, h_ee_w hz', h_ee_w hν, h_es_w hz', h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]
    · rw [fvec_cs, fvec_cs, hσe]
      have e : (a'.castSucc = π b'.castSucc) ↔ (piX π b' = a') := by
        rw [← piX_spec π b' (hne b')]; constructor
        · intro h; exact (Fin.castSucc_injective _ h).symm
        · rintro rfl; rfl
      simp [hYdef, YB, C2.monoP, e, hdb b', B2x4.herm_smul_left, B2x4.herm_smul_right, herm_rsmul_left, herm_rsmul_right, B2x4.herm_add_left, B2x4.herm_add_right, B2x4.herm_sub_left, B2x4.herm_sub_right, herm_neg_left, herm_neg_right, h_w_ee hz', h_w_ee hν, h_w_es hz', h_w_es hν, h_ee_w hz', h_ee_w hν, h_es_w hz', h_es_w hν, hzz, hνz, hνν, hzν, Complex.conj_ofReal]
  have hγu : IsUnit (m₀ * σ).det := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).unit _ hγ
  have hm0u : IsUnit m₀.det := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).unit _ hmU
  have hDl : d0 (Fin.last r) ≠ 0 := hd0 _
  have hDc : conj (d0 (Fin.last r)) ≠ 0 := by simpa using hDl
  have hsec : secMat k r S.z S.z' ν' m₀ π d0 = m₀ * σ := rfl
  rw [hsec]
  refine ⟨hγ, hZ, ?_, ?_, ?_⟩
  ·
    refine ⟨μ * κ, mul_pos hμ hκ0, ?_⟩
    have hcof : Formalism.FourierDecayAlt.D.cofR S (m₀ * σ) =
        ((C2.monoP π d0).det * (d0 (Fin.last r))⁻¹) • (m₀ *ᵥ (σ *ᵥ S.z')) := by
      unfold Formalism.FourierDecayAlt.D.cofR; rw [hZ]
      rw [Finset.sum_eq_single (Fin.last r)]
      · rw [monomialMatrix_adj π d0 hd0, if_pos hB, fvec_lastI, Matrix.mulVec_mulVec]
      · intro b _ hbne
        have : π b ≠ Fin.last r := by intro h; rw [← hB] at h; exact hbne (π.injective h)
        rw [monomialMatrix_adj π d0 hd0, if_neg this]; simp
      · simp
    rw [hcof, prW_smul, orthoProj_m0_intertwine m₀ hmU hme hms hz hz' μ hμ.ne' hmz hzz0, hσz]
    simp only [hYdef, YB, Matrix.cons_val_zero]
    rw [prW_smul, prW_sub, prW_smul, prW_perp hν hνz, prW_self hz' hzz0, sub_zero, hZ,
      Matrix.mulVec_smul, Matrix.mulVec_smul, smul_smul, smul_smul, hdl]
    congr 1
    push_cast; field_simp
  ·
    refine ⟨κ, hκ0, ?_⟩
    have hcof : Formalism.FourierDecayAlt.D.cofL S (m₀ * σ) =
        (conj ((C2.monoP π d0).det * (d0 (Fin.last r))⁻¹)) • S.z := by
      unfold Formalism.FourierDecayAlt.D.cofL; rw [hZ]
      rw [Finset.sum_eq_single (Fin.last r)]
      · rw [monomialMatrix_adj π d0 hd0, if_pos hB, fvec_lastI]
      · intro a _ hane; rw [monomialMatrix_adj π d0 hd0, if_neg (by rw [hB]; exact Ne.symm hane)]; simp
      · simp
    set Dp := d' (Fin.last r) with hDpdef
    have hvec : (-(conj Dp / (s : ℂ) ^ 2)) • Y (Sum.inr 0) + ((κ : ℂ) * conj Dp) • Y (Sum.inr 1) = S.z' := by
      simp only [hYdef, YB, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [show ∀ (α β p q c1 c2 : ℂ), α • (p • (c1 • ν' - S.z')) + β • (q • (ν' - c2 • S.z')) =
          (α * p * c1 + β * q) • ν' + (-(α * p) - β * q * c2) • S.z' from by intros; module]
      have h0 : -(conj Dp / (s : ℂ) ^ 2) * (Dp / (s : ℂ) ^ 2) * ((κ : ℂ) * (s : ℂ) ^ 2) +
          (κ : ℂ) * conj Dp * (Dp / (s : ℂ) ^ 2) = 0 := by field_simp; ring
      have h1 : -(-(conj Dp / (s : ℂ) ^ 2) * (Dp / (s : ℂ) ^ 2)) - (κ : ℂ) * conj Dp * (Dp / (s : ℂ) ^ 2) * (κ : ℂ) = 1 := by
        field_simp
        first | linear_combination -hκ | linear_combination hκ | linear_combination (-1 : ℂ) * hκ
      rw [h0, h1, zero_smul, zero_add, one_smul]
    set w := (μ : ℂ)⁻¹ • ((-(conj Dp / (s : ℂ) ^ 2)) • S.z' + ((κ : ℂ) * conj Dp) • ν') with hwdef
    have hw : (m₀ * σ) *ᵥ w = S.z := by
      rw [hwdef, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        hσz, hσn, hvec, hmz, smul_smul, inv_mul_cancel₀ hμ', one_smul]
    have hinv : (m₀ * σ)⁻¹ *ᵥ S.z = w := by
      rw [← hw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hγu, Matrix.one_mulVec]
    rw [hcof, Matrix.mulVec_smul, hinv, hwdef, prW_smul, prW_smul, prW_add, prW_smul, prW_smul, prW_self hz' hzz0,
      prW_perp hν hνz, hZ, smul_zero, zero_add, smul_smul, smul_smul, hdl]
    congr 1
    simp only [map_mul, map_inv₀, Complex.conj_ofReal]
    field_simp
  ·
    intro u hu
    set v := m₀⁻¹ *ᵥ u with hvdef
    have hmv : m₀ *ᵥ v = u := by
      rw [hvdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hm0u, Matrix.one_mulVec]
    have hv1 : ∀ a : Fin r, herm (Hpk k r) v (ee k r a) = 0 := by
      intro a; have := (hu a.castSucc).1; rw [fvec_cs, ← hmv, ← hme a, herm_m0_mulVec_invariant m₀ hmU] at this; exact this
    have hzeq : S.z = (μ : ℂ)⁻¹ • (m₀ *ᵥ S.z') := by rw [hmz, smul_smul, inv_mul_cancel₀ hμ', one_smul]
    have hv2 : herm (Hpk k r) v S.z' = 0 := by
      have := (hu (Fin.last r)).1
      rw [fvec_lastI, ← hmv, hzeq, B2x4.herm_smul_right, herm_m0_mulVec_invariant m₀ hmU] at this
      simpa [hμ'] using this
    have hvY : ∀ a, herm (Hpk k r) v (σ *ᵥ fvec k r S.z' a) = 0 := by
      intro a; have := (hu a).2; rw [← hmv, ← Matrix.mulVec_mulVec, herm_m0_mulVec_invariant m₀ hmU] at this; exact this
    have hv3 : herm (Hpk k r) v ν' = 0 := by
      have := hvY (Fin.last r)
      rw [fvec_lastI, hσz] at this
      simp only [hYdef, YB, Matrix.cons_val_zero, B2x4.herm_smul_right, B2x4.herm_sub_right, hv2, sub_zero] at this
      rcases mul_eq_zero.1 this with h | h
      · exfalso; have := hd' (Fin.last r); simp at h
        rcases h with h | h
        · exact this h
        · exact hs.ne' h
      · rcases mul_eq_zero.1 h with h | h
        · exfalso; simp at h
          rcases h with h | h
          · exact hκ0.ne' h
          · exact hs.ne' h
        · exact h
    have hv4 : ∀ c : Fin r, herm (Hpk k r) v (es k r c) = 0 := by
      intro c
      have hbl : π.symm c.castSucc ≠ Fin.last r := by
        intro h; have h2 := congrArg π h; rw [π.apply_symm_apply, hB] at h2
        exact Fin.castSucc_ne_last c h2
      obtain ⟨b', hb'⟩ := (cast_or_last (π.symm c.castSucc)).resolve_left hbl
      have hpx : piX π b' = c := by
        apply Fin.castSucc_injective; rw [piX_spec π b' (hne b'), ← hb', π.apply_symm_apply]
      have := hvY b'.castSucc
      rw [fvec_cs, hσe] at this
      simp only [hYdef, YB, hpx, B2x4.herm_smul_right] at this
      rcases mul_eq_zero.1 this with h | h
      · exfalso; have := hd' b'.castSucc; simp at h; exact this h
      · exact h
    have hfix : σ *ᵥ v = v := by
      apply sig_fix Y v
      intro i
      rcases i with ((b | b) | i)
      · exact hv4 b
      · exact hv1 b
      · fin_cases i
        · simp [wB, B2x4.herm_smul_right, herm_neg_right, hv2]
        · simpa [wB] using hv3
    have hinv : (m₀ * σ)⁻¹ *ᵥ u = v := by
      have : (m₀ * σ) *ᵥ v = u := by rw [← Matrix.mulVec_mulVec, hfix, hmv]
      rw [← this, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hγu, Matrix.one_mulVec]
    rw [hinv, ← hmv, orthoProj_m0_intertwine m₀ hmU hme hms hz hz' μ hμ.ne' hmz hzz0]

theorem secDiag_cont (z z' : Fin (2 * r + k + 1) → ℂ) (π : Equiv.Perm (Fin (r + 1))) (b : Fin (r + 1)) :
    Continuous fun d0 => secDiag k r z z' π d0 b := by
  unfold secDiag
  split_ifs <;> fun_prop

theorem secDiag_ne {z z' : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (π : Equiv.Perm (Fin (r + 1))) {d0 : Fin (r + 1) → ℂ} (hd0 : ∀ a, d0 a ≠ 0) (b : Fin (r + 1)) :
    secDiag k r z z' π d0 b ≠ 0 := by
  have hμ : 0 < Real.sqrt (Tz k r z' / Tz k r z) := Real.sqrt_pos.2 (div_pos hT' hT)
  have hμ' : ((Real.sqrt (Tz k r z' / Tz k r z) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  unfold secDiag
  split_ifs
  · exact mul_ne_zero hμ' (hd0 b)
  · exact hd0 b

theorem secKappa_cont {z z' : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (π : Equiv.Perm (Fin (r + 1))) :
    ContinuousOn (fun d0 => secKappa k r z z' π d0) {c | ∀ a, c a ≠ 0} := by
  unfold secKappa
  refine ContinuousOn.sqrt (continuousOn_const.sub (continuousOn_const.div ?_ ?_))
  · exact (Complex.continuous_normSq.comp (secDiag_cont z z' π _)).continuousOn
  · intro c hc
    exact (Complex.normSq_pos.2 (secDiag_ne hT hT' π hc _)).ne'

theorem secY_cont {z z' : Fin (2 * r + k + 1) → ℂ} (ν' : Fin (2 * r + k + 1) → ℂ) (hT : 0 < Tz k r z)
    (hT' : 0 < Tz k r z') (π : Equiv.Perm (Fin (r + 1))) (s : ℝ) (i : (Fin r ⊕ Fin r) ⊕ Fin 2) :
    ContinuousOn (fun d0 => YB π (secDiag k r z z' π d0) z' ν' s (secKappa k r z z' π d0) i)
      {c | ∀ a, c a ≠ 0} := by
  have hd := fun b => (secDiag_cont z z' π b).continuousOn (s := {c : Fin (r + 1) → ℂ | ∀ a, c a ≠ 0})
  have hκ : ContinuousOn (fun d0 => ((secKappa k r z z' π d0 : ℝ) : ℂ)) {c | ∀ a, c a ≠ 0} :=
    Complex.continuous_ofReal.comp_continuousOn (secKappa_cont hT hT' π)
  rcases i with ((b | b) | i)
  · simp only [YB]
    fun_prop
  · have h : ContinuousOn (fun d0 => (conj (secDiag k r z z' π d0 b.castSucc))⁻¹)
        {c : Fin (r + 1) → ℂ | ∀ a, c a ≠ 0} := by
      refine ContinuousOn.inv₀ (Complex.continuous_conj.comp_continuousOn (hd _)) ?_
      intro c hc
      simpa using secDiag_ne hT hT' π hc _
    simp only [YB]
    fun_prop
  · fin_cases i
    · simp only [YB, Fin.zero_eta, Matrix.cons_val_zero]
      fun_prop
    · simp only [YB, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      fun_prop

theorem secMat_cont {z z' : Fin (2 * r + k + 1) → ℂ} (ν' : Fin (2 * r + k + 1) → ℂ) (hT : 0 < Tz k r z)
    (hT' : 0 < Tz k r z') (m₀ : B.Mat k r) (π : Equiv.Perm (Fin (r + 1))) :
    ContinuousOn (secMat k r z z' ν' m₀ π) {c | ∀ a, c a ≠ 0} := by
  unfold secMat
  refine continuousOn_const.mul ?_
  refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => ?_
  simp only [smat, Matrix.of_apply]
  refine continuousOn_pi.1 ?_ a
  unfold smap
  refine continuousOn_const.add (continuousOn_finset_sum _ fun i _ => ?_)
  have h := secY_cont ν' hT hT' π (Real.sqrt (Tz k r z')) i
  fun_prop

theorem ptMatN_bigPt_eq (r : ℕ) (c : Fin (r + 1) → ℂ) :
    D.ptMatN (TBB.bigPt r c) (r + 1) = C2.monoP 1 c := by
  have h : D.ptMatN (TBB.bigPt r c) (r + 1) = U.hMat 1 c := Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt c
  rw [h]
  ext a b
  unfold U.hMat
  rw [Matrix.mul_diagonal]
  by_cases h : a = b
  · subst h; simp [U.wP, C2.monoP]
  · simp [U.wP, C2.monoP, h]

theorem exists_continuous_frame_section :
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
      (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r), D.IsBaseFrame Bs ν' m₀ →
      ∃ γ : (Fin (r + 1) → ℂ) → B.Mat k r,
        ContinuousOn γ {c | (∀ a, c a ≠ 0) ∧ Tz k r Bs.z * Tz k r Bs.z' < Complex.normSq (c (Fin.last r))} ∧
        ∀ c : Fin (r + 1) → ℂ, (∀ a, c a ≠ 0) → Tz k r Bs.z * Tz k r Bs.z' < Complex.normSq (c (Fin.last r)) →
          γ c ∈ B.GV k r ∧ Zhat k r Bs.z Bs.z' (γ c) = D.ptMatN (TBB.bigPt r c) (r + 1) ∧
            D.IsDFrame Bs ν' m₀ (γ c) := by
  intro k r Wp Wq _ _ _ _ _ _ Bs ν' m₀ hbase
  refine ⟨secMat k r Bs.z Bs.z' ν' m₀ 1, (secMat_cont ν' Bs.T_pos Bs.T'_pos m₀ 1).mono fun c hc => hc.1, ?_⟩
  intro c hc hG
  rw [ptMatN_bigPt_eq]
  exact sec_spec Bs ν' m₀ hbase 1 c hc rfl hG

end GlobalTheory.FrameSection
