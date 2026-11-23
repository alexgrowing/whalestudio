import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.FormalDegreeConstantDiscrete
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundOfCompact
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ShiftApply

open Matrix

noncomputable section

namespace CompanionTheory.Zuck

open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData ReciprocityTheory.ChartRestriction.DS

def thr (n : ℕ) (ε : Fin n → Bool) : ℝ := max (thrStar ε) (G2.thrS ε)

theorem thr_le {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) : thr n ε ≤ 43 * (n : ℝ) ^ 3 := by
  have hp : pOf ε ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have hq : qOf ε ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have h0 : S7.q0 ε ≤ n := by unfold S7.q0; omega
  have hp' : (pOf ε : ℝ) ≤ n := by exact_mod_cast hp
  have hq' : (qOf ε : ℝ) ≤ n := by exact_mod_cast hq
  have h0' : (S7.q0 ε : ℝ) ≤ n := by exact_mod_cast h0
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (n : ℝ) ≤ n ^ 3 := le_self_pow₀ h1 (by norm_num)
  have h3 : (n : ℝ) ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ h1 (by norm_num)
  have h4 : Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ 2 * n := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
  have h5 : 16 * (n : ℝ) * S7.q0 ε ≤ 16 * n * n := by gcongr
  have h6 : (n : ℝ) * pOf ε * qOf ε ≤ n * n * n := by gcongr
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_) <;> nlinarith

theorem dsigW_SK {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx k r → (H →L[ℂ] H)) : ∀ (W : List (Mx k r)) (v : H),
    Formalism.MainNotions.S.dsigW (k := k) (r := r) σ W v = PI.UpqRep.dsigW (k := k) (r := r) σ W v
  | [], _ => rfl
  | X :: W, v => by
    change Formalism.MainNotions.S.dsig σ X (Formalism.MainNotions.S.dsigW σ W v) = PI.UpqRep.dsig σ X (PI.UpqRep.dsigW σ W v)
    rw [dsigW_SK σ W v]; rfl

theorem zuckerman_library_bounds : Lib thr where
  zg := fun n ε μ H _ _ _ σ hμ hσ h hg ht =>
    have ht' : G2.thrS ε + 1 < h := lt_of_le_of_lt (by unfold thr; linarith [le_max_right (thrStar ε) (G2.thrS ε)]) ht
    ⟨G2.zuckerman_tensor_exists n ε μ H σ hμ hσ h hg ht', G2.zuckerman_dual_tensor_exists n ε μ H σ hμ hσ h hg ht'⟩
  dec := by
    intro k r ε μ U h m hU hg ht
    obtain ⟨C, Ws, hWs, hC⟩ := DecInf.decSm hU.1 hg m
      (lt_of_le_of_lt (by unfold thr; linarith [le_max_left (thrStar ε) (G2.thrS ε)]) ht) (σ := U.R.σ) hU.2
    refine ⟨C, Ws, fun W hW => (hWs W hW).2, fun u hu v hv g hg' => ?_⟩
    have h1 := hC u hu v hv g hg'
    simp only [dsigW_SK] at h1
    exact h1
  uniq := by
    intro k r ε μ R R' h hR hR' hg ht
    have h2 : 2 * ((2 * r + k + 1 : ℕ) : ℝ) < h :=
      lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right (thrStar ε) (G2.thrS ε))) ht
    obtain ⟨P, hP, hd⟩ := hR.2
    obtain ⟨P', hP', hd'⟩ := hR'.2
    have hU' := CompanionTheory.LimBd.SchurHpk.isURepOn_of_ds hR'.2
    obtain ⟨e, he⟩ := (G2.discrete_series_props_large_gap _ ε μ hR.1 h hg h2 R.H (fun g => R.σ (P⁻¹ * g * P)) hd).2.2.2.2 R'.H
      (fun g => R'.σ (P'⁻¹ * g * P')) hd'
    have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
    have hPu' : IsUnit P'.det := (Matrix.isUnit_iff_isUnit_det _).1 hP'.1.1
    have hb : P⁻¹ * P' ∈ GG k r := by
      have h1 : P⁻¹ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, Matrix.mul_nonsing_inv _ hPu, conjTranspose_one]
      show (P⁻¹ * P')ᴴ * PI.UpqRep.Hpk k r * (P⁻¹ * P') = PI.UpqRep.Hpk k r
      calc (P⁻¹ * P')ᴴ * PI.UpqRep.Hpk k r * (P⁻¹ * P')
          = P'ᴴ * (P⁻¹ᴴ * Pᴴ) * PI.UpqRep.Jm ε * (P * P⁻¹) * P' := by
            rw [← hP.1.2]; simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [h1, Matrix.mul_nonsing_inv _ hPu, Matrix.mul_one, Matrix.mul_one, hP'.1.2]
    obtain ⟨-, ha, hmul⟩ := PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r _ hb
    have hab : (P⁻¹ * P')⁻¹ = P'⁻¹ * P := by rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hPu]
    rw [hab] at ha
    have hba : P⁻¹ * P' * (P'⁻¹ * P) = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hPu', Matrix.nonsing_inv_mul _ hPu]
    have hab' : P'⁻¹ * P * (P⁻¹ * P') = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hPu, Matrix.nonsing_inv_mul _ hPu']
    have hm : ∀ a ∈ GG k r, ∀ b ∈ GG k r, ∀ x, R'.σ (a * b) x = R'.σ a (R'.σ b x) := fun a ha b hb x => by
      rw [hU'.1.2 a ha b hb]; rfl
    let f : R'.H ≃ₗᵢ[ℂ] R'.H := LinearIsometryEquiv.ofSurjective
      ⟨(R'.σ (P⁻¹ * P') : R'.H →ₗ[ℂ] R'.H), hU'.2.1 _ hb⟩ fun y => ⟨R'.σ (P'⁻¹ * P) y, by
        show R'.σ (P⁻¹ * P') (R'.σ (P'⁻¹ * P) y) = y
        rw [← hm _ hb _ ha, hba, hU'.1.1]; rfl⟩
    refine ⟨e.trans f, fun g hg x => ?_⟩
    have h3 := he _ (CompanionTheory.LimBd.SchurHpk.forth_mem hP.1 hg) x
    simp only [CompanionTheory.LimBd.SchurHpk.back_forth hP.1] at h3
    show R'.σ (P⁻¹ * P') (e (R.σ g x)) = R'.σ g (R'.σ (P⁻¹ * P') (e x))
    have hag := (PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r _ ha).2.2 _ hg
    have e1 : P'⁻¹ * (P * g * P⁻¹) * P' = P'⁻¹ * P * g * (P⁻¹ * P') := by simp only [Matrix.mul_assoc]
    rw [h3, e1, ← hm _ hb _ ((PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r _ hag).2.2 _ hb), ← hm _ hg _ hb,
      ← Matrix.mul_assoc (P⁻¹ * P') (P'⁻¹ * P * g), ← Matrix.mul_assoc (P⁻¹ * P') (P'⁻¹ * P), hba, Matrix.one_mul]
  exist := by
    intro k r ε μ μ' R h hR hμ' hg ht
    obtain ⟨P, hP, -⟩ := hR.2
    have h1 : G2.thrS ε < h := lt_of_le_of_lt (le_max_right (thrStar ε) (G2.thrS ε)) ht
    have h2 : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ) := by positivity
    have h3 := Real.sqrt_nonneg (2 * (S7.q0 ε : ℝ))
    obtain ⟨H, _, _, σ, hσ⟩ := G2.discrete_series_exists_large_gap _ ε μ' hμ' h hg (Or.inr (max_lt ((le_max_left _ _).trans_lt h1)
      (by have := (le_max_right _ _).trans_lt h1; linarith)))
    have := hσ.1
    refine ⟨{ H := H, σ := fun g => σ (P * g * P⁻¹) }, hμ', P, hP, ?_⟩
    have e : (fun g => σ (P * (P⁻¹ * g * P) * P⁻¹)) = σ :=
      funext fun g => congrArg σ (CompanionTheory.LimBd.SchurHpk.forth_back hP.1 g)
    show PI.UpqRep.IsDS ε μ' fun g => σ (P * (P⁻¹ * g * P) * P⁻¹)
    rw [e]
    exact hσ

end CompanionTheory.Zuck

end
