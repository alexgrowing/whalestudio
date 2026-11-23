import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CoefDecay
import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecInfPf

open Matrix
open scoped InnerProductSpace ContDiff

noncomputable section

namespace Formalism.L2.SG.Pf.CoefCC

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.L2.SG.Pf.CoefDecay

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem exists_exp_of_gapOK {ε : Fin (2 * r + k + 1) → Bool} {h : ℝ} (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) {A : ℝ}
    (hA0 : 0 ≤ A) (hA : A ≤ h / 2) : ∃ m' : ℕ, ReciprocityTheory.ChartRestriction.DS.thrStar ε + m' < h ∧ A ≤ m' := by
  obtain ⟨-, h120, -, -⟩ := hok
  have hn : 1 ≤ 2 * r + k + 1 := by omega
  have ht := Formalism.L2.SG.BesselDiscreteSeries.thrStar_le hn ε
  have hn1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast hn
  have hn3 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := one_le_pow₀ hn1
  refine ⟨⌈A⌉₊, ?_, Nat.le_ceil A⟩
  have hc := Nat.ceil_lt_add_one hA0
  linarith

section congr

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ev_congr {f₁ f₂ : B.Mat k r → E} (hf : ∀ y ∈ B.GV k r, f₁ y = f₂ y) :
    ∀ (ks : List Bool) (xs : List (B.Mat k r)), (∀ X ∈ xs, B.inLie k r X) →
      ∀ g ∈ B.GV k r, PI.ComplexConjugateDerivative.ev ks xs f₁ g = PI.ComplexConjugateDerivative.ev ks xs f₂ g
  | [], xs, _, g, hg => by cases xs <;> exact hf g hg
  | _ :: _, [], _, g, hg => hf g hg
  | b :: ks, X :: xs, hx, g, hg =>
    PI.ComplexConjugateDerivative.D_congr (b := b) (fun y hy => ev_congr hf ks xs (fun Y hY => hx Y (List.mem_cons_of_mem _ hY)) y hy) hg
      (hx X List.mem_cons_self)

theorem inCC_congr {A : ℝ} {m : ℕ} {f₁ f₂ : B.Mat k r → E} (hf : ∀ y ∈ B.GV k r, f₁ y = f₂ y)
    (h1 : B.InCC (k := k) (r := r) A m f₁) : B.InCC (k := k) (r := r) A m f₂ := by
  obtain ⟨c, hck, hb⟩ := h1
  refine ⟨c, fun g₀ hg₀ => ?_, fun u w hu hw hl g hg => ?_⟩
  · obtain ⟨U, f', hU, h0, hc, he⟩ := hck g₀ hg₀
    exact ⟨U, f', hU, h0, hc, fun y hy hyG => (hf y hyG).symm.trans (he y hy hyG)⟩
  · have e : B.dLR u w f₂ g = B.dLR u w f₁ g := by
      rw [PI.ComplexConjugateDerivative.dLR_eq_ev, PI.ComplexConjugateDerivative.dLR_eq_ev]
      exact (ev_congr hf _ (u ++ w) (fun X hX => by
        rcases List.mem_append.1 hX with h | h
        · exact (hu X h).1
        · exact (hw X h).1) g hg).symm
    rw [e]
    exact hb u w hu hw hl g hg

end congr

theorem coefM_translate_inCC {σ : B.Mat k r → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn (B.GV k r) σ) {A : ℝ}
    (hdec : ∀ a ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ, ∀ b ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ,
      ∃ C : ℝ, ∀ g ∈ B.GV k r, B.gN g ^ A * ‖⟪a, σ g b⟫_ℂ‖ ≤ C)
    {v v' : H} (hv : v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ)
    (hv' : v' ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ) {a b : B.Mat k r} (ha : a ∈ B.GV k r)
    (hb : b ∈ B.GV k r) (ξ : Wp) (ξ' : Wq) (m : ℕ) :
    B.InCC (k := k) (r := r) A m (fun g => Formalism.MainNotions.S.Pv.BetaCut.coefM σ v v' ξ ξ' (a * g * b)) := by
  have hai : a⁻¹ ∈ B.GV k r := Formalism.MainNotions.LowestKTypeMultiplicity.UH_inv ha
  have hdet : IsUnit a.det := Formalism.MainNotions.LowestKTypeMultiplicity.UH_det ha
  have haa : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a hdet
  refine inCC_congr (f₁ := Formalism.MainNotions.S.Pv.BetaCut.coefM σ (σ a⁻¹ v) (σ b v') ξ ξ') (fun g hg => ?_)
    (coefM_inCC_of_dec hσ hdec (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hv hai)
      (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hv' hb) ξ ξ' m)
  rw [coefM_eq, coefM_eq]
  show ⟪σ a⁻¹ v, σ g (σ b v')⟫_ℂ • rk1 ξ ξ' = ⟪v, σ (a * g * b) v'⟫_ℂ • rk1 ξ ξ'
  congr 1
  let L : H →ₗᵢ[ℂ] H := ⟨(σ a⁻¹ : H →ₗ[ℂ] H), fun x => hσ.2.1 _ hai x⟩
  have hgb : g * b ∈ B.GV k r := Formalism.MainNotions.LowestKTypeMultiplicity.UH_mul hg hb
  have e1 : σ (a * g * b) v' = σ a (σ g (σ b v')) := by
    rw [Matrix.mul_assoc, hσ.1.2 a ha _ hgb, hσ.1.2 g hg b hb]; rfl
  have e2 : σ a⁻¹ (σ a (σ g (σ b v'))) = σ g (σ b v') := by
    have := hσ.1.2 _ hai _ ha
    rw [haa, hσ.1.1] at this
    have h3 := congrArg (fun T : H →L[ℂ] H => T (σ g (σ b v'))) this
    simpa using h3.symm
  rw [e1, ← L.inner_map_map v (σ a (σ g (σ b v')))]
  show ⟪σ a⁻¹ v, σ g (σ b v')⟫_ℂ = ⟪σ a⁻¹ v, σ a⁻¹ (σ a (σ g (σ b v')))⟫_ℂ
  rw [e2]

theorem coefM_smul (σ : B.Mat k r → (H →L[ℂ] H)) (v v' : H) (ξ : Wp) (ξ' : Wq) (c : ℂ) :
    c • Formalism.MainNotions.S.Pv.BetaCut.coefM σ v v' ξ ξ' = Formalism.MainNotions.S.Pv.BetaCut.coefM σ v v' (c • ξ) ξ' := by
  funext g
  ext x
  simp only [Pi.smul_apply, Formalism.MainNotions.S.Pv.BetaCut.coefM, ContinuousLinearMap.smulRight_apply, _root_.smul_apply]
  rw [smul_comm c, smul_comm c]

theorem dec_of_DS {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    (hlam : Formalism.QuantumDeterminants.IsHCParam lam) {h : ℝ} (hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (m' : ℕ)
    (hm' : ReciprocityTheory.ChartRestriction.DS.thrStar ε + m' < h) {A : ℝ} (hA : A ≤ m') [CompleteSpace H]
    {σ : B.Mat k r → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsDSHpk k r ε lam σ) :
    ∀ a ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ, ∀ b ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ,
      ∃ C : ℝ, ∀ g ∈ B.GV k r, B.gN g ^ A * ‖⟪a, σ g b⟫_ℂ‖ ≤ C := by
  obtain ⟨C, Ws, -, hC⟩ := ReciprocityTheory.ChartRestriction.DS.DecInf.decSm hlam hgap m' hm' hσ
  intro a ha b hb
  refine ⟨C * (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w b‖).sum *
      (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w a‖).sum, fun g hg => ?_⟩
  have h1 := PI.ComplexConjugateDerivative.one_le_gN hg
  calc B.gN g ^ A * ‖⟪a, σ g b⟫_ℂ‖ ≤ B.gN g ^ (m' : ℝ) * ‖⟪a, σ g b⟫_ℂ‖ :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le h1 hA) (norm_nonneg _)
    _ = B.gN g ^ m' * ‖⟪a, σ g b⟫_ℂ‖ := by rw [Real.rpow_natCast]
    _ ≤ _ := hC b hb a ha g hg

theorem smul_coefM_translate_inCC_kfin_gapOK {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    (hlam : Formalism.QuantumDeterminants.IsHCParam lam) {h : ℝ} (hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) {A : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ h / 2) [CompleteSpace H]
    {σ : B.Mat k r → (H →L[ℂ] H)} (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) {v v' : H}
    (hv : PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v) (hv' : PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v')
    {a b : B.Mat k r} (ha : a ∈ B.GV k r) (hb : b ∈ B.GV k r) (c : ℂ) (ξ : Wp) (ξ' : Wq) (m : ℕ) :
    B.InCC (k := k) (r := r) A m (fun g => (c • Formalism.MainNotions.S.Pv.BetaCut.coefM σ v v' ξ ξ') (a * g * b)) := by
  obtain ⟨m', hm', hAm⟩ := exists_exp_of_gapOK (ε := ε) hok hA0 hA
  have hks := Formalism.L2.SG.LitS.kFinSmooth_pi Formalism.L2.SG.Pf.k_finite_smooth
  rw [coefM_smul]
  exact coefM_translate_inCC (Formalism.MainNotions.LowestKTypeMultiplicity.urep_of_DS hσ) (dec_of_DS hlam hgap m' hm' hAm hσ)
    (hks k r ε lam H σ (by exact hlam) hσ v hv) (hks k r ε lam H σ (by exact hlam) hσ v' hv') ha hb (c • ξ) ξ' m

end Formalism.L2.SG.Pf.CoefCC
