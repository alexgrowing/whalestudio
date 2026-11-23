import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TransvMem
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcWitnessExistence.DataXOfModel
import Formalism.LocalToGlobal.ProjectiveLattices.ExtendedPointBaseChange
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLam
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn
open scoped Matrix

namespace GlobalTheory.TransvModel

theorem herm_smul_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r) (S : Set E)
    (hΛ : X.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ S, ∃ u ∈ X.L', v = a • u}) {v : Fin r → E} (hv : v ∈ X.L')
    {x : Fin r → E} (hx : x ∈ X.Λ) : FD.herm X.Gm x v • v ∈ X.Λ := by
  rw [hΛ] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, u, hu, rfl⟩ := hx
    rw [GlobalTheory.TransvLevel.herm_smul_left, mul_smul, hΛ]
    exact Submodule.subset_span ⟨a, ha, _, GlobalTheory.FlagData.smul_mem_of_isIntegral _ (X.L'_int u hu v hv) hv, rfl⟩
  | zero => simp [FD.herm]
  | add x y _ _ hx hy =>
    have : FD.herm X.Gm (x + y) v = FD.herm X.Gm x v + FD.herm X.Gm y v := (X.toData.hermL v).map_add x y
    rw [this, add_smul]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [← algebraMap_smul E c x, GlobalTheory.TransvLevel.herm_smul_left, mul_smul, algebraMap_smul]
    exact Submodule.smul_mem _ c hx

theorem transv_mem_of_span {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r) (S : Set E)
    (hΛ : X.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ S, ∃ u ∈ X.L', v = a • u}) (m : ℕ)
    (hmκ : IsIntegral ℤ ((m : E) * X.κ0)) (v : Fin r → E) (hv : v ∈ X.L') (hiso : FD.herm X.Gm v v = 0) (b : E)
    (hb : cc b = b) (hbi : IsIntegral ℤ b) :
    ∃ γ ∈ X.Γ, ∀ τ : X.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 =
      X.flowMat v τ ((((X.g * m : ℕ) : ℝ) : ℂ) * τ.1 b) := by
  have hξ' : IsCMField.complexConj E X.ξ0 = -X.ξ0 := X.ξ0_im
  have hκc : IsCMField.complexConj E X.κ0 = -X.κ0 := by
    rcases X.κ0_xi with h | h <;> simp [h, hξ', map_ofNat]
  have hb' : IsCMField.complexConj E b = b := hb
  set α : E := ((X.g * m : ℕ) : E) * b * X.κ0 with hαdef
  have hα : cc α = -α := by
    simp [hαdef, cc, hb', hκc]
  have key : ∀ x ∈ X.Λ, (b * ((m : E) * X.κ0)) • (FD.herm X.Gm x v • v) ∈ X.Λ := fun x hx =>
    GlobalTheory.FlagData.smul_mem_of_isIntegral _ (hbi.mul hmκ) (herm_smul_mem X S hΛ hv hx)
  have e : ∀ x, (α * FD.herm X.Gm x v) • v =
      (X.g : E) • ((b * ((m : E) * X.κ0)) • (FD.herm X.Gm x v • v)) := by
    intro x
    rw [smul_smul, smul_smul, hαdef]
    congr 1
    push_cast
    ring
  have key' : ∀ x ∈ X.Λ, (α * FD.herm X.Gm x v) • v ∈ X.Λ := fun x hx => by
    rw [e]
    exact GlobalTheory.FlagData.smul_mem_of_isIntegral _ (isIntegral_natCast _) (key x hx)
  refine ⟨GlobalTheory.FlagData.transv X.Gm hiso α, X.cong _
    ⟨GlobalTheory.FlagData.herm_transvMat X.Gm_herm hiso hα, fun x => ?_⟩ (fun x hx => ?_), fun τ => ?_⟩
  · change x ∈ X.Λ ↔ transvMat X.Gm v α *ᵥ x ∈ X.Λ
    rw [GlobalTheory.FlagData.transvMat_mulVec]
    refine ⟨fun hx => Submodule.add_mem _ hx (key' x hx), fun hx => ?_⟩
    have h := key' _ hx
    rw [GlobalTheory.FlagData.herm_add_smul_left, hiso, mul_zero, add_zero] at h
    simpa using Submodule.sub_mem _ hx h
  · refine ⟨_, key x hx, ?_⟩
    change transvMat X.Gm v α *ᵥ x - x = _
    rw [GlobalTheory.FlagData.transvMat_mulVec, add_sub_cancel_left, e]
  · change (transvMat X.Gm v α).map τ.1 = _
    refine TransvectionPeriodicity.transvMat_map X.toData v τ α _ ?_
    rw [hαdef, map_mul, map_mul, TransvectionPeriodicity.emb_kappa X.toData τ, map_natCast]
    push_cast
    ring

theorem xiR_eq (D : D7) : xiR D = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := by
  have e1 : D.host.φ₀ D.host.xi0 =
      -1 / ((Ideal.absNorm D.host.ccK : ℂ) * D.host.φ₀ D.host.sqrtMinusD) := by
    unfold Formalism.BasicNotions.Host.xi0; simp [map_div₀, map_mul, map_neg, map_natCast]
  have e2 : ‖D.host.φ₀ D.host.sqrtMinusD‖ = Real.sqrt D.host.d := by
    have h0 : (D.host.φ₀ D.host.sqrtMinusD) ^ 2 = -(D.host.d : ℂ) := by
      rw [← map_pow, Formalism.BasicNotions.Host.sqrtMinusD_sq D.host, map_neg, map_natCast]
    rw [← Real.sqrt_sq (norm_nonneg (D.host.φ₀ D.host.sqrtMinusD)), ← norm_pow, h0, norm_neg,
      Complex.norm_natCast]
  unfold xiR; rw [e1, norm_div, norm_neg, norm_one, norm_mul, Complex.norm_natCast, e2]

theorem isIntegral_level_mul_kappa {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : FD.Data E r)
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d) (τ : E →+* ℂ) (hτ : ‖τ X.ξ0‖ = 1 / ((N : ℝ) * Real.sqrt d)) :
    IsIntegral ℤ (((N * d : ℕ) : E) * X.κ0) := by
  have h1 : τ (cc X.ξ0) = (starRingEnd ℂ) (τ X.ξ0) := IsCMField.complexEmbedding_complexConj E τ X.ξ0
  rw [X.ξ0_im, map_neg] at h1
  have h2 := Complex.mul_conj' (τ X.ξ0)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h3 : ‖τ X.ξ0‖ ^ 2 * ((N : ℝ) ^ 2 * d) = 1 := by
    rw [hτ, div_pow, mul_pow, Real.sq_sqrt hd'.le]
    field_simp
  have h4 : ((‖τ X.ξ0‖ : ℝ) : ℂ) ^ 2 * ((N : ℂ) ^ 2 * d) = 1 := by exact_mod_cast h3
  rw [← h1] at h2
  have h5 : X.κ0 ^ 2 = 4 * X.ξ0 ^ 2 := by
    rcases X.κ0_xi with h | h <;> rw [h] <;> ring
  have h6 : (((N * d : ℕ) : E) * X.κ0) ^ 2 = ((-(4 * d : ℤ) : ℤ) : E) := by
    apply τ.injective
    rw [mul_pow, h5, map_mul, map_mul, map_pow, map_pow, map_natCast, map_intCast, map_ofNat]
    push_cast
    linear_combination (-4 * (N : ℂ) ^ 2 * (d : ℂ) ^ 2) * h2 - 4 * (d : ℂ) * h4
  refine IsIntegral.of_pow two_pos ?_
  rw [h6]
  exact isIntegral_algebraMap (R := ℤ)

theorem transv_model : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ), InR D j → ∀ (k : (T.U j T.σ₀).Comp) (Xx : DataX D.host.E D.R.r), Xx.toData = ((T.U j T.σ₀).X k) → Xx.g = T.Q.l.M → Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} → ((D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK * D.host.d : ℕ) : ℝ) * Xx.k0 = 2 * (D.host.g 0 * D.host.g 1 : ℕ) * Real.sqrt D.host.d ∧ ∀ v ∈ Xx.L', FD.herm ((T.U j T.σ₀).X k).Gm v v = 0 → ∀ b : D.host.E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ ((T.U j T.σ₀).X k).Γ, ∀ τ : ((T.U j T.σ₀).X k).Ψ, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = ((T.U j T.σ₀).X k).flowMat v τ ((((D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK * D.host.d : ℕ) : ℝ) : ℂ) * τ.1 b) := by
  intro D T h j hj k Xx hX hg hΛ
  have hM : Xx.g = D.host.g 0 * D.host.g 1 := hg.trans h.pins.2.1.1
  have hN : 0 < Ideal.absNorm D.host.ccK :=
    Nat.pos_of_ne_zero fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hd : 0 < D.host.d := by have := D.host.qd_big.2; omega
  have habs : ∀ τ : D.host.E →+* ℂ,
      ‖τ Xx.ξ0‖ = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := fun τ => by
    rw [← xiR_eq, ← h.xiAbs j hj T.σ₀ T.good_σ₀ k τ, ← hX]
  rw [← hX]
  refine ⟨?_, fun v hv hiso b hb hbi => ?_⟩
  · obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ Xx.Ψ := by
      by_cases h0 : D.host.φ₀ ∈ Xx.Ψ
      · exact ⟨_, h0⟩
      · by_contra hc
        exact h0 ((Xx.cmType _).2 fun h1 => hc ⟨_, h1⟩)
    have h1 := Xx.ξ0_abs ⟨τ, hτ⟩
    rw [habs] at h1
    have hN' : (0 : ℝ) < Ideal.absNorm D.host.ccK := by exact_mod_cast hN
    have hd' : (0 : ℝ) < D.host.d := by exact_mod_cast hd
    have hs := Real.sqrt_pos.2 hd'
    have hk : Xx.k0 = 2 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := by
      rw [div_eq_mul_one_div, h1]; ring
    have hss := Real.mul_self_sqrt hd'.le
    rw [hk]
    push_cast
    field_simp
    linear_combination (-((D.host.g 0 : ℝ) * D.host.g 1)) * hss
  · have := transv_mem_of_span Xx (D.host.AA : Set D.host.E) hΛ (Ideal.absNorm D.host.ccK * D.host.d)
      (isIntegral_level_mul_kappa Xx.toData hN hd D.host.φ₀ (habs _)) v hv hiso b hb hbi
    rwa [hM, ← mul_assoc] at this

end GlobalTheory.TransvModel
