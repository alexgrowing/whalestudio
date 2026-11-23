import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RepRatioEqZero
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomLocFOfVdZero
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LamGEqOneOfOrtho
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsTotPosDefOfSmul

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace PinD

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem core (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (n : 𝓞 F) (hn : n ≠ 0)
    (S : VecSplit (algebraMap F K (n : F) • h) (algebraMap F K (n : F) • h'))
    (hs' : (algebraMap F K (n : F) • h).IsSymm) (hd' : IsTotPosDef (algebraMap F K (n : F) • h))
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (hx : (algebraMap F K (n : F) • h) S.x₀ S.x₀ = algebraMap F K (n : F)) :
    ∃ L₀ : Submodule (𝓞 K) V, Submodule.IsLattice K L₀ ∧
      Formalism.HermitianLatticesTheory.IsIntegralLat (algebraMap F K (n : F) • h) L₀ ∧
      repRatio (algebraMap F K (n : F) • h) L₀ 𝔭 n ≠ 0 ∧
      psiP S L₀ 𝔭 = (Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * vF 𝔭 n) *
        alphaStd K 𝔭 (finrank K V - 1) * repRatio (algebraMap F K (n : F) • h) L₀ 𝔭 n := by
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
  have hc : algebraMap F K (n : F) ≠ 0 := (map_ne_zero (algebraMap F K)).2 hnF
  set S₁ := unscale hc S with hS₁
  have hx1 : h S₁.x₀ S₁.x₀ = 1 := by
    have e := hx
    rw [smul_form_apply] at e
    exact mul_left_cancel₀ hc (e.trans (mul_one _).symm)
  have hs : h.IsSymm := isSymm_of_smul hF hc hs'
  have hd : IsTotPosDef h := isTotPosDef_of_smul hK hF hs hd' hx1
  have h1𝔭 : (1 : 𝓞 F) ∉ 𝔭 := fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hx1' : h S₁.x₀ S₁.x₀ = algebraMap F K ((1 : 𝓞 F) : F) := by
    rw [hx1]
    simp
  obtain ⟨L₀, hL, hLi, hxL, hvd⟩ := exists_lattice_vd_le_one hK hF hs hd h𝔭 hx1' h1𝔭
  have hs₁' : h'.IsSymm := S₁.isSymm hs
  have hd₁' : IsTotPosDef h' := S₁.isTotPosDef hd
  have hsc' := S.isSymm hs'
  have hdc' := S.isTotPosDef hd'
  have hadj : S₁.adjoin (S₁.cut L₀) = L₀ := S₁.adjoin_cut hx1 hLi hxL
  have hC : Submodule.IsLattice K (S₁.cut L₀) := by
    rw [← S₁.isLattice_adjoin_iff, hadj]
    exact hL
  have hCi : Formalism.HermitianLatticesTheory.IsIntegralLat h' (S₁.cut L₀) := Formalism.HermitianLattices.Ext.L3.UnimodularLocalization.isIntegralLat_cut S₁ hLi
  have hvdC : vd h' (S₁.cut L₀) 𝔭 = vd h L₀ 𝔭 := PinC.vd_cut hK hF hs hd S₁ hx1 hL hLi hxL h𝔭
  have hm := S₁.finrank_add_one
  have hLic := PinA.isIntegralLat_smul hLi n
  have hCic := PinA.isIntegralLat_smul hCi n
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    have hb : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hb)
  have hsplit : alphaL h L₀ 𝔭 = alphaN h L₀ 𝔭 1 * alphaL h' (S₁.cut L₀) 𝔭 :=
    alphaL_split hK hF hs hd S₁ hx1 hL hLi hxL h𝔭 hvd
  have hαpos : 0 < alphaL h L₀ 𝔭 := alphaL_pos hK hF hs hd hL hLi h𝔭
  have hαC : 0 < alphaL h' (S₁.cut L₀) 𝔭 := alphaL_pos hK hF hs₁' hd₁' hC hCi h𝔭
  have hαN : alphaN h L₀ 𝔭 1 ≠ 0 := by
    intro h0
    rw [hsplit, h0, zero_mul] at hαpos
    exact lt_irrefl _ hαpos
  have hNsm : alphaN (algebraMap F K (n : F) • h) L₀ 𝔭 n =
      (Ideal.absNorm 𝔭 : ℝ) ^ vF 𝔭 n * alphaN h L₀ 𝔭 1 := by
    have e := alphaN_smul hK hF hs hd hL hLi h𝔭 hn hs' hd' (by omega) one_ne_zero
    rwa [mul_one] at e
  have hLsm := alphaL_smul hK hF hs hd hL hLi h𝔭 hn hs' hd'
  have hvsm := PinA.vd_smul hK hF hs hd hL hLi h𝔭 hn
  have hvT : vd (algebraMap F K (n : F) • h') (locF 𝔭 (S₁.cut L₀)) 𝔭 =
      vd h' (S₁.cut L₀) 𝔭 + finrank K V' * vF 𝔭 n := by
    rw [vd_locF hK hF hsc' hdc' hC hCic h𝔭]
    exact PinA.vd_smul hK hF hs₁' hd₁' hC hCi h𝔭 hn
  have hαT : alphaL (algebraMap F K (n : F) • h') (locF 𝔭 (S₁.cut L₀)) 𝔭 =
      (Ideal.absNorm 𝔭 : ℝ) ^ (vF 𝔭 n * finrank K V' ^ 2) * alphaL h' (S₁.cut L₀) 𝔭 := by
    rw [← alphaL_smul hK hF hs₁' hd₁' hC hCi h𝔭 hn hsc' hdc']
    unfold alphaL
    simp only [akCount_locF hF _ (S₁.cut L₀) 𝔭 h𝔭]
  have hrep : IsLocReps S₁ L₀ 𝔭 {locF 𝔭 (S₁.cut L₀)} :=
    PinC.isLocReps_cut hK hF hs hd S₁ hx1 hL hLi hxL h𝔭 hvd
  have hrep' : IsLocReps S L₀ 𝔭 {locF 𝔭 (S₁.cut L₀)} := isLocReps_scale hF hc S hL hLi h𝔭 hrep
  have hpsi : psiP S L₀ 𝔭 = lamP (algebraMap F K (n : F) • h') (locF 𝔭 (S₁.cut L₀)) 𝔭 := by
    rw [psiP_eq_sum hK hF hs' hd' S hL hLic h𝔭 hrep', Finset.sum_singleton, fibLoc_unscale hc,
      PinC.fibLoc_cut hK hF hs hd S₁ hx1 hL hLi hxL h𝔭 hvd]
    simp
  refine ⟨L₀, hL, hLic, ?_, ?_⟩
  · unfold repRatio
    rw [hNsm, hLsm]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ hN) (mul_ne_zero (pow_ne_zero _ hN) hαN))
      (mul_ne_zero (pow_ne_zero _ hN) hαpos.ne')
  · rw [hpsi]
    unfold lamP repRatio
    rw [hvT, hαT, hNsm, hLsm, hvsm, hsplit, hvdC, ← hm, Nat.add_sub_cancel]
    have hA := hαC.ne'
    field_simp
    ring

end PinD

theorem liPin : LIPin := by
  unfold LIPin
  intro K F _ _ _ _ _ _ hK hF V V' _ _ _ _ _ _ _ _ _ _ h h' S 𝔭 n hs hd h𝔭 hn hx
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn
  have hc : algebraMap F K (n : F) ≠ 0 := (map_ne_zero _).2 hnF
  obtain ⟨h₀, rfl⟩ : ∃ h₀ : V →ₗ⋆[K] V →ₗ[K] K, algebraMap F K (n : F) • h₀ = h :=
    ⟨(algebraMap F K (n : F))⁻¹ • h, by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]⟩
  obtain ⟨h₀', rfl⟩ : ∃ h₀' : V' →ₗ⋆[K] V' →ₗ[K] K, algebraMap F K (n : F) • h₀' = h' :=
    ⟨(algebraMap F K (n : F))⁻¹ • h', by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]⟩
  exact PinD.core hK hF n hn S hs hd h𝔭 hx

end Formalism.HermitianLattices.Ext.L3
