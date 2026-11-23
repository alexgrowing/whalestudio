import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocalConditionCharacters.CharPolSupp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.OrdPlain
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompR
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TJacqOfU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TOrdAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DeRhamWeightsOfLocalArtinCharacters
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private UpperTheory.V.Sd.OrdinaryAbove.unr_val UpperTheory.V.Sd.OrdinaryAbove.abs_val UpperTheory.V.Sd.OrdinaryAbove.det_flag from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdAbove
open private embAt_of_induced from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocalGlobalCompatibilityGl2
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win UpperTheory.Gal.SV
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Z.Win.RR.ordAbove_of_alt (hX : ExRS) (hGd : GdOf) :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Sd.OrdAbove := by
  intro hP F Ω _ _ _ _ _ _ l _ hl _ ι ξ s c m a π r H w hw A h
  obtain ⟨-, hm, hs, ha, ⟨lam, hU, hlam⟩, hinf⟩ := H.above w hw
  obtain ⟨χ₀, hpol⟩ := H.pol
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := _root_.UpperTheory.V.Af.local_comp_real_of_printed_results hP.toClassicalTheorems F 2 π w
  have hiso := hiso σ hσ
  obtain ⟨rc, hrc⟩ := recTExists F Ω A w h
  obtain ⟨ar, har, ε, hLV⟩ := toV' hrc
  have hq0 : ((normV w : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (one_lt_normV w).ne_bot
  have hqc : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (one_lt_normV w).ne_bot
  have hqn : ‖((normV w : ℕ) : Qbar l)‖ ≠ 0 := norm_ne_zero_iff.2 hq0
  have hn : ‖ι.symm lam * (normV w : Qbar l) ^ m w 0‖ = 1 := by
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := ι.symm lam * (normV w : Qbar l) ^ m w 0 - a w) (y := a w)
      (by rw [ha]; exact hlam.ne)
    rwa [sub_add_cancel, ha, max_eq_right hlam.le] at this
  have hl0 : lam ≠ 0 := by
    rintro rfl
    simp at hn
  have hn' : ‖ι.symm lam‖ = ‖((normV w : ℕ) : Qbar l)‖ ^ (-m w 0) := by
    rw [norm_mul, norm_zpow] at hn
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_left hn
  obtain ⟨μ₁, μ₂, Lf, hL0, hunr, hval, hLf⟩ := _root_.UpperTheory.V.Sd.jacqOfU_alt hP.toClassicalTheorems F w σ 1 (Units.mk0 lam hl0) one_ne_zero
    (UpperTheory.hasUEigenvalue_of_locIsotypic F w _ π.finPart σ hiso 1 lam hU)
  obtain ⟨s1, s2, hsub, hcen⟩ := UpperTheory.isSubquotient_principalSeries_of_borel_functional F w σ μ₁ μ₂ Lf hL0 hLf
  set ω : Fin 2 → (w.adicCompletion F)ˣ →* ℂˣ := ![μ₁ * GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1), μ₂] with hω
  have hω0 : ∀ t : Weil h, (ω 0 (ar t) : ℂ) = lam ^ (-deg t) := fun t => by
    change ((μ₁ (ar t) * GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1) (ar t) : ℂˣ) : ℂ) = _
    rw [Units.val_mul, UpperTheory.V.Sd.OrdinaryAbove.abs_val, UpperTheory.V.Sd.OrdinaryAbove.unr_val w μ₁ hunr, har.ord_eq, Units.val_zpow_eq_zpow_val, ← mul_zpow, mul_comm, hval]
    rfl
  have hsm : ∀ j, GlobalTheory.SmGL.IsSmoothChar (ω j) := by
    refine Fin.forall_fin_two.2 ⟨?_, s2⟩
    exact Subgroup.isOpen_mono (H₁ := μ₁.ker ⊓ (GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1)).ker)
      (fun x hx => by
        change μ₁ x * GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1) x = 1
        rw [hx.1, hx.2, mul_one])
      (IsOpen.inter s1 (GlobalTheory.SmGL.isSmoothChar_of_isUnram (GlobalTheory.SmGL.isUnram_absPow _ _)))
  have hn0 : ∀ t : Weil h, ‖ι.symm (ω 0 (ar t) : ℂ)‖ = ‖((normV w : ℕ) : Qbar l)‖ ^ (m w 0 * deg t) := fun t => by
    rw [hω0, map_zpow₀, norm_zpow, hn', ← zpow_mul, neg_mul_neg]
  have hn1 : ∀ t : Weil h, ‖ι.symm (ω 1 (ar t) : ℂ)‖ = ‖((normV w : ℕ) : Qbar l)‖ ^ (m w 1 * deg t) := fun t => by
    have h1 := _root_.UpperTheory.V.Sd.OrdinaryAbove.central_weil_ordinary_above hP H hw h har hiso t _ (hcen (ar t))
    have h2 : ((μ₁ (ar t) * μ₂ (ar t) : ℂˣ) : ℂ) = (ω 0 (ar t) : ℂ) * (ω 1 (ar t) : ℂ) * ((normV w : ℕ) : ℂ) ^ deg t := by
      change _ = ((μ₁ (ar t) * GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1) (ar t) : ℂˣ) : ℂ) * (μ₂ (ar t) : ℂ) * _
      rw [Units.val_mul, Units.val_mul, UpperTheory.V.Sd.OrdinaryAbove.abs_val, har.ord_eq, zpow_neg]
      field_simp
    rw [h2, map_mul, map_mul, norm_mul, norm_mul, hn0, map_zpow₀, map_natCast, norm_zpow, ← hs,
      show (m w 0 + m w 1 + 1) * deg t = m w 0 * deg t + m w 1 * deg t + deg t by ring, zpow_add₀ hqn, zpow_add₀ hqn] at h1
    exact mul_left_cancel₀ (zpow_ne_zero _ hqn) (mul_right_cancel₀ (zpow_ne_zero _ hqn) h1)
  have hcp := RR.ps_alg hLV σ ω hsm hsub
  obtain ⟨-, wt, HT, -, -, hall⟩ := hX F Ω l ι 2 one_le_two π χ₀ H.reg hpol
  have hG := hall r H.cont H.att
  have hpl := (Birth.ordPlain F Ω l ι ξ s c m a π r H w σ hσ).elim id fun ⟨B, hB⟩ => hG.plain w B hB σ hσ
  have hdr : Hi.DRat ι h (r.comp (Dec (F := F) A).subtype) (fun _ => Finset.univ.val.map fun j => -m w j)
      fun s => (rc (algNorm σ)).charPol s := by
    intro O _ _ _ Bw hj
    obtain ⟨k1, k2⟩ := hG.loc w σ hσ hpl
    obtain ⟨h1, h2⟩ := k2 A h O Bw hj
    refine ⟨h1, fun τ LL' τ' hτ => ?_, fun s => ?_⟩
    · have e : HT τ = Finset.univ.val.map fun j => -m w j := by
        refine Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective ?_
        have := hG.weights τ _ (hinf τ (embAt_of_induced h Bw hj τ LL' τ' hτ))
        simp only [this, infOf, Multiset.map_map]
        exact Multiset.map_congr rfl fun i _ => by simp
      exact e ▸ h2 τ LL' τ' hτ
    · rw [((k1 A h rc hrc).2 O Bw hj (hGd F Ω A w h rc hrc 2 σ hpl)).2]
  rw [funext hcp] at hdr
  obtain ⟨κ, hκ, hv⟩ := _root_.UpperTheory.deRham_weights_of_localArtin_characters' hP.litN F Ω l hl ι 2 w hw A h ar har _ (H.cont.comp continuous_subtype_val) (m w)
    (fun i j hij => by fin_cases i <;> fin_cases j <;> first | exact hm | exact absurd hij (by decide)) ω hsm
    (Fin.forall_fin_two.2 ⟨hn0, hn1⟩) hdr
  have k0 : ∀ g : ↥(Dec (F := F) A), (g : G F Ω) ∈ Ine (F := F) A → κ 0 g = cycBar F Ω l g ^ m w 0 := fun g hg => by
    have h1 := hv 0 (ineIncl h ⟨g, hg⟩)
    rw [hω0, deg_ineIncl, mul_zero, zpow_zero, neg_zero, zpow_zero, map_one, mul_one, one_mul] at h1
    exact Units.ext (h1.trans (Units.val_zpow_eq_zpow_val _ _).symm)
  refine ⟨κ, hκ, Fin.forall_fin_two.2 ⟨k0, fun g hg => ?_⟩, fun g hg => ?_⟩
  · have h1 := UpperTheory.V.Sd.OrdinaryAbove.det_flag _ κ hκ g
    have h2 : Matrix.GeneralLinearGroup.det (r g) = cycBar F Ω l g ^ s * ξ g := DFunLike.congr_fun H.det (g : G F Ω)
    have h3 : ξ g = 1 := (H.ram w A h).2 (Or.inr hw) hg
    rw [h3, mul_one, ← hs, _root_.zpow_add] at h2
    rw [k0 g hg] at h1
    exact mul_left_cancel (h1.symm.trans h2)
  · let t : Weil h := ⟨g, mem_Weil_of_isFrob h hg⟩
    have hd : deg t = 1 := deg_eq_one_iff.2 hg
    have h1 := hv 0 t⁻¹
    rw [hω0, deg_inv, hd, neg_neg, zpow_one, mul_neg_one, zpow_neg] at h1
    have h2 : (κ 0 g⁻¹ : Qbar l) * ((normV w : Qbar l) ^ m w 0)⁻¹ = ι.symm lam * (cycBar F Ω l (g : G F Ω)⁻¹ : Qbar l) ^ m w 0 := h1
    have h3 : ((κ 0 g⁻¹ * cycBar F Ω l (g : G F Ω) ^ m w 0 : (Qbar l)ˣ) : Qbar l) = ι.symm lam * (normV w : Qbar l) ^ m w 0 := by
      rw [mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ hq0), map_inv (cycBar F Ω l), Units.val_inv_eq_inv_val (cycBar F Ω l _), inv_zpow] at h2
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, h2, mul_right_comm _ _ (_ ^ _), inv_mul_cancel_right₀ (zpow_ne_zero _ (Units.ne_zero _))]
    rw [h3]
    exact hlam
end
