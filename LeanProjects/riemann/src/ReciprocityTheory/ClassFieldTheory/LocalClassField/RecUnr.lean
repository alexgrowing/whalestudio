import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPair
import ReciprocityTheory.ClassFieldTheory.LocalClassField.InflationH2InjectiveOfSameRamification
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem exists_ur_lift (χ : charGrp (GK p K)) (hχ : TrivOn p K (MaximalUnramifiedExtension p K) χ) :
    ∃ t : GalLK p K (MaximalUnramifiedExtension p K) → ℚ, IsLocallyConstant t ∧
      ∀ g : GK p K, (QuotientAddGroup.mk (t (QuotientGroup.mk g)) : QZ) = χ.1 (Additive.ofMul g) := by
  let sec : QZ → ℚ := Function.surjInv (QuotientAddGroup.mk'_surjective (Int.castAddHom ℚ).range)
  have hsec : ∀ q : QZ, (QuotientAddGroup.mk (sec q) : QZ) = q :=
    Function.surjInv_eq (QuotientAddGroup.mk'_surjective (Int.castAddHom ℚ).range)
  let f : GK p K → QZ := fun g => χ.1 (Additive.ofMul g)
  have hf : IsLocallyConstant f := χ.2
  have hfq : ∀ g : GK p K, f (QuotientGroup.mk g : GalLK p K (MaximalUnramifiedExtension p K)).out = f g := by
    intro g
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul (subG p K (MaximalUnramifiedExtension p K)) g
    rw [hn]
    show χ.1 (Additive.ofMul g + Additive.ofMul n.1) = _
    rw [map_add, hχ n.1 n.2, add_zero]
  have hloc : IsLocallyConstant fun q : GalLK p K (MaximalUnramifiedExtension p K) => f q.out := by
    intro s
    rw [← QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.isOpen_preimage]
    have h0 : (QuotientGroup.mk : GK p K → GalLK p K (MaximalUnramifiedExtension p K)) ⁻¹'
        ((fun q : GalLK p K (MaximalUnramifiedExtension p K) => f q.out) ⁻¹' s) = f ⁻¹' s := by
      ext g
      show f (QuotientGroup.mk g : GalLK p K (MaximalUnramifiedExtension p K)).out ∈ s ↔ f g ∈ s
      rw [hfq]
    rw [h0]
    exact hf s
  refine ⟨fun q => sec (f q.out), hloc.comp sec, fun g => ?_⟩
  rw [hsec]
  exact hfq g

variable (p K) in

noncomputable def urOfK (a : Kˣ) : (urT p K).V :=
  toLayer p ⟨ofK p K (Additive.ofMul a), le_Kur (K := K) (ofK_mem p K _)⟩

theorem urOfK_val (a : Kˣ) : (urOfK p K a).1 = ofK p K (Additive.ofMul a) := rfl

theorem exists_ur_cocycle (a : Kˣ) (χ : charGrp (GK p K)) (hχ : TrivOn p K (MaximalUnramifiedExtension p K) χ) :
    ∃ (t : GalLK p K (MaximalUnramifiedExtension p K) → ℚ) (m : (Fin 2 → GalLK p K (MaximalUnramifiedExtension p K)) → ℤ) (z : (urT p K).coch.X 2)
      (hz : (urT p K).coch.d 2 z = 0), IsLocallyConstant t ∧
      (∀ g : GK p K, (QuotientAddGroup.mk (t (QuotientGroup.mk g)) : QZ) = χ.1 (Additive.ofMul g)) ∧
      (∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) ∧ (∀ g, z.1 g = m g • urOfK p K a) ∧
      pairBr p K a χ = (layerInf p K (MaximalUnramifiedExtension p K)).hom.H 2 ((urT p K).coch.cls 2 z hz) := by
  obtain ⟨t, ht, htχ⟩ := exists_ur_lift χ hχ
  have hex : ∀ g : Fin 2 → GalLK p K (MaximalUnramifiedExtension p K), ∃ k : ℤ, (k : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1) := by
    intro g
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (g 0)
    obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (g 1)
    have h0 : (QuotientAddGroup.mk (t (g 0) + t (g 1) - t (g 0 * g 1)) : QZ) = 0 := by
      rw [← hσ, ← hτ, ← QuotientGroup.mk_mul, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_add, htχ, htχ, htχ,
        ofMul_mul, map_add, sub_self]
    exact (QuotientAddGroup.eq_zero_iff _).1 h0
  choose m hm using hex
  have hmc : IsLocallyConstant m := by
    apply IsLocallyConstant.desc m (Int.cast : ℤ → ℚ) _ Int.cast_injective
    have h0 : ((Int.cast : ℤ → ℚ) ∘ m) = fun g => t (g 0) + t (g 1) - t (g 0 * g 1) := funext hm
    rw [h0]
    exact ((ht.comp_continuous (continuous_apply 0)).add (ht.comp_continuous (continuous_apply 1))).sub
      (ht.comp_continuous ((continuous_apply 0).mul (continuous_apply 1)))
  have hzc : Continuous fun g : Fin 2 → GalLK p K (MaximalUnramifiedExtension p K) => m g • urOfK p K a :=
    (hmc.comp fun k : ℤ => k • urOfK p K a).continuous
  let z : (urT p K).coch.X 2 := ⟨fun g => m g • urOfK p K a, hzc⟩
  have hinv := (layer_invariant_iff (urOfK p K a)).2 (ofK_mem p K _)
  have hz : (urT p K).coch.d 2 z = 0 := by
    apply LowDeg.coch_d_eq_zero
    funext g
    have h1 : m ![g 1, g 2] - m ![g 0 * g 1, g 2] + m ![g 0, g 1 * g 2] - m ![g 0, g 1] = 0 := by
      apply Int.cast_injective (α := ℚ)
      push_cast
      rw [hm, hm, hm, hm]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_assoc]
      ring
    rw [LowDeg.dn_two_apply]
    show (urT p K).rho (g 0) (m ![g 1, g 2] • urOfK p K a) - m ![g 0 * g 1, g 2] • urOfK p K a +
      m ![g 0, g 1 * g 2] • urOfK p K a - m ![g 0, g 1] • urOfK p K a = 0
    rw [map_zsmul, hinv, ← sub_smul, ← add_smul, ← sub_smul, h1, zero_smul]
  refine ⟨t, m, z, hz, ht, htχ, hm, fun _ => rfl, ?_⟩
  refine IsPairClass.unique (isPairClass_pairBr a χ)
    ⟨fun g => t (QuotientGroup.mk g), fun g => m fun i => QuotientGroup.mk (g i),
      (layerInf p K (MaximalUnramifiedExtension p K)).hom.f 2 z, by rw [← (layerInf p K (MaximalUnramifiedExtension p K)).hom.comm, hz, map_zero],
      ht.comp_continuous continuous_quot_mk, htχ, fun g => hm _, fun g => rfl, rfl⟩

theorem pairK_unit_unr (hK : FiniteDimensional ℚ_[p] K) (a : Kˣ) (ha : a ∈ UK p K) (χ : charGrp (GK p K))
    (hχ : TrivOn p K (MaximalUnramifiedExtension p K) χ) : pairK p K a χ = 0 := by
  obtain ⟨t, m, z, hz, -, -, -, hzm, h⟩ := exists_ur_cocycle a χ hχ
  have hv : vLayerMap p K (MaximalUnramifiedExtension p K) (urOfK p K a) = 0 := by
    apply Int.cast_injective (α := ℝ)
    rw [vLayerMap_spec p le_Kur, urOfK_val, vbar_apply]
    have ha' : ‖((a : K) : PadicAlgCl p)‖ = 1 := ha
    show (eK p (MaximalUnramifiedExtension p K) : ℝ) * - Real.logb p ‖((a : K) : PadicAlgCl p)‖ = _
    rw [ha']
    simp
  have hf0 : (vLayer p K (MaximalUnramifiedExtension p K)).hom.f 2 z = 0 := by
    apply Subtype.ext
    funext g
    show vLayerMap p K (MaximalUnramifiedExtension p K) (z.1 fun i => g i) = 0
    rw [hzm, map_zsmul, hv, smul_zero]
  have hc : (urT p K).coch.cls 2 z hz = 0 := by
    apply (valuation_unramified_closure_h2_bijective hK).1
    rw [map_zero]
    show (trivRep (GalLK p K (MaximalUnramifiedExtension p K)) ℤ).coch.cls 2 ((vLayer p K (MaximalUnramifiedExtension p K)).hom.f 2 z) _ = 0
    refine (LongExactSequenceMaps.cls_eq_zero _ 2 _ _).2 ?_
    rw [hf0]
    exact Submodule.zero_mem _
  unfold pairK
  rw [h, hc, map_zero, map_zero]

theorem pairK_uniformiser_unr (hK : FiniteDimensional ℚ_[p] K) (π : Kˣ) (hπ : vK p K π = 1) (χ : charGrp (GK p K))
    (hχ : TrivOn p K (MaximalUnramifiedExtension p K) χ) : pairK p K π χ = χ.1 (Additive.ofMul (frobK p K)) := by
  obtain ⟨t, m, z, hz, ht, htχ, hm, hzm, h⟩ := exists_ur_cocycle π χ hχ
  have h1 : (eK p K : ℝ) * vbar p (urOfK p K π).1 = 1 := by
    have h2 := vOn_spec p K ⟨ofK p K (Additive.ofMul π), ofK_mem p K _⟩
    have h3 : vOn p K ⟨ofK p K (Additive.ofMul π), ofK_mem p K _⟩ = 1 := hπ
    rw [h3, Int.cast_one] at h2
    exact h2.symm
  unfold pairK
  rw [h, invBr_layerInf hK, isInv_invUr hK (urOfK p K π) t m z hz (ofK_mem p K _) h1 ht hm hzm]
  exact htχ (frobK p K)

theorem pairK_unr (hK : FiniteDimensional ℚ_[p] K) (a : Kˣ) (χ : charGrp (GK p K)) (hχ : TrivOn p K (MaximalUnramifiedExtension p K) χ) :
    pairK p K a χ = vK p K a • χ.1 (Additive.ofMul (frobK p K)) := by
  obtain ⟨π, hπ⟩ := exists_vK_eq_one p K hK
  have hzpow : ∀ n : ℤ, pairK p K (π ^ n) χ = n • pairK p K π χ := by
    intro n
    obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
    · rw [zpow_natCast, pairK_pow, natCast_zsmul]
    · rw [zpow_neg, zpow_natCast, pairK_inv, pairK_pow, neg_smul, natCast_zsmul]
  have hu : a * (π ^ vK p K a)⁻¹ ∈ UK p K := by
    rw [mem_UK_iff p K hK, vK_mul, vK_inv, vK_zpow, hπ]
    ring
  have ha : a = a * (π ^ vK p K a)⁻¹ * π ^ vK p K a := by rw [inv_mul_cancel_right]
  conv_lhs => rw [ha]
  rw [pairK_mul, pairK_unit_unr hK _ hu χ hχ, zero_add, hzpow, pairK_uniformiser_unr hK π hπ χ hχ]

end ReciprocityTheory.DiscreteGroups.LocalClassField
