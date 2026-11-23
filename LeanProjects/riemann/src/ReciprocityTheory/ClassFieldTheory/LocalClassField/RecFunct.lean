import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPair
import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpen
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecFunctA
import ReciprocityTheory.GroupCohomology.InnerHolds

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem qz_div (n : ℕ) (hn : 0 < n) (q : QZ) : ∃ q' : QZ, n • q' = q := by
  induction q using QuotientAddGroup.induction_on with
  | H r =>
    refine ⟨QuotientAddGroup.mk (r / n), ?_⟩
    rw [← QuotientAddGroup.mk_nsmul]
    congr 1
    rw [nsmul_eq_mul]
    field_simp

theorem restriction_brauer_surjective (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) : Surjective ((resPair h).hom.H 2) := by
  intro y
  obtain ⟨q', hq'⟩ := qz_div (degLK p K L) (degLK_pos hL) (invBr p L y)
  obtain ⟨x, rfl⟩ := (invBr_bijective hK).2 q'
  exact ⟨x, (invBr_bijective hL).1 ((invBr_res hK hL h x).trans hq')⟩

theorem invBr_cor (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (cor : Br p L →+ Br p K)
    (hcor : ∀ x, cor ((resPair h).hom.H 2 x) = degLK p K L • x) (y : Br p L) :
    invBr p K (cor y) = invBr p L y := by
  obtain ⟨x, rfl⟩ := restriction_brauer_surjective hK hL h y
  rw [hcor, map_nsmul, invBr_res hK hL h]

theorem exists_cor_pairBr (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    ∃ cor : Br p L →+ Br p K, (∀ x, cor ((resPair h).hom.H 2 x) = degLK p K L • x) ∧
      ∀ (b : Lˣ) (a : Kˣ), ofK p K (Additive.ofMul a) = normHom p K L (ofK p L (Additive.ofMul b)) →
        ∀ χ : charGrp (GK p K), cor (pairBr p L b (resChar h χ)) = pairBr p K a χ := by
  have := finiteIndex_subG (K := K) hL
  have hU := isOpen_subG (K := K) hL
  obtain ⟨e, he, hc, hc'⟩ := exists_equiv_subG h
  have hes : ∀ g : subG p K L, resGK h (e.symm g) = g.1 := fun g => by
    rw [← he, MulEquiv.apply_symm_apply]
  let PLU : Pair (kbarT p L) ((kbarT p K).resSub (subG p K L)) :=
    { φ := e.symm.toMonoidHom
      u := LinearMap.id
      φ_cont := hc'
      u_cont := continuous_id
      equiv := fun g m => by
        show kbarRep p K (resGK h (e.symm g)) m = kbarRep p K g.1 m
        rw [hes] }
  obtain ⟨corP, hcorP, hcr⟩ := cor_holds ℤ (GK p K) (kbarT p K) (subG p K L) hU
  refine ⟨(corP.H 2).toAddMonoidHom.comp (PLU.hom.H 2).toAddMonoidHom, fun x => ?_, fun b a ha χ => ?_⟩
  · show corP.H 2 (PLU.hom.H 2 ((resPair h).hom.H 2 x)) = _
    have h1 : PLU.hom.H 2 ((resPair h).hom.H 2 x) =
        (Pair.res (kbarT p K) (subG p K L).subtype continuous_subtype_val).hom.H 2 x := by
      induction x using Cx.H_ind with
      | h x hx =>
        refine Cx.cls_congr _ _ (Subtype.ext (funext fun g => ?_))
        show x.1 (fun i => resGK h (e.symm (g i))) = x.1 fun i => (g i).1
        simp only [hes]
    rw [h1, hcr]; rfl
  · show corP.H 2 (PLU.hom.H 2 (pairBr p L b (resChar h χ))) = _
    obtain ⟨t, m, z, hz, ht, htχ, hm, hzm, hcl⟩ := isPairClass_pairBr a χ
    obtain ⟨y, hy, hym⟩ := exists_int_cocycle t m ht hm
    have hm' : ∀ g : Fin 2 → GK p L, ((m fun i => resGK h (g i) : ℤ) : ℚ) =
        t (resGK h (g 0)) + t (resGK h (g 1)) - t (resGK h (g 0 * g 1)) := fun g => by
      rw [hm, map_mul]
    obtain ⟨zL, hzL, hzL1⟩ := exists_defect_cocycle (kbarT p L) (a := ofK p L (Additive.ofMul b))
      (fun g => kbarT_rho_ofK g _) (t := fun g => t (resGK h g)) (ht.comp_continuous (resGK_continuous h))
      (m := fun g => m fun i => resGK h (g i)) hm'
    have hpL : pairBr p L b (resChar h χ) = (kbarT p L).coch.cls 2 zL hzL :=
      (isPairClass_pairBr b (resChar h χ)).unique
        ⟨_, _, zL, hzL, ht.comp_continuous (resGK_continuous h), fun g => htχ _, hm', hzL1, rfl⟩
    rw [hpL, hcl]
    refine cor_smul_cocycle (kbarT p K) (subG p K L) hU corP hcorP (ofK p L (Additive.ofMul b))
      (fun g hg => (mem_multOf_iff_fixed h _).1 (ofK_mem p L _) g hg) (ofK p K (Additive.ofMul a))
      ((corFun_zero_eq_normHom hL _ (ofK_mem p L _) _ (fun _ => rfl) _).trans ha.symm) y hy
      (PLU.hom.f 2 zL) (Cx.Hom.d_f_eq_zero _ hzL) (fun g => ?_) z hz (fun g => ?_)
    · show zL.1 (fun i => e.symm (g i)) = _
      rw [hzL1, hym]
      simp only [hes]
      rfl
    · rw [hzm, hym]

theorem pairK_norm (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (b : Lˣ) (a : Kˣ)
    (ha : ofK p K (Additive.ofMul a) = normHom p K L (ofK p L (Additive.ofMul b))) (χ : charGrp (GK p K)) :
    pairK p K a χ = pairK p L b (resChar h χ) := by
  obtain ⟨cor, hcor, hpr⟩ := exists_cor_pairBr hK hL h
  unfold pairK
  rw [← hpr b a ha χ, invBr_cor hK hL h cor hcor]

noncomputable def conjL (σ : GK p K) (hσ : ∀ x ∈ L, σ x ∈ L) : GK p L →* GK p L where
  toFun g :=
    { (σ.toRingEquiv.trans (g.toRingEquiv.trans σ.symm.toRingEquiv)) with
      commutes' := fun x => by
        show σ.symm (g (σ x.1)) = x.1
        rw [show g (σ x.1) = σ x.1 from g.commutes ⟨σ x.1, hσ x.1 x.2⟩, AlgEquiv.symm_apply_apply] }
  map_one' := AlgEquiv.ext fun x => σ.symm_apply_apply x
  map_mul' g g' := AlgEquiv.ext fun x => by
    show σ.symm (g (g' (σ x))) = σ.symm (g (σ (σ.symm (g' (σ x)))))
    rw [AlgEquiv.apply_symm_apply]

theorem resGK_conjL (h : K ≤ L) (σ : GK p K) (hσ : ∀ x ∈ L, σ x ∈ L) (g : GK p L) :
    resGK h (conjL σ hσ g) = σ⁻¹ * resGK h g * σ := rfl

theorem conjL_continuous (h : K ≤ L) (σ : GK p K) (hσ : ∀ x ∈ L, σ x ∈ L) : Continuous (conjL σ hσ) := by
  rw [(isClosedEmbedding_resGK h).isInducing.continuous_iff]
  exact (continuous_const.mul (resGK_continuous h)).mul continuous_const

noncomputable def conjPairL (h : K ≤ L) (σ : GK p K) (hσ : ∀ x ∈ L, σ x ∈ L) : Pair (kbarT p L) (kbarT p L) where
  φ := conjL σ hσ
  u := kbarRep p K σ
  φ_cont := conjL_continuous h σ hσ
  u_cont := continuous_of_discreteTopology
  equiv _ _ := Units.ext (σ.apply_symm_apply _)

noncomputable def innPair (σ : GK p K) : Pair (kbarT p K) (kbarT p K) where
  φ := (MulAut.conj σ⁻¹).toMonoidHom
  u := kbarRep p K σ
  φ_cont := (continuous_const.mul continuous_id).mul continuous_const
  u_cont := continuous_of_discreteTopology
  equiv _ _ := Units.ext (σ.apply_symm_apply _)

theorem conjPairL_res (h : K ≤ L) (σ : GK p K) (hσ : ∀ x ∈ L, σ x ∈ L) (n : ℕ) (x : (kbarT p K).H n) :
    (conjPairL h σ hσ).hom.H n ((resPair h).hom.H n x) = (resPair h).hom.H n x := by
  have h1 : (innPair σ).hom.H n = LinearMap.id :=
    inner_holds ℤ (GK p K) (kbarT p K) (innPair σ) σ (fun g => by simp [innPair]) (fun _ => rfl) n
  have h2 : (conjPairL h σ hσ).hom.H n ((resPair h).hom.H n x) =
      (resPair h).hom.H n ((innPair σ).hom.H n x) := by
    induction x using Cx.H_ind with
    | h x hx => rfl
  rw [h2, h1]; rfl

theorem conjugation_pairing_h2_fixed (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (σ : GK p K)
    (hσ : ∀ x ∈ L, σ x ∈ L) (y : Br p L) : (conjPairL h σ hσ).hom.H 2 y = y := by
  obtain ⟨x, rfl⟩ := restriction_brauer_surjective hK hL h y
  exact conjPairL_res h σ hσ 2 x

theorem pairBr_conj (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (σ : GK p K)
    (hσ : ∀ x ∈ L, σ x ∈ L) (b b' : Lˣ)
    (hb : ((b' : L) : PadicAlgCl p) = σ ((b : L) : PadicAlgCl p)) (χ χ' : charGrp (GK p L))
    (hχ : ∀ g g' : GK p L, resGK h g' = σ * resGK h g * σ⁻¹ →
      χ'.1 (Additive.ofMul g') = χ.1 (Additive.ofMul g)) :
    pairBr p L b' χ' = pairBr p L b χ := by
  obtain ⟨t, m, z, hz, ht, htχ, hm, hzm, hc⟩ := isPairClass_pairBr b χ
  rw [← conjugation_pairing_h2_fixed hK hL h σ hσ (pairBr p L b χ)]
  refine (isPairClass_pairBr b' χ').unique ?_
  have hbb : ofK p L (Additive.ofMul b') = kbarRep p K σ (ofK p L (Additive.ofMul b)) := Units.ext hb
  refine ⟨fun g => t (conjL σ hσ g), fun g => m fun i => conjL σ hσ (g i), (conjPairL h σ hσ).hom.f 2 z,
    by rw [← (conjPairL h σ hσ).hom.comm, hz, map_zero],
    ht.comp_continuous (conjL_continuous h σ hσ), fun g => ?_, fun g => ?_, fun g => ?_, by rw [hc]; rfl⟩
  · rw [htχ]
    refine (hχ _ _ ?_).symm
    rw [resGK_conjL]; group
  · rw [hm]; simp only [map_mul]
  · show kbarRep p K σ (z.1 fun i => conjL σ hσ (g i)) = _
    rw [hzm, hbb]
    exact LinearMap.map_smul (kbarRep p K σ) _ _

theorem pairK_conj (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (σ : GK p K)
    (hσ : ∀ x ∈ L, σ x ∈ L) (b b' : Lˣ)
    (hb : ((b' : L) : PadicAlgCl p) = σ ((b : L) : PadicAlgCl p)) (χ χ' : charGrp (GK p L))
    (hχ : ∀ g g' : GK p L, resGK h g' = σ * resGK h g * σ⁻¹ →
      χ'.1 (Additive.ofMul g') = χ.1 (Additive.ofMul g)) :
    pairK p L b' χ' = pairK p L b χ := by
  unfold pairK
  rw [pairBr_conj hK hL h σ hσ b b' hb χ χ' hχ]

end ReciprocityTheory.DiscreteGroups.LocalClassField
