import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

section Real

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E]

private noncomputable def diagR (E : Type) [Field E] [NumberField E] [IsTotallyReal E] : E →+* TR.Rinf E :=
  (TR.pInf E).comp (algebraMap E (Ad E))

private theorem infDiag_eqR (k : Eˣ) : infDiag k = TR.infId E (Units.map (diagR E).toMonoidHom k) := by
  classical
  have h : ((infDiag k : Ideles E) : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace E, w.Completion) →* AdeleRing (𝓞 E) E :=
      MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)
    change ∏ w : InfinitePlace E, ι (Pi.mulSingle w (algebraMap E w.Completion k)) =
      ι (fun w => algebraMap E w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [h]
  refine Prod.ext ?_ ?_
  · change _ = 1 - TR.infEq E 1 + TR.infEq E ((TR.infEq E).symm (algebraMap E (InfiniteAdeleRing E) k))
    simp
  · change (1 : Af E) = 1 - 0 + 0
    simp

private theorem denseRange_diagR : DenseRange (diagR E) := by
  have hc : Continuous (TR.infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)
  exact (TR.infEq E).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hc

private theorem denseRange_unitsR : DenseRange (Units.map (diagR E).toMonoidHom) := by
  refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ => ?_
  obtain ⟨k, v, hv, hk⟩ := denseRange_diagR.exists_mem_open (Units.isOpenEmbedding_val.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have h0 : k ≠ 0 := by
    rintro rfl
    exact v.ne_zero (hk.trans (map_zero _))
  exact ⟨v, hv, Units.mk0 k h0, Units.ext hk.symm⟩

private theorem diagR_mk (φ : E →+* ℂ) (k : E) : ((diagR E k (InfinitePlace.mk φ) : ℝ) : ℂ) = φ k := by
  have hr := IsTotallyReal.isReal (InfinitePlace.mk φ)
  have e : diagR E k (InfinitePlace.mk φ) = InfinitePlace.embedding_of_isReal hr k :=
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hr (WithAbs.toAbs _ k)
  rw [e, InfinitePlace.embedding_of_isReal_apply,
    InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hr)]

private theorem chiInf_pos {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) (u : (TR.Rinf E)ˣ)
    (hu : ∀ v, 0 < u.val v) :
    ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ n φ := by
  have hc : ∀ v, Continuous fun u : (TR.Rinf E)ˣ => u.val v := fun v => (continuous_apply v).comp Units.continuous_val
  have ho : IsOpen {u : (TR.Rinf E)ˣ | ∀ v, 0 < u.val v} := by
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (hc v)
  have hcl : IsClosed {u : (TR.Rinf E)ˣ |
      ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ n φ} :=
    isClosed_eq (Units.continuous_val.comp (TR.continuous_chiInf χ)) (continuous_finsetProd _ fun φ _ =>
      (Complex.continuous_ofReal.comp (hc _)).zpow₀ _ fun u => Or.inl
        (Complex.ofReal_ne_zero.2 (TR.unit_ne_zero u _)))
  refine closure_minimal ?_ hcl (denseRange_unitsR.open_subset_closure_inter ho hu)
  rintro _ ⟨hk, k, rfl⟩
  have h1 := h k fun φ => by
    have h2 := hk (InfinitePlace.mk (Complex.ofRealHom.comp φ))
    have h3 := diagR_mk (Complex.ofRealHom.comp φ) (k : E)
    exact h2.trans_eq (Complex.ofReal_injective h3)
  rw [HChar.inf, MonoidHom.comp_apply, infDiag_eqR] at h1
  refine h1.trans (Finset.prod_congr rfl fun φ _ => ?_)
  exact congrArg (· ^ n φ) (diagR_mk φ (k : E)).symm

open Classical in
private noncomputable def negAt (v : InfinitePlace E) : (TR.Rinf E)ˣ :=
  Units.map (MonoidHom.mulSingle (fun _ : InfinitePlace E => ℝ) v) (-1)

private theorem infId_negAt (v : InfinitePlace E) : TR.infId E (negAt v) = ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E v (-1) := by
  classical
  apply Units.ext
  refine Prod.ext ?_ ?_
  · change 1 - TR.infEq E 1 + TR.infEq E (Pi.mulSingle v (-1)) = Pi.mulSingle v (-1)
    rw [map_one, sub_self]
    refine (zero_add _).trans (funext fun w => ?_)
    change (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm
      ((Pi.mulSingle v (-1) : TR.Rinf E) w) = _
    by_cases h : w = v
    · subst h
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same, map_neg, map_one]
    · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h, map_one]
  · change (1 : Af E) - 0 + 0 = 1
    simp

private theorem bij_mk : Function.Bijective (InfinitePlace.mk : (E →+* ℂ) → InfinitePlace E) := by
  refine ⟨fun φ ψ h => ?_, fun w => ⟨w.embedding, w.mk_embedding⟩⟩
  rw [← InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal φ), h,
    InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal ψ)]

private theorem chiInf_all {χ : HChar E} {b : ℤ} (h : IsAlgPos χ fun _ => b)
    (hs : ∀ v : InfinitePlace E, χ.locInf v (-1) = (-1) ^ b) (u : (TR.Rinf E)ˣ) :
    ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ b := by
  classical
  let s : (TR.Rinf E)ˣ := ∏ v, if u.val v < 0 then negAt v else 1
  have h1 : ∀ w, s.val w = if u.val w < 0 then -1 else 1 := fun w => by
    simp only [s, Units.coe_prod, Finset.prod_apply]
    rw [Finset.prod_eq_single w _ fun hw => absurd (Finset.mem_univ w) hw]
    · split_ifs
      · exact Pi.mulSingle_eq_same (M := fun _ : InfinitePlace E => ℝ) w _
      · rfl
    · intro v _ hv
      split_ifs
      · exact Pi.mulSingle_eq_of_ne (M := fun _ : InfinitePlace E => ℝ) hv.symm _
      · rfl
  have h2 : ((TR.chiInf χ s : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((s.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ b := by
    rw [bij_mk.prod_comp fun w => ((s.val w : ℝ) : ℂ) ^ b]
    simp only [h1]
    simp only [s, map_prod, Units.coe_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    split_ifs
    · have e : TR.chiInf χ (negAt v) = χ.locInf v (-1) := congrArg χ.1 (infId_negAt v)
      rw [e, hs]
      simp
    · simp
  have h3 := chiInf_pos h (s * u) fun w => by
    change 0 < s.val w * u.val w
    rw [h1]
    split_ifs with hw
    · linarith
    · rw [one_mul]
      exact lt_of_le_of_ne (not_lt.1 hw) (TR.unit_ne_zero u w).symm
  rw [map_mul, Units.val_mul] at h3
  refine mul_left_cancel₀ (TR.chiInf χ s).ne_zero (h3.trans ?_)
  rw [h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun φ _ => ?_
  rw [← mul_zpow, ← Complex.ofReal_mul]
  rfl

end Real

theorem UpperTheory.heckeChar_algebraic_of_sign :
    UpperTheory.V.Af.Cr.AlgOfSign := by
  intro F _ _ _ χ b h hs k
  rw [HChar.inf, MonoidHom.comp_apply, infDiag_eqR]
  refine (chiInf_all h hs _).trans (Finset.prod_congr rfl fun φ _ => ?_)
  exact congrArg (· ^ b) (diagR_mk φ (k : F))
