import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaTApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaHeisenbergCommutingThetaOperator
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SymplOHFNegNeg

noncomputable section

open scoped TensorProduct Matrix ComplexConjugate Pointwise
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace PositivityTheory.ThKW.DblSchur

open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.DblTargetDelta PositivityTheory.ThKW.Dbl GlobalTheory.ThetaSchurF
open GlobalTheory.WeilSchrodinger.DblTargetF (dblG)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {nS nT : ℕ}

def glue {R : Type} (a b : Matrix (Fin nT) (Fin nS) R) : Matrix (Fin (nT + nT)) (Fin nS) R :=
  fun i j => Sum.elim a b (finSumFinEquiv.symm i) j

theorem top_glue (a b : WOF F E nS nT) : topR (glue a b : WOF F E nS (nT + nT)) = a := by
  ext i j
  show Sum.elim a b (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i))) j = a i j
  rw [Equiv.symm_apply_apply]; rfl

theorem bot_glue (a b : WOF F E nS nT) : botR (glue a b : WOF F E nS (nT + nT)) = b := by
  ext i j
  show Sum.elim a b (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i))) j = b i j
  rw [Equiv.symm_apply_apply]; rfl

theorem tb_ext {x y : WOF F E nS (nT + nT)} (h1 : topR x = topR y) (h2 : botR x = botR y) : x = y := by
  ext i j
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective i
  rcases k with k | k
  · exact congrFun (congrFun h1 k) j
  · exact congrFun (congrFun h2 k) j

theorem continuous_glue : Continuous fun p : WOF F E nS nT × WOF F E nS nT => (glue p.1 p.2 : WOF F E nS (nT + nT)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective i
  rcases k with k | k
  · exact ((continuous_apply j).comp ((continuous_apply k).comp continuous_fst)).congr fun p : WOF F E nS nT × WOF F E nS nT =>
      (congrFun (congrFun (top_glue p.1 p.2) k) j).symm
  · exact ((continuous_apply j).comp ((continuous_apply k).comp continuous_snd)).congr fun p : WOF F E nS nT × WOF F E nS nT =>
      (congrFun (congrFun (bot_glue p.1 p.2) k) j).symm

variable (F E nS nT) in

def glueE : (WOF F E nS nT × WOF F E nS nT) ≃+ WOF F E nS (nT + nT) where
  toFun p := glue p.1 p.2
  invFun x := (topR x, botR x)
  left_inv p := Prod.ext (top_glue _ _) (bot_glue _ _)
  right_inv x := tb_ext (top_glue _ _) (bot_glue _ _)
  map_add' p q := tb_ext (by rw [topR_add, top_glue, top_glue, top_glue]; rfl)
    (by rw [botR_add, bot_glue, bot_glue, bot_glue]; rfl)

theorem top_rat {x : WOF F E nS (nT + nT)} (h : x ∈ ratLF F E nS (nT + nT)) : topR x ∈ ratLF F E nS nT := by
  obtain ⟨γ, rfl⟩ := h
  exact ⟨γ.submatrix (finSumFinEquiv ∘ Sum.inl) id, rfl⟩

theorem bot_rat {x : WOF F E nS (nT + nT)} (h : x ∈ ratLF F E nS (nT + nT)) : botR x ∈ ratLF F E nS nT := by
  obtain ⟨γ, rfl⟩ := h
  exact ⟨γ.submatrix (finSumFinEquiv ∘ Sum.inr) id, rfl⟩

theorem glue_rat {a b : WOF F E nS nT} (ha : a ∈ ratLF F E nS nT) (hb : b ∈ ratLF F E nS nT) :
    (glue a b : WOF F E nS (nT + nT)) ∈ ratLF F E nS (nT + nT) := by
  obtain ⟨γ, rfl⟩ := ha
  obtain ⟨γ', rfl⟩ := hb
  refine ⟨glue γ γ', tb_ext ?_ ?_⟩
  · rw [top_glue]
    ext i j
    show incAF F E (Sum.elim γ γ' (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i))) j) = incAF F E (γ i j)
    rw [Equiv.symm_apply_apply]; rfl
  · rw [bot_glue]
    ext i j
    show incAF F E (Sum.elim γ γ' (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i))) j) = incAF F E (γ' i j)
    rw [Equiv.symm_apply_apply]; rfl

variable (F E nS nT) in
theorem exists_prod_domain : ∃ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    (μ₂ : Measure (WOF F E nS (nT + nT))) (𝓕₂ : Set (WOF F E nS (nT + nT))),
    μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ ∧
    μ₂.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratLF F E nS (nT + nT)) 𝓕₂ μ₂ ∧
    ∀ φ χ : WOF F E nS nT → ℂ, ∫ x in 𝓕₂, φ (topR x) * χ (botR x) ∂μ₂ = (∫ x in 𝓕, φ x ∂μ) * ∫ x in 𝓕, χ x ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS nT
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS (nT + nT)
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  have : BorelSpace (WOF F E nS (nT + nT)) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, -⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WOF F E nS nT) (ratLF F E nS nT) K hK hKc).1
  have hc' : Continuous (glueE F E nS nT).symm := continuous_topR.prodMk continuous_botR
  let eh : (WOF F E nS nT × WOF F E nS nT) ≃ₜ WOF F E nS (nT + nT) :=
    { (glueE F E nS nT).toEquiv with continuous_toFun := continuous_glue, continuous_invFun := hc' }
  let em := eh.toMeasurableEquiv
  have mp : MeasurePreserving em.symm ((μ.prod μ).map em) (μ.prod μ) :=
    (⟨em.measurable, rfl⟩ : MeasurePreserving em (μ.prod μ) ((μ.prod μ).map em)).symm em
  have qt : Measure.QuasiMeasurePreserving topR ((μ.prod μ).map em) μ :=
    Measure.quasiMeasurePreserving_fst.comp mp.quasiMeasurePreserving
  have qb : Measure.QuasiMeasurePreserving botR ((μ.prod μ).map em) μ :=
    Measure.quasiMeasurePreserving_snd.comp mp.quasiMeasurePreserving
  refine ⟨μ, 𝓕, (μ.prod μ).map em, topR ⁻¹' 𝓕 ∩ botR ⁻¹' 𝓕, hμ, h𝓕,
    (glueE F E nS nT).isAddHaarMeasure_map (μ.prod μ) continuous_glue hc', ⟨?_, ?_, ?_⟩, fun φ χ => ?_⟩
  · exact (h𝓕.nullMeasurableSet.preimage qt).inter (h𝓕.nullMeasurableSet.preimage qb)
  · filter_upwards [qt.ae h𝓕.ae_covers, qb.ae h𝓕.ae_covers] with x ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨⟨glue a.1 b.1, glue_rat a.2 b.2⟩, ?_, ?_⟩
    · show topR (glue a.1 b.1 + x) ∈ 𝓕
      rw [topR_add, top_glue]; exact ha
    · show botR (glue a.1 b.1 + x) ∈ 𝓕
      rw [botR_add, bot_glue]; exact hb
  · intro g g' hne
    let a : ratLF F E nS nT := ⟨topR g.1, top_rat g.2⟩
    let a' : ratLF F E nS nT := ⟨topR g'.1, top_rat g'.2⟩
    let b : ratLF F E nS nT := ⟨botR g.1, bot_rat g.2⟩
    let b' : ratLF F E nS nT := ⟨botR g'.1, bot_rat g'.2⟩
    by_cases h1 : a = a'
    · have h2 : b ≠ b' := fun h2 => hne (Subtype.ext (tb_ext (congrArg Subtype.val h1) (congrArg Subtype.val h2)))
      refine measure_mono_null ?_ (qb.preimage_null (h𝓕.aedisjoint h2))
      rintro x ⟨⟨y, hy, e⟩, ⟨y', hy', e'⟩⟩
      exact ⟨⟨botR y, hy.2, by rw [← e]; rfl⟩, ⟨botR y', hy'.2, by rw [← e']; rfl⟩⟩
    · refine measure_mono_null ?_ (qt.preimage_null (h𝓕.aedisjoint h1))
      rintro x ⟨⟨y, hy, e⟩, ⟨y', hy', e'⟩⟩
      exact ⟨⟨topR y, hy.1, by rw [← e]; rfl⟩, ⟨topR y', hy'.1, by rw [← e']; rfl⟩⟩
  · rw [setIntegral_map_equiv, ← setIntegral_prod_mul]
    have e1 : em ⁻¹' (topR ⁻¹' 𝓕 ∩ botR ⁻¹' 𝓕) = 𝓕 ×ˢ 𝓕 := by
      ext p
      show (topR (glue p.1 p.2) ∈ 𝓕 ∧ botR (glue p.1 p.2) ∈ 𝓕) ↔ _
      rw [top_glue, bot_glue]; rfl
    rw [e1]
    congr 1
    funext p
    show φ (topR (glue p.1 p.2)) * χ (botR (glue p.1 p.2)) = _
    rw [top_glue, bot_glue]

variable {σ : E →ₐ[F] E} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}

theorem act_one_left {m : ℕ} {J : Matrix (Fin m) (Fin m) E} (h : GAF σ J) (x : WOF F E nS m) :
    actOF σ JS J 1 h x = (mtF σ J h * x : Matrix (Fin m) (Fin nS) (AEF F E)) := by
  unfold actOF
  rw [inv_one, show mtF σ JS 1 = 1 from rfl, Matrix.mul_one]

theorem act_glue (h : GAF σ JT) (hd : GAF σ (dblG JT))
    (e : mtF σ (dblG JT) hd = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (mtF σ JT h) 0 0 1))
    (a b : WOF F E nS nT) : actOF σ JS (dblG JT) 1 hd (glue a b) = glue (actOF σ JS JT 1 h a) b := by
  rw [act_one_left, act_one_left, e]
  ext i j
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective i
  rw [Matrix.mul_apply, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [glue, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases k with k | k
  · simp
    rfl
  · simp [Matrix.one_apply]
    rfl

theorem abstract {n m : ℕ} {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin m) (Fin m) E} {ξ₀ : E} {ψ : AddChar (AF F) ℂ}
    (hψ : IsCharAF F ψ) (hskew : ∀ x y : WOF F E n m, symplOF σ J J' ξ₀ y x = -symplOF σ J J' ξ₀ x y)
    (hann : ∀ x : WOF F E n m, (∀ γ ∈ ratLF F E n m, ψ (symplOF σ J J' ξ₀ x γ) = 1) ↔ x ∈ ratLF F E n m)
    {ι : Type} (A B : ι → WOF F E n m → ℂ) (hA : ∀ i, IsThetaFunOF σ J J' ξ₀ ψ (A i))
    (hB : ∀ i, IsThetaFunOF σ J J' ξ₀ ψ (B i))
    (hH : ∀ w i, ∃ i', heisOF σ J J' ξ₀ ψ w (A i) = A i' ∧ heisOF σ J J' ξ₀ ψ w (B i) = B i')
    (μ : Measure (WOF F E n m)) (𝓕 : Set (WOF F E n m)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E n m) 𝓕 μ)
    (hs : ∀ i i', ∫ x in 𝓕, A i x * star (A i' x) ∂μ = ∫ x in 𝓕, B i x * star (B i' x) ∂μ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ i, A i = c • B i := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E n m
  have : BorelSpace (WOF F E n m) := ⟨rfl⟩
  have : Countable (ratLF F E n m) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E n m) (ratLF F E n m) hK hKc μ h𝓕⟩
  have hint : ∀ g g', IsThetaFunOF σ J J' ξ₀ ψ g → IsThetaFunOF σ J J' ξ₀ ψ g' →
      Integrable (fun x => g x * star (g' x)) (μ.restrict 𝓕) := fun g g' hg hg' => by
    have hcont : Continuous fun x => g x * star (g' x) := hg.cont.mul hg'.cont.star
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    refine Integrable.of_bound hcont.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← prod_periodic hψ.2.1 hg hg' hγ w]
    exact hC _ h
  have h1 : ∀ i i' x, A i x * star (A i' x) = B i x * star (B i' x) := fun i i' x => by
    have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (WOF F E n m) (ratLF F E n m) K hK hKc
      (ratLF F E n m) (fun γ x => ψ (symplOF σ J J' ξ₀ x γ))
      (fun γ => hψ.1.comp (continuous_symplOF_left _))
      (fun γ x y => by simp only [symplOF_add_left, AddChar.map_add_eq_mul])
      (fun γ γ' x => by simp only [AddSubgroup.coe_add, symplOF_add_right, AddChar.map_add_eq_mul])
      (fun x => by simp only [AddSubgroup.coe_zero, symplOF_zero_right, AddChar.map_zero_eq_one])
      (fun γ x => hψ.2.1 _)
      (fun x => by
        rw [← hann x]
        exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
      μ 𝓕 hμ h𝓕 (fun x => A i x * star (A i' x) - B i x * star (B i' x))
      (((hA i).cont.mul (hA i').cont.star).sub ((hB i).cont.mul (hB i').cont.star))
      (fun γ hγ x => by
        rw [prod_periodic hψ.2.1 (hA i) (hA i') hγ, prod_periodic hψ.2.1 (hB i) (hB i') hγ])
      (fun γ => by
        obtain ⟨k, k1, k2⟩ := hH γ i
        have e : (fun x => ψ (symplOF σ J J' ξ₀ x γ) * (A i x * star (A i' x) - B i x * star (B i' x))) = fun x =>
            A k x * star (A i' x) - B k x * star (B i' x) := by
          funext x
          rw [← k1, ← k2, heis_rat hskew (hA i) γ.2, heis_rat hskew (hB i) γ.2]
          ring
        rw [e, integral_sub (hint _ _ (hA k) (hA i')) (hint _ _ (hB k) (hB i')), hs, sub_self])
    exact sub_eq_zero.1 (congrFun key x)
  have h2 : ∀ i i' x y, A i x * star (A i' y) = B i x * star (B i' y) := fun i i' x y => by
    obtain ⟨k, k1, k2⟩ := hH (y - x) i'
    have h := h1 i k x
    rw [← k1, ← k2] at h
    simp only [heisOF, add_sub_cancel, star_mul'] at h
    linear_combination ψ (symplOHF σ J J' ξ₀ x (y - x)) * h -
      (A i x * star (A i' y) - B i x * star (B i' y)) * mul_star_psi hψ.2.1 (symplOHF σ J J' ξ₀ x (y - x))
  have hn : ∀ i y, ‖A i y‖ = ‖B i y‖ := fun i y => by
    have := congrArg norm (h2 i i y y)
    rw [norm_mul, norm_mul, norm_star, norm_star] at this
    exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).1 this
  by_cases h0 : ∃ i y, A i y ≠ 0
  · obtain ⟨i₀, y, hy⟩ := h0
    have hs : star (A i₀ y) ≠ 0 := star_ne_zero.2 hy
    refine ⟨star (B i₀ y) / star (A i₀ y), ?_, fun i => ?_⟩
    · rw [norm_div, norm_star, norm_star, ← hn, div_self (norm_ne_zero_iff.2 hy)]
    · funext x
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hs, h2, mul_comm]
  · push Not at h0
    refine ⟨1, norm_one, fun i => funext fun y => ?_⟩
    rw [one_smul, h0, eq_comm, ← norm_eq_zero, ← hn, h0, norm_zero]

end PositivityTheory.ThKW.DblSchur

open PositivityTheory.ThKW.DblSchur PositivityTheory.ThKW.Dbl Formalism.IndefR.DatumF MeasureTheory GlobalTheory.DblTargetDelta in
theorem PositivityTheory.ThKW.weil_rep_unitary_pair_equivariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle)
        (ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ)),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
          Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
          (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (h : Formalism.IndefR.DatumF.GAF σ JT) (hd : Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)),
        Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) hd =
          Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.IndefR.DatumF.mtF σ JT h) 0 0 1) →
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ → Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ →
        ωd (1, hd) (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) = c • GlobalTheory.DblTargetDelta.deltaT (ω (1, h) f₁) f₂ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ χS χT ω hω ωd hωd h hd e
  have hψ : IsCharAF F B.ψ := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB).1
  have hinv : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
  have hT' := GlobalTheory.WeilSchrodinger.DblTargetF.isHermND_dblG hT
  have hth := fun w f hf => GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB nS nT JS JT ξ₀ w f hf
  obtain ⟨μ, 𝓕, μ₂, 𝓕₂, hμ, h𝓕, hμ₂, h𝓕₂, hprod⟩ := exists_prod_domain F E nS nT
  let T := {f // IsThetaFunOF σ JS JT ξ₀ B.ψ f}
  have hδ : ∀ f₁ f₂ g₁ g₂ : WOF F E nS nT → ℂ, ∫ x in 𝓕₂, deltaT f₁ f₂ x * star (deltaT g₁ g₂ x) ∂μ₂ =
      (∫ x in 𝓕, f₁ x * star (g₁ x) ∂μ) * ∫ x in 𝓕, conj (f₂ (-x)) * star (conj (g₂ (-x))) ∂μ := fun f₁ f₂ g₁ g₂ => by
    rw [← hprod]
    congr 1
    funext x
    simp only [deltaT_apply, star_mul']
    ring
  obtain ⟨c, hc, H⟩ := abstract hψ (GlobalTheory.T.adelicSymplecticTraceForm_alternating_swap F E σ hinv _ _ JS _ hS hT' ξ₀ hσξ)
    (GlobalTheory.T.rational_points_self_annihilator_symplectic_standardChar F E σ B hB _ _ JS _ hS hT' ξ₀ hξ)
    (fun p : T × T => ωd (1, hd) (deltaT p.1.1 p.2.1)) (fun p => deltaT (ω (1, h) p.1.1) p.2.1)
    (fun p => hωd.om_pres _ _ (theta_delta hψ.2.1 p.1.2 p.2.2))
    (fun p => theta_delta hψ.2.1 (hω.om_pres _ _ p.1.2) p.2.2)
    (fun w p => by
      have e1 : actOF σ JS JT 1 h (actOF σ JS JT 1 h⁻¹ (topR w)) = topR w := by
        rw [← GlobalTheory.WeilPartsF.actOF_mul, mul_one, mul_inv_cancel, act_one_left, show mtF σ JT 1 = 1 from rfl, Matrix.one_mul]
      have e2 : actOF σ JS _ 1 hd (glue (actOF σ JS JT 1 h⁻¹ (topR w)) (botR w)) = w := by
        rw [act_glue h hd e, e1]
        exact tb_ext (top_glue _ _) (bot_glue _ _)
      refine ⟨(⟨_, hth (actOF σ JS JT 1 h⁻¹ (topR w)) _ p.1.2⟩, ⟨_, hth (-botR w) _ p.2.2⟩), ?_, ?_⟩
      · have := hωd.om_heis 1 hd (glue (actOF σ JS JT 1 h⁻¹ (topR w)) (botR w)) _ (theta_delta hψ.2.1 p.1.2 p.2.2)
        rw [e2, heis_delta hψ.2.1, top_glue, bot_glue] at this
        exact this.symm
      · have := hω.om_heis 1 h (actOF σ JS JT 1 h⁻¹ (topR w)) _ p.1.2
        rw [e1] at this
        show _ = deltaT (ω (1, h) _) _
        rw [this, heis_delta hψ.2.1])
    μ₂ 𝓕₂ hμ₂ h𝓕₂ (fun p q => by
      rw [GlobalTheory.ThetaSchurF.scalar_eq hψ.2.1 μ₂ 𝓕₂ hμ₂ h𝓕₂ (ωd (1, hd)) (hωd.om_pres _) (hωd.om_unit μ₂ 𝓕₂ hμ₂ h𝓕₂ _) _ _
        (theta_delta hψ.2.1 p.1.2 p.2.2) (theta_delta hψ.2.1 q.1.2 q.2.2), hδ, hδ,
        GlobalTheory.ThetaSchurF.scalar_eq hψ.2.1 μ 𝓕 hμ h𝓕 (ω (1, h)) (hω.om_pres _) (hω.om_unit μ 𝓕 hμ h𝓕 _) _ _ p.1.2 q.1.2])
  exact ⟨c, hc, fun f₁ f₂ h₁ h₂ => H (⟨f₁, h₁⟩, ⟨f₂, h₂⟩)⟩

end
