import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDetProdConstAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSignatureSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRepUnitaryTwistExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLocalLanglandsUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWittModelUnitaryActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearWittModelLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupWPairVWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupVPairVWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupSurjectsGeneralLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedCharIntertwiningUnifStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetSubquotientRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetDetInducedTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetFieldIsoTransportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KpImpliesCuspidalSpectrumGLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDataLocalExpansionStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
  GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.DetProd
open scoped TensorProduct

namespace GlobalTheory.ThK.MidJacGlobal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Pair

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isHecke_div {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

theorem isPair_big {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) := by
  refine ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, isHecke_div h.chars.heckeβ h.chars.heckeα,
    h.chars.resβ, fun x => ?_, h.weil⟩
  have e := h.chars.resβ x
  have e' := h.chars.resα x
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ a' with hm | hm <;> rw [hm] <;> ring

omit [NumberField F] [NumberField E] in

theorem smul_extH_sub_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] [CommRing R''] [Algebra F R''] (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (j' : R' →ₗ[F] R'')
    (hj' : ∀ a b, j' (a * b) = j' a * j' b) (u : R'') (hu : ∀ b, u * j' (j b) = 0) (x : HA R σ J) :
    u • ((HA.mat R'' σ J (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.extH σ J j' hj' (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.extH σ J j hj x))).1 - 1) = 0 := by
  have key : ∀ z : R ⊗[F] E, u • GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (E := E) j' hj' (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU j hj z) = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, smul_add, hx, hy, add_zero]
    | tmul b e =>
      rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul, TensorProduct.smul_tmul', smul_eq_mul, hu,
        TensorProduct.zero_tmul]
  ext r s
  have e := key ((HA.mat R σ J x).1 r s - (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) r s)
  rw [Matrix.smul_apply, Matrix.zero_apply, ← e]
  congr 1
  rw [Matrix.sub_apply, GlobalTheory.AutFunCompare.mat_extH, GlobalTheory.AutFunCompare.mat_extH]
  by_cases h : r = s
  · subst h
    simp only [Matrix.one_apply_eq, mul_one, map_add, map_sub]
    ring
  · simp only [Matrix.one_apply_ne h, mul_zero, zero_add, sub_zero]

theorem at_emb {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (v : HeightOneSpectrum (𝓞 F)) (x : GLoc σ J v) :
    At (evFin F v) ((matHom _ σ J (emb σ J v x)).1 - 1) := by
  intro u hu
  refine smul_extH_sub_one (R'' := AF F) (singleFin v) (singleFin_mul v) (LinearMap.inr F (Ainf F) (Af F))
    (fun _ _ => Prod.ext (mul_zero _).symm rfl) u (fun b => ?_) x
  refine Prod.ext (show u.1 * (0 : Ainf F) = 0 from mul_zero _) ?_
  change u.2 * singleFin v b = 0
  refine af_ext fun w => ?_
  rw [map_mul, map_zero]
  by_cases h : w = v
  · subst h
    have : evalV F w u.2 = 0 := hu
    rw [this, zero_mul]
  · rw [evalV_singleFin_ne h, mul_zero]

end Pair

open GlobalTheory.SmGL GlobalTheory.LeviBlockExponent GlobalTheory.ThK.MidJac GlobalTheory.KSplit GlobalTheory.WeilM in

theorem exists_intertwiners (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (hK : GlobalTheory.ThK.KP) (hT : IsTriple B G X om om')
    (c : E) (hc : c ≠ 0) (hcs : σ c = -c) (Φ : Fn F a (a + a')) (hΦ : Φ ∈ GlobalTheory.ThK.PolData B G.M)
    (B₀ : GL (Fin (a + a')) (Fv F B.v₁)) :
    ∃ (m : ℕ) (T : Fin m → IndSp (e2 a a') (ofChar (twoDet a a' (chrW X.α B.τ₁) (chrW X.β B.τ₁))) →ₗ[ℂ]
        (GAd σ (c • G.W.J.map σ) → ℂ))
      (x : Fin m → IndSp (e2 a a') (ofChar (twoDet a a' (chrW X.α B.τ₁) (chrW X.β B.τ₁)))),
      (∀ j, IsIntertw σ (c • G.W.J.map σ) B.τ₁ B₀ (detInd a a' (chrW X.α B.τ₁) (chrW X.β B.τ₁)) (T j)) ∧
      (fun y => G.M.I om Φ ((toGAd hσ G.W.J hc).symm y)) = ∑ j, T j (x j) := by
  have hcm := hT.base.cm
  have hJ := GlobalTheory.ThK.SqIntHerm.isHermND_smul_map F E σ B _ G.W _ _ hT.geo.hW c hc hcs
  have hP := isPair_big hT
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_linear_witt_model_local hK.base F E σ B _ _ G.V G.W G.M _ _ om _ _ _ _ hP B.v₁ B.τ₁ 1 B₀
  have hW1 := GlobalTheory.T.linear_witt_model_unitary_action hK.base F E σ B _ _ G.V G.W G.M _ _ om _ _ _ _ hP B.v₁ B.τ₁ 1 B₀ ι hι
  have hν : (chrW (X.β / X.α) B.τ₁)⁻¹ = chrW X.ν B.τ₁ := by
    ext y
    simp [chrW, Chars.ν, GlobalTheory.LFun.locChar]
  have hνβ : chrW X.ν B.τ₁ * chrW X.β B.τ₁ = chrW X.α B.τ₁ := by
    ext y
    simp [chrW, Chars.ν, GlobalTheory.LFun.locChar]
  rw [hν] at hW1
  rw [← hνβ]
  obtain ⟨⟨sν, uν⟩, -⟩ := GlobalTheory.ChrWLocal.chrW_local F E X.ν (isHecke_div hT.chars.heckeα hT.chars.heckeβ) B.v₁ B.τ₁
  obtain ⟨⟨sβ, uβ⟩, -⟩ := GlobalTheory.ChrWLocal.chrW_local F E X.β hT.chars.heckeβ B.v₁ B.τ₁
  have hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt B.v₁) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F B.v₁)).choose_spec
  have hν1 : chrW X.ν B.τ₁ (unifAt B.v₁) ≠ 1 := by
    simpa using GlobalTheory.T.character_at_uniformizer_not_root_of_unity F E σ B a a' G X om om' hT B.v₁ hT.chars.good B.τ₁ 1 one_ne_zero
  obtain ⟨m, φ, L, hφ, hLV', hLW, hsum⟩ := GlobalTheory.T.polynomial_data_local_expansion F E σ B a a' G X om om' hK hT Φ hΦ
  have hLV : ∀ j, ∀ g ∈ UAt σ G.V (evFin F B.v₁), ∀ ψ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁),
      ∀ ψ₁ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), Acts (evFin F B.v₁) (om (g, 1)) ψ ψ₁ → L j ψ₁ = L j ψ :=
    fun j g hg ψ hψ ψ₁ hψ₁ hA => sub_eq_zero.1 (by
      rw [← map_sub]
      exact hLV' j (Submodule.subset_span ⟨g, hg, ψ, hψ, ψ₁, hψ₁, hA, rfl⟩))
  obtain ⟨s, hs⟩ := (ι.domRestrict (SB (Fin a × Fin (a + a') → Fv F B.v₁))).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 fun p q h => Subtype.ext (hι.bij.injOn p.2 q.2 h))
  have hs' : ∀ ψ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), (s (ι ψ)).1 = ψ := fun ψ hψ =>
    congrArg Subtype.val (LinearMap.congr_fun hs ⟨ψ, hψ⟩)
  let L' : Fin m → (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁) → ℂ) →ₗ[ℂ] (GAd σ (c • G.W.J.map σ) → ℂ) := fun j =>
    LinearMap.funLeft ℂ ℂ (toGAd hσ G.W.J hc).symm ∘ₗ L j ∘ₗ (Submodule.subtype _) ∘ₗ s
  have hL' : ∀ j, ∀ ψ ∈ SB (Fin a × Fin (a + a') → Fv F B.v₁), ∀ y, L' j (ι ψ) y = L j ψ ((toGAd hσ G.W.J hc).symm y) :=
    fun j ψ hψ y => congrArg (fun z => L j z ((toGAd hσ G.W.J hc).symm y)) (hs' ψ hψ)
  let κ : GL (Fin (a + a')) (Fv F B.v₁) → GLoc σ (c • G.W.J.map σ) B.v₁ := fun h => (splitEquivIn hcm hJ B.τ₁ B₀).symm h
  have h1V : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F B.v₁) := fun u _ => by simp [mat]
  have h1W : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F B.v₁) := fun u _ => by simp [mat]
  have key : ∀ j, ∃ T : IndSp (e2 a a') (ofChar (twoDet a a' (chrW X.ν B.τ₁ * chrW X.β B.τ₁) (chrW X.β B.τ₁))) →ₗ[ℂ]
      (GAd σ (c • G.W.J.map σ) → ℂ),
      (∀ h y, T (detInd a a' (chrW X.ν B.τ₁ * chrW X.β B.τ₁) (chrW X.β B.τ₁) h y) =
        fun z => T y (z * emb σ _ B.v₁ (κ h))) ∧
      ∀ Ψ ∈ SB (Matrix (Fin a) (Fin (a + a')) (Fv F B.v₁)), ∃ y, L' j Ψ = T y := by
    intro j
    refine GlobalTheory.T.induced_char_intertwining_unif hK.base.bernsteinUnitaryProductIrreducible (Fv F B.v₁) a a' _ _ sν uν sβ uβ _ hϖ hν1 _
      (fun h f z => f (z * emb σ _ B.v₁ (κ h))) (L' j) (fun g' Ψ hΨ => ?_) (fun h' Ψ hΨ => ?_)
    · obtain ⟨ψ, hψ, rfl⟩ := hι.bij.surjOn hΨ
      obtain ⟨g, hg, hgg⟩ := GlobalTheory.SurjAtPlaceV.surj_at_place hK.base F E σ B a a' G X om om' hT B.v₁ hT.chars.good B.τ₁ g'
      obtain ⟨ψ₁, hψ₁, hA⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupV_pairVW F E σ B a a' G X om om' hT B.v₁ g hg ψ hψ
      have e := hW1 g hg 1 h1W ψ hψ ψ₁ hψ₁ hA
      have e1 : locMat B.τ₁ 1 g = g' := Units.ext (by rw [locMat_val, hgg]; simp)
      rw [map_one, e1] at e
      funext y
      rw [← e, hL' j _ hψ₁, hL' j _ hψ, hLV j g hg ψ hψ ψ₁ hψ₁ hA]
    · obtain ⟨ψ, hψ, rfl⟩ := hι.bij.surjOn hΨ
      set h := (toGAd hσ G.W.J hc).symm (emb σ _ B.v₁ (κ h')) with hh
      have hm : mat h = (matHom _ σ _ (emb σ (c • G.W.J.map σ) B.v₁ (κ h'))).1 := rfl
      have hAt : h ∈ UAt σ G.W (evFin F B.v₁) := by
        change At _ (mat h - 1)
        rw [hm]
        exact at_emb _ _
      obtain ⟨ψ₁, hψ₁, hA⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupW_pairVW F E σ B a a' G X om om' hT B.v₁ h hAt ψ hψ
      have e := hW1 1 h1V h hAt ψ hψ ψ₁ hψ₁ hA
      have e1 : locMat B.τ₁ B₀ h = h' := by
        have e2 : splitEquivIn hcm hJ B.τ₁ B₀ (proj σ _ B.v₁ (emb σ _ B.v₁ (κ h'))) = h' := by
          rw [proj_emb_self]
          exact (splitEquivIn hcm hJ B.τ₁ B₀).apply_symm_apply h'
        rw [← e2, splitEquivIn_apply]
        refine Units.ext ?_
        rw [locMat_val, hm]
        rfl
      rw [map_one, e1] at e
      funext y
      rw [← e, hL' j _ hψ₁, hL' j _ hψ, hLW j h hAt ψ hψ ψ₁ hψ₁ hA, map_mul]
  choose T hT1 hT2 using key
  choose x hx using fun j => hT2 j (ι (φ j)) (hι.bij.mapsTo (hφ j))
  refine ⟨m, T, x, fun j g y hy w z => ?_, funext fun y => ?_⟩
  · have : y = κ g := by
      refine (splitEquivIn hcm hJ B.τ₁ B₀).injective ?_
      rw [show splitEquivIn hcm hJ B.τ₁ B₀ (κ g) = g from (splitEquivIn hcm hJ B.τ₁ B₀).apply_symm_apply g,
        splitEquivIn_apply, show splitHom σ _ B.τ₁ y = B₀ * g * B₀⁻¹ from Units.ext hy]
      group
    rw [hT1, this]
  · rw [hsum, Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [← hx, hL' j _ (hφ j)]

theorem valuation_eq_one_iff {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) (y : p.adicCompletion K) :
    ValuativeRel.valuation (p.adicCompletion K) y = 1 ↔
      (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative ℤ))) y = 1 := by
  haveI : (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have h := ValuativeRel.isEquiv (ValuativeRel.valuation (p.adicCompletion K))
    (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative ℤ)))
  rw [le_antisymm_iff, le_antisymm_iff, h.le_one_iff_le_one, ← not_lt, ← not_lt, h.lt_one_iff_lt_one]
  exact and_congr Iff.rfl not_lt

open GlobalTheory.CuspRep GlobalTheory.SmGL Formalism.L2.Host in

theorem exists_twist_isUnitary {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} (hn : 1 ≤ n)
    (τ : CuspSub E n) (w : HeightOneSpectrum (𝓞 E)) :
    ∃ (ν : HChar E) (x : ℝ), (CG.mk (τ.twist ν)).IsUnitary ∧ ν.loc w = absPow (w.adicCompletion E) (x : ℂ) := by
  obtain ⟨ω, hω⟩ := GlobalTheory.CuspRep.Central.exists_hasCentChar (CG.mk τ)
  have hωc : Continuous (ω.1 : _ → ℂˣ) := ω.2.1
  let t : ℝ := -(1 / (n : ℝ))
  let ν : HChar E := ⟨(UnitTwist.normPowHom t).comp ω.1, (UnitTwist.continuous_normPowHom t).comp hωc, fun k => by
    rw [MonoidHom.comp_apply, ω.2.2 k, map_one]⟩
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.SplitFlip.exists_isUnif (k := w.adicCompletion E)
  have hνu : GlobalTheory.SplitWeil.IsUnram (ν.loc w) := fun y hy => by
    have hy' : IsUnitAt w y := (valuation_eq_one_iff w _).1 hy
    change UnitTwist.normPowHom t (ω.loc w y) = 1
    ext
    rw [UnitTwist.normPowHom_val, UnitTwist.norm_loc_eq_one ω hy', Real.one_rpow]
    simp
  have h0 := nabs_pos' (w.adicCompletion E) ϖ
  have h1 : GlobalTheory.SplitWeil.nabs (w.adicCompletion E) ϖ ≠ 1 := fun e =>
    (hϖ.symm ▸ ValuativeRel.uniformizer_lt_one :
      ValuativeRel.valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) < 1).ne ((GlobalTheory.SplitWeil.nabs_eq_one_iff ϖ).1 e)
  have hp : 0 < ‖((ω.loc w ϖ : ℂˣ) : ℂ)‖ ^ t := Real.rpow_pos_of_pos (norm_pos_iff.2 (Units.ne_zero _)) _
  refine ⟨ν, Real.logb (GlobalTheory.SplitWeil.nabs (w.adicCompletion E) ϖ) (‖((ω.loc w ϖ : ℂˣ) : ℂ)‖ ^ t),
    ⟨ω * ν ^ n, fun x => ?_, hω.twist ν⟩, ?_⟩
  · change ‖((ω.1 x * (UnitTwist.normPowHom t (ω.1 x)) ^ n : ℂˣ) : ℂ)‖ = 1
    have hr : 0 < ‖((ω.1 x : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
    have ha' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    rw [Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow, UnitTwist.norm_normPowHom, ← Real.rpow_natCast,
      ← Real.rpow_mul hr.le]
    have : t * (n : ℝ) = -1 := by
      simp only [t]
      field_simp
    rw [this, Real.rpow_neg_one, mul_inv_cancel₀ hr.ne']
  · rw [eq_unrChar hνu hϖ, eq_unrChar (isUnram_absPow _ _) hϖ]
    congr 1
    ext
    rw [val_absPow_ofReal, Real.rpow_logb h0 h1 hp]
    rfl

theorem isSubquotient_twRep {H V W : Type} [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {Q : Representation ℂ H V} {R : Representation ℂ H W} {χ χ' : H →* ℂˣ} (h : χ = χ')
    (hQ : GlobalTheory.SmGL.IsSubquotient (GlobalTheory.SmGL.twist Q χ') R) : GlobalTheory.SmGL.IsSubquotient (GlobalTheory.CuspRep.twRep Q χ) R := by
  subst h
  exact hQ

open GlobalTheory.SmGL GlobalTheory.LFun.SplitTie GlobalTheory.CuspRep in

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin (a + a')) (Fin r) E), IsWittFrame σ (c • G.W.J.map σ) Xf Yf →
        ∀ K, IsMaxCpt σ (c • G.W.J.map σ) K →
          IsAut σ (c • G.W.J.map σ) K (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) →
          ∀ S s, GlobalTheory.StdPar.IsCuspExp σ (c • G.W.J.map σ) Xf Yf S K (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) s →
            ∀ (k : Fin r) (l : ℕ), k ∈ S → l ≤ k.val → (∀ j ∈ S, j < k → j.val < l) → (l = 0 ∨ ∃ j ∈ S, j.val + 1 = l) →
            ∀ n : ℕ, n = k.val + 1 - l →
            ∀ h : l + n ≤ a + a',
            ∃ (w : HeightOneSpectrum (𝓞 E)) (τ : GlobalTheory.CuspRep.CuspSub E n)
              (ρ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) (w.adicCompletion E))) (z : ℝ),
              X.Good (w.under (𝓞 F)) ∧ (GlobalTheory.CuspRep.CG.mk τ).IsUnitary ∧ τ.IsLocComp w ρ ∧
                GlobalTheory.ThK.MidJac.IsMidJacAt w a a' l h (GlobalTheory.LFun.locChar X.α w * GlobalTheory.ThK.MidJac.absPowAt w (z : ℂ))
                  (GlobalTheory.LFun.locChar X.β w * GlobalTheory.ThK.MidJac.absPowAt w (z : ℂ)) ρ.ρ := by
  intro F E _ _ _ _ _ _ σ hσ B a a' G X om om' hK hT c hc hcs Φ hΦ r Xf Yf hW K hKc hAut S s hs k l hk hlk hlt hl0 n hn h
  have hcm := hT.base.cm
  have hJ := GlobalTheory.ThK.SqIntHerm.isHermND_smul_map F E σ B _ G.W _ _ hT.geo.hW c hc hcs
  obtain ⟨φc, hφc, f', hf', hf0, -⟩ := hs
  have hne : φc ≠ 0 := by
    rintro rfl
    refine hf0 ((Submodule.span_le (p := ⊥)).2 ?_ hf')
    rintro _ ⟨u, y, -, rfl⟩
    rfl
  obtain ⟨B₀, hB₀⟩ := GlobalTheory.T.witt_frame_local_langlands_unitary hK (GlobalTheory.T.kp_implies_cuspidal_spectrum_GL hK) F E σ hcm (a + a') (c • G.W.J.map σ) hJ r Xf Yf hW hK.automorphicFormsUnitary.2 B.v₁ B.τ₁
  obtain ⟨m, T, x, hTi, hsum⟩ := exists_intertwiners F E σ hσ B a a' G X om om' hK hT c hc hcs Φ hΦ B₀
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hld, τ, W', _, _, Q, hQ, f, hf⟩ := hB₀ K hKc _ hAut _ _ (isSmooth_parInd _ _) m T x hTi hsum S φc hφc hne l n hn1
    (fun j h1 h2 hj => by have := hlt j hj (show j.val < k.val by omega); omega) ⟨k, hk, by omega⟩ hl0
  have hBZ := hK.base.bernsteinZelevinskyFiniteness
  have sα := (GlobalTheory.ChrWLocal.chrW_local F E X.α hT.chars.heckeα B.v₁ B.τ₁).1.1
  have sβ := (GlobalTheory.ChrWLocal.chrW_local F E X.β hT.chars.heckeβ B.v₁ B.τ₁).1.1
  have hfl : HasFiniteLength (GlobalTheory.ThK.MidJac.detInd a a' (chrW X.α B.τ₁) (chrW X.β B.τ₁)) :=
    (hBZ (Fv F B.v₁)).2.2.1 _ _ _ _ _ _ ((isSmooth_ofChar_iff _).2
      (IsSmoothChar.mul ((IsSmoothChar.detChar sα).comp _ (continuous_apply _))
        ((IsSmoothChar.detChar sβ).comp _ (continuous_apply _))))
      (hasFiniteLength_of_isIrreducible (isIrreducible_ofChar _))
  obtain ⟨ρ, hρ, g, hg⟩ := GlobalTheory.T.jacquet_subquotient_restriction hBZ (Fv F B.v₁) (a + a') l n hld _ _ (isSmooth_parInd _ _) hfl _ Q hQ _ _ f hf
  let e := complEquiv B.τ₁ (splitPrime_under B.τ₁)
  obtain ⟨c1, c2⟩ : Continuous e ∧ Continuous e.symm := by
    obtain ⟨ψ, hψ, -, -, c1, c2⟩ := GlobalTheory.LFun.SplitChart.exists_equiv_complMap B.τ₁ (splitPrime_under B.τ₁)
    obtain rfl : ψ = e := RingEquiv.ext hψ
    exact ⟨c1, c2⟩
  have hρ' := GlobalTheory.T.jacquet_field_iso_transport (Fv F B.v₁) _ e c1 c2 a a' l n hld _ _ (GlobalTheory.LFun.locChar X.α (splitPrime B.τ₁))
    (GlobalTheory.LFun.locChar X.β (splitPrime B.τ₁)) (fun _ => congrArg _ (Units.ext rfl)) (fun _ => congrArg _ (Units.ext rfl)) _ ρ.ρ hρ
  let ρ' : SmIrr (GL (Fin n) ((splitPrime B.τ₁).adicCompletion E)) :=
    { V := ρ.V
      ρ := ρ.ρ.comp (glEquiv n e).symm.toMonoidHom
      smooth := fun y => (ρ.smooth y).preimage (Continuous.units_map _ (continuous_id.matrix_map c2))
      irred := by
        obtain ⟨h0, h1⟩ := (isIrreducible_iff _).1 ρ.irred
        exact (isIrreducible_iff _).2 ⟨h0, fun U hU => h1 U fun y z hz => by
          simpa using hU (glEquiv n e y) z hz⟩ }
  have hloc : τ.IsLocComp (splitPrime B.τ₁) ρ' := by
    refine ⟨g.toLinearMap, fun h0 => hg (Representation.IntertwiningMap.ext h0), fun y z => ?_⟩
    exact (g.isIntertwining _ _ ((glEquiv n e).symm y) z).trans
      (congrArg (fun u => τ.locRep (splitPrime B.τ₁) u (g z)) ((glEquiv n e).apply_symm_apply y))
  obtain ⟨ν, y, hνu, hν⟩ := exists_twist_isUnitary hn1 τ (splitPrime B.τ₁)
  obtain ⟨z, hz⟩ := GlobalTheory.T.jacquet_det_induced_twist ((splitPrime B.τ₁).adicCompletion E) a a' l n hld y
  refine ⟨splitPrime B.τ₁, τ.twist ν, _, z, (splitPrime_under B.τ₁).symm ▸ hT.chars.good, hνu, hloc.twist ν, ?_⟩
  have hχ : CuspSub.locDet n ν (splitPrime B.τ₁) = detChar (Fin n) (absPow _ (y : ℂ)) :=
    congrArg (fun χ => MonoidHom.comp χ Matrix.GeneralLinearGroup.det) hν
  exact isSubquotient_twRep hχ (hz _ _ _ _ hρ')

end GlobalTheory.ThK.MidJacGlobal
