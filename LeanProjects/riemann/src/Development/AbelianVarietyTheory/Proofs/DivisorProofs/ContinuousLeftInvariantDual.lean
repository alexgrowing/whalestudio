import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EncardSmulMemLeEncardSmulInterNonempty
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKContSmall

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isHecke_div {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

theorem resEtaPow_div {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

variable {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem isPair_big (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, isHecke_div h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
    resEtaPow_div h.chars.resβ h.chars.resα rfl, h.weil⟩

theorem isPair_small (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, isHecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
    resEtaPow_div h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩

theorem so_le_schA {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ)
    {v : Pl F} (t : E →ₐ[F] Fv F v) : M.So ψ t ≤ schA F _ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, φ, h1, h2, -, rfl⟩
  have h3 := (h2.and hM.std).mono fun w hw => hw.1.trans hw.2
  exact Submodule.subset_span ⟨f, _, ⟨isLocallyConstant_finprod_evalV φ h1 h3,
    GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ h1 h3⟩, rfl⟩

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨rfl, A, hA⟩ := h
  let A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm
  have e : A'ᵀ * M * A'.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) _ ℂ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]; rfl
  intro h0
  have e2 := congrArg Matrix.det e
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_neg] at e2
  simp at e2
  exact absurd e2.symm (by simp)

theorem measure_fundamental_domain_lt_top (hS : GlobalTheory.Published.SiegelSetUnitary) (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : IsHermND σ J) (H : Subgroup (GL (Fin n) (AE F E))) (hH : H = HR (AF F) σ J) (μ : @Measure H (borel H))
    (hμ : @Measure.IsHaarMeasure H _ _ (borel H) μ) (D : Set H)
    (hD : letI := borel H; IsFundamentalDomain
      ((Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range.subgroupOf H) D μ) :
    μ D < ⊤ := by
  subst hH
  letI : MeasurableSpace (HR (AF F) σ J) := borel _
  haveI : BorelSpace (HR (AF F) σ J) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨S, -, hcov, -, hvol, -⟩ := GlobalTheory.SiegelSet.exists_cover hS hσ hJ
  set Γ := (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range.subgroupOf (HR (AF F) σ J)
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  haveI : Countable (GL (Fin n) E) := Units.val_injective.countable
  haveI : Countable Γ := by
    have : Countable (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range :=
      (MonoidHom.rangeRestrict_surjective _).countable
    exact Function.Injective.countable (f := fun γ : Γ =>
      (⟨γ.1.1, γ.2⟩ : (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range))
      fun x y h => Subtype.ext (Subtype.ext (Subtype.mk.inj h))
  haveI : MeasurableConstSMul Γ (HR (AF F) σ J) := ⟨fun γ => (continuous_mul_left γ.1).measurable⟩
  haveI : SMulInvariantMeasure Γ (HR (AF F) σ J) μ := ⟨fun γ s _ => measure_preimage_mul μ γ.1 s⟩
  refine lt_of_le_of_lt (GlobalTheory.measure_le_of_isFundamentalDomain_of_ae_covers hD (.of_forall fun g => ?_)) (hvol μ hμ)
  obtain ⟨γ, ⟨δ, -, hδ⟩, s, hs, e⟩ := hcov g
  let γ' : Γ := ⟨γ, δ, hδ⟩
  refine ⟨γ'⁻¹, ?_⟩
  have : γ'⁻¹ • g = s := inv_smul_eq_iff.2 e
  rw [this]; exact hs

theorem measure_dom_lt_top (hS : GlobalTheory.Published.SiegelSetUnitary) (hB : B.IsGood σ) {n d r s : ℕ} {Y : Spc F E n} {W : Spc F E d}
    (hY : Y.IsHerm σ B r s) {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ) : M.μ M.dom < ⊤ := by
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hB.cm
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hd : Y.J.det ≠ 0 := fun h0 => det_ne_zero_of_hasSig (hY.sig w) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero])
  have hJ : IsHermND σ ((1 : E) • Y.J.map σ) := by
    rw [one_smul]
    refine ⟨fun i j => congrArg σ (hY.herm i j), ?_⟩
    have e : (Y.J.map σ).det = σ Y.J.det := ((σ : E →+* E).map_det _).symm
    rw [e]
    exact (map_ne_zero σ).2 hd
  exact measure_fundamental_domain_lt_top hS hB.cm hJ _ (GlobalTheory.SiegelSet.ug_eq_hr hσ one_ne_zero) M.μ hM.haar M.dom hM.dom

theorem contSmall : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      Continuous (G.M'.I om' Φ') ∧ ∀ γ ∈ ratU σ G.W.J, ∀ h, G.M'.I om' Φ' (γ * h) = G.M'.I om' Φ' h := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT Φ' hΦ'
  have hPair := isPair_small hT
  have hSo : Φ' ∈ G.M'.So B.ψ B.τ₁ := (Submodule.mem_inf.1 hΦ').2
  have hS : Φ' ∈ schA F _ := so_le_schA hT.geo.hM' _ hSo
  have hB := (GlobalTheory.T.theta_basic_properties hP.base F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPair).1 Φ' hS
  refine ⟨?_, fun γ hγ h => ?_⟩
  · obtain ⟨C, k, hC⟩ := GlobalTheory.T.schwartz_orbit_decay hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPair Φ' hSo 0
    haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
    have hv := measure_dom_lt_top hP.siegelSetUnitary hT.base hT.geo.hV' hT.geo.hM'
    have hht : Continuous (fun h : UA σ G.W.J => (ht h : ℝ)) :=
      NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)
    haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
    haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
    haveI : SecondCountableTopology (AE F E) := by
      obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
      exact e.secondCountableTopology
    haveI hMat : SecondCountableTopology (Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) :=
      inferInstanceAs (SecondCountableTopology (Fin (a + a') → Fin (a + a') → AE F E))
    haveI : SecondCountableTopology (Matrix (Fin (a + a')) (Fin (a + a')) (AE F E))ᵐᵒᵖ :=
      (MulOpposite.opHomeomorph (M := Matrix (Fin (a + a')) (Fin (a + a')) (AE F E))).symm.secondCountableTopology
    haveI : SecondCountableTopology (GL (Fin (a + a')) (AE F E)) :=
      Units.isEmbedding_embedProduct.secondCountableTopology
    haveI : SecondCountableTopology (UA σ G.W.J) :=
      (Topology.IsEmbedding.subtypeVal (p := fun x : GL (Fin (a + a')) (AE F E) => x ∈ GlobalTheory.WeilM.UG (cA σ) (incM F G.W.J))).secondCountableTopology
    haveI : FirstCountableTopology (UA σ G.W.J) :=
      TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
    rw [continuous_iff_continuousAt]
    intro h₀
    have hev : ∀ᶠ h in 𝓝 h₀, (ht h : ℝ) < ht h₀ + 1 :=
      hht.continuousAt.eventually_lt continuousAt_const (lt_add_one _)
    unfold Model.I
    refine continuousAt_of_dominated (bound := fun _ => max C 0 * ((ht h₀ : ℝ) + 1) ^ k) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun h =>
        (hB.1.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · filter_upwards [hev] with h hh
      refine Eventually.of_forall fun g => ?_
      have h1 := hC g h
      rw [pow_zero, mul_one] at h1
      calc ‖theta om' Φ' g h‖ ≤ C * (ht h : ℝ) ^ k := h1
        _ ≤ max C 0 * (ht h : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (NNReal.coe_nonneg _) _)
        _ ≤ max C 0 * ((ht h₀ : ℝ) + 1) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) hh.le _) (le_max_right _ _)
    · exact integrableOn_const hv.ne
    · exact Eventually.of_forall fun g =>
        (hB.1.comp (continuous_const.prodMk continuous_id)).continuousAt
  · unfold Model.I
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    have e := hB.2.1 1 (one_mem _) γ hγ g h
    rw [one_mul] at e
    exact e

end GlobalTheory.ThKContSmall

end
