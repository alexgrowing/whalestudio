import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EncardSmulMemLeEncardSmulInterNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitDecayStatement

noncomputable section

open scoped NNReal TensorProduct Matrix
open NumberField MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.ThK

namespace GlobalTheory.KDecayProof

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

theorem kDecay_of_parts (hS : GlobalTheory.Published.SiegelSetUnitary) (h1 : ThetaBasic) (h2 : WeilConv) (h3 : SoDecay) : KDecay := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  have hv := measure_dom_lt_top hS hT.base hT.geo.hV' hT.geo.hM'
  have hlt : a + a' + 2 * min (a - G.p) G.p < 2 * a := by
    have := hT.geo.eBig
    have := min_le_right (a - G.p) G.p
    omega
  refine ⟨fun Φ hΦ => ((h2 F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (isPair_big hT) (Or.inl hlt)).1 Φ hΦ).1, fun Φ' hΦ' => ?_⟩
  have hd := h3 F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (isPair_small hT) Φ' hΦ'
  have hc := ((h1 F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (isPair_small hT)).1 Φ' (so_le_schA hT.geo.hM' _ hΦ')).1
  obtain ⟨C, k, hC⟩ := hd 0
  refine ⟨hd, fun h => ?_, C * (G.M'.μ G.M'.dom).toReal, k, fun h => ?_⟩
  · refine Measure.integrableOn_of_bounded (M := C * (ht h : ℝ) ^ k) hv.ne
      (hc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => ?_)
    simpa using hC g h
  · have := norm_setIntegral_le_of_norm_le_const hv (fun g _ => by simpa using hC g h)
    unfold Model.I
    refine this.trans (le_of_eq ?_)
    rw [Measure.real]; ring

theorem kDecay_of_classicalTheorems (hP : KP) : KDecay :=
  kDecay_of_parts hP.siegelSetUnitary (GlobalTheory.T.theta_basic_properties hP.base) (GlobalTheory.T.weil_convergence_of_kernel hP) (GlobalTheory.T.schwartz_orbit_decay hP)

end GlobalTheory.KDecayProof
