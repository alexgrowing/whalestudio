import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToOfComponents

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem fderiv_line {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (F : V → ℂ) (v₀ w : V)
    (hF : DifferentiableAt ℂ F v₀) :
    DifferentiableAt ℂ (fun z : Fin 1 → ℂ => F (v₀ + z 0 • w)) 0 ∧
      fderiv ℂ (fun z : Fin 1 → ℂ => F (v₀ + z 0 • w)) 0 (fun _ => 1) = fderiv ℂ F v₀ w := by
  have hℓ : HasFDerivAt (fun z : Fin 1 → ℂ => v₀ + z 0 • w)
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight w) 0 := by
    have h1 : HasFDerivAt (fun z : Fin 1 → ℂ => z 0 • w)
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight w) 0 :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight w).hasFDerivAt
    exact h1.const_add v₀
  have hF' : HasFDerivAt F (fderiv ℂ F v₀) ((fun z : Fin 1 → ℂ => v₀ + z 0 • w) 0) := by
    simpa using hF.hasFDerivAt
  have hc : HasFDerivAt (fun z : Fin 1 → ℂ => F (v₀ + z 0 • w))
      ((fderiv ℂ F v₀).comp ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight w)) 0 :=
    hF'.comp (0 : Fin 1 → ℂ) hℓ
  refine ⟨hc.differentiableAt, ?_⟩
  rw [hc.fderiv]
  simp

private theorem exists_isDerivAt0_line_of_isHolTo {X : Scheme.{0}} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {B : Set V} {t : V → (Sp ℂ ⟶ X)} (ht : IsHolTo B t) {v₀ : V} (hv : v₀ ∈ B) (w : V) :
    ∃ x, IsDerivAt0 (fun z : Fin 1 → ℂ => t (v₀ + z 0 • w)) (fun _ => 1) x := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ ((t v₀) default)) isOpen_univ
  have hW0 : ⊤ ≤ t v₀ ⁻¹ᵁ W := by
    rw [top_le_preimage_iff_mem]
    have hd : (@default (PrimeSpectrum ℂ) _) = (@default (↥(Sp ℂ)) _) := Subsingleton.elim _ _
    rw [hd]
    exact hxW
  have hℓc : Continuous (fun z : Fin 1 → ℂ => v₀ + z 0 • w) := by
    fun_prop
  have hℓ0 : (fun z : Fin 1 → ℂ => v₀ + z 0 • w) 0 = v₀ := by
    simp
  have hev : ∀ᶠ z in 𝓝 (0 : Fin 1 → ℂ), ⊤ ≤ t (v₀ + z 0 • w) ⁻¹ᵁ W := by
    have h1 := LocalLift.hol_eventually_mem ht hv hW0
    have h2 : Tendsto (fun z : Fin 1 → ℂ => v₀ + z 0 • w) (𝓝 0) (𝓝 v₀) := by
      have := hℓc.tendsto 0
      simpa using this
    exact (h2.eventually h1).mono (fun z hz => hz.2)
  have hdiff : ∀ a : Γ(X, W), DifferentiableAt ℂ (fun z : Fin 1 → ℂ => valAt' (t (v₀ + z 0 • w)) W a) 0 :=
    fun a => (fderiv_line (fun v => valAt' (t v) W a) v₀ w
      (LocalLift.hol_differentiableAt ht hv hW0 a)).1
  let ψ : Γ(X, W) →+* DualNumber ℂ :=
    { toFun := fun a => FibreDeriv.jet (fun _ => 1) (fun z : Fin 1 → ℂ => valAt' (t (v₀ + z 0 • w)) W a)
      map_one' := by
        have hc : (fun z : Fin 1 → ℂ => valAt' (t (v₀ + z 0 • w)) W 1) =ᶠ[𝓝 0] (fun _ => (1 : ℂ)) :=
          hev.mono (fun z hz => valAt'_one _ hz)
        rw [FibreDeriv.jet_congr _ hc, FibreDeriv.jet_const]
        simp
      map_mul' := by
        intro a b
        simp only [valAt'_mul]
        exact FibreDeriv.jet_mul _ (hdiff a) (hdiff b)
      map_zero' := by
        simp only [valAt'_zero]
        rw [FibreDeriv.jet_const]
        simp
      map_add' := by
        intro a b
        simp only [valAt'_add]
        exact FibreDeriv.jet_add _ (hdiff a) (hdiff b) }
  obtain ⟨x, hx, hxψ⟩ := TangentOrigin.exists_evalPt_eq hW ψ
  refine ⟨x, FibreDeriv.isDerivAt0_of_affine ?_ hW hx (fun a => ⟨hdiff a, ?_⟩)⟩
  · have h' : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ x) ⁻¹ᵁ W :=
      (TangentOrigin.top_le_preimage_iff x W).mp hx
    have h0 : ⊤ ≤ t (v₀ + (0 : Fin 1 → ℂ) 0 • w) ⁻¹ᵁ W := by
      simpa using hW0
    refine TangentOrigin.ext_evalPt hW h' h0 (RingHom.ext (fun a => ?_))
    rw [TangentOrigin.evalPt_spMap_comp _ x W hx h' a, hxψ, ← TangentOrigin.valAt'_eq_evalPt]
    exact FibreDeriv.fst_jet (fun _ => 1) (fun z : Fin 1 → ℂ => valAt' (t (v₀ + z 0 • w)) W a)
  · show TangentOrigin.evalPt x W hx a = _
    rw [hxψ]
    rfl

private theorem isDerivAt0_line_const_of_flat {X : Scheme.{0}} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {B : Set V} {t : V → (Sp ℂ ⟶ X)} (ht : IsHolTo B t) {v₀ : V} (hv : v₀ ∈ B) (w : V)
    (hf : Flat t v₀ w) :
    IsDerivAt0 (fun z : Fin 1 → ℂ => t (v₀ + z 0 • w)) (fun _ => 1)
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ t v₀) := by
  have h := LocalLift.isDerivAt0_const (fun z : Fin 1 → ℂ => t (v₀ + z 0 • w)) (fun _ => 1)
    (fun U f hU => by
      have hU' : ⊤ ≤ t v₀ ⁻¹ᵁ U := by
        simpa using hU
      rw [(fderiv_line (fun v => valAt' (t v) U f) v₀ w
        (LocalLift.hol_differentiableAt ht hv hU' f)).2]
      exact hf U f hU')
  simpa using h

private theorem flat_of_isDerivAt0_line_const {X : Scheme.{0}} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {B : Set V} {t : V → (Sp ℂ ⟶ X)} (ht : IsHolTo B t) {v₀ : V} (hv : v₀ ∈ B) (w : V)
    (hd : IsDerivAt0 (fun z : Fin 1 → ℂ => t (v₀ + z 0 • w)) (fun _ => 1)
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ t v₀)) :
    Flat t v₀ w := by
  intro U f hU
  rw [← (fderiv_line (fun v => valAt' (t v) U f) v₀ w
    (LocalLift.hol_differentiableAt ht hv hU f)).2]
  have hc : IsDerivAt0 (fun _ : Fin 1 → ℂ => t v₀) (fun _ => 1)
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ t v₀) :=
    LocalLift.isDerivAt0_const (fun _ : Fin 1 → ℂ => t v₀) (fun _ => 1)
      (fun U' f' _ => by simp)
  have h : ⊤ ≤ (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ t v₀) ⁻¹ᵁ U := by
    rw [TangentOrigin.top_le_preimage_iff, hc.1]
    exact hU
  rw [← hd.2 U h f, hc.2 U h f]
  simp

theorem UpperTheory.Gal.W2.pbFlat_of :
    UpperTheory.Gal.W2.FlatAffine → UpperTheory.Gal.W2.PbFlat := by
  intro hFA V _ _ P Y₁ Y₂ T p₁ p₂ f₁ f₂ hpb B s v₀ w hB hv h1 h2 hf1 hf2
  have hs : IsHolTo B s :=
    HolPullback.isHolTo_of_components V B Y₁ P T Y₂ p₁ p₂ f₁ f₂ s hpb hB h1 h2
  obtain ⟨x, hx⟩ := exists_isDerivAt0_line_of_isHolTo hs hv w
  have hc1 := isDerivAt0_line_const_of_flat h1 hv w hf1
  have hc2 := isDerivAt0_line_const_of_flat h2 hv w hf2
  have hx1 := FibreDeriv.isDerivAt0_comp hx p₁
  have hx2 := FibreDeriv.isDerivAt0_comp hx p₂
  have he1 : x ≫ p₁ = (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ s v₀) ≫ p₁ := by
    rw [Category.assoc]
    exact VerticalDeriv.isDerivAt0_unique hx1 hc1
  have he2 : x ≫ p₂ = (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ s v₀) ≫ p₂ := by
    rw [Category.assoc]
    exact VerticalDeriv.isDerivAt0_unique hx2 hc2
  have hxe : x = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ s v₀ := hpb.hom_ext he1 he2
  rw [hxe] at hx
  exact flat_of_isDerivAt0_line_const hs hv w hx
