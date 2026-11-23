import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory.Points
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.UPoinc.ChartAt

theorem spec_ext_of_isFractionRing {A K T : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing T] (h₁ h₂ : Sp T ⟶ Sp K) (e : h₁ ≫ spMap (algebraMap A K) = h₂ ≫ spMap (algebraMap A K)) : h₁ = h₂ := by
  obtain ⟨g₁, rfl⟩ := Spec.map_surjective h₁
  obtain ⟨g₂, rfl⟩ := Spec.map_surjective h₂
  rw [spMap, ← Spec.map_comp, ← Spec.map_comp] at e
  have e' := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  congr 1
  ext1
  exact IsLocalization.ringHom_ext (nonZeroDivisors A) e'

theorem exists_int_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {cf : Coeff l} (C : UCompact Xo cf) {a : C.o} (ha : a ≠ 0) :
    ∃ n : ℤ, n ≠ 0 ∧ a ∣ (n : C.o) := by
  haveI := C.ded
  have h1 : IsAlgebraic ℚ (C.b a) := Algebra.IsAlgebraic.isAlgebraic _
  have h2 : IsAlgebraic ℤ (C.b a) := (IsFractionRing.isAlgebraic_iff ℤ ℚ cf.F).2 h1
  have h3 : IsAlgebraic ℤ a := (isAlgebraic_algHom_iff C.b.toIntAlgHom C.inj).1 h2
  have h4 := Ideal.comap_ne_bot_of_algebraic_mem ha (Ideal.mem_span_singleton_self a) h3
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h4
  refine ⟨n, hn0, ?_⟩
  have := Ideal.mem_span_singleton.1 (Ideal.mem_comap.1 hn)
  simpa using this

end GlobalTheory.UPoinc.ChartAt

namespace GlobalTheory.UPoinc.ChartAt

theorem exists_affine_chart_ratLift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (w : X.M.Z), X.π w ∈ Set.range C.i → ∃ (U₀ : X.M.Z.Opens) (u₀ : Sp (ratHull (X.M.ringOn U₀)) ⟶ Xo.XF cf), IsAffineOpen U₀ ∧ w ∈ U₀ ∧ spMap (ratHull (X.M.ringOn U₀)).val.toRingHom ≫ u₀ = X.uΩ := by
  intro E _ _ _ H Dw l Xo cf C X w hw
  haveI := X.ar.char
  haveI := C.iF_open
  haveI := C.ded
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hemb := Scheme.Hom.isEmbedding (pullback.fst C.z (spMap C.b))
  obtain ⟨V, hVo, hV⟩ := hemb.isInducing.isOpen_iff.1 C.iF.isOpenEmbedding.isOpen_range
  set V' : X.M.Z.Opens := X.π ⁻¹ᵁ ⟨V, hVo⟩ with hV'def
  have hwV : w ∈ V' := by
    obtain ⟨x, hx⟩ := hw
    show X.π w ∈ V
    have : C.iF x ∈ pullback.fst C.z (spMap C.b) ⁻¹' V := hV ▸ ⟨x, rfl⟩
    rw [← hx]
    simpa using this
  obtain ⟨U, hU, hwU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := X.M.Z) (U := V') hwV
  have hne : ((U : X.M.Z.Opens) : Set X.M.Z).Nonempty := ⟨w, hwU⟩
  set R₀ := X.M.ringOn U with hR₀
  let φ : Γ(X.M.Z, U) ⟶ CommRingCat.of R₀ := CommRingCat.ofHom (X.M.sectionsEquiv U hne).toRingHom
  let f : Sp R₀ ⟶ X.M.Z := Spec.map φ ≫ hU.fromSpec
  let g : Sp (ratHull R₀) ⟶ C.Z := spMap (toRat R₀) ≫ f ≫ X.π
  have hgV : ∀ y, g y ∈ V := by
    intro y
    have hy : hU.fromSpec (Spec.map φ (spMap (toRat R₀) y)) ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
    rw [hU.range_fromSpec] at hy
    exact hUV hy
  let ψ : C.o →+* ratHull R₀ := (Spec.preimage (g ≫ C.z)).hom
  have hψ : ∀ a : nonZeroDivisors C.o, IsUnit (ψ a) := by
    rintro ⟨a, ha⟩
    obtain ⟨n, hn, hdvd⟩ := exists_int_dvd C (nonZeroDivisors.ne_zero ha)
    exact isUnit_of_dvd_unit (map_dvd ψ hdvd) (by simpa using isUnit_intCast_ratHull R₀ hn)
  let θ : cf.F →+* ratHull R₀ := IsLocalization.lift (M := nonZeroDivisors C.o) hψ
  have hθ : θ.comp (algebraMap C.o cf.F) = ψ := IsLocalization.lift_comp hψ
  have hw' : g ≫ C.z = spMap θ ≫ spMap C.b := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    change _ = Spec.map (CommRingCat.ofHom (θ.comp (algebraMap C.o cf.F)))
    rw [hθ]
    exact (Spec.map_preimage _).symm
  let g' : Sp (ratHull R₀) ⟶ pullback C.z (spMap C.b) := pullback.lift g (spMap θ) hw'
  have hrange : Set.range g' ⊆ Set.range C.iF := by
    rintro _ ⟨y, rfl⟩
    rw [← hV]
    show pullback.fst C.z (spMap C.b) (g' y) ∈ V
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact hgV y
  refine ⟨U, IsOpenImmersion.lift C.iF g' hrange, hU, hwU, ?_⟩
  have hpt : ⊤ ≤ X.M.pt ⁻¹ᵁ U := X.M.top_le_preimage_pt hne
  have hφ : φ ≫ CommRingCat.ofHom R₀.val.toRingHom = valMap X.M.pt U hpt := by
    ext a
    show ((X.M.sectionsEquiv U hne a : X.M.ringOn U) : X.Ω₁) = _
    rw [RatModel.coe_sectionsEquiv, ← valR_eq, valF_eq_valR]
  have hf : spMap R₀.val.toRingHom ≫ f = X.M.pt := by
    simp only [f, ← Category.assoc]
    rw [spMap, ← Spec.map_comp, hφ, specMap_valMap_fromSpec]
  have hfst : spMap (ratHull R₀).val.toRingHom ≫ g = X.uΩ ≫ C.i := by
    show spMap (ratHull R₀).val.toRingHom ≫ spMap (toRat R₀) ≫ f ≫ X.π = _
    rw [← Category.assoc, spMap_val_toRat, ← Category.assoc, hf, X.comp]
    simp only [USetup.uΩ, Category.assoc]
  rw [← cancel_mono C.iF, Category.assoc, IsOpenImmersion.lift_fac]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hfst]
    simp only [UCompact.i, Category.assoc]
  · have key : spMap (ratHull R₀).val.toRingHom ≫ g' ≫ pullback.snd C.z (spMap C.b) ≫ spMap C.b =
        X.uΩ ≫ C.iF ≫ pullback.snd C.z (spMap C.b) ≫ spMap C.b := by
      rw [← pullback.condition, ← Category.assoc g', pullback.lift_fst, reassoc_of% hfst]
      simp only [UCompact.i, Category.assoc]
    exact spec_ext_of_isFractionRing (A := C.o) _ _ (by simpa only [Category.assoc] using key)

end GlobalTheory.UPoinc.ChartAt
