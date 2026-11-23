import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapCompStalkAlg
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory.LogKSDiv.LocSpan

theorem deriv_ext {k R A : Type} [CommRing k] [CommRing R] [CommRing A] [Algebra k A] (φ : R →+* A)
    (M : Submonoid R) (hloc : letI := φ.toAlgebra; IsLocalization M A) (D₁ D₂ : Derivation k A A)
    (h : ∀ r, D₁ (φ r) = D₂ (φ r)) : D₁ = D₂ := by
  letI := φ.toAlgebra
  ext y
  obtain ⟨⟨r, t⟩, e⟩ := IsLocalization.surj M y
  have hu : IsUnit (φ t) := IsLocalization.map_units A t
  have e' : y * φ t = φ r := e
  have h1 := congrArg D₁ e'
  have h2 := congrArg D₂ e'
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1 h2
  rw [h r, h t] at h1
  have : φ t * D₁ y = φ t * D₂ y := by linear_combination h1 - h2
  exact hu.mul_left_cancel this

end GlobalTheory.LogKSDiv.LocSpan

namespace GlobalTheory.LogKSDiv.LocSpan

theorem sum_apply {k R M : Type} [CommRing k] [CommRing R] [AddCommGroup M] [Algebra k R] [Module R M] [Module k M]
    {n : ℕ} (f : Fin n → Derivation k R M) (x : R) : (∑ j, f j) x = ∑ j, f j x := by
  rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  rfl

theorem span_eq_top {k R A : Type} [Field k] [CommRing R] [CommRing A] [Algebra k R] [Algebra k A]
    [Algebra.FiniteType k R] (φ : R →+* A) (hk : φ.comp (algebraMap k R) = algebraMap k A)
    (M : Submonoid R) (hloc : letI := φ.toAlgebra; IsLocalization M A) (a : R) (ha : IsUnit (φ a)) {n : ℕ}
    (v : Fin n → Derivation ℤ R R)
    (hlog : ∀ D : Derivation k R R, a • D.restrictScalars ℤ ∈ Submodule.span R (Set.range v))
    (δ : Fin n → Derivation k A A) (hδ : ∀ j r, δ j (φ r) = φ (v j r)) :
    Submodule.span A (Set.range δ) = ⊤ := by
  letI := φ.toAlgebra
  haveI : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq fun c => (congrArg (· c) hk).symm
  haveI : Algebra.FinitePresentation k R := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  rw [Submodule.eq_top_iff']
  intro d
  let g : Derivation k R A := d.compAlgebraMap R
  obtain ⟨h, s, hs⟩ :=
    Module.FinitePresentation.exists_lift_of_isLocalizedModule M (Algebra.linearMap R A) g.liftKaehlerDifferential
  let D' : Derivation k R R := h.compDer (KaehlerDifferential.D k R)
  have hD' : ∀ r, φ (D' r) = φ s * d (φ r) := by
    intro r
    have := congrArg (fun L : Ω[R⁄k] →ₗ[R] A => L (KaehlerDifferential.D k R r)) hs
    simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply, LinearMap.smul_apply,
      Derivation.liftKaehlerDifferential_comp_D] at this
    rw [Submonoid.smul_def, Algebra.smul_def] at this
    exact this
  obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hlog D')
  have hsu : IsUnit (φ s) := IsLocalization.map_units A s
  have hu : IsUnit (φ a * φ s) := ha.mul hsu
  have key : (φ a * φ s) • d = ∑ j, φ (cf j) • δ j := by
    refine deriv_ext φ M hloc _ _ fun r => ?_
    have e1 := congrArg (fun D : Derivation ℤ R R => φ (D r)) hcf
    simp only [sum_apply, Derivation.coe_smul, Pi.smul_apply, smul_eq_mul, map_sum,
      map_mul, Derivation.coe_restrictScalars] at e1
    simp only [sum_apply, Derivation.coe_smul, Pi.smul_apply, smul_eq_mul, hδ]
    rw [e1, hD']
    ring
  have hmem : (φ a * φ s) • d ∈ Submodule.span A (Set.range δ) := by
    rw [key]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hmem' : ((hu.unit : Aˣ) : A) • d ∈ Submodule.span A (Set.range δ) := by
    rw [hu.unit_spec]
    exact hmem
  have := Submodule.smul_mem _ ((hu.unit⁻¹ : Aˣ) : A) hmem'
  rwa [smul_smul, Units.inv_mul, one_smul] at this

end GlobalTheory.LogKSDiv.LocSpan

namespace GlobalTheory.LogKSDiv.LocSpan

theorem appLE_germ {X S : Scheme.{0}} (f : X ⟶ S) (W : S.Opens) (V T : X.Opens) (hV : V ≤ f ⁻¹ᵁ W)
    (hT : T ≤ f ⁻¹ᵁ W) (x : X) (hxV : x ∈ V) (hxT : x ∈ T) :
    f.appLE W V hV ≫ X.presheaf.germ V x hxV = f.appLE W T hT ≫ X.presheaf.germ T x hxT := by
  rw [← X.presheaf.germ_res (homOfLE (inf_le_left : V ⊓ T ≤ V)) x ⟨hxV, hxT⟩,
    ← X.presheaf.germ_res (homOfLE (inf_le_right : V ⊓ T ≤ T)) x ⟨hxV, hxT⟩,
    Scheme.Hom.appLE_map_assoc, Scheme.Hom.appLE_map_assoc]

theorem appLE_appLE_germ {X Y S : Scheme.{0}} (ι : X ⟶ Y) (s : Y ⟶ S) (W : S.Opens) (U : Y.Opens) (V T : X.Opens)
    (h1 : U ≤ s ⁻¹ᵁ W) (hV : V ≤ ι ⁻¹ᵁ U) (h2 : T ≤ (ι ≫ s) ⁻¹ᵁ W) (x : X) (hxV : x ∈ V) (hxT : x ∈ T) :
    s.appLE W U h1 ≫ ι.appLE U V hV ≫ X.presheaf.germ V x hxV = (ι ≫ s).appLE W T h2 ≫ X.presheaf.germ T x hxT := by
  rw [Scheme.Hom.appLE_comp_appLE_assoc]
  exact appLE_germ _ _ _ _ _ _ _ _ _

end GlobalTheory.LogKSDiv.LocSpan

namespace GlobalTheory.LogKSDiv.LocSpan

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem stalkHom_comp_algX (TF : TorFlag Xo c) (Z : Comp Xo c) (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens)
    (hx : (barComp TF.Y Z).ι x ∈ U.1) :
    (stalkHom TF Z x U hx).comp (algX TF.Y.s U.1) = stalkAlg TF Z x := by
  ext a
  simp only [stalkHom, stalkAlg, algX, RingHom.comp_apply]
  have key : TF.Y.s.appLE ⊤ U.1 (by simp) ≫ (barComp TF.Y Z).ι.app U.1 ≫
      (X₀ TF.Y Z).presheaf.germ ((barComp TF.Y Z).ι ⁻¹ᵁ U.1) x hx =
      (s₀ TF.Y Z).appLE ⊤ ⊤ (by simp) ≫ (X₀ TF.Y Z).presheaf.germ ⊤ x trivial := by
    rw [Scheme.Hom.app_eq_appLE]
    exact appLE_appLE_germ _ _ _ _ _ _ _ _ _ _ _ _
  exact congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom a)) key

end GlobalTheory.LogKSDiv.LocSpan

namespace GlobalTheory.LogKSDiv.LocSpan

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem finiteType_algX (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) : (algX TF.Y.s U.1).FiniteType := by
  haveI := TF.smooth
  haveI : Smooth TF.Y.s := SmoothOfRelativeDimension.smooth Dw.dim _
  have h1 : (TF.Y.s.appLE ⊤ U.1 (by simp)).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType TF.Y.s inferInstance ⟨⊤, isAffineOpen_top _⟩ U _
  exact h1.comp (RingHom.FiniteType.of_surjective _
    (Scheme.ΓSpecIso (CommRingCat.of c.F)).symm.commRingCatIsoToRingEquiv.surjective)

theorem isLocalization_stalkHom (TF : TorFlag Xo c) (Z : Comp Xo c) (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens)
    (hx : (barComp TF.Y Z).ι x ∈ U.1) :
    letI := (stalkHom TF Z x U hx).toAlgebra
    IsLocalization.AtPrime ((X₀ TF.Y Z).presheaf.stalk x) (U.2.primeIdealOf ⟨_, hx⟩).asIdeal := by
  letI := TopCat.Presheaf.algebra_section_stalk TF.Y.X.presheaf (⟨_, hx⟩ : U.1)
  have h1 := U.2.isLocalization_stalk ⟨_, hx⟩
  let e := (asIso ((barComp TF.Y Z).ι.stalkMap x)).commRingCatIsoToRingEquiv
  have h2 := (IsLocalization.isLocalization_iff_of_ringEquiv _ e).1 h1
  have heq : stalkHom TF Z x U hx = e.toRingHom.comp (TF.Y.X.presheaf.germ U.1 _ hx).hom :=
    RingHom.ext fun y => (Scheme.Hom.germ_stalkMap_apply _ _ _ hx y).symm
  rw [heq]
  convert h2

theorem exists_unit (TF : TorFlag Xo c) (Z : Comp Xo c) (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens)
    (hx : (barComp TF.Y Z).ι x ∈ U.1) (hint : x ∈ (j₀ TF.Y Z).opensRange) :
    ∃ a ∈ (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl).ideal U,
      IsUnit (stalkHom TF Z x U hx a) := by
  have hin : (barComp TF.Y Z).ι x ∈ LogKS.interior TF.Y := by
    obtain ⟨y, rfl⟩ := hint
    refine ⟨i₀ TF.Y Z y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← j₀_ι, Scheme.Hom.comp_apply]
  obtain ⟨a, hle, hxa⟩ := U.2.exists_basicOpen_le (V := U.1 ⊓ LogKS.interior TF.Y) ⟨_, hx, hin⟩ hx
  refine ⟨a, ?_, ?_⟩
  · rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
    intro p hp
    by_contra hpa
    have h3 : p ∈ PrimeSpectrum.basicOpen a := hpa
    rw [← U.2.fromSpec_preimage_basicOpen] at h3
    exact hp (hle h3).2
  · have h4 : x ∈ (barComp TF.Y Z).ι ⁻¹ᵁ TF.Y.X.basicOpen a := hxa
    rw [Scheme.preimage_basicOpen] at h4
    exact ((X₀ TF.Y Z).mem_basicOpen _ x hx).1 h4

end GlobalTheory.LogKSDiv.LocSpan

theorem GlobalTheory.LogKSDiv.span_logDer_germs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1) (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)), letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra; ∀ δ : Fin Dw.dim → Derivation c.F ((X₀ TF.Y Z).presheaf.stalk x) ((X₀ TF.Y Z).presheaf.stalk x), (∀ j r, δ j (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r) = GlobalTheory.LogKSDiv.stalkHom TF Z x U hx ((b j).1 r)) → x ∈ (j₀ TF.Y Z).opensRange → Submodule.span ((X₀ TF.Y Z).presheaf.stalk x) (Set.range δ) = ⊤ := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U _ hx b
  intro δ hδ hint
  letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra
  letI : Algebra c.F Γ(TF.Y.X, U.1) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX TF.Y.s U.1).toAlgebra
  haveI : Algebra.FiniteType c.F Γ(TF.Y.X, U.1) := LocSpan.finiteType_algX TF U
  obtain ⟨a, haI, hau⟩ := LocSpan.exists_unit TF Z x U hx hint
  refine LocSpan.span_eq_top (stalkHom TF Z x U hx) (LocSpan.stalkHom_comp_algX TF Z x U hx) _
    (LocSpan.isLocalization_stalkHom TF Z x U hx) a hau (fun j => (b j).1) ?_ δ hδ
  intro D
  have hmem : a • D.restrictScalars ℤ ∈
      LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U := by
    refine ⟨fun a' => ?_, fun f _ => ?_⟩
    · show a * D (constFn TF.Y.s U.1 a') = 0
      rw [show constFn TF.Y.s U.1 a' = algebraMap c.F _ a' from rfl, D.map_algebraMap, mul_zero]
    · show a * D f ∈ _
      exact Ideal.mul_mem_right _ _ haI
  have h7 := congrArg Subtype.val (b.sum_repr ⟨_, hmem⟩)
  rw [Submodule.coe_sum] at h7
  simp only [Submodule.coe_smul] at h7
  rw [← h7]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
