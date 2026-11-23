import Development.WeilBound.CoreStatements.CentralCharts.AnalyticAtEval
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPullWedge
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonemptyCptOverOfFlatPreimmersion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentOpenStalksDomain
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFlagDegreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLineLatticeVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameDomainInSegreChartStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentMatchesModelComponentStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeLatticeComparisonStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagCmTypeLatticeComparisonStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExteriorCoeffBaseChangeCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeExteriorLatticeComparisonStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagWeightedDegreeSectionStatement

noncomputable section

namespace AnalyticReference.An

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open Filter Topology GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

theorem int_frac (F : Type) [Field F] [NumberField F] : Function.Injective (algebraMap (𝓞 F) F) ∧ IsNoetherianRing (𝓞 F) ∧
    ∀ x : F, ∃ a b : 𝓞 F, algebraMap (𝓞 F) F b ≠ 0 ∧ x * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a := by
  refine ⟨IsFractionRing.injective _ _, inferInstance, fun x => ?_⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have : algebraMap (𝓞 F) F b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  exact ⟨a, b, this, div_mul_cancel₀ _ this⟩

theorem isCoeffAt_of_smul {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {V : Type}
    [AddCommGroup V] [Module Ω V] {A B : Lat ξ V} {p q : ℕ} {a a' : ⋀[Ω]^p V} {b b' : ⋀[Ω]^q V} {x : Cpt ξ}
    {d₁ d₂ : Ω} (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) (ea : a' = d₁ • a) (eb : b' = d₂ • b)
    (h : IsCoeffAt A B p q a' b' x 1) : IsCoeffAt A B p q a b x (d₁ / d₂)⁻¹ := by
  obtain ⟨α, β, hα, hβ, hA, hB, e⟩ := h
  rw [_root_.one_mul] at e
  subst e
  refine ⟨α * d₁, α * d₂, mul_ne_zero hα h₁, mul_ne_zero hα h₂, ?_, ?_, ?_⟩
  · rw [hA, ea, smul_smul]
  · rw [hB, eb, smul_smul]
  · field_simp

theorem unitAt_of_span_eq {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}
    {a b : Ω} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Submodule.span (regAt ξ p) {a} = Submodule.span (regAt ξ p) {b}) : unitAt ξ p (a / b) := by
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 (h ▸ Submodule.mem_span_singleton_self a :
    a ∈ Submodule.span (regAt ξ p) {b})
  obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.1 (h ▸ Submodule.mem_span_singleton_self b :
    b ∈ Submodule.span (regAt ξ p) {a})
  refine ⟨div_ne_zero ha hb, ?_, ?_⟩
  · have : a / b = (u : Ω) := by rw [← hu]; exact mul_div_cancel_right₀ _ hb
    rw [this]; exact u.2
  · have : (a / b)⁻¹ = (v : Ω) := by rw [inv_div, ← hv]; exact mul_div_cancel_right₀ _ ha
    rw [this]; exact v.2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} [NumberField c.F] {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type}
  [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem exists_cptOver (𝔐 : HodgeCpt Y S y) :
    ∃ (U : Set (Xo.XF c)) (Z : CptOver Y U), genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j) := by
  have hβ := int_frac c.F
  haveI : IsProper Y.s := GlobalTheory.SchemeWords.isProper_of_isProjOver Y.proj
  haveI : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  obtain ⟨W, hW, -, -⟩ := cpt_open_integral Y.X 𝔐.Ω₀ 𝔐.ξ₀ 𝔐.gen₀
  have hsq : (𝔐.ξ ≫ 𝔐.f) ≫ Y.s = spMap 𝔐.cst ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [Category.assoc, 𝔐.cst_over]
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let w := pullback.lift (𝔐.ξ ≫ 𝔐.f) (spMap 𝔐.cst) hsq
  have hw1 : w ≫ pullback.fst _ _ = 𝔐.ξ ≫ 𝔐.f := pullback.lift_fst _ _ _
  have hgen : genPt (𝔐.ξ ≫ 𝔐.f) = genPt 𝔐.ξ₀ := by
    rw [show 𝔐.ξ ≫ 𝔐.f = _ from 𝔐.fn_over]
    exact congrArg (fun x => 𝔐.ξ₀ x) (Subsingleton.elim (α := PrimeSpectrum 𝔐.Ω₀) _ _)
  have hne : ((pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) ⁻¹ᵁ W : Scheme.Opens _) :
      Set ↥(pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)))).Nonempty := by
    refine ⟨genPt w, ?_⟩
    have e : genPt (w ≫ pullback.fst _ _) ∈ W := by
      rw [hw1, hgen]
      exact (hW _).2 specializes_rfl
    exact e
  obtain ⟨_, ⟨u, rfl⟩, hu⟩ := Y.jQ_dense.exists_mem_open (TopologicalSpace.Opens.isOpen _) hne
  have hu' : genPt 𝔐.ξ₀ ⤳ Y.j u := (hW _).1 hu
  obtain ⟨Z⟩ := nonempty_cptOver_of_fraction hβ.1 hβ.2.2 Y (irreducibleComponent u)
    (irreducibleComponent_mem_irreducibleComponents u)
  have hz : genPt (Z.ξ₀ ≫ Y.j) ⤳ Y.j u := ((Z.closure u).1 mem_irreducibleComponent).map Y.j.continuous
  exact ⟨_, Z, ((genPt_specializes_of_specializes _ 𝔐.gen₀ hu' hz).antisymm
      (genPt_specializes_of_specializes _ Z.gen hz hu')).eq⟩

theorem isGeom_of_split (hS : SplitComps Y) {U : Set (Xo.XF c)} (Z : CptOver Y U) : Z.IsGeom := by
  rintro x ⟨f, hf, hx⟩
  letI : Algebra c.F Z.Ω := Z.inc.toAlgebra
  haveI : CharZero Z.Ω := charZero_of_injective_ringHom Z.inc.injective
  haveI : Algebra.IsAlgebraic ℤ c.F := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ)).2 inferInstance
  have h0 : IsAlgebraic c.F x := ⟨f, hf, hx⟩
  have h1 : IsAlgebraic ℤ x := h0.restrictScalars ℤ
  refine hS Z.Ω (Z.ξ₀ ≫ Y.j) Z.inc Z.gen ?_ x h1
  have e : spMap (Z.inc.comp (algebraMap (𝓞 c.F) c.F)) = spMap Z.inc ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [e, ← Z.over_inc, ← Y.jQ_over]
  simp only [Model.j, Category.assoc, pullback.condition]

theorem central (h0 : FlatLineGenerator) (h1 : FlatLineGeneratorComponent) (hS : SplitComps Y) (hpq : 1 ≤ D.p + D.q) (𝔐 : HodgeCpt Y S y)
    (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω)
    (hx : CMType H × Fin (D.p + D.q) → HermLine J) (hroot : Fl.RootLines xdeg e)
    (hhod : ∀ r, Fl.IsHodgeLine r (e r) (hx r)) (hdg : ∀ r, (hx r).a = xdeg r) (τ : CMType H) :
    ∃ (c₁ : Ω) (a : K → ℤ) (tt : (c.F →+* ℂ) → ℝ), ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w →
      ∀ cc : (k : K) → J k, (∀ k, w ⟨k, cc k⟩ ≠ 0) →
        (∃ u : ℂ, u ≠ 0 ∧ ValAt 𝔐.ξ z (c₁ / ((∏ k, y ⟨k, cc k⟩ ^ a k) * ∏ i, e (τ, i))) u) ∧
        (𝔐.Interior z → ∀ s : c.F →+* ℂ, (∀ x, ValAt 𝔐.ξ z (𝔐.cst x) (s x)) → ∀ u : ℂ,
          ValAt 𝔐.ξ z (c₁ / ((∏ k, y ⟨k, cc k⟩ ^ a k) * ∏ i, e (τ, i))) u →
          ‖u‖ * ∏ k, ‖w ⟨k, cc k⟩‖ ^ a k = Real.exp (tt s) * ∏ i, (hx (τ, i)).h w) := by
  have hβ := int_frac c.F
  obtain ⟨U, Z, hgp⟩ := exists_cptOver 𝔐
  have hgeom := isGeom_of_split hS Z
  obtain ⟨φ, hφ, hflat, -⟩ := h0 E H D l Xo c _ _ Y U Z τ.1 hβ hpq τ.2 hgeom
  obtain ⟨hinf, -⟩ := h1 E H D l Xo c _ _ Y U Z τ.1 φ hβ hpq τ.2 hgeom hφ hflat
  choose t hinf _ using hinf
  obtain ⟨-, a, b, hgen, hrep⟩ := id hflat
  obtain ⟨i, j, hT⟩ := GlobalTheory.T.hodge_component_matches_model_component E H D l Xo c Y U Z S Ω K J y 𝔐 hgp
  obtain ⟨a', b', d₁, d₂, h₁, h₂, ha0, hb0, ha', hb', ea, eb⟩ :=
    GlobalTheory.T.flag_cm_type_lattice_comparison E H D l Xo c Y U Z S Ω K J y 𝔐 Fl τ i j a b hT hgen
  have hdeg := GlobalTheory.T.hodge_cpt_flag_degree E H D l Xo c _ _ Y S Ω K J y 𝔐 Fl xdeg e τ hroot
  have he : ∏ i, e (τ, i) ≠ 0 := hdeg.1
  have hchar : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  have hfr : ∀ p ∈ genFibre ℤ 𝔐.ξ, IsCoeffAt (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) D.p D.q a' b' p 1 := by
    intro p hp
    obtain ⟨⟨x₀, hx₀, ex⟩, hs₁, hs₂⟩ := GlobalTheory.T.cm_type_lattice_comparison E H D l Xo c Y U Z S Ω K J y 𝔐 τ i j hT p hp
    obtain ⟨hv₁, hv₂, -, -⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c _ _ Y U Z τ.1 hβ τ.2
    obtain ⟨W₁, hW₁, u₁, -, hu₁⟩ := hv₁ x₀ hx₀
    obtain ⟨W₂, hW₂, u₂, -, hu₂⟩ := hv₂ x₀ hx₀
    exact GlobalTheory.T.exterior_coeff_base_change_compat _ _ _ _ _ _ 𝔐.f i _ _ j _ _ _ _ D.p D.q a b a' b' p x₀ u₁ u₂ Z.gen 𝔐.tie.gen hT.1 hT.2.2.1 ex
      (hu₁ x₀ hx₀ hW₁) (hu₂ x₀ hx₀ hW₂) hs₁ hs₂ (hgen.2.2 x₀ hx₀) ha' hb'
  have haF : exteriorPower.ιMulti Ω _ (Fl.b (.inl τ)) ≠ 0 := fun h => ha0 (by
    have e2 : d₁ • (exteriorPower.ιMulti Ω (labelRk D (.inl τ)) (Fl.b (.inl τ))) = 0 := by rw [h, smul_zero]
    exact ea.trans e2)
  have hbF : exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)) ≠ 0 := fun h => hb0 (by
    have e2 : d₂ • (exteriorPower.ιMulti Ω (labelRk D (.inr τ)) (Fl.b (.inr τ))) = 0 := by rw [h, smul_zero]
    exact eb.trans e2)
  have hVA : (𝔐.V (.inl τ)).IsVB (labelRk D (.inl τ)) _ := 𝔐.vb (.inl τ)
  have hVB : (𝔐.V (.inr τ)).IsVB (labelRk D (.inr τ)) _ := 𝔐.vb (.inr τ)
  have hco : ∀ p ∈ genFibre ℤ 𝔐.ξ, IsCoeffAt (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
      (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))) p (d₁ / d₂)⁻¹ :=
    fun p hp => isCoeffAt_of_smul h₁ h₂ ea eb (hfr p hp)
  have hd0 : d₁ / d₂ ≠ 0 := div_ne_zero h₁ h₂
  let A : HermLine J := PB.combLine (fun i => hx (τ, i)) fun _ => 1
  have hAa : A.a = ∑ i, xdeg (τ, i) := by
    funext k
    simp [A, PB.combLine_a, hdg, Finset.sum_apply]
  have hAh : ∀ w, A.h w = ∏ i, (hx (τ, i)).h w := fun w => by simp [A, PB.combLine_h]
  refine ⟨d₁ / d₂, A.a, t, fun z w hz cc hcc => ⟨?_, fun hint s hs u hu => ?_⟩⟩
  · have hc := 𝔐.all (centre z)
    have hp : (⟨centre z, hc⟩ : Cpt 𝔐.ξ) ∈ genFibre ℤ 𝔐.ξ := fun o ho => by
      have v1 := valAt_int (ξ := 𝔐.ξ) hc o
      have v2 := CxVal.inv v1 (by exact_mod_cast ho)
      obtain ⟨_, s1, e1, -⟩ := v1
      obtain ⟨_, s2, e2, -⟩ := v2
      exact ⟨by simpa using ho, ⟨s1, by simpa using e1⟩, ⟨s2, by simpa using e2⟩⟩
    obtain ⟨-, hL2, -⟩ := GlobalTheory.T.wedge_line_lattice_vector_bundle 𝔐.X Ω 𝔐.ξ 𝔐.Li (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) _ _ _ _ Set.univ
      (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))) hVA hVB haF hbF
      ⟨_, trivial, _, hco _ hp⟩
    have hgn := (hL2 _ trivial _).2 ⟨hd0, hco _ hp⟩
    have hch := (GlobalTheory.T.frame_domain_in_segre_chart 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie z w cc 1 hc hz
      ⟨hcc, 1, (GlobalTheory.T.valAt_iff_value_at 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie z w hc hz 1 1).1 (CxVal.one hc), one_ne_zero⟩).1
    have h3 := hdeg.2 _ trivial cc hch
    rw [hgn.2, smul_eq_mul, ← hAa] at h3
    refine exists_val_ne hc (unitAt_of_span_eq hd0 (mul_ne_zero ?_ he) h3)
    exact Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hz.2 k (cc k) (IsUnit.mk0 _ (hcc k))).1
  · rw [← hAh]
    refine GlobalTheory.T.flag_weighted_degree_section E H D l Xo c Y S Ω K J y 𝔐 Fl xdeg e hx A τ (t s) (d₁ / d₂) z w hroot hhod hAa
      (fun w'' _ => hAh w'') hz hint hd0 ?_ cc u hcc hu
    intro hc bp bq Γ Δ α κ u' h1 h2 h3 h4 h5 h6 h7 h8 h9
    refine GlobalTheory.T.cm_type_exterior_lattice_comparison E H D l Xo c Y U Z S Ω K J y 𝔐 τ i j a b a' b' φ s _ z hc bp bq Γ Δ (d₁ * α) (d₂ * κ) u' hT hφ
      hgen hrep (hinf _) ha' hb' hint hs h1 h2 h3 h4 h5 h6 ?_ ?_ ?_
    · rw [mul_smul]
      exact ea.trans (congrArg (d₁ • ·) h7)
    · rw [mul_smul]
      exact eb.trans (congrArg (d₂ • ·) h8)
    · rw [← div_mul_div_comm, ← mul_div_assoc]
      exact h9

end AnalyticReference.An
