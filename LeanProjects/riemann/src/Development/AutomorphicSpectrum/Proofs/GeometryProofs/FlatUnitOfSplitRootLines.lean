import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsVerticalBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsClopenIrreducibleCptStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointFactorsOpenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentGenericIsGenericPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentMatchesModelComponentStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeLatticeComparisonStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagCmTypeLatticeComparison
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExteriorCoeffBaseChangeCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFlagDegreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLineLatticeVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalization
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsProject
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenOnFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrder

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht.FlatGen

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Ht.JoinFacts
open GroundTheory.Heights₂.Heights.HilbertSamuel.GenOnFibres (homog_cmon aeval_cmon)

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω L : Type} [Field Ω] [Field L]
  {y : (Σ k, ι k) → Ω} {w : (Σ k, ι k) → L}

theorem isVal_inv (hw : w ∈ ptsOver L (mCoordIdeal y)) {a : Ω} {v : L} (hv : v ≠ 0) (h : IsVal y w a v) :
    IsVal y w a⁻¹ v⁻¹ := by
  obtain ⟨d, g, h', hg, hh, hn, hy, hv'⟩ := h
  have hgw : aeval w g ≠ 0 := by rw [hv']; exact mul_ne_zero hv hn
  have hgy := aeval_ne_zero_of hw hg hgw
  have ha : a ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hy
    exact hgy hy
  have hhy : aeval y h' ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hy
    exact hgy hy
  refine ⟨d, h', g, hh, hg, hgw, ?_, ?_⟩
  · rw [hy]; field_simp
  · rw [hv']; field_simp

theorem prod_toNat {F : Type} [Field F] (x : K → F) (hx : ∀ k, x k ≠ 0) (a : K → ℤ) :
    ∏ k, x k ^ (a k).toNat = (∏ k, x k ^ a k) * ∏ k, x k ^ (-a k).toNat := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hx k)]
  congr 1
  omega

theorem hasVal_of_isVal {c : ∀ k, ι k} (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (hz : ∀ k, w ⟨k, c k⟩ ≠ 0) (a : K → ℤ) {t : Ω} {v : L}
    (h : IsVal y w t v) : HasVal y a (t * ∏ k, y ⟨k, c k⟩ ^ a k) w (v * ∏ k, w ⟨k, c k⟩ ^ a k) := by
  obtain ⟨d, g, h', hg, hh, hn, e₁, e₂⟩ := h
  have hy₁ := prod_toNat (fun k => y ⟨k, c k⟩) hy a
  have hz₁ := prod_toNat (fun k => w ⟨k, c k⟩) hz a
  have hz₂ : ∏ k, w ⟨k, c k⟩ ^ (-a k).toNat ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hz k)
  refine ⟨d + fun k => (a k).toNat, d + fun k => (-a k).toNat,
    g * GroundTheory.Heights₂.Heights.HilbertSamuel.GenOnFibres.cmon c fun k => (a k).toNat,
    h' * GroundTheory.Heights₂.Heights.HilbertSamuel.GenOnFibres.cmon c fun k => (-a k).toNat,
    GlobalTheory.CompanionTheory.Ar.LocVal.homog_mul hg (homog_cmon c _), GlobalTheory.CompanionTheory.Ar.LocVal.homog_mul hh (homog_cmon c _),
    fun k => ?_, ?_, ?_, ?_⟩
  · simp only [Pi.add_apply, Nat.cast_add]
    omega
  · rw [map_mul, map_mul, aeval_cmon, aeval_cmon, e₁, hy₁]
    ring
  · rw [map_mul, aeval_cmon]
    exact mul_ne_zero hn hz₂
  · rw [map_mul, map_mul, aeval_cmon, aeval_cmon, e₂, hz₁]
    ring

end Values

section Point

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K]
  {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem unitAt_div_of_span {p : Cpt ξ} {g m : Ω} (hg : g ≠ 0) (hm : m ≠ 0)
    (h : Submodule.span (regAt ξ p) {g} = Submodule.span (regAt ξ p) {m}) : unitAt ξ p (g / m) := by
  have h₁ : g ∈ Submodule.span (regAt ξ p) {m} := h ▸ Submodule.mem_span_singleton_self g
  have h₂ : m ∈ Submodule.span (regAt ξ p) {g} := h ▸ Submodule.mem_span_singleton_self m
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 h₁
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 h₂
  have e₁ : (r : Ω) * m = g := hr
  have e₂ : (s : Ω) * g = m := hs
  refine ⟨div_ne_zero hg hm, ?_, ?_⟩
  · rw [← e₁, mul_div_cancel_right₀ _ hm]
    exact r.2
  · rw [inv_div, ← e₂, mul_div_cancel_right₀ _ hg]
    exact s.2

theorem isCoeffAt_of_smul {V : Type} [AddCommGroup V] [Module Ω V] {A B : Lat ξ V} {p q : ℕ} {a a' : ⋀[Ω]^p V}
    {b b' : ⋀[Ω]^q V} {x : Cpt ξ} {d₁ d₂ : Ω} (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) (ea : a' = d₁ • a) (eb : b' = d₂ • b)
    (h : IsCoeffAt A B p q a' b' x 1) : IsCoeffAt A B p q a b x (d₁ / d₂)⁻¹ := by
  obtain ⟨α, β, hα, hβ, hA, hB, e⟩ := h
  rw [one_mul] at e
  subst e
  refine ⟨α * d₁, α * d₂, mul_ne_zero hα h₁, mul_ne_zero hα h₂, ?_, ?_, ?_⟩
  · rw [hA, ea, smul_smul]
  · rw [hB, eb, smul_smul]
  · field_simp

theorem genUnit_of_gen (ht : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) {Λ : Lat ξ Ω} {a : K → ℤ} {e₀ g : Ω}
    (hdeg : Λ.IsDegOn Set.univ y a e₀) (hg : ∀ p ∈ genFibre ℤ ξ, Λ.IsGenAt p g) : GenUnit y a (g / e₀) := by
  classical
  intro L _ _ z hz
  choose c hc using hz.1
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => coord_ne_zero hz (hc k)
  have hxc : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hyc k
  let x : ((k : K) → J k) → Ω := fun c' => ∏ k, y ⟨k, c' k⟩
  let A := Algebra.adjoin ℤ (Set.range fun j => x j / x c)
  have hA : ∀ s ∈ A, s ∈ locRing y z := by
    intro s hs
    induction hs using Algebra.adjoin_induction with
    | mem s hs =>
      obtain ⟨j, rfl⟩ := hs
      have e : x j / x c = ∏ k, y ⟨k, j k⟩ / y ⟨k, c k⟩ := by
        simp only [x, Finset.prod_div_distrib]
      show x j / x c ∈ locRing y z
      rw [e]
      exact Subring.prod_mem _ fun k _ => ⟨_, isVal_ratio hz k (c k) (j k) (hc k)⟩
    | algebraMap r => exact intCast_mem _ r
    | add s t _ _ h₁ h₂ => exact add_mem h₁ h₂
    | mul s t _ _ h₁ h₂ => exact mul_mem h₁ h₂
  let incl : A →+* locRing y z := (A.val.toRingHom).codRestrict (locRing y z) fun s => hA s s.2
  let ev : A →+* L := (locHom hz).comp incl
  have hev : ∀ s : A, IsVal y z (s : Ω) (ev s) := fun s => isVal_locVal (incl s)
  obtain ⟨p, ⟨hpc, hp⟩, -⟩ := GlobalTheory.CompanionTheory.Ar.chart_point_of_prime X Ω ξ ℤ _ x ht c hxc (RingHom.ker ev)
    (RingHom.ker_isPrime ev)
  have hgf : p ∈ genFibre ℤ ξ := by
    intro o ho
    refine (hp (algebraMap ℤ A o)).1 ?_
    rw [RingHom.mem_ker, eq_intCast, map_intCast]
    exact_mod_cast ho
  obtain ⟨hg0, hgs⟩ := hg p hgf
  have hd := hdeg.2 p trivial c hpc
  have hM : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyc k)
  have hu : unitAt ξ p (g / ((∏ k, y ⟨k, c k⟩ ^ a k) * e₀)) :=
    unitAt_div_of_span hg0 (mul_ne_zero hM hdeg.1) (by rw [← hgs, hd, smul_eq_mul])
  have hval : ∀ t ∈ regAt ξ p, ∃ v, IsVal y z t v := by
    intro t ht'
    obtain ⟨s, hsA, hsu, hst⟩ := (GlobalTheory.CompanionTheory.Ar.regAt_iff_exists_chart_fraction X Ω ξ ℤ _ x ht c p hpc t).1 ht'
    have hs0 : ev ⟨s, hsA⟩ ≠ 0 := fun h => (hp ⟨s, hsA⟩).2 hsu (RingHom.mem_ker.2 h)
    have h₂ := (isVal_inv hz hs0 (hev ⟨s, hsA⟩)).mul (hev ⟨s * t, hst⟩)
    have e : (((⟨s, hsA⟩ : A) : Ω))⁻¹ * (((⟨s * t, hst⟩ : A) : Ω)) = t := inv_mul_cancel_left₀ hsu.1 t
    rw [e] at h₂
    exact ⟨_, h₂⟩
  obtain ⟨v, hv⟩ := hval _ hu.2.1
  obtain ⟨v', hv'⟩ := hval _ hu.2.2
  have hvv : v * v' = 1 := by
    have h₁ := hv.mul hv'
    rw [mul_inv_cancel₀ hu.1] at h₁
    exact h₁.unique hz isVal_one
  have hv0 : v ≠ 0 := left_ne_zero_of_mul_eq_one hvv
  refine ⟨v * ∏ k, z ⟨k, c k⟩ ^ a k, mul_ne_zero hv0 (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)), ?_⟩
  have e : g / e₀ = g / ((∏ k, y ⟨k, c k⟩ ^ a k) * e₀) * ∏ k, y ⟨k, c k⟩ ^ a k := by
    have := hdeg.1
    field_simp
  rw [e]
  exact hasVal_of_isVal hyc hc a hv

end Point

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem exists_cptOver [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) ∧ IsNoetherianRing (𝓞 c.F) ∧
      ∀ x : c.F, ∃ a b : 𝓞 c.F, algebraMap (𝓞 c.F) c.F b ≠ 0 ∧ x * algebraMap (𝓞 c.F) c.F b = algebraMap (𝓞 c.F) c.F a)
    {Ω₀ : Type} [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (hg : IsCptGen ξ₀) :
    ∃ (U : Set (Xo.XF c)) (Z : CptOver Y U), genPt ξ₀ = genPt (Z.ξ₀ ≫ Y.j) := by
  have hgen := GlobalTheory.CompanionTheory.Ar.GenPtModel.genPt_mem_genericPoints E H D l Xo c Y Ω₀ ξ₀ hg
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.generic_point_factors_open E H D l Xo c Y Ω₀ ξ₀ hgen
  obtain ⟨U, Z, hu, -, -⟩ := GlobalTheory.T.exists_clopen_irreducible_cpt E H D l Xo c _ _ Y (genPt y₀) hβ
  refine ⟨U, Z, ?_⟩
  have h₁ : genPt Z.ξ₀ ⤳ genPt y₀ := (Z.closure _).1 hu
  have h₂ : genPt (Z.ξ₀ ≫ Y.j) ⤳ genPt ξ₀ := by
    rw [hy₀]
    exact h₁.map Y.j.continuous
  have hmax : Maximal IsIrreducible (closure {genPt ξ₀}) := hgen
  have hsub := specializes_iff_closure_subset.1 h₂
  have hle := hmax.le_of_ge isIrreducible_singleton.closure hsub
  exact (inseparable_iff_closure_eq.2 (hsub.antisymm hle)).eq

theorem isGeom_of_splitComps [NumberField c.F] {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} (hs : SplitComps Y)
    {U : Set (Xo.XF c)} (Z : CptOver Y U) : Z.IsGeom := by
  rintro x ⟨f, hf, hfx⟩
  have hover : (Z.ξ₀ ≫ Y.j) ≫ Y.s = spMap (Z.inc.comp (algebraMap (𝓞 c.F) c.F)) := by
    simp only [Model.j, Category.assoc]
    rw [pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, Z.over_inc]
    simp [spMap, ← Spec.map_comp]
  letI : Algebra c.F Z.Ω := Z.inc.toAlgebra
  have hx : IsAlgebraic c.F x := ⟨f, hf, by rw [Polynomial.aeval_def]; exact hfx⟩
  haveI : Algebra.IsAlgebraic ℤ c.F := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := c.F)).2 inferInstance
  have hz : IsAlgebraic ℤ x := hx.restrictScalars ℤ
  obtain ⟨a, ha⟩ := hs Z.Ω (Z.ξ₀ ≫ Y.j) Z.inc Z.gen hover x hz
  exact ⟨a, ha⟩

theorem flat_unit_of_root_lines : Flat.FlatLineGenerator → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (R : Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S R.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → R.Ω), 1 ≤ D.p + D.q → SplitComps Y → Fl.RootLines R.xdeg e → Ht.FlatUnit R := by
  intro hA0 E _ _ _ H D l Xo c Y S R 𝔐 Fl e hpq hs hroot τ
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) ∧ IsNoetherianRing (𝓞 c.F) ∧
      ∀ x : c.F, ∃ a b : 𝓞 c.F, algebraMap (𝓞 c.F) c.F b ≠ 0 ∧ x * algebraMap (𝓞 c.F) c.F b = algebraMap (𝓞 c.F) c.F a := by
    refine ⟨RingOfIntegers.coe_injective, inferInstance, fun x => ?_⟩
    obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (A := 𝓞 c.F) x
    exact ⟨a, b, (map_ne_zero_iff _ RingOfIntegers.coe_injective).2 (nonZeroDivisors.ne_zero hb), by
      rw [← e, div_mul_cancel₀ _ ((map_ne_zero_iff _ RingOfIntegers.coe_injective).2 (nonZeroDivisors.ne_zero hb))]⟩
  obtain ⟨U, Z, hgp⟩ := exists_cptOver Y hβ 𝔐.ξ₀ 𝔐.gen₀
  obtain ⟨φ, -, ⟨-, a, b, hgen, -⟩, -⟩ := hA0 E H D l Xo c _ _ Y U Z τ.1 hβ hpq τ.2 (isGeom_of_splitComps hs Z)
  obtain ⟨i, j, hT⟩ := GlobalTheory.T.hodge_component_matches_model_component E H D l Xo c Y U Z S R.Ω R.K R.ι R.y 𝔐 hgp
  obtain ⟨a', b', d₁, d₂, h₁, h₂, ha0, hb0, ha', hb', ea, eb⟩ :=
    GlobalTheory.CompanionTheory.Ar.Flat.CptWedge.exists_pullWedge_flag E H D l Xo c Y U Z S R.Ω R.K R.ι R.y 𝔐 Fl τ i j a b hT hgen
  have hdeg := GlobalTheory.T.hodge_cpt_flag_degree E H D l Xo c _ _ Y S R.Ω R.K R.ι R.y 𝔐 Fl R.xdeg e τ hroot
  have hfr : ∀ p ∈ genFibre ℤ 𝔐.ξ, IsCoeffAt (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) D.p D.q a' b' p 1 := by
    intro p hp
    obtain ⟨⟨x₀, hx₀, ex⟩, hs₁, hs₂⟩ := GlobalTheory.T.cm_type_lattice_comparison E H D l Xo c Y U Z S R.Ω R.K R.ι R.y 𝔐 τ i j hT p hp
    obtain ⟨hv₁, hv₂, -, -⟩ := GlobalTheory.CompanionTheory.Ar.Flat.isVBOn_eig_genFib E H D l Xo c _ _ Y U Z τ.1 hβ τ.2
    obtain ⟨W₁, hW₁, u₁, -, hu₁⟩ := hv₁ x₀ hx₀
    obtain ⟨W₂, hW₂, u₂, -, hu₂⟩ := hv₂ x₀ hx₀
    exact GlobalTheory.CompanionTheory.Ar.Flat.LinePull.isCoeffAt_pull _ _ _ _ _ _ 𝔐.f i _ _ j _ _ _ _ D.p D.q a b a' b' p x₀ u₁ u₂ Z.gen
      𝔐.tie.gen hT.1 hT.2.2.1 ex (hu₁ x₀ hx₀ hW₁) (hu₂ x₀ hx₀ hW₂) hs₁ hs₂ (hgen.2.2 x₀ hx₀) ha' hb'
  haveI hchar : CharZero R.Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  let x₀ : Cpt 𝔐.ξ := ⟨genPt 𝔐.ξ, specializes_rfl⟩
  have hx₀ : x₀ ∈ genFibre ℤ 𝔐.ξ := fun o ho =>
    ⟨by simpa using ho, CoordBase.mem_regAt_gen 𝔐.tie.gen _, CoordBase.mem_regAt_gen 𝔐.tie.gen _⟩
  have haF : exteriorPower.ιMulti R.Ω _ (Fl.b (.inl τ)) ≠ 0 := fun h => ha0 (by
    have e2 : d₁ • (exteriorPower.ιMulti R.Ω (labelRk D (.inl τ)) (Fl.b (.inl τ))) = 0 := by rw [h, smul_zero]
    exact ea.trans e2)
  have hbF : exteriorPower.ιMulti R.Ω _ (Fl.b (.inr τ)) ≠ 0 := fun h => hb0 (by
    have e2 : d₂ • (exteriorPower.ιMulti R.Ω (labelRk D (.inr τ)) (Fl.b (.inr τ))) = 0 := by rw [h, smul_zero]
    exact eb.trans e2)
  have hVA : (𝔐.V (.inl τ)).IsVB (labelRk D (.inl τ)) _ := 𝔐.vb (.inl τ)
  have hVB : (𝔐.V (.inr τ)).IsVB (labelRk D (.inr τ)) _ := 𝔐.vb (.inr τ)
  have hco : ∀ p ∈ genFibre ℤ 𝔐.ξ, IsCoeffAt (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
      (exteriorPower.ιMulti R.Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti R.Ω _ (Fl.b (.inr τ))) p (d₁ / d₂)⁻¹ :=
    fun p hp => isCoeffAt_of_smul h₁ h₂ ea eb (hfr p hp)
  obtain ⟨-, hL2, -⟩ := GlobalTheory.T.wedge_line_lattice_vector_bundle 𝔐.X R.Ω 𝔐.ξ 𝔐.Li (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) _ _ _ _ Set.univ
    (exteriorPower.ιMulti R.Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti R.Ω _ (Fl.b (.inr τ))) hVA hVB haF hbF
    ⟨x₀, trivial, _, hco x₀ hx₀⟩
  have hd0 : d₁ / d₂ ≠ 0 := div_ne_zero h₁ h₂
  have hu := genUnit_of_gen 𝔐.tie hdeg fun p hp => (hL2 p trivial _).2 ⟨hd0, hco p hp⟩
  obtain ⟨c', hc'⟩ := GlobalTheory.T.exists_vertical_bound R.K R.ι R.Ω R.y _ R.arith R.birational _ _ hu
  have ha : (fun b => (((1 : ℕ) : ℤ)) * ∑ i, R.xdeg (τ, i) b) = ∑ i, R.xdeg (τ, i) := by
    funext b
    simp [Finset.sum_apply]
  refine ⟨1, d₁ / d₂ / ∏ i, e (τ, i), c', one_pos, ?_, ?_⟩
  · rw [ha]; exact hu
  · rw [ha]; exact hc'

end Main

end GlobalTheory.CompanionTheory.Ar.Ht.FlatGen
