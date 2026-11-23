import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineLatticeGenericSectionsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToGermTop
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ConstRatio

theorem ratio_mem {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {x : Cpt ξ}
    {W : Type} [AddCommGroup W] [Module Ω W] {e : W} {s t : Ω} (he : e ≠ 0) (hs : s ≠ 0)
    (hst : Submodule.span (regAt ξ x) {s • e} = Submodule.span (regAt ξ x) {t • e}) : t / s ∈ regAt ξ x := by
  have : t • e ∈ Submodule.span (regAt ξ x) {s • e} := hst ▸ Submodule.mem_span_singleton_self _
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp this
  have hr' : ((r : Ω) * s) • e = t • e := by rw [mul_smul]; exact hr
  have := smul_left_injective Ω he hr'
  rw [← this, mul_div_cancel_right₀ _ hs]; exact r.2

theorem exists_smul_eq {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {x : Cpt ξ}
    {W : Type} [AddCommGroup W] [Module Ω W] {a a' : W} {α α' : Ω} (hα' : α' ≠ 0)
    (h : Submodule.span (regAt ξ x) {α • a} = Submodule.span (regAt ξ x) {α' • a'}) : ∃ f : Ω, a' = f • a := by
  have : α' • a' ∈ Submodule.span (regAt ξ x) {α • a} := h ▸ Submodule.mem_span_singleton_self _
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp this
  have hr' : ((r : Ω) * α) • a = α' • a' := by rw [mul_smul]; exact hr
  refine ⟨α'⁻¹ * ((r : Ω) * α), ?_⟩
  rw [mul_smul, hr', smul_smul, inv_mul_cancel₀ hα', one_smul]

theorem unit_of_coeff {X : Scheme.{0}} {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {A B : Lat ξ V} {p q : ℕ} {a : ⋀[Ω]^p V} {b : ⋀[Ω]^q V} {s t : Ω}
    {x : Cpt ξ} (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0) (h : IsCoeffAt A B p q a b x 1)
    (h' : IsCoeffAt A B p q (s • a) (t • b) x 1) : unitAt ξ x (s / t) := by
  obtain ⟨α, β, hα, -, hA, hB, e⟩ := h
  obtain ⟨α', β', hα', -, hA', hB', e'⟩ := h'
  rw [_root_.one_mul] at e e'
  subst e e'
  rw [smul_smul] at hA' hB'
  have k1 := ratio_mem ha hα (hA.symm.trans hA')
  have k2 := ratio_mem ha (mul_ne_zero hα' hs) (hA'.symm.trans hA)
  have k3 := ratio_mem hb hα (hB.symm.trans hB')
  have k4 := ratio_mem hb (mul_ne_zero hα' ht) (hB'.symm.trans hB)
  refine ⟨div_ne_zero hs ht, ?_, ?_⟩
  · have := mul_mem k1 k4
    convert this using 1; field_simp
  · have := mul_mem k2 k3
    convert this using 1; field_simp

theorem exists_factors {X : Scheme.{0}} {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {A B : Lat ξ V} {p q : ℕ} {a a' : ⋀[Ω]^p V} {b b' : ⋀[Ω]^q V}
    {T : Set (Cpt ξ)} (hT : T.Nonempty) (h : IsLineGenOn A B p q a b T) (h' : IsLineGenOn A B p q a' b' T) :
    ∃ s t : Ω, s ≠ 0 ∧ t ≠ 0 ∧ a' = s • a ∧ b' = t • b ∧ ∀ x ∈ T, unitAt ξ x (s / t) := by
  obtain ⟨ha, hb, h⟩ := h
  obtain ⟨ha', hb', h'⟩ := h'
  obtain ⟨x₀, hx₀⟩ := hT
  obtain ⟨s, hs⟩ : ∃ s : Ω, a' = s • a := by
    obtain ⟨α, β, -, -, hA, -, -⟩ := h x₀ hx₀
    obtain ⟨α', β', hα', -, hA', -, -⟩ := h' x₀ hx₀
    exact exists_smul_eq hα' (hA.symm.trans hA')
  obtain ⟨t, ht⟩ : ∃ t : Ω, b' = t • b := by
    obtain ⟨α, β, -, -, -, hB, -⟩ := h x₀ hx₀
    obtain ⟨α', β', -, hβ', -, hB', -⟩ := h' x₀ hx₀
    exact exists_smul_eq hβ' (hB.symm.trans hB')
  have hs0 : s ≠ 0 := by rintro rfl; exact ha' (by rw [hs, zero_smul])
  have ht0 : t ≠ 0 := by rintro rfl; exact hb' (by rw [ht, zero_smul])
  refine ⟨s, t, hs0, ht0, hs, ht, fun x hx => ?_⟩
  have := h' x hx
  rw [hs, ht] at this
  exact unit_of_coeff ha hb hs0 ht0 (h x hx) this

theorem isProper_of_proj {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) :
    IsProper f := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  infer_instance

theorem const_ratio : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (a a' : ⋀[Z.Ω]^D.p Z.V) (b b' : ⋀[Z.Ω]^D.q Z.V), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → Z.IsGeom → IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a b Z.genFib → IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a' b' Z.genFib → ∃ (x : c.F) (s t : Z.Ω), x ≠ 0 ∧ t ≠ 0 ∧ s = Z.inc x * t ∧ a' = s • a ∧ b' = t • b := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ a a' b b' ⟨hβ, hN, hfrac⟩ hG h h'
  haveI : IsDomain O := hβ.isDomain β
  letI : Algebra O Z.Ω := (Z.inc.comp β).toAlgebra
  have halg : ∀ o : O, algebraMap O Z.Ω o = Z.inc (β o) := fun _ => rfl
  have hover : (Z.ξ₀ ≫ Y.j) ≫ Y.s = Spec.map (CommRingCat.ofHom (algebraMap O Z.Ω)) := by
    have e : (Z.ξ₀ ≫ Y.j) ≫ Y.s = spMap Z.inc ≫ spMap β := by
      rw [Model.j, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over,
        ← Category.assoc, Z.over_inc]
    rw [e, spMap, spMap, ← Spec.map_comp]
    rfl
  have hinj : Function.Injective (algebraMap O Z.Ω) := Z.inc.injective.comp hβ
  have hcc : ConstClosed O Z.Ω := by
    rintro w ⟨f, hf0, hf⟩
    obtain ⟨x, rfl⟩ := hG w ⟨f.map β, (Polynomial.map_ne_zero_iff hβ).2 hf0, by
      rw [Polynomial.eval₂_map]; exact hf⟩
    obtain ⟨u, v, hv, e⟩ := hfrac x
    refine ⟨u, v, fun h0 => hv (by rw [h0, map_zero]), ?_⟩
    rw [halg, halg, ← map_mul, e]
  have hsub : genFibre O (Z.ξ₀ ≫ Y.j) ⊆ Z.genFib := by
    intro p hp
    have hbot : (Y.s p.1).asIdeal = ⊥ := by
      refine (Submodule.eq_bot_iff _).2 fun o ho => ?_
      by_contra h0
      exact ((ConstReg.regular_const _ _ _ O Y.s hover p o).2 Z.gen).1 (hp o h0) ho
    obtain ⟨w⟩ : Nonempty (Sp c.F) := inferInstance
    have e : Y.s p.1 = spMap β w := by
      refine PrimeSpectrum.ext ?_
      rw [hbot]
      refine ((Submodule.eq_bot_iff _).2 fun o ho => ?_).symm
      have h1 : β o ∈ w.asIdeal := ho
      by_contra h0
      have h2 : β o ≠ 0 := fun e0 => h0 (hβ (by rw [e0, map_zero]))
      exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (isUnit_iff_ne_zero.2 h2))
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ e
    exact ⟨z, hz⟩
  have hne : Z.genFib.Nonempty := ⟨⟨genPt (Z.ξ₀ ≫ Y.j), specializes_rfl⟩, ⟨Y.jQ (genPt Z.ξ₀), rfl⟩⟩
  obtain ⟨s, t, hs, ht, rfl, rfl, hu⟩ := exists_factors hne h h'
  haveI : IsProper Y.s := isProper_of_proj Y.proj
  let L : Lat (Z.ξ₀ ≫ Y.j) Z.Ω := fun p => Submodule.span (regAt (Z.ξ₀ ≫ Y.j) p) {1}
  obtain ⟨x', y', hy', e⟩ := (GlobalTheory.T.line_lattice_generic_sections Y.X Z.Ω (Z.ξ₀ ≫ Y.j) O Y.s hover hinj Z.gen hcc L 1
    (fun p _ => ⟨one_ne_zero, rfl⟩) (s / t)).1 (fun p hp =>
      Submodule.mem_span_singleton.2 ⟨⟨s / t, (hu p (hsub hp)).2.1⟩, by
        show (s / t) * 1 = _
        rw [_root_.mul_one]⟩)
  have hy : β y' ≠ 0 := fun h0 => hy' (hβ (by rw [h0, map_zero]))
  rw [_root_.mul_one, halg, halg] at e
  have hx' : β x' ≠ 0 := by
    intro h0
    rw [h0, map_zero] at e
    exact (mul_ne_zero (div_ne_zero hs ht) (by simpa using hy)) e
  refine ⟨β x' / β y', s, t, div_ne_zero hx' hy, ht, ?_, rfl, rfl⟩
  have hyΩ : Z.inc (β y') ≠ 0 := by simpa using hy
  rw [map_div₀, ← e]
  field_simp

end GlobalTheory.CompanionTheory.Ar.Flat.ConstRatio
