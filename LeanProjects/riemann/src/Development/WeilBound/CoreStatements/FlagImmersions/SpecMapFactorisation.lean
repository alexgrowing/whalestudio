import Development.WeilBound.CoreStatements.FlagImmersions.FibSandwich
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfParts
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfResolutionGagaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatZeroFromResolutionAndGagaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatFirstFromResolutionAndGagaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KroneckerCharacterPeriodFormulaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatGenFrameComplexCompatStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_inj {R S : Type} [CommRing R] [CommRing S] {f g : R →+* S} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem spec_map_factorisation {X : Scheme.{0}} {A A' B B' : CommRingCat.{0}} (u : A ⟶ B) [IsIso u] (r : A ⟶ A') (v : A' ⟶ B')
    (a : Spec A ⟶ X) (a' : Spec A' ⟶ X) (x : Spec B ⟶ X) (x' : Spec B' ⟶ X) (e : Spec.map u ≫ a = x)
    (e' : Spec.map v ≫ a' = x') (e₂ : Spec.map r ≫ a = a') : Spec.map (inv u ≫ r ≫ v) ≫ x = x' := by
  subst e e' e₂
  rw [← Category.assoc (Spec.map _), ← Spec.map_comp, IsIso.hom_inv_id_assoc, Spec.map_comp, Category.assoc]

theorem exists_factor {X : Scheme.{0}} {Ω₀ Ω₁ : Type} [Field Ω₀] [Field Ω₁] {ξ₀ : Sp Ω₀ ⟶ X} (ξ₁ : Sp Ω₁ ⟶ X)
    (h₀ : IsCptGen ξ₀) (h : genPt ξ₁ ⤳ genPt ξ₀) : ∃ i : Ω₀ →+* Ω₁, spMap i ≫ ξ₀ = ξ₁ := by
  haveI : IsIso (Scheme.stalkClosedPointTo ξ₀) := (ConcreteCategory.isIso_iff_bijective _).2 h₀.bij
  refine ⟨(inv (Scheme.stalkClosedPointTo ξ₀) ≫ X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo ξ₁).hom, ?_⟩
  exact spec_map_factorisation (Scheme.stalkClosedPointTo ξ₀) (X.presheaf.stalkSpecializes h) (Scheme.stalkClosedPointTo ξ₁) _ _ ξ₀ ξ₁
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₀) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₁)
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) h)

theorem genPt_spMap {X : Scheme.{0}} {Ω₀ Ω₁ : Type} [Field Ω₀] [Field Ω₁] (i : Ω₀ →+* Ω₁) (ξ : Sp Ω₀ ⟶ X) :
    genPt (spMap i ≫ ξ) = genPt ξ :=
  congrArg (fun x => ξ x) (Subsingleton.elim (α := PrimeSpectrum Ω₀) _ _)

theorem int_frac (F : Type) [Field F] [NumberField F] : Function.Injective (algebraMap (𝓞 F) F) ∧ IsNoetherianRing (𝓞 F) ∧
    ∀ x : F, ∃ a b : 𝓞 F, algebraMap (𝓞 F) F b ≠ 0 ∧ x * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a := by
  refine ⟨IsFractionRing.injective _ _, inferInstance, fun x => ?_⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have : algebraMap (𝓞 F) F b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  exact ⟨a, b, this, div_mul_cancel₀ _ this⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem isGeom_of {l : Level H} {Xo : Moduli D l} {c : Coeff l} [NumberField c.F]
    {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {M : Top.RootModel (CMType H) (D.p + D.q)}
    {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y Sys}
    (o : RootOrigin Y S M Fx) {U : Set (Xo.XF c)} (Z : CptOver Y U)
    (h : genPt o.𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j)) : Z.IsGeom := by
  have e1 : genPt Fx.ξf = genPt (Z.ξ₀ ≫ Y.j) := by
    rw [← h, ← genPt_spMap o.g Fx.ξf, ← o.g_over, ← genPt_spMap o.𝔐.fn o.𝔐.ξ₀]
    exact congrArg genPt o.𝔐.fn_over
  obtain ⟨i, hi⟩ := exists_factor Fx.ξf Z.gen (e1 ▸ specializes_rfl)
  have hb : (o.g.comp i).comp Z.inc = o.𝔐.cst := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) (spMap_inj ?_)
    rw [← o.𝔐.cst_over, ← Category.assoc, o.g_over, ← hi, spMap_comp', spMap_comp', spMap_comp', ← Z.over_inc,
      ← Y.jQ_over]
    simp only [Model.j, Category.assoc, pullback.condition]
  rintro x ⟨f, hf, hx⟩
  letI : Algebra c.F Z.Ω := Z.inc.toAlgebra
  haveI : CharZero Z.Ω := charZero_of_injective_ringHom Z.inc.injective
  haveI : Algebra.IsAlgebraic ℤ c.F := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ)).2 inferInstance
  have h0 : IsAlgebraic c.F x := ⟨f, hf, hx⟩
  have h1 : IsAlgebraic ℤ x := h0.restrictScalars ℤ
  obtain ⟨b, hb'⟩ := o.g_const (i x) (h1.algHom i.toIntAlgHom)
  refine ⟨b, (o.g.comp i).injective ?_⟩
  rw [← hb] at hb'
  exact hb'

theorem exists_norms (hG : Top.Given) (hFD : FlatDegree) (hP : PeriodOf) (hχ : ChiEx) (Xo : ∀ l : Level H, Moduli D l)
    (l : Level H) (c : Coeff l) [NumberField c.F] (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
    (U : Set ((Xo l).XF c)) (Z : CptOver Y U) (τ : CMType H) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (hp : 1 ≤ D.p)
    (hq : 1 ≤ D.q) (hU : IsClopen U) (hUi : IsIrreducible U) (hZ : Z.IsGeom) :
    ∃ (φ : FrameFn (Xo l) c) (N : LogNorms c.F), FlatOnModel Z τ.1 φ ∧ (∀ s, HasInfNorm U τ.1 φ s (N.inf s)) ∧
      (∀ s, N.inf (ComplexEmbedding.conjugate s) = N.inf s) ∧ (∀ p κ, HasFinNorm U τ.1 φ p κ (N.fin p κ)) ∧
      N.IsAdelic ∧ N.deg = ((D.p : ℝ) - D.q) / 2 *
        (Real.eulerMascheroniConstant + Real.log (2 * Real.pi) - Real.log (hostRd E) - hostLval H) := by
  obtain ⟨g, ty, FU, i, hty, hper⟩ := hP hG E H D l (Xo l) c Y U Z hp hq hU hUi hZ
  obtain ⟨⟨hI, -⟩, -, -, -, hRes, -, -, hGa, -⟩ := hG
  have hpq : 1 ≤ D.p + D.q := by omega
  obtain ⟨φ, hl, hf, -⟩ := GlobalTheory.T.flat_zero_from_resolution_and_gaga hRes hGa E H D l (Xo l) c _ _ Y U Z τ.1 (int_frac c.F) hpq τ.2 hZ
  obtain ⟨hinf, hfg⟩ := GlobalTheory.T.flat_first_from_resolution_and_gaga hRes hGa E H D l (Xo l) c _ _ Y U Z τ.1 φ (int_frac c.F) hpq τ.2 hZ hl hf
  have hφ : IsFlatGen U τ.1 φ FU i := hfg g ty FU i hty fun P y hPer hu hy => (hper y hy).2 ⟨P, hPer, hu⟩
  obtain ⟨φ', N', hφ', hN', -⟩ := GlobalTheory.T.flat_theorem_of_resolution_gaga hRes hGa hI E H D Xo l c U τ.1 g ty FU i hpq τ.2 hg hty hU hUi hper
  obtain ⟨a, ha, he⟩ := GlobalTheory.T.flat_gen_frame_complex_compat E H D l (Xo l) c U τ.1 φ' φ g ty FU i hty hφ' hφ fun y hy hr => (hper y hy).1 hr
  have hfin : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm U τ.1 φ p κ t := fun p κ =>
    ⟨_, TopA.hasFinNorm_of_eq hl ha he (hN'.2 p κ)⟩
  choose t ht ht' using hinf
  choose tf htf using hfin
  let N : LogNorms c.F := ⟨fun s => t (InfinitePlace.mk s).embedding, tf⟩
  have hN : ∀ s, HasInfNorm U τ.1 φ s (N.inf s) := fun s => by
    show HasInfNorm U τ.1 φ s (t (InfinitePlace.mk s).embedding)
    rcases InfinitePlace.embedding_mk_eq s with h | h
    · rw [h]; exact ht s
    · rw [h]
      have e : (starRingEnd ℂ).comp (ComplexEmbedding.conjugate s) = s := by
        ext x; simp [ComplexEmbedding.conjugate_coe_eq]
      have := ht' (ComplexEmbedding.conjugate s)
      rwa [e] at this
  haveI : NeZero H.d := ⟨H.d_prime.ne_zero⟩
  obtain ⟨χ, hχ1, hχ2⟩ := hχ E H
  obtain ⟨h1, h2⟩ := GlobalTheory.T.kronecker_character_period_formula hFD E H D l (Xo l) c g ty FU i U τ.1 φ N χ hχ1 hty τ.2 hφ hN htf
  refine ⟨φ, N, hf, hN, fun s => ?_, htf, h1, by rw [h2, hχ2]⟩
  show t _ = t _
  rw [InfinitePlace.mk_conjugate_eq]

end RootFieldNumerics.RF
