import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Flat

def CptFlatInputs : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c))
    (Z : CptOver Y U) (φ : FrameFn Xo c) (τ : CMType H) (t : (c.F →+* ℂ) → ℝ) (S : Finset ℕ)
    (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ)
    (e : CMType H × Fin (D.p + D.q) → Ω) (hx : CMType H × Fin (D.p + D.q) → HermLine J) (A : HermLine J) (n : ℕ)
    (F' : Type) [Field F'] [NumberField F'] (ι : c.F →+* F') (ψ : F' →+* Ω),
    Z.IsGeom → FlatOnModel Z τ.1 φ → (∀ s, HasInfNorm U τ.1 φ s (t s)) →
    genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j) →
    ψ.comp ι = 𝔐.cst → (∀ x : Ω, (∃ f : Polynomial F', f ≠ 0 ∧ f.eval₂ ψ x = 0) → x ∈ Set.range ψ) →
    Birational y → IsArithVar (mCoordIdeal y) n →
    Fl.RootLines xdeg e → (∀ r, Fl.IsHodgeLine r (e r) (hx r)) →
    IsSmoothHerm A → IsConjInvariantH A → A.a = ∑ i, xdeg (τ, i) →
    (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → 𝔐.Interior z →
      A.h w = ∏ i, (hx (τ, i)).h w) →
    (∀ p ∈ S, ExactModLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (p : Ω) (D.p + D.q)) →
    (∀ p : ℕ, p.Prime → p ∉ S →
      NumTrivMod (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
        (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))) (p : Ω)) →
    ∃ (c₀ : Ω) (r : HeightOneSpectrum (𝓞 F') →₀ ℚ) (cinf : (F' →+* ℂ) → ℝ), c₀ ≠ 0 ∧
      (∀ σ, cinf σ = Real.exp (t (σ.comp ι))) ∧
      (∀ p ∈ genFibre ℤ 𝔐.ξ, (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
        (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))).IsGenAt p
          (c₀ * ∏ i, e (τ, i))) ∧
      (∀ (v : HeightOneSpectrum (𝓞 F')) (π : F'), v.valuation F' π = WithZero.exp (-1 : ℤ) →
        ∃ (m : ℕ) (k : ℤ), 0 < m ∧ (k : ℚ) = m * r v ∧ ∀ p : Cpt 𝔐.ξ,
          (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt 𝔐.ξ p) →
          OrderAt (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
        (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))))
            (c₀ * ∏ i, e (τ, i)) (ψ π) m k p) ∧
      (∀ σ, 0 < cinf σ) ∧
      ∀ (σ : F' →+* ℂ) z (g h : MRing J) (dg dh : K → ℕ), PtOver y ψ σ z → IsMultiHomog g dg →
        IsMultiHomog h dh → (∀ k, (dg k : ℤ) - dh k = A.a k) → aeval y g = c₀ * aeval y h →
          ‖evC z g‖ = cinf σ * A.h z * ‖evC z h‖

namespace CptInputs

theorem exists_constants {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
    {y : (Σ k, J k) → Ω} (hy : Birational y) {F : Type} [Field F] [NumberField F] (cst : F →+* Ω) :
    ∃ (F' : Type) (_ : Field F') (_ : NumberField F') (ι : F →+* F') (ψ : F' →+* Ω), ψ.comp ι = cst ∧
      ∀ x : Ω, (∃ f : Polynomial F', f ≠ 0 ∧ f.eval₂ ψ x = 0) → x ∈ Set.range ψ := by
  classical
  letI : Algebra F Ω := cst.toAlgebra
  have hle : ∀ g : MRing J, aeval y g ∈ IntermediateField.adjoin F (Set.range y) := fun g => by
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, aeval_X]; exact mul_mem hp (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  haveI : Algebra.EssFiniteType F Ω := by
    rw [← IntermediateField.fg_top_iff]
    refine ⟨(Set.finite_range y).toFinset, ?_⟩
    rw [Set.Finite.coe_toFinset, eq_top_iff]
    intro a _
    obtain ⟨d, g, h, -, -, h0, e⟩ := hy a
    rw [eq_div_of_mul_eq h0 e.symm]
    exact div_mem (hle g) (hle h)
  let L := algebraicClosure F Ω
  haveI : FiniteDimensional F L := GlobalTheory.finiteDimensional_algebraicClosure_of_essFiniteType F Ω
  haveI : NumberField L := NumberField.of_module_finite F L
  refine ⟨L, inferInstance, inferInstance, algebraMap F L, algebraMap L Ω, rfl, ?_⟩
  rintro x ⟨f, hf, hx⟩
  have h1 : IsAlgebraic L x := ⟨f, hf, hx⟩
  exact ⟨⟨x, mem_algebraicClosure_iff.2 (h1.restrictScalars F)⟩, rfl⟩

theorem orders_const {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {F' : Type} [Field F']
    [NumberField F'] (ψ : F' →+* Ω) {a : F'} (ha : a ≠ 0) {e : Ω} (he : e ≠ 0) :
    ∃ r : HeightOneSpectrum (𝓞 F') →₀ ℚ, (∀ v, r v = (-WithZero.log (v.valuation F' a) : ℤ)) ∧
      ∀ (v : HeightOneSpectrum (𝓞 F')) (π : F'), v.valuation F' π = WithZero.exp (-1 : ℤ) →
        ∃ (m : ℕ) (k : ℤ), 0 < m ∧ (k : ℚ) = m * r v ∧ ∀ p : Cpt ξ,
          (∀ b : F', v.valuation F' b ≤ 1 → ψ b ∈ regAt ξ p) →
          OrderAt (fun p => Submodule.span (regAt ξ p) {e} : Lat ξ Ω) (ψ a * e) (ψ π) m k p := by
  have hfin : (Function.support fun v : HeightOneSpectrum (𝓞 F') =>
      ((-WithZero.log (v.valuation F' a) : ℤ) : ℚ)).Finite := by
    refine ((HeightOneSpectrum.Support.finite (𝓞 F') a).union
      (HeightOneSpectrum.Support.finite (𝓞 F') a⁻¹)).subset fun v hv => ?_
    by_contra hn
    simp only [HeightOneSpectrum.Support, Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt, map_inv₀] at hn
    have h0 : 0 < v.valuation F' a := zero_lt_iff.2 (by simpa using ha)
    have : v.valuation F' a = 1 := le_antisymm hn.1 ((inv_le_one₀ h0).1 hn.2)
    exact hv (by simp [this])
  refine ⟨Finsupp.ofSupportFinite _ hfin, fun _ => rfl, fun v π hπ =>
    ⟨1, -WithZero.log (v.valuation F' a), one_pos, by rw [Nat.cast_one, one_mul]; rfl, fun p hp => ?_⟩⟩
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ; exact WithZero.exp_ne_zero hπ.symm
  have hu : v.valuation F' (a / π ^ (-WithZero.log (v.valuation F' a))) = 1 := by
    rw [map_div₀, map_zpow₀, hπ, ← WithZero.exp_zsmul]
    simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
    rw [WithZero.exp_log (by simpa using ha), div_self (by simpa using ha)]
  refine ⟨e, ψ a, he, rfl, rfl, ?_⟩
  rw [pow_one, ← map_zpow₀, ← map_div₀]
  exact ⟨(map_ne_zero ψ).2 (div_ne_zero ha (zpow_ne_zero _ hπ0)), hp _ hu.le,
    by rw [← map_inv₀]; exact hp _ (by rw [map_inv₀, hu, inv_one])⟩

example (hI : CptFlatInputs) (hG : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω]
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω) (τ : CMType H)
    (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (A : HermLine J) (c₀ : Ω)
    (r : HeightOneSpectrum (𝓞 F') →₀ ℚ) (cinf : (F' →+* ℂ) → ℝ),
    Fl.RootLines xdeg e → A.a = ∑ i, xdeg (τ, i) → Birational y → IsConjInvariantH A → c₀ ≠ 0 →
    (∀ p ∈ genFibre ℤ 𝔐.ξ, (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
        (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))).IsGenAt p (c₀ * ∏ i, e (τ, i))) →
    (∀ (v : HeightOneSpectrum (𝓞 F')) (π : F'), v.valuation F' π = WithZero.exp (-1 : ℤ) →
      ∃ (m : ℕ) (k : ℤ), 0 < m ∧ (k : ℚ) = m * r v ∧ ∀ p : Cpt 𝔐.ξ,
        (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt 𝔐.ξ p) →
        OrderAt (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
        (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))) (c₀ * ∏ i, e (τ, i)) (ψ π) m k p) →
    (∀ σ, 0 < cinf σ) →
    (∀ (σ : F' →+* ℂ) z (g h : MRing J) (dg dh : K → ℕ), PtOver y ψ σ z → IsMultiHomog g dg → IsMultiHomog h dh →
      (∀ k, (dg k : ℤ) - dh k = A.a k) → aeval y g = c₀ * aeval y h → ‖evC z g‖ = cinf σ * A.h z * ‖evC z h‖) →
    OverInt y ψ ∧ ∃ Sf : FlatHerm y ψ A, Sf.ht = ((r.sum fun v q => (q : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) -
      ∑ σ : F' →+* ℂ, Real.log (cinf σ)) / (Module.finrank ℚ F' : ℝ)) :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c))
    (Z : CptOver Y U) (φ : FrameFn Xo c) (τ : CMType H) (t : (c.F →+* ℂ) → ℝ) (S : Finset ℕ)
    (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ)
    (e : CMType H × Fin (D.p + D.q) → Ω) (hx : CMType H × Fin (D.p + D.q) → HermLine J) (A : HermLine J) (n : ℕ),
    Z.IsGeom → FlatOnModel Z τ.1 φ → (∀ s, HasInfNorm U τ.1 φ s (t s)) →
    genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j) →
    Birational y → IsArithVar (mCoordIdeal y) n →
    Fl.RootLines xdeg e → (∀ r, Fl.IsHodgeLine r (e r) (hx r)) →
    IsSmoothHerm A → IsConjInvariantH A → A.a = ∑ i, xdeg (τ, i) →
    (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → 𝔐.Interior z →
      A.h w = ∏ i, (hx (τ, i)).h w) →
    (∀ p ∈ S, ExactModLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (p : Ω) (D.p + D.q)) →
    (∀ p : ℕ, p.Prime → p ∉ S →
      NumTrivMod (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
        (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))) (p : Ω)) →
    ∃ (F' : Type) (_ : Field F') (_ : NumberField F') (ι : c.F →+* F') (ψ : F' →+* Ω)
      (r : HeightOneSpectrum (𝓞 F') →₀ ℚ), ψ.comp ι = 𝔐.cst ∧ OverInt y ψ ∧ ∃ Sf : FlatHerm y ψ A,
        Sf.ht = ((r.sum fun v q => (q : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) -
          ∑ σ : F' →+* ℂ, t (σ.comp ι)) / (Module.finrank ℚ F' : ℝ) := by
  intro E _ _ _ H D l Xo c _ Y U Z φ τ t S Ω _ K _ J _ y 𝔐 Fl xdeg e hx A n h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    h12 h13 h14
  obtain ⟨F', _, _, ι, ψ, hc, hcl⟩ := exists_constants h5 𝔐.cst
  obtain ⟨c₀, r, cinf, g0, g1, g2, g3, g4, g5⟩ := hI E H D l Xo c Y U Z φ τ t S Ω K J y 𝔐 Fl xdeg e hx A n F' ι ψ
    h1 h2 h3 h4 hc hcl h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  obtain ⟨k1, Sf, k2⟩ := hG E H D l Xo c _ _ Y S Ω K J y 𝔐 Fl xdeg e τ F' ψ A c₀ r cinf h7 h11 h5 h10 g0 g2 g3 g4 g5
  exact ⟨F', inferInstance, inferInstance, ι, ψ, r, hc, k1, Sf, by simpa only [g1, Real.log_exp] using k2⟩

end CptInputs

end GlobalTheory.CompanionTheory.Ar.Flat
