import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasPhiExistsExtAndUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QValPullbackMulRamificationCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPelUnifPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SlopeRec

theorem valV_map_of_vV {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    [IsDiscreteValuationRing V'] (ψ : FractionRing V →+* FractionRing V') {r : ℕ}
    (h : ∀ x, x ≠ 0 → vV V' (ψ x) = (r : ℤ) * vV V x) {x : FractionRing V} (hx : x ≠ 0) :
    valV V' (ψ x) = valV V x ^ r := by
  have h1 := h x hx
  simp only [vV] at h1
  rw [← WithZero.exp_log (valV_ne_zero (V := V') ((map_ne_zero ψ).2 hx)),
    ← WithZero.exp_log (valV_ne_zero (V := V) hx), ← WithZero.exp_nsmul]
  congr 1
  rw [nsmul_eq_mul]; linarith

theorem exists_ringHom_of_vV {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V']
    [IsDomain V'] [IsDiscreteValuationRing V'] (ψ : FractionRing V →+* FractionRing V') {r : ℕ}
    (h : ∀ x, x ≠ 0 → vV V' (ψ x) = (r : ℤ) * vV V x) :
    ∃ g : V →+* V', (algebraMap V' (FractionRing V')).comp g = ψ.comp (algebraMap V (FractionRing V)) ∧
      ∀ (ϖ : V) (ϖ' : V'), Irreducible ϖ → Irreducible ϖ' → Associated (g ϖ) (ϖ' ^ r) := by
  have hi := IsFractionRing.injective V' (FractionRing V')
  have hex : ∀ a : V, ∃ b : V', algebraMap V' (FractionRing V') b = ψ (algebraMap V (FractionRing V) a) := fun a => by
    by_cases ha : algebraMap V (FractionRing V) a = 0
    · exact ⟨0, by rw [ha, map_zero, map_zero]⟩
    refine IsDiscreteValuationRing.exists_lift_of_le_one (K := FractionRing V') ?_
    refine (valV_map_of_vV ψ h ha).trans_le (pow_le_one₀ zero_le ?_)
    exact HeightOneSpectrum.valuation_le_one _ a
  choose g hg using hex
  let g' : V →+* V' :=
    { toFun := g
      map_one' := hi (by rw [hg, map_one, map_one, map_one])
      map_mul' := fun a b => hi (by rw [map_mul, hg, hg, hg, map_mul, map_mul])
      map_zero' := hi (by rw [hg, map_zero, map_zero, map_zero])
      map_add' := fun a b => hi (by rw [map_add, hg, hg, hg, map_add, map_add]) }
  refine ⟨g', RingHom.ext hg, fun ϖ ϖ' hϖ hϖ' => ?_⟩
  have key : ∀ {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] {π : W}, Irreducible π →
      valV W (algebraMap W (FractionRing W) π) = WithZero.exp (-1 : ℤ) := fun {W} _ _ _ π hπ => by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton _ hπ.ne_zero hπ.maximalIdeal_eq
  have h0 : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_valuation_eq (A := V')
    (algebraMap V' (FractionRing V') (g ϖ)) (algebraMap V' (FractionRing V') (ϖ' ^ r)) (by
      change valV V' _ = valV V' _
      rw [hg, valV_map_of_vV ψ h h0, map_pow, map_pow, key hϖ, key hϖ'])
  refine ⟨u, hi ?_⟩
  rw [← hu, map_mul, _root_.mul_comm, Units.smul_def, Algebra.smul_def]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem HasPhi.baseChange {T T' : CDVR} {io : c.F →+* T.Fr} {io' : c.F →+* T'.Fr} {y : IntFr Xo c T io}
    {y' : IntFr Xo c T' io'} {r : ℕ} (hr : 0 < r) (ψ : T.Fr →+* T'.Fr)
    (hv : ∀ x, x ≠ 0 → vV T'.V (ψ x) = (r : ℤ) * vV T.V x)
    (hx : letI := io.toAlgebra; letI := io'.toAlgebra; y'.1.x = spMap ψ ≫ y.1.x) {φ : ℝ} (h : HasPhi y φ) :
    HasPhi y' (r * φ) := by
  letI := io.toAlgebra; letI := io'.toAlgebra
  obtain ⟨G, t, m1, m2, P, ϖ, Q, β, hϖ, hQ, h0, hβ, rfl⟩ := h
  obtain ⟨h₁, -, h₃, h₄, h₅⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨g, hg, hass⟩ := exists_ringHom_of_vV ψ hv
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible T'.V
  have ha := hass ϖ ϖ' hϖ hϖ'
  have ig : Function.Injective g := by
    have : Function.Injective ((algebraMap T'.V T'.Fr).comp g) := by
      rw [hg]; exact ψ.injective.comp (IsFractionRing.injective T.V T.Fr)
    exact Function.Injective.of_comp (f := algebraMap T'.V T'.Fr) this
  have hI : (maximalIdeal T.V).map g ≤ maximalIdeal T'.V := by
    rw [hϖ.maximalIdeal_eq, hϖ'.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_le_span_singleton]
    exact (dvd_pow_self ϖ' hr.ne').trans ha.symm.dvd
  obtain ⟨G', m₀, P', hD, -, -, -, -, hxe, -⟩ := ArcDataDescent.exists_pelUnif_pull h₃.cubePull h₁.polBaseChange
    h₄.unifBaseChange h₅ ⟨inferInstance, inferInstance, inferInstance, T.cpl⟩
    ⟨inferInstance, inferInstance, inferInstance, T'.cpl⟩ G P g ig hI
  obtain ⟨_, _, _, _, _, n, -⟩ := sabPull h₃.cubePull (spMap ψ) t
  obtain ⟨n1, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m1 n
  obtain ⟨n2, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m2 n
  have sq : spMap ψ ≫ spMap (algebraMap T.V T.Fr) = spMap (algebraMap T'.V T'.Fr) ≫ spMap g :=
    (spMap_comp _ ψ).symm.trans ((congrArg spMap hg.symm).trans (spMap_comp g _))
  rw [sq] at n2
  rw [← hx] at n1
  obtain ⟨n3, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m₀ n2
  let e : P'.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X := { hD.xe with map_smul' := hxe }
  obtain ⟨β', hβ', hφ⟩ := GlobalTheory.EtaVal.phiC_smul_pull E _ _ _ e β r (Nat.cast_nonneg r)
  refine ⟨G', _, n1, n3, P', ϖ', fun a => r * Q (hD.xe a), β', hϖ',
    fun a => GlobalTheory.QValPull.main T T' g _ _ hD ϖ ϖ' r ig hϖ hϖ' ha a _ (hQ _),
    fun a => mul_nonneg (Nat.cast_nonneg r) (h0 _), fun a => ?_, hφ.symm⟩
  rw [hβ', hβ]
  change (r : ℝ) * (2 * (Q (hD.xe a) : ℝ)) = _
  push_cast
  ring

theorem phi_eq_mul_of_frMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T T' : CDVR) (io : c.F →+* T.Fr) (io' : c.F →+* T'.Fr) (y : IntFr Xo c T io) (y' : IntFr Xo c T' io') (r : ℕ), 0 < r → (letI := io.toAlgebra; letI := io'.toAlgebra; ∃ ψ : T.Fr →ₐ[c.F] T'.Fr, (∀ x, x ≠ 0 → vV T'.V (ψ x) = (r : ℤ) * vV T.V x) ∧ FrMap ψ y.1 y'.1) → ∀ φ φ' : ℝ, HasPhi y φ → HasPhi y' φ' → φ' = r * φ := by
  rintro E _ _ _ H Dw l Xo c T T' io io' y y' r hr ⟨ψ, hv, hm⟩ φ φ' h h'
  letI := io.toAlgebra; letI := io'.toAlgebra
  exact HasPhi.unique h' (HasPhi.baseChange hr ψ.toRingHom hv hm.1 h)

end GlobalTheory.SlopeRec
