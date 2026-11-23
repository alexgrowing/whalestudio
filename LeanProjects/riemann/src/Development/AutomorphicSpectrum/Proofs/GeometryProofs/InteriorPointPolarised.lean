import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

theorem injective_ringOfIntegers_toComplex {F : Type} [Field F] [NumberField F] (g : 𝓞 F →+* ℂ) :
    Function.Injective g := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  have h : Ideal.comap (algebraMap ℤ (𝓞 F)) (RingHom.ker g) = RingHom.ker (g.comp (algebraMap ℤ (𝓞 F))) :=
    RingHom.comap_ker _ _
  rw [h, (RingHom.injective_iff_ker_eq_bot _).1]
  have e : g.comp (algebraMap ℤ (𝓞 F)) = Int.castRingHom ℂ := RingHom.ext_int _ _
  rw [e]
  exact Int.cast_injective

theorem exists_comp_eq_of_ringOfIntegers {F : Type} [Field F] [NumberField F] (g : 𝓞 F →+* ℂ) :
    ∃ g' : F →+* ℂ, g'.comp (algebraMap (𝓞 F) F) = g :=
  ⟨IsFractionRing.lift (injective_ringOfIntegers_toComplex g), by
    ext a
    simp⟩

theorem exists_spMap_of_ringOfIntegers {F : Type} [Field F] [NumberField F] {X : Scheme.{0}} (s : X ⟶ Sp (𝓞 F))
    (u : Sp ℂ ⟶ X) : ∃ g' : F →+* ℂ, u ≫ s = spMap g' ≫ spMap (algebraMap (𝓞 F) F) := by
  obtain ⟨g', hg'⟩ := exists_comp_eq_of_ringOfIntegers (Spec.preimage (u ≫ s)).hom
  refine ⟨g', ?_⟩
  rw [← spMap_comp, hg']
  exact (Spec.map_preimage (u ≫ s)).symm

theorem polarisedAt_of_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type)
    [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), 𝔐.Interior z → HodgeMetric.PolarisedAt 𝔐.t z := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 z hz
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  let p : Sp ℂ := IsLocalRing.closedPoint ℂ
  have hsub : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  have h₁ : (z ≫ 𝔐.f) p ∈ abLocus Y.t.G := by
    have := (abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 (z p)).2 hz
    simpa using this

  obtain ⟨g', hg'⟩ := exists_spMap_of_ringOfIntegers Y.s (z ≫ 𝔐.f)
  let w : Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) :=
    pullback.lift (z ≫ 𝔐.f) (spMap g') hg'
  have hw : w ≫ pullback.fst _ _ = z ≫ 𝔐.f := pullback.lift_fst _ _ _

  have h₂ : w p ∈ Set.range Y.jQ := by
    rw [← Y.ab_gen]
    show (pullback.fst Y.s _) (w p) ∈ abLocus Y.t.G
    have : (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) (w p) = (z ≫ 𝔐.f) p := by
      rw [← hw]; simp
    rw [this]; exact h₁
  have h₃ : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rwa [Subsingleton.elim q p]
  haveI := Y.jQ_open
  let v : Sp ℂ ⟶ Xo.XF c := IsOpenImmersion.lift Y.jQ w h₃
  have hv : v ≫ Y.jQ ≫ pullback.fst _ _ = z ≫ 𝔐.f := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, hw]

  obtain ⟨t', ⟨m₁⟩⟩ := exists_sab z 𝔐.t
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ 𝔐.m m₁
  have cancel : ∀ (q : Sp ℂ ⟶ Y.X) (_ : q = v ≫ Y.jQ ≫ pullback.fst _ _) (_ : SABMap t' Y.t q),
      Nonempty (SABMap t' Y.oF.t v) := by
    intro q hq n; subst hq
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m₃⟩ := cancel _ hv.symm n
  obtain ⟨w₂, g₂, -⟩ := m₃.lin
  obtain ⟨am, -⟩ := amplePt _ _ v _ _ m₃.φ m₃.cart _ _ Y.oF.t.PP.isLB t'.PP.isLB ⟨w₂, g₂⟩ Y.oF.ample Y.oF.ktriv
  exact ⟨t', m₁, MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 Y.oF.proper, am⟩

end GlobalTheory.CompanionTheory.Ar.HodgeMetric
