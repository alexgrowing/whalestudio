import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemAbLocusIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem ringOfIntegers_hom_injective {F : Type} [Field F] [NumberField F] {R : Type} [Field R] [CharZero R]
    (a : 𝓞 F →+* R) : Function.Injective a := by
  have hI : (RingHom.ker a).comap (algebraMap ℤ (𝓞 F)) = ⊥ := by
    rw [eq_bot_iff]
    intro n hn
    have h0 : ((n : ℤ) : R) = 0 := by
      have h1 : a (algebraMap ℤ (𝓞 F) n) = 0 := hn
      simpa using h1
    have h2 : n = 0 := by exact_mod_cast h0
    simp [h2]
  exact (RingHom.injective_iff_ker_eq_bot a).2 (Ideal.eq_bot_of_comap_eq_bot hI)

theorem exists_ringHom_extend {F : Type} [Field F] [NumberField F] {R : Type} [Field R] [CharZero R]
    (a : 𝓞 F →+* R) : ∃ κ : F →+* R, κ.comp (algebraMap (𝓞 F) F) = a :=
  ⟨IsFractionRing.lift (ringOfIntegers_hom_injective a),
    RingHom.ext fun x => IsFractionRing.lift_algebraMap (ringOfIntegers_hom_injective a) x⟩

theorem exists_isOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X), 𝔐.Interior z → ∃ (κ : c.F →+* ℂ) (p : Sp ℂ ⟶ Xo.X), IsOver 𝔐 z κ p := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 z hz
  have := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  let a : 𝓞 c.F →+* ℂ := (Spec.preimage (z ≫ 𝔐.f ≫ Y.s)).hom
  have ha : z ≫ 𝔐.f ≫ Y.s = spMap a := by
    unfold spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨κ, hκ⟩ := exists_ringHom_extend a
  have hc : (z ≫ 𝔐.f) ≫ Y.s = spMap κ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [Category.assoc, ha, ← hκ, Chg.spMap_comp']
  let w : Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) := pullback.lift (z ≫ 𝔐.f) (spMap κ) hc
  have hw₁ : w ≫ pullback.fst _ _ = z ≫ 𝔐.f := pullback.lift_fst _ _ _
  have hw₂ : w ≫ pullback.snd _ _ = spMap κ := pullback.lift_snd _ _ _
  have := Y.jQ_open
  have hr : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨u, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, hw₁, Scheme.Hom.comp_apply]
    have hu : u = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hu
    exact (abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 _).2 hz
  let x : Sp ℂ ⟶ Xo.XF c := IsOpenImmersion.lift Y.jQ w hr
  have hx : x ≫ Y.jQ = w := IsOpenImmersion.lift_fac _ _ _
  refine ⟨κ, x ≫ pullback.fst _ _, x, ?_, rfl, ?_⟩
  · rw [Model.j, ← Category.assoc, hx, hw₁]
  · rw [← Y.jQ_over, ← Category.assoc, hx, hw₂]

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
