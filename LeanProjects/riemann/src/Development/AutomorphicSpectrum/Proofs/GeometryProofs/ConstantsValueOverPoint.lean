import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToGermTop
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.OverVal

theorem closedPoint_germ_const {X : Scheme.{0}} {F : Type} [Field F] {O : Type} [CommRing O]
    (s : X ⟶ Spec (CommRingCat.of O)) (z : Spec (CommRingCat.of F) ⟶ X) (φ : O →+* F)
    (hz : z ≫ s = Spec.map (CommRingCat.ofHom φ)) (o : O) :
    (Scheme.stalkClosedPointTo z).hom ((X.presheaf.germ ⊤ (centre z) trivial).hom
      (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) = φ o := by
  letI : Algebra O F := φ.toAlgebra
  have h := GlobalTheory.CompanionTheory.Ar.Flat.ConstReg.genMap_germ_const z s hz ⟨genPt z, specializes_rfl⟩ o
  have e : genMap z ⟨genPt z, specializes_rfl⟩ = (Scheme.stalkClosedPointTo z).hom := by
    ext t
    simp only [genMap, TopCat.Presheaf.stalkSpecializes_refl]
    exact congrArg (fun q : X.presheaf.stalk (genPt z) ⟶ CommRingCat.of F => q.hom t)
      (Category.id_comp (Scheme.stalkClosedPointTo z))
  rw [e] at h
  exact h

theorem val_const {X : Scheme.{0}} {Ω : Type} [Field Ω] {F : Type} [Field F] {O : Type} [CommRing O]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (all : ∀ q : X, genPt ξ ⤳ q)
    (s : X ⟶ Spec (CommRingCat.of O)) (ψ : O →+* Ω)
    (hs : ξ ≫ s = Spec.map (CommRingCat.ofHom ψ))
    (z : Spec (CommRingCat.of F) ⟶ X) (φ : O →+* F)
    (hz : z ≫ s = Spec.map (CommRingCat.ofHom φ)) (o : O) : ValAt ξ z (ψ o) (φ o) := by
  letI : Algebra O Ω := ψ.toAlgebra
  exact ⟨all _, _, GlobalTheory.CompanionTheory.Ar.Flat.ConstReg.genMap_germ_const ξ s hs ⟨centre z, all _⟩ o, closedPoint_germ_const s z φ hz o⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.OverVal

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

open GlobalTheory.CompanionTheory.Ar.RootHt.ArchB OverVal

theorem isOver_base {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
    {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω]
    {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y} {z : Sp ℂ ⟶ 𝔐.X} {κ : c.F →+* ℂ}
    {p : Sp ℂ ⟶ Xo.X} (h : IsOver 𝔐 z κ p) :
    z ≫ 𝔐.f ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F)) := by
  obtain ⟨x, hx, -, hk⟩ := h
  have h1 : z ≫ 𝔐.f ≫ Y.s = x ≫ Y.j ≫ Y.s := by
    rw [← Category.assoc, ← hx, Category.assoc]
  rw [h1, Model.j, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hk]
  exact (Spec.map_comp _ _).symm

theorem val_cst : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) (κ : c.F →+* ℂ) (p : Sp ℂ ⟶ Xo.X), IsOver 𝔐 z κ p → ∀ x : c.F, ValAt 𝔐.ξ z (𝔐.cst x) (κ x) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 z κ p h x
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have hc : ∀ o : 𝓞 c.F, ValAt 𝔐.ξ z (𝔐.cst (algebraMap (𝓞 c.F) c.F o)) (κ (algebraMap (𝓞 c.F) c.F o)) := fun o =>
    val_const 𝔐.ξ 𝔐.all (𝔐.f ≫ Y.s) (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) 𝔐.cst_over z
      (κ.comp (algebraMap (𝓞 c.F) c.F)) (isOver_base h) o
  obtain ⟨a, n, hn, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 c.F) x
  have hn0 : algebraMap (𝓞 c.F) c.F n ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 c.F) c.F)).2 (nonZeroDivisors.ne_zero hn)
  have hk0 : κ (algebraMap (𝓞 c.F) c.F n) ≠ 0 := (map_ne_zero κ).2 hn0
  rw [map_div₀, map_div₀, div_eq_mul_inv, div_eq_mul_inv]
  exact val_mul (hc a) (by simpa only [map_inv₀] using val_inv₀ hk0 (hc n))

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
