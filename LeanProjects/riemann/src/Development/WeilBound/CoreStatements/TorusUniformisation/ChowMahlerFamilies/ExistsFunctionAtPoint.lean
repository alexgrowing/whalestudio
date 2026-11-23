import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyCoordIdealStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecStalkSpecializesComp
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.FunctionAtPoint

theorem germ_frac {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {R : Type} [CommRing R]
    (φ : R →+* Ω) (hφ : Function.Injective φ) (x : Spec (CommRingCat.of R) ⟶ X) (hx : spMap φ ≫ x = ξ)
    (z : Spec (CommRingCat.of R)) (hz : genPt ξ ⤳ x z) (a : X.presheaf.stalk (x z)) :
    ∃ r s : R, s ∉ z.asIdeal ∧ φ s * genMap ξ ⟨x z, hz⟩ a = φ r ∧ (r ∉ z.asIdeal → IsUnit a) := by
  haveI : z.asIdeal.IsPrime := PrimeSpectrum.isPrime z
  letI alg : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk z) := StructureSheaf.stalkAlgebra R z
  haveI loc : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk z) z.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R z
  have hu : ∀ s : z.asIdeal.primeCompl, IsUnit (φ s) := by
    intro s
    refine IsUnit.mk0 _ fun h => s.2 ?_
    have h0 : (s : R) = 0 := hφ (h.trans (map_zero φ).symm)
    rw [h0]
    exact z.asIdeal.zero_mem
  let lam : (Spec (CommRingCat.of R)).presheaf.stalk z →+* Ω := IsLocalization.lift (M := z.asIdeal.primeCompl) hu
  let lam' : (Spec (CommRingCat.of R)).presheaf.stalk z ⟶ CommRingCat.of Ω := CommRingCat.ofHom lam
  have hlam : ∀ r : R, lam (algebraMap R _ r) = φ r := fun r => IsLocalization.lift_eq hu r
  have e0 : (Spec (CommRingCat.of R)).fromSpecStalk z =
      Spec.map (CommRingCat.ofHom (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk z))) :=
    Spec.fromSpecStalk_eq' _ _
  have e1 : Spec.map (CommRingCat.ofHom lam) ≫ (Spec (CommRingCat.of R)).fromSpecStalk z = spMap φ := by
    rw [e0, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hlam
  have e2 : Spec.map (x.stalkMap z ≫ lam') ≫ X.fromSpecStalk (x z) = ξ := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) e1).trans hx)
  have e3 : spMap (genMap ξ ⟨x z, hz⟩) ≫ X.fromSpecStalk (x z) = ξ :=
    GlobalTheory.CompanionTheory.Ar.LieStalk.spMap_genMap_fromSpecStalk ⟨x z, hz⟩
  have e4 : x.stalkMap z ≫ lam' = CommRingCat.ofHom (genMap ξ ⟨x z, hz⟩) :=
    Spec.map_injective ((cancel_mono (X.fromSpecStalk (x z))).1 (e2.trans e3.symm))
  have e5 : lam ((x.stalkMap z).hom a) = genMap ξ ⟨x z, hz⟩ a := ConcreteCategory.congr_hom e4 a
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj z.asIdeal.primeCompl ((x.stalkMap z).hom a)
  refine ⟨r, s, s.2, ?_, fun hr => ?_⟩
  · rw [← e5, ← hlam, ← hlam, ← map_mul, mul_comm]
    exact congrArg lam hrs
  · have h1 : IsUnit (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk z) r) :=
      IsLocalization.map_units _ (⟨r, hr⟩ : z.asIdeal.primeCompl)
    rw [← hrs] at h1
    exact isUnit_of_map_unit (x.stalkMap z).hom a (isUnit_of_mul_isUnit_left h1)

theorem inv_reg {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {R : Type} [CommRing R]
    (φ : R →+* Ω) (hφ : Function.Injective φ) (x : Spec (CommRingCat.of R) ⟶ X) (hx : spMap φ ≫ x = ξ)
    (z : Spec (CommRingCat.of R)) (hz : genPt ξ ⤳ x z) {b : Ω} (hb : b ∈ regAt ξ ⟨x z, hz⟩) (w : R)
    (hw : φ w * b = 1) : φ w ∈ regAt ξ ⟨x z, hz⟩ := by
  obtain ⟨a, rfl⟩ := hb
  obtain ⟨r, s, hs, e, hu⟩ := germ_frac ξ φ hφ x hx z hz a
  have e1 : s = w * r := by
    apply hφ
    rw [map_mul, ← e, mul_left_comm, hw, _root_.mul_one]
  have hr : r ∉ z.asIdeal := fun h => hs (e1 ▸ z.asIdeal.mul_mem_left w h)
  obtain ⟨a', ha'⟩ := (hu hr).exists_right_inv
  refine ⟨a', ?_⟩
  have e2 := congrArg (genMap ξ ⟨x z, hz⟩) ha'
  rw [map_mul, map_one] at e2
  rw [← _root_.one_mul (genMap ξ ⟨x z, hz⟩ a'), ← hw, _root_.mul_assoc, e2, _root_.mul_one]

end PositivityTheory.Xgn.FunctionAtPoint

theorem PositivityTheory.Xgn.exists_function_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (z : Spec (CommRingCat.of (CR O y c'))), InChart 𝔐.ξ (mseg y) c' ⟨P.x z, 𝔐.all _⟩ ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩) ∧ ∀ a ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩, ∃ r s : CR O y c', s ∉ z.asIdeal ∧ (s : Ω) * a = r := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hd p _ _ A _ _ _ m _ _ O _ _ _ _ _ _ _ G c' hc' P z
  have hC : HasConstants ℤ A y := (GlobalTheory.T.arith_variety_coord_ideal E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd A).2.2.2.1
  have hφ : Function.Injective (algebraMap (CR O y c') Ω) := Subtype.val_injective
  have hinv := fun {b : Ω} (hb : b ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩) (w : CR O y c') =>
    PositivityTheory.Xgn.FunctionAtPoint.inv_reg 𝔐.ξ _ hφ P.x P.x_gen z (𝔐.all _) hb w
  obtain ⟨c'', hc''⟩ : ∃ c'', InChart 𝔐.ξ (mseg y) c'' ⟨P.x z, 𝔐.all _⟩ := 𝔐.tie.cover ⟨P.x z, 𝔐.all _⟩
  have hA : ∀ a : A, algebraMap A Ω a ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩ := fun a =>
    GlobalTheory.CompanionTheory.Ar.Fam.chartRing_le_regAt ℤ y c'' _ hc'' (fun o => by simp) (hC c'' hc''.1 a)
  refine ⟨⟨hc', fun j => ?_⟩, fun o => ?_, ?_⟩
  · have h1 : mseg y c'' / mseg y c' ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩ :=
      hinv (hc''.2 c') ⟨mseg y c'' / mseg y c', Algebra.subset_adjoin ⟨c'', rfl⟩⟩ (by
        have h0 := hc''.1
        change mseg y c'' / mseg y c' * (mseg y c' / mseg y c'') = 1
        field_simp)
    have h2 := mul_mem (hc''.2 j) h1
    have h0 := hc''.1
    have e : mseg y j / mseg y c'' * (mseg y c'' / mseg y c') = mseg y j / mseg y c' := by field_simp
    rwa [e] at h2
  · obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.surj m.primeCompl o
    obtain ⟨u, hu⟩ := (IsLocalization.map_units O s).exists_left_inv
    have h1 : algebraMap O Ω u ∈ regAt 𝔐.ξ ⟨P.x z, 𝔐.all _⟩ :=
      hinv (hA s) (algebraMap O (CR O y c') u) (by
        change algebraMap O Ω u * _ = 1
        rw [IsScalarTower.algebraMap_apply A O Ω, ← map_mul, hu, map_one])
    have e : o = algebraMap A O a * u := by
      have has' : o * algebraMap A O s = algebraMap A O a := has
      rw [← has', _root_.mul_assoc, mul_comm _ u, hu, _root_.mul_one]
    rw [e, map_mul, ← IsScalarTower.algebraMap_apply]
    exact mul_mem (hA a) h1
  · rintro _ ⟨a, rfl⟩
    obtain ⟨r, s, hs, e, -⟩ :=
      PositivityTheory.Xgn.FunctionAtPoint.germ_frac 𝔐.ξ _ hφ P.x P.x_gen z (𝔐.all _) a
    exact ⟨r, s, hs, e⟩
