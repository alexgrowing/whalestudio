import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericSectionExtendsNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportGeneratorLbPowToAmpleBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralHodgeBundleGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFourthPowerUnderIsogeny
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TozCore

theorem exists_extension_of_cover_hodge : ∀ (o : Type) [CommRing o] (g : ℕ) (Z S' : Scheme.{0}) (z : Z ⟶ Sp o) (π : S' ⟶ Z) [IsProper z] [IsProper π] (OZ : LB Z), OZ.IsLB → GlobalTheory.IsAmpleLB OZ → ∀ (G : Over S') [GrpObj G] [IsCommMonObj G] (N : ℕ), IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → LBIso (OZ.pull π) (lbPow (hodge G g) N) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (b : o →+* R) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (y : Sp (FractionRing R) ⟶ S') (α : pullback G₁.hom (jK R) ⟶ G.left), IsGrpPullback ((Over.pullback (jK R)).obj G₁) G y α → y ≫ π ≫ z = jK R ≫ spMap b → ∃ a : Sp R ⟶ Z, jK R ≫ a = y ≫ π := by
  intro o _ g Z S' z π _ _ OZ hOZ hA G _ _ N hG hsm hw R _ _ _ _ _ _ b G₁ _ _ hG₁ y α hα hy
  have := hA.compactSpace
  have := hA.quasiSeparatedSpace
  have := hG.separated
  have : QuasiSeparated G.hom := inferInstance
  have hL : (hodge G g).IsLB := isLB_hodge G g
  obtain ⟨T, hT, hTv⟩ := GlobalTheory.T.exists_transport_generator_lbPow_to_ampleBundle S' Z π OZ (hodge G g) N hOZ hL hw
  obtain ⟨e₀, he₀, H⟩ := GlobalTheory.T.exists_integral_hodgeBundle_generator S' g G hG hsm R G₁ hG₁ y α hα
  have amp : ∀ z : Z, ∃ (d : ℕ) (s : H0 OZ d), 1 ≤ d ∧ z ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s) := by
    intro x
    obtain ⟨n, hn, s, hs, ha⟩ := hA.exists_affine x
    refine ⟨n, GlobalTheory.ThetaShift.secFinOne s, hn, ?_, ?_⟩
    · rw [GlobalTheory.ThetaShift.nonzeroLocus_secFinOne]; exact hs
    · rw [GlobalTheory.ThetaShift.nonzeroLocus_secFinOne]; exact ha
  refine GlobalTheory.ExtLB.exists_extension Z OZ hOZ amp R (y ≫ π) (T _ y e₀) (hT _ y e₀ he₀) ?_
  intro W _ _ _ hW φ gam hg
  have := hW.1
  have sq : spMap gam ≫ jK R = jK W ≫ spMap φ := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext hg)
  obtain ⟨χ', hχ', -⟩ := val_exists (π ≫ z) (spMap gam ≫ y) (spMap φ ≫ spMap b) (by
    rw [Category.assoc, hy, ← Category.assoc, sq, Category.assoc])
  obtain ⟨e₀', he₀', hv⟩ := H W hW φ gam hg χ' hχ'.symm
  refine ⟨χ' ≫ π, by rw [← Category.assoc, ← hχ', Category.assoc], T _ χ' e₀', hT _ χ' e₀' he₀', ?_⟩
  exact hTv _ _ _ y χ' e₀ e₀' (spMap gam) (jK W) he₀ he₀' hχ'.symm hv

end GlobalTheory.TozCore
