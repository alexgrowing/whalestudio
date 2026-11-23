import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricPolarisationFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricDataComparePolarisedUpToFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleFreeAbelianIsCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataRescaleCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomEvenDefectBimultiplicativePeriodsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeRawDegenerationDataInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenDefectDegenerationDataBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonomialTrivialisationSqrtRefinedPolarisedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataOfMonomialEvenBimultiplicativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqrtLatticeHomFiniteExtensionCompleteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedPeriodComparisonSymmCocycleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauBimultOfRefinesPolarisedDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescaleDegDataTrivialisationsPsiEvenOfSqrtStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PolDeg.refine_monomial_of_polarised : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (m : ℕ) (t : Fin m → R) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), IsCN R → Q.IsMonomialTau t δ → (∀ i, t i ∈ maximalIdeal R) → (∀ i, t i ≠ 0) → (∀ i y z, δ i y z = δ i z y) → (∀ i y, 0 ≤ δ i y y) → (∀ y, y ≠ 0 → ∃ i, 0 < δ i y y) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (r : Fin m → R') (D : DegData R' (maximalIdeal R')) (e : D.toPre.X ≃+ Q.X), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ (∀ i, r i ^ 2 = ρ (t i)) ∧ Refines Q ρ D.toPre e ∧ IsMonomial D.toPre r fun i => (2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ i) := by
  intro R _ _ _ Q m t δ hCN hmono htm ht0 hsymm hnn hdef
  obtain ⟨R₁, _, _, _, ρ₁, P, β, β₂, hCN₁, hinj₁, hfin₁, hloc₁, hpb, hsq, hiso⟩ := GlobalTheory.T.exists_symmetricPolarisation_finiteExtension R Q hCN
  haveI : IsNoetherianRing R₁ := hCN₁.1
  obtain ⟨D, e, f, hD⟩ := GlobalTheory.T.exists_symmetric_data_compare_polarised_up_to_function R R₁ Q ρ₁ P β β₂ hinj₁ hpb hsq hiso
  obtain ⟨hfs, hfc⟩ := GlobalTheory.T.polarisedPeriod_comparison_symm_cocycle R R₁ Q ρ₁ D e f hinj₁ hD
  obtain ⟨g, hg⟩ := GlobalTheory.T.symmetric_twoCocycle_free_abelian_isCoboundary D.X _ f hfs hfc
  have hD₁ : Half Q ρ₁ (rescale D g) e (fun _ _ => 1) :=
    GlobalTheory.T.refinesPolarisedData_rescale_coboundary R R₁ Q ρ₁ D e f (fun _ _ => 1) g hD (fun a b => by rw [hg a b, _root_.mul_one])
  have hb₁ : (rescale D g).TauBimult := GlobalTheory.T.tauBimult_of_refines_polarised_data R R₁ Q ρ₁ (rescale D g) e hinj₁ hD₁
  obtain ⟨h, hhom, hev⟩ := GlobalTheory.T.exists_hom_evenDefect_bimultiplicative_periods R₁ (rescale D g) hb₁
  obtain ⟨R₂, _, _, _, σ, gam, r, et, hCN₂, hinj₂, hfin₂, hloc₂, hgam, hr, hη, hη2⟩ :=
    GlobalTheory.T.exists_sqrt_latticeHom_finiteExtension_complete R₁ (rescale D g).X h m (fun i => ρ₁ (t i)) hCN₁ hhom
  haveI : IsNoetherianRing R₂ := hCN₂.1
  obtain ⟨D₂, β', v, xe, hpb', hv, hc', hrig, hpsi⟩ := GlobalTheory.T.exists_baseChange_raw_degenerationData_injective R₁ R₂ σ (rescale D g) gam hgam
  have hD₂ := GlobalTheory.T.refinesPolarisedData_baseChange_symmetric R Q R₁ R₂ σ (rescale D g) D₂ β' v xe gam hgam hpb' hv hc' hrig hpsi ρ₁ e hinj₁ hD₁
  have hev₂ := GlobalTheory.T.evenDefect_degenerationData_baseChange R₁ R₂ σ (rescale D g) D₂ β' v xe gam hgam hpb' hv hc' hrig hpsi h hev
  have hinj : Function.Injective (σ.comp ρ₁) := hinj₂.comp hinj₁
  have hηx : ∀ a b : D₂.X, et (xe (a + b)) = et (xe a) * et (xe b) := fun a b => by rw [map_add, hη]
  have hD₃ : Half Q (σ.comp ρ₁) (rescale D₂ fun χ => et (xe χ)) (xe.trans e) (fun _ _ => 1) :=
    GlobalTheory.T.refinesPolarisedData_rescale_coboundary R R₂ Q (σ.comp ρ₁) D₂ (xe.trans e) (fun _ _ => 1) (fun _ _ => 1) (fun χ => et (xe χ)) hD₂
      (fun a b => by rw [hηx, _root_.mul_one, mul_right_comm (et (xe a)), mul_inv_cancel, _root_.one_mul, mul_inv_cancel])
  have hev₃ : (rescale D₂ fun χ => et (xe χ)).PsiEven :=
    GlobalTheory.T.rescaleDegDataTrivialisations_psiEven_of_sqrt R₂ D₂ _ (fun χ => et (xe χ)) hev₂ hηx (fun a => hη2 (xe a))
  have hb₃ : (rescale D₂ fun χ => et (xe χ)).TauBimult :=
    GlobalTheory.T.tauBimult_of_refines_polarised_data R R₂ Q (σ.comp ρ₁) _ (xe.trans e) hinj hD₃
  have hr' : ∀ i, r i ^ 2 = (σ.comp ρ₁) (t i) := fun i => hr i
  have hmon := GlobalTheory.T.exists_monomial_trivialisation_sqrt_refinedPolarisedData R R₂ Q (σ.comp ρ₁) (rescale D₂ fun χ => et (xe χ)) (xe.trans e) m t r δ hCN₂ hinj hD₃
    hev₃ hb₃ hmono hnn ht0 hr'
  have hrm : ∀ i, r i ∈ maximalIdeal R₂ := by
    intro i
    refine (inferInstance : (maximalIdeal R₂).IsPrime).mem_of_pow_mem 2 ?_
    rw [hr' i, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (mem_maximalIdeal _).1 (htm i) ((isUnit_map_iff (σ.comp ρ₁) _).1 hu)
  have key : ∀ (D₃ : DegPre R₂) (e' : D₃.X ≃+ Q.X), D₃.PsiEven → D₃.TauBimult →
      Half Q (σ.comp ρ₁) D₃ e' (fun _ _ => 1) →
      IsMonomial D₃ r (fun i => (2 : ℤ) • pull e'.toIntLinearEquiv.toLinearMap (δ i)) →
      ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (r : Fin m → R')
        (D : DegData R' (maximalIdeal R')) (e : D.toPre.X ≃+ Q.X), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧
        IsLocalHom ρ ∧ (∀ i, r i ^ 2 = ρ (t i)) ∧ Refines Q ρ D.toPre e ∧
        IsMonomial D.toPre r fun i => (2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ i) := by
    intro D₃ e' h1 h2 h3 h4
    obtain ⟨DD, rfl⟩ := GlobalTheory.T.degenerationData_of_monomial_even_bimultiplicative R₂ D₃ m r (fun i => (2 : ℤ) • pull e'.toIntLinearEquiv.toLinearMap (δ i))
      h1 h2 h4 hrm (fun i y z => by simp [pull, hsymm i (e' y) (e' z)])
      (fun y hy => by
        obtain ⟨i, hi⟩ := hdef (e' y) (by simpa using hy)
        exact ⟨i, by simpa [pull] using hi⟩)
    exact ⟨R₂, inferInstance, inferInstance, inferInstance, σ.comp ρ₁, r, DD, e', hCN₂, hinj,
      hfin₂.comp hfin₁, inferInstance, hr', h3.refines, h4⟩
  exact key _ _ hev₃ hb₃ hD₃ hmon
