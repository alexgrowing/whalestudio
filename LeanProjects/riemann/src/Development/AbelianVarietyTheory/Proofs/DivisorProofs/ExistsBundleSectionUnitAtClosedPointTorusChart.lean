import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTwistedLineBundleNonzeroClosedFibreStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.SecConst

open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic in

theorem exists_secB_isUnit_const : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → ∀ mu α : P.D.toPre.X, ∃ σ : P.D.toPre.SecB e α, ∀ zz J, Good P.D.toPre.P.L zz J → IsUnit (sval σ (spMap (constHom ρ) ≫ (P.D.toPre.c mu).left) zz J) := by
  intro E _ _ _ H k _ _ m d t P gam _ _ _ Y n' v' dd _ D q _ h _ _ _ ρ hρ B' _ π₁ π₂ c' _ _ _ _
  refine ⟨6, fun e he mu al => ?_⟩
  have hpt : ∀ zz, (spMap (constHom ρ) ≫ (P.D.toPre.c mu).left) zz =
      (P.D.toPre.c mu).left (IsLocalRing.closedPoint (ChartRing k m d)) := by
    intro zz
    rw [Scheme.Hom.comp_apply]
    congr 1
    have key : ∀ r : ChartRing k m d,
        (constHom ρ) r = algebraMap k (DualNumber k) (MvPowerSeries.constantCoeff r) := by
      intro r
      simp [constHom, hρ r]
    apply PrimeSpectrum.ext
    ext r
    show (constHom ρ) r ∈ PrimeSpectrum.asIdeal (R := DualNumber k) zz ↔
      r ∈ IsLocalRing.maximalIdeal (ChartRing k m d)
    rw [key, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
      isUnit_iff_ne_zero, not_not]
    by_cases h0 : MvPowerSeries.constantCoeff r = 0
    · simp [h0, Ideal.zero_mem]
    · refine iff_of_false (fun hm => ?_) h0
      have hu : IsUnit (algebraMap k (DualNumber k) (MvPowerSeries.constantCoeff r)) :=
        (isUnit_iff_ne_zero.2 h0).map _
      exact (PrimeSpectrum.isPrime (R := DualNumber k) zz).ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)
  have hxc : P.D.toPre.P.A.hom ((P.D.toPre.c mu).left (IsLocalRing.closedPoint (ChartRing k m d))) =
      IsLocalRing.closedPoint (ChartRing k m d) := by
    show ((P.D.toPre.c mu).left ≫ P.D.toPre.P.A.hom) _ = _
    rw [Over.w (P.D.toPre.c mu)]
    rfl
  obtain ⟨σ₂, hσ₂⟩ := GlobalTheory.T.exists_section_twistedLineBundle_nonzero_closedFibre (ChartRing k m d) (GlobalTheory.MumfordChart.admissibleBase_chartRing k m d).2.2.2 P.D.toPre al _ hxc
  have hA := (GlobalTheory.abelianSchemeLaws_all).1.ample
  obtain ⟨N, s, hcov⟩ := (hA (Spec (CommRingCat.of (ChartRing k m d))) P.D.toPre.P (e - 2) (by omega)).1 ⊤
    (isAffineOpen_top _)
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : P.D.toPre.P.A.left ⟶ (P.D.toPre.P.A.hom ⁻¹ᵁ ⊤).toScheme,
      ρ' ≫ (P.D.toPre.P.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift _ (𝟙 _) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show ρ' ((P.D.toPre.c mu).left (IsLocalRing.closedPoint (ChartRing k m d))) ∈ ⨆ i, nonzeroLocus (s i) by
      rw [hcov]; trivial)
  have hF : FormEq (Sum.elim (DegPre.famφB P.D.toPre al)
      (fun _ : Fin (e - 2) => ρ' ≫ (P.D.toPre.P.A.hom ⁻¹ᵁ ⊤).ι))
      (Sum.elim (DegPre.famε 2) (fun _ => 1)) (DegPre.famφB P.D.toPre al) (DegPre.famε e) := by
    intro U _ hh
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hρ', Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, zpow_one, Fin.prod_univ_four]
    have e0 : DegPre.famφB P.D.toPre al 0 = 𝟙 _ := rfl
    have x0 : DegPre.famε 2 0 = 1 := by simp [DegPre.famε]
    have y0 : DegPre.famε e 0 = (e : ℤ) - 1 := rfl
    have x1 : DegPre.famε 2 1 = DegPre.famε e 1 := rfl
    have x2 : DegPre.famε 2 2 = DegPre.famε e 2 := rfl
    have x3 : DegPre.famε 2 3 = DegPre.famε e 3 := rfl
    rw [x0, y0, x1, x2, x3, e0, show (e : ℤ) - 1 = 1 + ((e - 2 : ℕ) : ℤ) by omega, zpow_add, zpow_natCast,
      zpow_one]
    ac_rfl
  obtain ⟨σ, hσ⟩ := exists_sec P.D.toPre.P.isLB hF (mulSec σ₂ (pullSec (s i) ρ'))
  refine ⟨σ, fun zz J hJ => ?_⟩
  rw [hσ _ _ zz J hJ, sval_mulSec _ _ _ zz hJ]
  erw [sval_pullSec (s i) ρ' _ zz hJ]
  refine IsUnit.mul ?_ ?_
  · obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hσ₂
    exact isUnit_sval σ₂ _ zz hJ j (by rw [hpt]; exact hj)
  · obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    exact isUnit_sval (s i) _ zz hJ j (by rw [Scheme.Hom.comp_apply, hpt]; exact hj)

end GlobalTheory.SecConst
