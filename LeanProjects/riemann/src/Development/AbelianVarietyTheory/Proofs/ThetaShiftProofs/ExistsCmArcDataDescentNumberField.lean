import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDataDescendsPrincipalIdealSubringStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldNormalisedDegenerationDataStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegenerationStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRosatiActionWeilPairingBalancedTriple
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolFibreIdCompCancel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem DescNum.isPolFibre_of_isPullDeg {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {f : R →+* R'}
    {D : Out.DegPre R} {D' : Out.DegPre R'} (p : Out.IsPullDeg f D D') : IsPolFibre f D.P D'.P (prj p) :=
  ⟨H1.dim_unique _ D'.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (pull_grp p).1 D.P.smoothDim)
    (eSec D'.P.A (Classical.arbitrary (PrimeSpectrum R'))), pull_grp p, LBIso.symm ⟨p.w, p.w_gen⟩⟩

theorem DescNum.epi_of_isPullback_field {K K' : Type} [Field K] [Field K'] (f : K →+* K') {X X' : Scheme.{0}} {φ : X' ⟶ X}
    {s' : X' ⟶ Sp K'} {s : X ⟶ Sp K} (h : IsPullback φ s' s (spMap f)) : Epi φ := by
  letI := f.toAlgebra
  haveI h₁ : Flat (spMap f) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (inferInstance : Module.Flat K K')
  haveI h₂ : Surjective (spMap f) := ⟨fun p => ⟨(⊥ : PrimeSpectrum K'), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  haveI : Flat φ := MorphismProperty.of_isPullback (P := @Flat) h.flip h₁
  haveI : Surjective φ := MorphismProperty.of_isPullback (P := @Surjective) h.flip h₂
  exact Flat.epi_of_flat_of_surjective φ

theorem exists_arcIn_numberField : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (σ₁ : K →+* ℂ) (σ : c.F →+* ℂ) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (φ : aC.D₀.P.A.left ⟶ B.pol.A.left) (n : ℕ), letI := H.starRing; σ₁.comp (algebraMap c.F K) = σ → 0 < n → IsPolFibre (σ₁.comp (algebraMap (𝓞 K) K)) B.pol aC.D₀.P φ → (∀ x, (aC.oa.onB.act x).left ≫ φ = φ ≫ (B.t.act.act x).left) → TauCan aC.D₀ n → ∃ (K₂ : Type) (_ : Field K₂) (_ : NumberField K₂) (_ : Algebra c.F K₂) (i : K →ₐ[c.F] K₂) (σ₂ : K₂ →+* ℂ) (a : ArcIn Dw l (RingHom.id c.F) K₂ (algebraMap c.F K₂)) (p : Out.IsPullDeg σ₂ a.D₀ aC.D₀) (ψ : a.D₀.P.A.left ⟶ B.pol.A.left), σ₂.comp (i : K →+* K₂) = σ₁ ∧ InBC σ₂ a aC p ∧ TauCan a.D₀ n ∧ IsPolFibre ((i : K →+* K₂).comp (algebraMap (𝓞 K) K)) B.pol a.D₀.P ψ ∧ ∀ x, (a.oa.onB.act x).left ≫ ψ = ψ ≫ (B.t.act.act x).left := by
  intro hK E _ _ _ H Dw l c K _ _ _ σ₁ σ B aC φ n hσ hn hφ hact htau
  letI := H.starRing
  obtain ⟨oa, hoa, -⟩ := GlobalTheory.LamF.exists_oAct_rosatiConj hK.laws E H (fun _ => rfl) K B
  obtain ⟨P, φP, hP⟩ := exists_isPolFibre hK.laws.polBaseChange (algebraMap (𝓞 K) K) B.pol
  obtain ⟨φ₁, hφ₁, e₁⟩ := PolFibre.cancel hP hφ
  obtain ⟨K₂, _, _, i₂, σ₂, D₂, p₂, ψ₂, hi₂, hψ₂, e₂⟩ :=
    GlobalTheory.T.exists_numberField_normalised_degenerationData hK K σ₁ P aC.D₀ φ₁ n hn hφ₁ aC.even aC.bimult htau
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  obtain ⟨K₃, _, _, i₃, σ₃, D₃, q, p₃, hi₃, e₃, hQ⟩ :=
    GlobalTheory.T.exists_numberField_qkPoints_complex_degeneration hK K₂ σ₂ D₂ aC.D₀ p₂ n l.M' hn hM aC.bimult htau.1
  have hψ : IsPolFibre ((i₃.comp i₂).comp (algebraMap (𝓞 K) K)) B.pol D₃.P ((prj q ≫ ψ₂) ≫ φP) :=
    PolFibre.comp hP (PolFibre.comp hψ₂ (DescNum.isPolFibre_of_isPullDeg q))
  have eψ : prj p₃ ≫ (prj q ≫ ψ₂) ≫ φP = φ := by
    rw [← e₁, ← e₂, ← e₃]; simp only [Category.assoc]
  generalize (prj q ≫ ψ₂) ≫ φP = ψ at hψ eψ
  obtain ⟨oB, hoB⟩ := polOActPull _ _ _ B.pol D₃.P ψ hψ.2.1 hψ.2.2 (𝓞 E) oa
  letI : Algebra c.F K₃ := ((i₃.comp i₂).comp (algebraMap c.F K)).toAlgebra
  let i : K →ₐ[c.F] K₃ := { i₃.comp i₂ with commutes' := fun _ => rfl }
  have hσ₃ : σ₃.comp (i₃.comp i₂) = σ₁ := by rw [← RingHom.comp_assoc, hi₃, hi₂]
  have hb : σ = σ₃.comp (algebraMap c.F K₃) := by rw [← hσ, ← hσ₃]; rfl
  have hp₃ := (pull_grp p₃).1
  have hcomm : ∀ x, (aC.oa.onB.act x).left ≫ prj p₃ = prj p₃ ≫ (oB.act x).left := fun x => by
    have w : prj p₃ ≫ D₃.P.A.hom = aC.D₀.P.A.hom ≫ spMap σ₃ := hp₃.w
    generalize prj p₃ = π at eψ w
    refine hψ.2.1.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, eψ, hoB, ← Category.assoc, eψ, hact, hoa]
    · rw [Category.assoc, Category.assoc, Over.w, w, ← Category.assoc, Over.w]
  obtain ⟨a, p', ha, hp', hbc, hta⟩ := GlobalTheory.T.arcData_descends_principalIdealSubring hK E H Dw l c c.F (RingHom.id c.F) K₃ ℂ σ₃ (algebraMap c.F K₃) σ
    aC D₃ p₃ n oB σ₃.injective hb hn htau hcomm (fun v => hQ _ (Nat.dvd_lcm_left _ _) _)
    (fun v => hQ _ (Nat.dvd_lcm_right _ _) _)
  subst ha
  obtain rfl := eq_of_heq hp'
  refine ⟨K₃, inferInstance, inferInstance, inferInstance, i, σ₃, a, p', ψ, hσ₃, hbc, hta, hψ, fun x => ?_⟩
  have hepi : Epi (prj p') := DescNum.epi_of_isPullback_field σ₃ hp₃
  have h := hbc.2.2.2.1 x
  generalize prj p' = π at eψ h hepi
  rw [← cancel_epi π, ← Category.assoc, ← h, Category.assoc, eψ, ← Category.assoc, eψ, hact]

end GlobalTheory.ArcCM
