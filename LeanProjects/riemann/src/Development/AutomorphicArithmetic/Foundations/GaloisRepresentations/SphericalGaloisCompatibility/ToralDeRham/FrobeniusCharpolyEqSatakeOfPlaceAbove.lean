import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalArtinCompNormCompat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatWDCharPolChars
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.LocalComponentsOfSmoothCharacters
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportTwistNuCharacters
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnlinkedCharsCompNormU
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.NormEqOneOfIsUnitarisable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIsWeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharNorm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.Chl

open GlobalTheory.RoadU

namespace GalTw
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.TorLift

theorem hasSat_charPol_above : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra E M] [IsScalarTower E M Ω] (l : ℕ) [Fact l.Prime] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (u : HeightOneSpectrum (𝓞 M)) (h : IsPlaceOver A w) (h' : IsPlaceOver A u) [u.asIdeal.LiesOver w.asIdeal], ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), π.IsLocComp w σ → ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport (algNorm σ).rep (chars ξ hξ) → Unlinked (chars ξ hξ) → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ P : CuspSub M n, CharLift π P → (∀ j (x : (u.adicCompletion M)ˣ), Valued.v (x : u.adicCompletion M) = 1 → (ξ j * absPow (w.adicCompletion E) (-((((1 : ℝ) - n) / 2 : ℝ) : ℂ))) (GlobalTheory.BCChar.normU w u x) = 1) → ∃ B : Multiset ℂˣ, (CG.mk P).HasSat u B ∧ ∀ (g₀ : Weil h) (g' : Weil h'), (∀ z : Ω, (g₀ : G E Ω) z = (g' : G M Ω) z) → (satWD h' n B).charPol g' = ∏ j, (X - C ((ξ j (a g₀) : ℂˣ) : ℂ)) := by
  intro hI Ω _ E _ _ _ _ _ M _ _ _ _ _ _ _ l _ n hn π χ hsc A w u h h' _ σ hσ ξ hξ hsup hun a ha P hcl hunr
  classical
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  set s₀ : ℂ := ((((1 : ℝ) - n) / 2 : ℝ) : ℂ) with hs₀
  let ξ0 : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ) := fun j => ξ j * absPow (w.adicCompletion E) (-s₀)
  have hξ0 : ∀ j, IsSmoothChar (ξ0 j) := fun j => (hξ j).mul (isSmoothChar_absPow _)
  have hback : ∀ j, ξ j = ξ0 j * absPow (w.adicCompletion E) s₀ := fun j => by
    simp only [ξ0, mul_assoc, ← absPow_add, neg_add_cancel, absPow_zero, mul_one]

  have hN : ∀ t : ℂ, (absPow (w.adicCompletion E) t).comp (GlobalTheory.BCChar.normU w u) = absPow (u.adicCompletion M) t := by
    letI : Algebra (w.adicCompletion E) (u.adicCompletion M) := (GroundTheory.Global.adicCompletionMap w u).toAlgebra
    have hf := GroundTheory.Global.continuous_adicCompletionMap w u
    haveI : ContinuousSMul (w.adicCompletion E) (u.adicCompletion M) := continuousSMul_of_algebraMap _ _ hf
    haveI : IsScalarTower E (w.adicCompletion E) (u.adicCompletion M) :=
      .of_algebraMap_eq fun x => by
        show _ = GroundTheory.Global.adicCompletionMap w u _
        rw [GroundTheory.Global.adicCompletionMap_algebraMap, IsScalarTower.algebraMap_apply E M (u.adicCompletion M)]
    haveI : FiniteDimensional (w.adicCompletion E) (u.adicCompletion M) := GroundTheory.Global.finite_adicCompletion w u
    haveI : IsModuleTopology (w.adicCompletion E) (u.adicCompletion M) := by
      letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
      exact isModuleTopologyOfFiniteDimensional
    exact fun t => GlobalTheory.LBCNu.absPow_comp_norm t

  have hx := (GlobalTheory.RoadU.TwistSupp.supp_nu_chars (w.adicCompletion E) (IrrGL.of σ.ρ σ.smooth σ.irred) n ξ0 ξ hξ0 hξ s₀
    hback).1
  have hsupσ : HasSupport σ.ρ (chars ξ0 hξ0) :=
    (hx.2 hsup).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm

  obtain ⟨T, hT, -⟩ := LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL M n P u
  have hsupT := hcl.2 w u σ T hσ hT ξ0 hξ0 hsupσ

  obtain ⟨wt, hwt⟩ := GlobalTheory.PolarizedWeight.exists_isWeight E l n hn π χ hsc
  have hwin := GlobalTheory.RoadU.window hI E l n hn π χ hsc wt hwt w σ hσ ξ hξ hsup hun
  have hunlN := GlobalTheory.RoadU.unlinked_chars_comp_normU E M w u n ((wt : ℝ) / 2) ξ hξ hwin
  have hunl0 : Unlinked (chars (fun j => (ξ0 j).comp (GlobalTheory.BCChar.normU w u))
      fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU w u (hξ0 j)) := by
    rw [GlobalTheory.RoadU.TwistSupp.chars_eq_map_nu (fun j => (ξ j).comp (GlobalTheory.BCChar.normU w u))
      (fun j => (ξ0 j).comp (GlobalTheory.BCChar.normU w u)) (fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU w u (hξ j))
      (fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU w u (hξ0 j)) (-s₀) (fun j => by
        rw [← hN (-s₀)]
        ext x
        rfl), GlobalTheory.RoadU.TwistSupp.unlinked_map_nu]
    exact hunlN

  obtain ⟨ϖ0, hϖ0⟩ := u.valuation_exists_uniformizer M
  have hv : Valued.v ((ϖ0 : M) : u.adicCompletion M) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hϖ0]
  have hne : ((ϖ0 : M) : u.adicCompletion M) ≠ 0 := (Valuation.ne_zero_iff _).1 (by rw [hv]; exact WithZero.exp_ne_zero)
  let ϖ' : (u.adicCompletion M)ˣ := Units.mk0 _ hne
  have hϖ' : Valued.v (ϖ' : u.adicCompletion M) = WithZero.exp (-1 : ℤ) := hv
  have hunrN : ∀ j (x : (u.adicCompletion M)ˣ), Valued.v (x : u.adicCompletion M) = 1 →
      (ξ0 j).comp (GlobalTheory.BCChar.normU w u) x = 1 := hunr
  have hsat := GlobalTheory.SphUnr.hasSat_of_unlinked_unr hI M n hn P u T hT (fun j => (ξ0 j).comp (GlobalTheory.BCChar.normU w u))
    (fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU w u (hξ0 j)) hsupT hunl0 hunrN ϖ' hϖ'
  refine ⟨_, hsat, ?_⟩

  obtain ⟨a', ha'⟩ := GlobalTheory.localArtinExists_holds M Ω A u h'
  intro g₀ g' hgg
  rw [GlobalTheory.SatChar.satWD_charPol_chars Ω M u A h' n (fun j => (ξ0 j).comp (GlobalTheory.BCChar.normU w u))
    (fun j => (ξ0 j).comp (GlobalTheory.BCChar.normU w u) * absPow (u.adicCompletion M) s₀) (fun j => rfl) hunrN ϖ' hϖ' a' ha' g']
  have hart := GlobalTheory.ArtinNormU.localArtin_normU E M Ω A w u h h' a a' ha ha' g₀ g' hgg
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hart, hback j, ← hN s₀]
  rfl

end GlobalTheory.RoadU.TorLift

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.T.frobenius_charpoly_eq_satake_of_place_above : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra E M] [IsScalarTower E M Ω] (l : ℕ) [Fact l.Prime] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (u : HeightOneSpectrum (𝓞 M)) (h : IsPlaceOver A w) (h' : IsPlaceOver A u) [u.asIdeal.LiesOver w.asIdeal], ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), π.IsLocComp w σ → ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport (algNorm σ).rep (chars ξ hξ) → Unlinked (chars ξ hξ) → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ P : CuspSub M n, CharLift π P → (∀ j (x : (u.adicCompletion M)ˣ), Valued.v (x : u.adicCompletion M) = 1 → (ξ j * absPow (w.adicCompletion E) (-((((1 : ℝ) - n) / 2 : ℝ) : ℂ))) (GlobalTheory.BCChar.normU w u x) = 1) → ∃ B : Multiset ℂˣ, (CG.mk P).HasSat u B ∧ ∀ (g₀ : Weil h) (g' : Weil h'), (∀ z : Ω, (g₀ : G E Ω) z = (g' : G M Ω) z) → (satWD h' n B).charPol g' = ∏ j, (X - C ((ξ j (a g₀) : ℂˣ) : ℂ)) := by
  first | (exact @GlobalTheory.RoadU.TorLift.hasSat_charPol_above) | (exact GlobalTheory.RoadU.TorLift.hasSat_charPol_above) | (intros; apply GlobalTheory.RoadU.TorLift.hasSat_charPol_above  <;> assumption)

end
