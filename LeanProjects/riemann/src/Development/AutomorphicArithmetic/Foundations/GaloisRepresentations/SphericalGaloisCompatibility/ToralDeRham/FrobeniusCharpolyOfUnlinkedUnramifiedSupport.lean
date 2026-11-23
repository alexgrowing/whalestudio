import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIsPlaceOverFiniteExtensionOfIsPlaceOverStatement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.WeaklyAttachedToralOfCmLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedCompNormOfKilledInertiaFixingStatement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.FrobeniusCharpolyEqSatakeOfPlaceAbove
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.Chl

open GlobalTheory.RoadU

namespace GalTw
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU

theorem liesOver_of_isPlaceOver {E M Ω : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Field Ω]
    [Algebra E Ω] [Algebra M Ω] [Algebra E M] [IsScalarTower E M Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} {u : HeightOneSpectrum (𝓞 M)} (h : IsPlaceOver A w) (h' : IsPlaceOver A u) :
    u.asIdeal.LiesOver w.asIdeal := by
  refine ⟨Ideal.ext fun x => ?_⟩
  rw [Ideal.under, Ideal.mem_comap, ← h x, ← h' _]
  have : algebraMap M Ω ((algebraMap (𝓞 E) (𝓞 M) x : 𝓞 M) : M) = algebraMap E Ω (x : E) := by
    rw [IsScalarTower.algebraMap_apply E M Ω]
    rfl
  rw [this]

theorem exists_sph_lift_of_toral : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r → ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), π.IsLocComp w σ → ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport (algNorm σ).rep (chars ξ hξ) → Unlinked (chars ξ hξ) → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ g : Weil h, deg g ≠ 0 → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω) (u : HeightOneSpectrum (𝓞 M)) (h' : IsPlaceOver A u) (P : CuspSub M n) (χ' : HChar (maximalRealSubfield M)), InScope .all l P χ' ∧ IsLift π P ∧ (∀ x : M, (g : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) ∧ ∃ B : Multiset ℂˣ, (CG.mk P).HasSat u B ∧ ∀ (g₀ : Weil h) (g' : Weil h'), (∀ z : Ω, (g₀ : G E Ω) z = (g' : G M Ω) z) → (satWD h' n B).charPol g' = ∏ j, (X - C ((ξ j (a g₀) : ℂˣ) : ℂ)) := by
  intro hI Ω _ E _ _ _ _ _ l _ ι n hn π χ hπ r hr w A h σ hσ ξ hξ hsupp hunl a ha g hg
  let ξ₀ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ) := fun j =>
    ξ j * absPow (w.adicCompletion E) (-((((1 : ℝ) - n) / 2 : ℝ) : ℂ))
  have hξ₀ : ∀ j, IsSmoothChar (ξ₀ j) := fun j => (hξ j).mul (isSmoothChar_absPow _)
  obtain ⟨M, _, _, _, _, _, _, _, P, χ', hP, hcl, hfix, hkill⟩ :=
    GlobalTheory.T.weaklyAttached_toral_of_cm_lift hI Ω E l ι n hn π χ hπ r hr w A h ξ₀ hξ₀ a ha g hg
  obtain ⟨u, h', -⟩ := GlobalTheory.T.exists_isPlaceOver_finiteExtension_of_isPlaceOver E M Ω A w h
  haveI := liesOver_of_isPlaceOver (M := M) h h'
  have hunr := GlobalTheory.T.unramified_comp_norm_of_killed_inertia_fixing Ω E M A w u h h' n ξ₀ a ha hkill
  obtain ⟨B, hB, hch⟩ :=
    GlobalTheory.T.frobenius_charpoly_eq_satake_of_place_above hI Ω E M l n hn π χ hπ A w u h h' σ hσ ξ hξ hsupp hunl a ha P hcl hunr
  exact ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    u, h', P, χ', hP, hcl.1, hfix, B, hB, hch⟩

end GlobalTheory.RoadU

end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.T.frobenius_charpoly_of_unlinked_unramified_support : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r → ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), π.IsLocComp w σ → ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport (algNorm σ).rep (chars ξ hξ) → Unlinked (chars ξ hξ) → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ g : Weil h, deg g ≠ 0 → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω) (u : HeightOneSpectrum (𝓞 M)) (h' : IsPlaceOver A u) (P : CuspSub M n) (χ' : HChar (maximalRealSubfield M)), InScope .all l P χ' ∧ IsLift π P ∧ (∀ x : M, (g : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) ∧ ∃ B : Multiset ℂˣ, (CG.mk P).HasSat u B ∧ ∀ (g₀ : Weil h) (g' : Weil h'), (∀ z : Ω, (g₀ : G E Ω) z = (g' : G M Ω) z) → (satWD h' n B).charPol g' = ∏ j, (X - C ((ξ j (a g₀) : ℂˣ) : ℂ)) := by
  first | (exact @GlobalTheory.RoadU.exists_sph_lift_of_toral) | (exact GlobalTheory.RoadU.exists_sph_lift_of_toral) | (intros; apply GlobalTheory.RoadU.exists_sph_lift_of_toral  <;> assumption)

end
