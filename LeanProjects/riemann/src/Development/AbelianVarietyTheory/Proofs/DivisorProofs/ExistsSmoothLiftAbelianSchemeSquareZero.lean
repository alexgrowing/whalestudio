import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroAugmentedAlgebra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchemePresentingSquareZeroSmoothLiftSystem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothLiftOfSquareZeroLiftSystemPresents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySmoothLiftPresystemSquareZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegreeTwoObstructionClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeTwoObstructionClassNaturalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctorialLiftsOfObstructionTwoZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySquareZeroSmoothLiftSystemOfIsFunStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Obs.exists_smooth_lift_of_abelian : FormSt → PrimitiveExtendedDegTwoVanish → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (A₀ : Over (Sp R₀)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∃ (X : Over (Sp R)) (i : A₀.left ⟶ X.left), IsPullback i A₀.hom X.hom (spMap π) ∧ Smooth X.hom := by
  intro hF hP R R₀ _ _ I hI π hπ hk A₀ _ g hab hsm
  haveI := hsm
  haveI : Smooth A₀.hom := SmoothOfRelativeDimension.smooth g _
  haveI : Smooth (A₀ ⊗ A₀).hom := inferInstanceAs (Smooth (Limits.pullback.fst A₀.hom A₀.hom ≫ A₀.hom))
  obtain ⟨R₁, _, _, ⟨α⟩⟩ := GlobalTheory.Obs.exists_aug R R₀ I hI π hπ hk
  obtain ⟨hPar, hProj, hadd⟩ := hF R₀ A₀ g hab hsm
  obtain ⟨L⟩ := GlobalTheory.T.nonempty_smoothLiftPresystem_squareZero R R₀ I hI π hπ hk _ (OAff A₀.hom) (fun T ↦ smooth_sec_affine A₀.hom T.unop)
  obtain ⟨L₂⟩ := GlobalTheory.T.nonempty_smoothLiftPresystem_squareZero R R₀ I hI π hπ hk _ (OAff (A₀ ⊗ A₀).hom)
    (fun T ↦ smooth_sec_affine (A₀ ⊗ A₀).hom T.unop)
  have key : ∀ w, L.IsOb2 α w 0 := by
    intro w
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_degreeTwoObstructionClass R R₀ I hI π hπ hk R₁ α _ _ L w
    have nat : ∀ (f : A₀ ⊗ A₀ ⟶ A₀) (w' : GlobForm (A₀ ⊗ A₀).hom) (c' : CatCoh.H2 (ext R₁ (OAff (A₀ ⊗ A₀).hom))),
        IsPullForm (overW f) w w' → L₂.IsOb2 α w' c' → IsExtendedPullbackDegTwo R₁ (overW f) c c' := by
      intro f w' c' hw hc'
      refine GlobalTheory.T.degreeTwoObstructionClass_natural R R₀ I hI π hπ hk R₁ α _ (OAff A₀.hom) _ (OAff (A₀ ⊗ A₀).hom) _ (pairFst f.left)
        (pairPull (overW f)) L L₂ w w' c c' (fun T ↦ ?_) hc hc'
      exact (congrArg (fun z : Glob1 (OPair f.left (A₀ ⊗ A₀).hom) ↦ z.1 T) hw).trans
        (cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff (A₀ ⊗ A₀).hom) (pairFst f.left) T _)
    obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.exists_degreeTwoObstructionClass R R₀ I hI π hπ hk R₁ α _ _ L₂ (pullForm (overW (fst A₀ A₀)) w)
    obtain ⟨c₂, hc₂⟩ := GlobalTheory.T.exists_degreeTwoObstructionClass R R₀ I hI π hπ hk R₁ α _ _ L₂ (pullForm (overW (snd A₀ A₀)) w)
    have hm : pullForm (overW μ[A₀]) w = pullForm (overW (fst A₀ A₀)) w + pullForm (overW (snd A₀ A₀)) w :=
      hadd w _ _ _ (isPullForm_pullForm _ w) (isPullForm_pullForm _ w) (isPullForm_pullForm _ w)
    have hcm : L₂.IsOb2 α (pullForm (overW μ[A₀]) w) (c₁ + c₂) := by
      rw [hm]; exact isOb2_add R R₀ I hI π hπ hk R₁ α _ _ L₂ _ _ c₁ c₂ hc₁ hc₂
    have h0 : c = 0 := hP R₀ R₁ α.q α.sq A₀ g hab hsm c c₁ c₂
      (nat _ _ _ (isPullForm_pullForm _ w) hcm) (nat _ _ _ (isPullForm_pullForm _ w) hc₁)
      (nat _ _ _ (isPullForm_pullForm _ w) hc₂)
    rw [← h0]; exact hc
  obtain ⟨L', hL'⟩ := GlobalTheory.T.exists_functorial_lifts_of_obstructionTwo_zero R R₀ I hI π hπ hk R₁ α _ A₀.hom hPar hProj L key
  obtain ⟨S⟩ := GlobalTheory.T.nonempty_squareZeroSmoothLiftSystem_of_isFun R R₀ I hI π hπ hk _ A₀.hom L' hL'
  obtain ⟨X, s, i, hci, hsi, ⟨hpres⟩⟩ := GlobalTheory.LiftGlue.exists_presents R R₀ I hI π hπ hk _ A₀.hom S
  obtain ⟨hpb, hsmooth⟩ := GlobalTheory.LiftSys.presents_isLift R R₀ I hI π hπ hk _ A₀.hom S X s i hci hsi hpres
  exact ⟨Over.mk s, i, hpb, hsmooth⟩
