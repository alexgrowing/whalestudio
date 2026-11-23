import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProjStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSec
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueExpansionSectionAdmissibleBase

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecLift
open GlobalTheory.CompleteBaseExpansion

theorem exists_lift : ∀ (A A' S : Type) [CommRing A] [CommRing A'] [CommRing S] (g' : A →+* A') (g : A →+* S), (∀ (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) A) (D₁ : Matrix (Fin c) (Fin b) A), D₁ * D₀ = 0 → (∀ w : Fin b → S, (D₁.map g).mulVec w = 0 → ∃ v, (D₀.map g).mulVec v = w) → ∀ v' : Fin a → A', (D₀.map g').mulVec v' = 0 → ∃ v, D₀.mulVec v = 0 ∧ ∀ k, g' (v k) = v' k) → ∀ (X X' XS : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of A')) (fS : XS ⟶ Spec (CommRingCat.of S)) (β : X' ⟶ X) (σ : XS ⟶ X), Smooth f → IsProjBy f → IsPullback β f' f (Spec.map (CommRingCat.ofHom g')) → IsPullback σ fS f (Spec.map (CommRingCat.ofHom g)) → ∀ (W : Scheme.{0}) (L : LB W) (K : Type) [Fintype K] (φ : K → (X ⟶ W)) (φ' : K → (X' ⟶ W)) (ε : K → ℤ), L.IsLB → (∀ k, β ≫ φ k = φ' k) → FirstCohomologyVanishes ((LB.LinComb L φ ε).pull σ) → ∀ s' : LB.Sec (LB.LinComb L φ' ε), ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ z J, Good L z J → sval s β z J = sval s' (𝟙 _) z J := by
  intro A A' S _ _ _ g' g hlift X X' XS f f' fS β σ hs hp pb' pbS W L K _ φ φ' ε hL hφ hH s'
  obtain rfl : (fun k => β ≫ φ k) = φ' := funext hφ
  have hN := DVR.linComb_isLB L hL φ ε
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj A X f hs hp _ hN
  have pb₀ : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id A))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E₀, H₀⟩ := P.sec A (RingHom.id A) X (𝟙 _) f pb₀
  obtain ⟨E, H⟩ := P.sec A' g' X' β f' pb'
  obtain ⟨t', ht'⟩ := exists_in (φ := φ) β s'
  obtain ⟨v, hv, hv'⟩ := hlift P.a P.b P.c P.D₀ P.D₁ P.comp (P.exact S g XS σ fS pbS hH) _ (E.symm t').2
  have hv₀ : (P.D₀.map (RingHom.id A)).mulVec v = 0 := hv
  have hs' := (GlobalTheory.SecAlg.sval_eq_iff (P := P) hN H₀ H g' (RingHom.comp_id _) β (Category.comp_id _) pb'.w
    (E₀ ⟨v, hv₀⟩) t').2 (fun k => by rw [E₀.symm_apply_apply]; exact hv' k)
  obtain ⟨s₁, hs₁⟩ := exists_out (𝟙 _) (E₀ ⟨v, hv₀⟩)
  obtain ⟨s, hs⟩ := exists_sec hL (φ' := φ) (ε' := ε) (fun U _ h => by simp only [Category.id_comp]) s₁
  refine ⟨s, fun z J hJ => (hs _ _ z J hJ).trans ((hs₁ _ _ z _ (hJ.mem _ _)).trans ?_)⟩
  have hG : Good (LB.LinComb L φ ε) z (fun ψ i => J (ψ ≫ φ i)) := fun ψ => hJ.mem _ ψ
  refine Eq.trans ?_ ((hs' z _ hG).trans ((ht' _ _ z _ (hG.mem (fun _ : PUnit => β) _)).trans ?_))
  · exact (sval_of (E₀ ⟨v, hv₀⟩) _ z _ _ (fun _ => funext fun i => congrArg J (Category.assoc _ _ _))).symm
  · exact (sval_of s' _ z J _ (fun i => congrArg J (Category.assoc _ _ _).symm)).symm

end GlobalTheory.SecLift
