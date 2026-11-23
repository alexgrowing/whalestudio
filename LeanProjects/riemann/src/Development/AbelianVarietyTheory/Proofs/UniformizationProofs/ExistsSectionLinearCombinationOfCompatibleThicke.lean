import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueExpansionSectionAdmissibleBase
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSec

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SecAlgLinComb
open GlobalTheory.CompleteBaseExpansion GlobalTheory.BaseExpansionExists

theorem exists_sec_linComb : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ (W : Scheme.{0}) (L : LB W) (K : Type) [Fintype K] (φ : K → (Y.left ⟶ W)) (ε : K → ℤ) (φ' : ∀ e, K → ((thickObj R I e Y).left ⟶ W)), L.IsLB → (∀ e k, pullback.fst Y.hom (thick R I e) ≫ φ k = φ' e k) → ∀ f : ∀ e, LB.Sec (LB.LinComb L (φ' e) ε), (∀ e z J, Good L z J → sval (f (e + 1)) (thickMap R I e Y) z J = sval (f e) (𝟙 _) z J) → ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e Y).left) (z : Z) (J), Good L z J → sval s (r ≫ pullback.fst Y.hom (thick R I e)) z J = sval (f e) r z J := by
  intro R _ _ I hI Y hsm hp W L K _ φ ε φ' hL hφ f hf
  obtain rfl : φ' = fun e k => (fstG I e Y).left ≫ φ k := funext fun e => funext fun k => (hφ e k).symm
  choose f' hf' using fun e => exists_in (φ := φ) (fstG I e Y).left (f e)
  obtain ⟨s', hs', -⟩ := GlobalTheory.SecAlg.existsUnique_sec R I hI Y hsm hp _ (DVR.linComb_isLB _ hL _ _) f'
    fun e z J hJ => by
      refine (hf' _ _ _ z _ (hJ.mem (fun _ : PUnit => (fstG I (e + 1) Y).left) _)).trans
        (Eq.trans ?_ (hf' _ _ _ z _ (hJ.mem (fun _ : PUnit => (fstG I e Y).left) _)).symm)
      have E : thickMap R I e Y ≫ (fstG I (e + 1) Y).left = 𝟙 _ ≫ (fstG I e Y).left :=
        ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).trans (Category.id_comp _).symm
      beta_reduce
      rw [E]
      exact gs_eq_of_sval hL _ _ _ _ (fun i => (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ φ i) E).trans (Category.assoc _ _ _))) z (hf e z) _
        (pull_le _ _ (hJ.mem (fun _ : PUnit => (fstG I e Y).left) _))
  obtain ⟨s₁, hs₁⟩ := exists_out (𝟙 _) s'
  obtain ⟨s, hs⟩ := exists_sec hL (φ' := φ) (ε' := ε)
    (fun U _ h => by simp only [Category.id_comp]) s₁
  have key : ∀ e z J, Good L z J → sval s (fstG I e Y).left z J = sval (f e) (𝟙 _) z J := by
    refine fun e z J hJ => (hs _ _ z J hJ).trans ((hs₁ _ _ z _ (hJ.mem _ _)).trans ?_)
    have hN : Good (LB.LinComb L φ ε) z (fun ψ i => J (ψ ≫ φ i)) :=
      fun ψ => hJ.mem _ ψ
    refine Eq.trans ?_ ((hs' e z _ hN).trans
      ((hf' _ _ _ z _ (hN.mem (fun _ : PUnit => (fstG I e Y).left) _)).trans ?_))
    · exact (sval_of s' _ z _ _ (fun _ => funext fun i => congrArg J (Category.assoc _ _ _))).symm
    · exact (sval_of (f e) _ z J _ (fun i => congrArg J (Category.assoc _ _ _).symm)).symm
  refine ⟨s, fun e Z r z J hJ => (sval_eq_of_id (key e) r z hJ).trans ?_⟩
  exact congrArg (fun p => sval (f e) p z J) (Category.comp_id _)

end GlobalTheory.SecAlgLinComb
end
