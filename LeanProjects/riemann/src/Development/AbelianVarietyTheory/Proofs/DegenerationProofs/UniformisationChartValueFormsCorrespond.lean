import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.SameB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmResPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLiftUnitTensor
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpTOfExpandsAt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.LN.PreForm

theorem gs_comp_stalk {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (U : X.Opens) (hU : h (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ h) z U a = (r.stalkMap z).hom (gs h (r z) U a) := by
  rw [← gs_pull r h z U hU, gs_eq r z (h ⁻¹ᵁ U) hU, gs_eq h (r z) U hU]
  exact (Scheme.Hom.germ_stalkMap_apply r (h ⁻¹ᵁ U) z hU _).symm

theorem sval_comp_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval s (r ≫ h) z J = (r.stalkMap z).hom (sval s h (r z) (fun ψ => J (r ≫ ψ))) := by
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp_stalk r h z _ (Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)) _

theorem sval_eq_of_id {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y' ⟶ X)} {ε' : K' → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (h : Y' ⟶ Y)
    (H : ∀ y J, Good L y J → sval s' (𝟙 Y') y J = sval s h y J)
    (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    sval s' r z J = sval s (r ≫ h) z J := by
  have e := sval_comp_stalk s' (𝟙 Y') r z hJ
  rw [Category.comp_id] at e
  rw [e, sval_comp_stalk s h r z hJ, H (r z) (fun ψ => J (r ≫ ψ)) (fun ψ => hJ (r ≫ ψ))]

theorem under_iff_match {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    (U : PreU I D.toPre A G) (U₀ : UnifPre I D A G) : Under U U₀ ↔ Match U U₀ :=
  ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a.symm, b.symm, c.symm, d.symm, e.symm, f.symm⟩,
    fun ⟨a, b, c, d, e, f⟩ => ⟨a.symm, b.symm, c.symm, d.symm, e.symm, f.symm⟩⟩

theorem under_exists_and_expands : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → (∀ U₀ : UnifPre I D A G, ∃ U : PreU I D.toPre A G, Under U U₀) ∧ (∀ U : PreU I D.toPre A G, ∃ U₀ : UnifPre I D A G, Under U U₀) ∧ ∀ (U : PreU I D.toPre A G) (U₀ : UnifPre I D A G), Under U U₀ → ∀ (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D.toPre (𝟙_ _) k α) (σ₀ : H0 U₀.LG.L k) (f₀ : ∀ α, D.toPre.SecB k α), (∀ σ₁ : H0 U.P.L.L k, HEq σ₁ σ₀ → ∀ z J, Good U.P.L.L z J → sval σ (𝟙 _) z J = sval σ₁ (snd (𝟙_ _) G).left z J) → (∀ α z J, Good D.toPre.P.L z J → sval (f α) (𝟙 _) z J = sval (f₀ α) (snd (𝟙_ _) D.toPre.P.A).left z J) → (U.ExpT (𝟙_ _) k σ f ↔ ∀ e, U₀.ExpandsAt e k σ₀ f₀) := by
  intro hL _ R _ _ I D A G _ _ hG
  refine ⟨fun U₀ => ?_, fun U => ?_, fun U U₀ hU k σ f σ₀ f₀ hσ hf => ?_⟩
  · obtain ⟨w, hw⟩ := U₀.ext
    obtain ⟨U, hU, -⟩ := GlobalTheory.ValueForm.exists_preU_match hL.globalFns R I D A G U₀ hG w hw
    exact ⟨U, (under_iff_match U U₀).2 hU⟩
  · obtain ⟨U₀, hU⟩ := GlobalTheory.UU.ToChart.exists_match R I D A G U
    exact ⟨U₀, (under_iff_match U U₀).2 hU⟩
  · have hM := (under_iff_match U U₀).1 hU
    have ht : H0 U₀.LG.L k = H0 U.P.L.L k := by rw [hM.LG]
    have hc : HEq (cast ht σ₀) σ₀ := cast_heq ht σ₀
    have sG : SameG (cast ht σ₀) σ := fun Z r z J hJ => sval_eq_of_id _ _ _ (hσ _ hc) Z r z J hJ
    have sB : SameB f₀ f := fun α Z r z J hJ => sval_eq_of_id _ _ _ (hf α) Z r z J hJ
    exact ⟨expandsAt_of_expT R I D A G U U₀ hM k σ₀ _ σ f₀ f hc.symm sG sB,
      expT_of_expandsAt R I D A G U U₀ hM k σ₀ _ σ f₀ f hc.symm sG sB⟩

end GlobalTheory.LN.PreForm
end
