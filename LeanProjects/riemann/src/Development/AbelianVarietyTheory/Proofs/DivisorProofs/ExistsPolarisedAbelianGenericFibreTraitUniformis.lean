import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAV
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamilyFibreEqUniformisedPullbackGenericFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointRepresentingWeightMumfordQuotient
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TraitGeneric

theorem exists_polAV_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → UnifTrait D G P.L.L →
    ∃ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom ∧
      LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) := by
  intro R _ _ _ _ D G _ _ P _ hU
  obtain ⟨W, _, _, _, φ, G', _, _, β, D', A', U', -, hinj, -, hGP, hLβ, -⟩ := hU
  have hnz : nonZeroDivisors R ≤ (nonZeroDivisors W).comap φ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hinj
  let ga : FractionRing R →+* FractionRing W := IsLocalization.map (FractionRing W) φ hnz
  have hga : ga.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ :=
    IsLocalization.map_comp hnz
  have hsq : jK W ≫ spMap φ = spMap ga ≫ jK R := by
    simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hga]
  let GK := (Over.pullback (jK R)).obj G
  let L : LB GK.left := P.L.L.pull (pullback.fst G.hom (jK R))
  have hL : L.IsLB := pull_isLB P.L.isLB _
  have hS : Out.Sym GK L :=
    GlobalTheory.PolBaseChange.sym_pull (isGrpPullback_pullback G (jK R)) (GlobalTheory.WtPoint.sym_of_cp P)
  have := U'.gen_hom
  set ψ₀ := U'.gen.inv.left ≫ pullback.fst G'.hom (jK W) with hψ₀
  have g₀ : IsGrpPullback A'.A G' (jK W) ψ₀ := by
    have : IsMonHom U'.gen.symm.hom := by show IsMonHom U'.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso U'.gen.symm).comp (isGrpPullback_pullback G' (jK W))).congr
      (Category.id_comp _) rfl
  have g₁ : IsGrpPullback A'.A G (spMap ga ≫ jK R) (ψ₀ ≫ β) := (g₀.comp hGP).congr hsq rfl
  have gb := isGrpPullback_pullback G (jK R)
  have w₁ : (ψ₀ ≫ β) ≫ G.hom = (A'.A.hom ≫ spMap ga) ≫ jK R :=
    g₁.1.w.trans (Category.assoc _ _ _).symm
  obtain ⟨α, e₁, e₂⟩ : ∃ α : A'.A.left ⟶ GK.left, α ≫ pullback.fst G.hom (jK R) = ψ₀ ≫ β ∧
      α ≫ GK.hom = A'.A.hom ≫ spMap ga :=
    ⟨gb.1.lift _ _ w₁, gb.1.lift_fst _ _ _, gb.1.lift_snd _ _ _⟩
  have gα : IsGrpPullback A'.A GK (spMap ga) α := gb.cancel (g₁.congr rfl e₁.symm) e₂
  have hgi : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hext : LBIso (A'.L.pull U'.gen.hom.left) (U'.LG.L.pull (pullback.fst G'.hom (jK W))) := U'.ext
  have h1 : LBIso (A'.L.pull (U'.gen.inv.left ≫ U'.gen.hom.left)) (U'.LG.L.pull ψ₀) :=
    LBIso.chartPull (Geo.Tor.chartPullSame A'.L _ (fun _ => U'.gen.hom.left) _ U'.gen.inv.left fun _ => rfl)
      (Geo.Tor.chartPullSame U'.LG.L _ (fun _ => pullback.fst G'.hom (jK W)) _ U'.gen.inv.left fun _ => rfl) hext
  have l₁ : LBIso A'.L (U'.LG.L.pull ψ₀) :=
    LBIso.chartPull (Geo.Tor.chartPullUnpull A'.L _ hgi)
      (Geo.Tor.chartPullSame U'.LG.L _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h1
  have l₂ : LBIso (U'.LG.L.pull ψ₀) (P.L.L.pull (ψ₀ ≫ β)) := GlobalTheory.Ex.GenericFibre.lbIso_pull hLβ ψ₀ rfl
  have l₃ : LBIso (L.pull α) (P.L.L.pull (ψ₀ ≫ β)) :=
    GlobalTheory.Ex.GenericFibre.lbIso_pull (GlobalTheory.PolBaseChange.lbIso_refl hL) α e₁.symm
  have hw : LBIso A'.L (L.pull α) :=
    LBIso.trans A'.isLB (pull_isLB P.L.isLB _) (pull_isLB hL _)
      (LBIso.trans A'.isLB (pull_isLB U'.LG.isLB _) (pull_isLB P.L.isLB _) l₁ l₂) l₃.symm
  exact GlobalTheory.PolFieldDescent.exists_polAV _ _ ga GK L hL hS A' α gα hw

end GlobalTheory.Mum.TraitGeneric
