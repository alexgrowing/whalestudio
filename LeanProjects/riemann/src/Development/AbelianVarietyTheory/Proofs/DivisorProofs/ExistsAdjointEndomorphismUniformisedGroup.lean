import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianExtensionOverNormalBase
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdjointEndomorphismsCubeLBOfDenseFibres
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.TrivLocusFlat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GroupAdjoint

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem exists_adjoint {K : Type} [CommRing K] (Q : PolAV (Sp K)) (f : Q.A ⟶ Q.A) [IsMonHom f] :
    ∃ x : Q.A ⟶ Q.A, IsMonHom x ∧ ∀ (Y : Over (Sp K)) (a b : Y ⟶ Q.A),
      lam (cls Q.L Q.isLB) (a ≫ f) b = lam (cls Q.L Q.isLB) a (b ≫ x) := by
  have := Q.isAb.comm
  have hd : IsDual Q.A Q.A (abelian₂ Q.A Q.L) := CompanionTheory.PfDual.kTrivDual K Q.A Q.g Q.isAb Q.smoothDim Q.L Q.isLB Q.ktriv
  have hΛ : (abelian₂ Q.A Q.L).IsLB := hd.isLB
  have e : ∀ (Y : Over (Sp K)) (a b : Y ⟶ Q.A), evc hΛ a b = lam (cls Q.L Q.isLB) a b := fun Y a b ↦ by
    rw [evc, show cls _ hΛ = lam (cls Q.L Q.isLB) (fst Q.A Q.A) (snd Q.A Q.A) from
      cls_cube_two Q.isLB _ _ hΛ, pull_lam, lift_fst, lift_snd]
  have l₁ : ∀ (Y : Over (Sp K)) (a a' b : Y ⟶ Q.A), evc hΛ (a * a') b = evc hΛ a b + evc hΛ a' b :=
    (isAdditive_iff hΛ).1 hd.additive
  have l₂ : ∀ (Y : Over (Sp K)) (a b b' : Y ⟶ Q.A), evc hΛ a (b * b') = evc hΛ a b + evc hΛ a b' := fun Y a b b' ↦ by
    rw [e, e, e, lam_comm, lam_comm _ a b, lam_comm _ a b', ← e, ← e, ← e]
    exact l₁ _ _ _ _
  have a₂ : IsAdditive (swap (abelian₂ Q.A Q.L)) := (BirigidLift.isAdditive_swap_iff hΛ).2 l₂
  have hM := pull_isLB hΛ (lift (fst Q.A Q.A ≫ f) (snd Q.A Q.A)).left
  have m : ∀ (Y : Over (Sp K)) (a b : Y ⟶ Q.A), evc hM a b = evc hΛ (a ≫ f) b := fun Y a b ↦ by
    rw [evc_ev hΛ]
    simp only [lift_fst_assoc, lift_snd]
  obtain ⟨x, hx, ex⟩ := BirigidLift.exists_hom hd a₂ hM
    ((isAdditive_iff hM).2 fun Y u u' t ↦ by rw [m, m, m, MonObj.mul_comp, l₁])
    ((BirigidLift.isAdditive_swap_iff hM).2 fun Y u t t' ↦ by rw [m, m, m, l₂])
  refine ⟨x, hx, fun Y a b ↦ ?_⟩
  rw [← e, ← e, ← m]
  exact BirigidLift.evc_of_cls hd.isLB hM ex a b

theorem exists_adjoint_on_group : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ g : G ⟶ G, IsMonHom g → ∃ g' : G ⟶ G, IsMonHom g' ∧ LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) := by
  intro R _ _ _ hR D A G _ _ hG U g hg
  have hN : IsNoetherianRing R := hR.1.1
  have hI : IsIntegrallyClosed R := hR.1.2.2.1
  have := U.gen_hom
  have hL := U.LG.isLB
  have hp := isGrpPullback_pullback G (jK R)
  obtain ⟨x, hx, ex⟩ := exists_adjoint A (U.gen.inv ≫ (Over.pullback (jK R)).map g ≫ U.gen.hom)
  have hj : GlobalTheory.IsGenericPointHom (S := Sp R) (jK R) := .fractionField R (FractionRing R)
  obtain ⟨g', ⟨hg', eg'⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.of_isGenericPointHom
    (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec R) hj hG hG (U.gen.hom ≫ x ≫ U.gen.inv)
  refine ⟨g', hg', ?_⟩
  have := hG.smooth
  have := hG.geomConnected
  have := GlobalTheory.smooth_tensorObj_hom G G
  have := GlobalTheory.geometricallyIntegral_tensorObj_hom G G
  have h₁ : (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L).IsLB := LB.isLB_linComb hL _ _
  have h₂ : (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L).IsLB := LB.isLB_linComb hL _ _
  refine GlobalTheory.T.lineBundleIso_of_generic_normal_local_base R (G ⊗ G) (1 : 𝟙_ _ ⟶ G ⊗ G).left (Over.w _) _ _ h₁ h₂ ?_
  refine (cls_eq_iff (pull_isLB h₁ _) (pull_isLB h₂ _)).1 ?_

  have ec : pull U.gen.hom.left (cls A.L A.isLB) = pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL) := by
    rw [← cls_pull A.isLB _ (pull_isLB A.isLB _), ← cls_pull hL _ (pull_isLB hL _)]
    exact (cls_eq_iff _ _).2 U.ext
  have key : ∀ a b : G ⊗ G ⟶ G, pull (pullback.fst (G ⊗ G).hom (jK R)) (lam (cls U.LG.L hL) a b) =
      lam (cls A.L A.isLB) ((Over.pullback (jK R)).map a ≫ U.gen.hom) ((Over.pullback (jK R)).map b ≫ U.gen.hom) := by
    intro a b
    rw [← lam_pull, ec, lam_pull_of_isGrpPullback hp]
    refine GlobalTheory.CompanionTheory.DualScheme.pull_lam_of_left (T' := Over.mk (_ ≫ jK R)) _ _ ?_ ?_
    · exact (ExtUnique.pullback_map_left_fst (jK R) a).symm
    · exact (ExtUnique.pullback_map_left_fst (jK R) b).symm
  rw [cls_pull h₁, cls_pull h₂, cls_cube_two hL, cls_cube_two hL, key, key, Functor.map_comp, Functor.map_comp, eg']
  have := ex _ ((Over.pullback (jK R)).map (fst G G) ≫ U.gen.hom) ((Over.pullback (jK R)).map (snd G G) ≫ U.gen.hom)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using this

end GlobalTheory.Mum.GroupAdjoint
