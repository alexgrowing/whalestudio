import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PrimitiveNonSym
open GlobalTheory.PrimitiveOverField GlobalTheory.CechPic GlobalTheory.AbLaw GlobalTheory.UU

theorem exists_point_translate_of_ample : ∀ (A : Type) [Field A] [IsAlgClosed A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L O : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∃ t : LB.Gen (Theta B L), t.IsGen) → O.IsLB → (∃ u : LB.Gen (abelian₂ B O), u.IsGen) → ∃ x : 𝟙_ _ ⟶ B, LBIso O (LB.LinComb L (K := Fin 2) ![((toUnit B ≫ x) * 𝟙 B).left, 𝟙 B.left] ![1, -1]) := by
  intro K _ _ B _ _ g L O hB _ hLl _ hK hΘ hO hu
  by_contra hno
  have := hB.smooth
  have := hB.proper
  have hpr : IsProjBy B.hom := GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme K B hB
  have hproj : ∀ (R : Type) [CommRing R] (u : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (X : Scheme.{0})
      (π : X ⟶ B.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f B.hom u → IsProjBy f :=
    fun R _ u X π f h => GlobalTheory.StabFlat.isProjBy_baseChange hpr h
  have lamO : lam (cls O hO) (fst B B) (snd B B) = 0 :=
    (cls_cube_two hO _ _ (LB.isLB_linComb hO _ _)).symm.trans ((cls_eq_zero_iff _).2 hu)
  obtain ⟨F, hF, eF⟩ := cls_surj (lam (cls L hLl) (fst B B) (snd B B) -
    CechPic.pull (snd B B).left (cls O hO))
  have hpq : IsPullback (fst B B).left (snd B B).left B.hom B.hom := IsPullback.of_hasPullback _ _
  have cst_left : ∀ x : 𝟙_ _ ⟶ B, (toUnit B ≫ x).left = B.hom ≫ x.left := fun x =>
    congrArg (· ≫ x.left) ((Category.comp_id _).symm.trans (Over.w (toUnit B)))
  have s₁ : ∀ x : 𝟙_ _ ⟶ B, cls _ (pull_isLB hF (lift (toUnit B ≫ x) (𝟙 B)).left) =
      lam (cls L hLl) (toUnit B ≫ x) (𝟙 B) - cls O hO := fun x => by
    rw [cls_pull hF, eF, map_sub, pull_lam, ← pull_comp, ← Over.comp_left, lift_fst, lift_snd, Over.id_left, pull_id]
  have s₂ : ∀ x : 𝟙_ _ ⟶ B, cls _ (pull_isLB hF (lift (𝟙 B) (toUnit B ≫ x)).left) =
      lam (cls L hLl) (toUnit B ≫ x) (𝟙 B) := fun x => by
    rw [cls_pull hF, eF, map_sub, pull_lam, ← pull_comp, ← Over.comp_left, lift_fst, lift_snd, pull_const, sub_zero,
      lam_comm]
  have total : Ac ((fst B B).left ≫ B.hom) F := by
    refine (GlobalTheory.T.lineBundle_product_acyclic_of_affine_base_acyclic K _ _ _ _ _ _ _ hpq inferInstance inferInstance inferInstance inferInstance F hF).1
      fun R _ t Y π f h ht => ac_of_slices hproj hpq h hF fun x hx _ => ?_
    let x' : 𝟙_ _ ⟶ B := Over.homMk x hx
    refine ⟨(lift (toUnit B ≫ x') (𝟙 B)).left, ?_, ?_, ac_of_primitive hB hpr (pull_isLB hF _) ?_ ?_⟩
    · exact (congrArg CommaMorphism.left (lift_fst (toUnit B ≫ x') (𝟙 B))).trans (cst_left x')
    · exact congrArg CommaMorphism.left (lift_snd (toUnit B ≫ x') (𝟙 B))
    · rw [s₁, lam_sub, lam_lam hLl hΘ, lamO, sub_zero]
    · rw [s₁, sub_ne_zero, lam_const]
      refine fun e => hno ⟨x', (cls_eq_iff hO (LB.isLB_linComb hLl _ _)).1 (e.symm.trans ?_)⟩
      refine Eq.trans ?_ (cls_linComb hLl _ _ _).symm
      rw [Fin.sum_univ_two, sub_eq_add_neg]
      exact (congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)).symm
  rw [hpq.w] at total
  let o : Spec (CommRingCat.of K) ⟶ B.left := η[B].left
  have ho : o ≫ B.hom = 𝟙 _ := Over.w η[B]
  have hcl : IsClosed ({o (IsLocalRing.closedPoint K)} : Set B.left) := by
    have : IsClosedImmersion (o ≫ B.hom) := by rw [ho]; infer_instance
    have : IsClosedImmersion o := IsClosedImmersion.of_comp o B.hom
    have h := o.isClosedEmbedding.isClosedMap {IsLocalRing.closedPoint K}
      (by rw [show ({IsLocalRing.closedPoint K} : Set (Spec (CommRingCat.of K))) = Set.univ from
        Set.eq_univ_of_forall fun z => Subsingleton.elim (α := PrimeSpectrum K) _ _]; exact isClosed_univ)
    exact (congrArg IsClosed Set.image_singleton).mp h
  have all := (GlobalTheory.T.lineBundle_product_acyclic_of_affine_base_acyclic K _ _ _ _ _ _ _ hpq.flip inferInstance inferInstance inferInstance inferInstance F hF).2
    _ hcl (fun R _ t Y π f h ht hne => ac_of_slices hproj hpq.flip h hF fun x hx hr => by
      let x' : 𝟙_ _ ⟶ B := Over.homMk x hx
      refine ⟨(lift (𝟙 B) (toUnit B ≫ x')).left, ?_, ?_, ac_of_primitive hB hpr (pull_isLB hF _) ?_ ?_⟩
      · exact (congrArg CommaMorphism.left (lift_snd (𝟙 B) (toUnit B ≫ x'))).trans (cst_left x')
      · exact congrArg CommaMorphism.left (lift_fst (𝟙 B) (toUnit B ≫ x'))
      · rw [s₂, lam_lam hLl hΘ]
      · rw [s₂]
        intro e
        have e₁ : x' = η[B] := (eq_one_of_lam_eq_zero hLl hK x' e).trans (by
          rw [Hom.one_def, toUnit_unit, Category.id_comp])
        have e₂ : x = o := congrArg CommaMorphism.left e₁
        obtain ⟨y, hy⟩ := hr (IsLocalRing.closedPoint K)
        exact hne y (e₂ ▸ hy)) total
  have hs := ac_slice hproj hpq.flip hF all o ho (lift (𝟙 B) (toUnit B ≫ η[B])).left
    ((congrArg CommaMorphism.left (lift_snd (𝟙 B) (toUnit B ≫ η[B]))).trans (cst_left η[B]))
    (congrArg CommaMorphism.left (lift_fst (𝟙 B) (toUnit B ≫ η[B])))
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : Nonempty B.left := ⟨o (IsLocalRing.closedPoint K)⟩
  exact not_ac_of_cls_eq_zero _ (pull_isLB hF _) ((s₂ _).trans (lam_one_left _ _)) hs

end GlobalTheory.PrimitiveNonSym
