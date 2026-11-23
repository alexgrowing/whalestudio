import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableExtensionMultiplesOfSemistable
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSubgroupEqRangeOfLists
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.OActDescendOfGenerators

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.Spread

theorem eta_pullback_fst {S S' : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (j : S' ⟶ S)
    [IsCommMonObj ((Over.pullback j).obj G)] :
    η[(Over.pullback j).obj G].left ≫ pullback.fst G.hom j = j ≫ η[G].left := by
  simp
  first
  | (simp only [pullback.lift_fst]; rw [← Category.assoc, ← pullback.condition, Category.comp_id])
  | (erw [pullback.lift_fst]; rw [← Category.assoc, ← pullback.condition, Category.comp_id])

theorem eta_left_hom {S : Scheme.{0}} (G : Over S) [GrpObj G] :
    η[G].left ≫ G.hom = 𝟙 _ := by
  simpa using Over.w η[G]

theorem nonempty_algHom_of_finiteType (k C : Type) [Field k] [IsAlgClosed k] [CommRing C] [Nontrivial C]
    [Algebra k C] [Algebra.FiniteType k C] : Nonempty (C →ₐ[k] k) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal C
  letI : Field (C ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (C ⧸ m) := Algebra.FiniteType.trans (S := C) inferInstance inferInstance
  haveI : Module.Finite k (C ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (C ⧸ m)
  let e : k ≃ₐ[k] (C ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId k (C ⧸ m))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  exact ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m)⟩

private theorem pullback_mu_fst_eq {S S' : Scheme.{0}} (G : Over S) [GrpObj G] (j : S' ⟶ S) :
    μ[(Over.pullback j).obj G].left ≫ pullback.fst G.hom j =
      pullback.lift ((fst ((Over.pullback j).obj G) ((Over.pullback j).obj G)).left ≫ pullback.fst G.hom j)
        ((snd ((Over.pullback j).obj G) ((Over.pullback j).obj G)).left ≫ pullback.fst G.hom j)
        (by
          rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc]
          congr 1
          exact (Over.w (fst ((Over.pullback j).obj G) ((Over.pullback j).obj G))).trans
            (Over.w (snd ((Over.pullback j).obj G) ((Over.pullback j).obj G))).symm) ≫ μ[G].left := by
  simp
  erw [pullback.lift_fst]
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc]
    erw [Over.μ_pullback_left_fst_fst, pullback.lift_fst]
    try rfl
  · rw [Category.assoc]
    erw [Over.μ_pullback_left_fst_snd, pullback.lift_snd]
    try rfl

private theorem bcMap_comp_pullback_map {k₀ K : Type} [Field k₀] [Field K] [Algebra k₀ K] (R : Subalgebra k₀ K)
    {X Y : Over (Sp k₀)} (u : X ⟶ Y) :
    bcMap X.hom R.val ≫ ((Over.pullback (spMap (algebraMap k₀ R))).map u).left =
      ((Over.pullback (spMap (algebraMap k₀ K))).map u).left ≫ bcMap Y.hom R.val := by
  apply pullback.hom_ext
  · simp only [Category.assoc, GlobalTheory.ActDescent.pullback_map_left_fst, bcMap_fst_assoc, bcMap_fst]
  · have e1 : ((Over.pullback (spMap (algebraMap k₀ R))).map u).left ≫ pullback.snd Y.hom _ =
        pullback.snd X.hom _ := Over.w _
    have e2 : ((Over.pullback (spMap (algebraMap k₀ K))).map u).left ≫ pullback.snd Y.hom _ =
        pullback.snd X.hom _ := Over.w _
    rw [Category.assoc, e1, Category.assoc, bcMap_snd, bcMap_snd, ← Category.assoc, e2]

set_option maxHeartbeats 1000000 in

theorem exists_endo_spread_specialise : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K]
    (B : Over (Sp k₀)) [GrpObj B], IsAbelianScheme B →
    ∀ f : (Over.pullback (spMap (algebraMap k₀ K))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ K))).obj B,
    IsMonHom f → ∃ (R : Subalgebra k₀ K) (g : R →ₐ[k₀] k₀)
      (Ψ : (Over.pullback (spMap (algebraMap k₀ R))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ R))).obj B)
      (f₀ : B ⟶ B) (σ : B.left ⟶ pullback B.hom (spMap (algebraMap k₀ R))),
      IsMonHom Ψ ∧ IsMonHom f₀ ∧ GlobalTheory.Spread.bcMap B.hom R.val ≫ Ψ.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _ ∧
      σ ≫ pullback.fst _ _ = 𝟙 _ ∧ σ ≫ pullback.snd _ _ = B.hom ≫ spMap g.toRingHom ∧
      f₀.left = σ ≫ Ψ.left ≫ pullback.fst _ _ := by
  intro k₀ K _ _ _ _ B _ hB f hf
  have : IsCommMonObj B := hB.comm
  have : Smooth B.hom := hB.smooth
  have : IsProper B.hom := hB.proper
  have hw : f.left ≫ pullback.snd B.hom (spMap (algebraMap k₀ K)) = pullback.snd _ _ := Over.w f
  have hφ : (f.left ≫ pullback.fst B.hom (spMap (algebraMap k₀ K))) ≫ B.hom =
      pullback.fst B.hom (spMap (algebraMap k₀ K)) ≫ B.hom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
  obtain ⟨R, ψ, hRfg, hψ1, hψ2⟩ := exists_fg_comp_eq B.hom B.hom
    (f.left ≫ pullback.fst B.hom (spMap (algebraMap k₀ K))) hφ
  have hcond : ψ ≫ B.hom = pullback.snd B.hom (spMap (algebraMap k₀ R)) ≫ spMap (algebraMap k₀ R) := by
    rw [hψ1, pullback.condition]
  let Ψl : pullback B.hom (spMap (algebraMap k₀ R)) ⟶ pullback B.hom (spMap (algebraMap k₀ R)) :=
    pullback.lift ψ (pullback.snd _ _) hcond
  have hΨfst : Ψl ≫ pullback.fst _ _ = ψ := pullback.lift_fst _ _ _
  have hΨsnd : Ψl ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  let Ψ : (Over.pullback (spMap (algebraMap k₀ R))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ R))).obj B :=
    Over.homMk Ψl hΨsnd
  haveI : Algebra.FiniteType k₀ R := (Subalgebra.fg_iff_finiteType R).mp hRfg
  obtain ⟨g⟩ := nonempty_algHom_of_finiteType k₀ R
  have hgc : spMap g.toRingHom ≫ spMap (algebraMap k₀ R) = 𝟙 _ := by
    first
    | (rw [spMap_algHom_comp, Algebra.algebraMap_self]; simp [spMap])
    | (rw [spMap_algHom_comp]; simp [spMap])
  let σ : B.left ⟶ pullback B.hom (spMap (algebraMap k₀ R)) :=
    pullback.lift (𝟙 _) (B.hom ≫ spMap g.toRingHom)
      (by rw [Category.id_comp, Category.assoc, hgc, Category.comp_id])
  have hσfst : σ ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _
  have hσsnd : σ ≫ pullback.snd _ _ = B.hom ≫ spMap g.toRingHom := pullback.lift_snd _ _ _
  have hf0w : (σ ≫ Ψl ≫ pullback.fst _ _) ≫ B.hom = B.hom := by
    rw [hΨfst, Category.assoc, hψ1, ← Category.assoc, hσfst, Category.id_comp]
  let f₀ : B ⟶ B := Over.homMk (σ ≫ Ψl ≫ pullback.fst _ _) hf0w

  have hηR : η[(Over.pullback (spMap (algebraMap k₀ R))).obj B].left ≫ pullback.fst B.hom _ =
      spMap (algebraMap k₀ R) ≫ η[B].left := eta_pullback_fst B _
  have hηK : η[(Over.pullback (spMap (algebraMap k₀ K))).obj B].left ≫ pullback.fst B.hom _ =
      spMap (algebraMap k₀ K) ≫ η[B].left := eta_pullback_fst B _
  have hηRs : η[(Over.pullback (spMap (algebraMap k₀ R))).obj B].left ≫ pullback.snd B.hom _ = 𝟙 (Sp R) :=
    Over.w η[(Over.pullback (spMap (algebraMap k₀ R))).obj B]
  have hηKs : η[(Over.pullback (spMap (algebraMap k₀ K))).obj B].left ≫ pullback.snd B.hom _ = 𝟙 (Sp K) :=
    Over.w η[(Over.pullback (spMap (algebraMap k₀ K))).obj B]
  have hbcη : spMap R.val.toRingHom ≫ η[(Over.pullback (spMap (algebraMap k₀ R))).obj B].left =
      η[(Over.pullback (spMap (algebraMap k₀ K))).obj B].left ≫ bcMap B.hom R.val := by
    apply pullback.hom_ext
    · rw [Category.assoc, hηR, Category.assoc, bcMap_fst, hηK, ← Category.assoc, spMap_algHom_comp]
    · rw [Category.assoc, hηRs, Category.comp_id, Category.assoc, bcMap_snd, ← Category.assoc, hηKs,
        Category.id_comp]
  have hfη : η[(Over.pullback (spMap (algebraMap k₀ K))).obj B].left ≫ f.left =
      η[(Over.pullback (spMap (algebraMap k₀ K))).obj B].left := by
    rw [← Over.comp_left, IsMonHom.one_hom f]
  have hinj : Function.Injective R.val.toRingHom := Subtype.val_injective
  have hone : η[(Over.pullback (spMap (algebraMap k₀ R))).obj B].left ≫ ψ =
      η[(Over.pullback (spMap (algebraMap k₀ R))).obj B].left ≫ pullback.fst _ _ := by
    apply point_ext R.val.toRingHom hinj B.hom
    · rw [Category.assoc, Category.assoc, hψ1]
    · calc spMap R.val.toRingHom ≫ η[(Over.pullback (spMap (algebraMap k₀ R))).obj B].left ≫ ψ
          = η[(Over.pullback (spMap (algebraMap k₀ K))).obj B].left ≫ bcMap B.hom R.val ≫ ψ := by
            rw [← Category.assoc, hbcη, Category.assoc]
        _ = η[(Over.pullback (spMap (algebraMap k₀ K))).obj B].left ≫ f.left ≫ pullback.fst _ _ := by
            rw [hψ2]
        _ = η[(Over.pullback (spMap (algebraMap k₀ K))).obj B].left ≫ pullback.fst _ _ := by
            rw [← Category.assoc, hfη]
        _ = spMap R.val.toRingHom ≫ η[(Over.pullback (spMap (algebraMap k₀ R))).obj B].left ≫
              pullback.fst _ _ := by
            rw [← Category.assoc, hbcη, Category.assoc, bcMap_fst]
  have hΨone : η[(Over.pullback (spMap (algebraMap k₀ R))).obj B] ≫ Ψ =
      η[(Over.pullback (spMap (algebraMap k₀ R))).obj B] := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · show (η[(Over.pullback (spMap (algebraMap k₀ R))).obj B].left ≫ Ψl) ≫ _ = _
      rw [Category.assoc, hΨfst, hone]
    · show (η[(Over.pullback (spMap (algebraMap k₀ R))).obj B].left ≫ Ψl) ≫ _ = _
      rw [Category.assoc, hΨsnd]

  have hbcμ := bcMap_comp_pullback_map R μ[B]
  have hbcfst := bcMap_comp_pullback_map R (fst B B)
  have hbcsnd := bcMap_comp_pullback_map R (snd B B)
  have hδμR : (Functor.OplaxMonoidal.δ (Over.pullback (spMap (algebraMap k₀ R))) B B).left ≫ μ[((Over.pullback (spMap (algebraMap k₀ R))).obj B)].left =
      ((Over.pullback (spMap (algebraMap k₀ R))).map μ[B]).left := by
    rw [← Over.comp_left]; congr 1; simp
  have hδμK : (Functor.OplaxMonoidal.δ (Over.pullback (spMap (algebraMap k₀ K))) B B).left ≫ μ[((Over.pullback (spMap (algebraMap k₀ K))).obj B)].left =
      ((Over.pullback (spMap (algebraMap k₀ K))).map μ[B]).left := by
    rw [← Over.comp_left]; congr 1; simp
  have hδfR : (Functor.OplaxMonoidal.δ (Over.pullback (spMap (algebraMap k₀ R))) B B).left ≫ (fst ((Over.pullback (spMap (algebraMap k₀ R))).obj B) ((Over.pullback (spMap (algebraMap k₀ R))).obj B)).left =
      ((Over.pullback (spMap (algebraMap k₀ R))).map (fst B B)).left := by
    rw [← Over.comp_left, Functor.OplaxMonoidal.δ_fst]
  have hδsR : (Functor.OplaxMonoidal.δ (Over.pullback (spMap (algebraMap k₀ R))) B B).left ≫ (snd ((Over.pullback (spMap (algebraMap k₀ R))).obj B) ((Over.pullback (spMap (algebraMap k₀ R))).obj B)).left =
      ((Over.pullback (spMap (algebraMap k₀ R))).map (snd B B)).left := by
    rw [← Over.comp_left, Functor.OplaxMonoidal.δ_snd]
  have hδfK : (Functor.OplaxMonoidal.δ (Over.pullback (spMap (algebraMap k₀ K))) B B).left ≫ (fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B) ((Over.pullback (spMap (algebraMap k₀ K))).obj B)).left =
      ((Over.pullback (spMap (algebraMap k₀ K))).map (fst B B)).left := by
    rw [← Over.comp_left, Functor.OplaxMonoidal.δ_fst]
  have hδsK : (Functor.OplaxMonoidal.δ (Over.pullback (spMap (algebraMap k₀ K))) B B).left ≫ (snd ((Over.pullback (spMap (algebraMap k₀ K))).obj B) ((Over.pullback (spMap (algebraMap k₀ K))).obj B)).left =
      ((Over.pullback (spMap (algebraMap k₀ K))).map (snd B B)).left := by
    rw [← Over.comp_left, Functor.OplaxMonoidal.δ_snd]
  have hffst : (f ⊗ₘ f).left ≫ (fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B) ((Over.pullback (spMap (algebraMap k₀ K))).obj B)).left = (fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B) ((Over.pullback (spMap (algebraMap k₀ K))).obj B)).left ≫ f.left := by
    rw [← Over.comp_left, ← Over.comp_left, tensorHom_fst]
  have hfsnd : (f ⊗ₘ f).left ≫ (snd ((Over.pullback (spMap (algebraMap k₀ K))).obj B) ((Over.pullback (spMap (algebraMap k₀ K))).obj B)).left = (snd ((Over.pullback (spMap (algebraMap k₀ K))).obj B) ((Over.pullback (spMap (algebraMap k₀ K))).obj B)).left ≫ f.left := by
    rw [← Over.comp_left, ← Over.comp_left, tensorHom_snd]
  have hfμ : μ[((Over.pullback (spMap (algebraMap k₀ K))).obj B)].left ≫ f.left = (f ⊗ₘ f).left ≫ μ[((Over.pullback (spMap (algebraMap k₀ K))).obj B)].left := by
    rw [← Over.comp_left, ← Over.comp_left, IsMonHom.mul_hom f]
  have hLc : ((fst ((Over.pullback (spMap (algebraMap k₀ R))).obj B) ((Over.pullback (spMap (algebraMap k₀ R))).obj B)).left ≫ ψ) ≫ B.hom = ((snd ((Over.pullback (spMap (algebraMap k₀ R))).obj B) ((Over.pullback (spMap (algebraMap k₀ R))).obj B)).left ≫ ψ) ≫ B.hom := by
    rw [Category.assoc, Category.assoc, hψ1, pullback.condition, ← Category.assoc, ← Category.assoc]
    congr 1
    exact (Over.w (fst ((Over.pullback (spMap (algebraMap k₀ R))).obj B) ((Over.pullback (spMap (algebraMap k₀ R))).obj B))).trans (Over.w (snd ((Over.pullback (spMap (algebraMap k₀ R))).obj B) ((Over.pullback (spMap (algebraMap k₀ R))).obj B))).symm
  have hμψ : μ[((Over.pullback (spMap (algebraMap k₀ R))).obj B)].left ≫ ψ =
      pullback.lift ((fst ((Over.pullback (spMap (algebraMap k₀ R))).obj B) ((Over.pullback (spMap (algebraMap k₀ R))).obj B)).left ≫ ψ) ((snd ((Over.pullback (spMap (algebraMap k₀ R))).obj B) ((Over.pullback (spMap (algebraMap k₀ R))).obj B)).left ≫ ψ) hLc ≫ μ[B].left := by
    haveI : IsIso (Functor.OplaxMonoidal.δ (Over.pullback (spMap (algebraMap k₀ R))) B B).left :=
      (inferInstance : IsIso ((Over.forget _).map (Functor.OplaxMonoidal.δ (Over.pullback (spMap (algebraMap k₀ R))) B B)))
    rw [← cancel_epi (Functor.OplaxMonoidal.δ (Over.pullback (spMap (algebraMap k₀ R))) B B).left, ← Category.assoc, hδμR]
    apply hom_ext_bcMap (B ⊗ B).hom R.val hinj B.hom
    · have e1 : ((Over.pullback (spMap (algebraMap k₀ R))).map μ[B]).left ≫ pullback.snd B.hom (spMap (algebraMap k₀ R)) =
          pullback.snd (B ⊗ B).hom (spMap (algebraMap k₀ R)) := Over.w _
      have e2 : μ[B].left ≫ B.hom = pullback.fst B.hom B.hom ≫ B.hom := Over.w μ[B]
      have e3 : (Functor.OplaxMonoidal.δ (Over.pullback (spMap (algebraMap k₀ R))) B B).left ≫
          (fst ((Over.pullback (spMap (algebraMap k₀ R))).obj B) ((Over.pullback (spMap (algebraMap k₀ R))).obj B)).left ≫ pullback.snd B.hom (spMap (algebraMap k₀ R)) = pullback.snd (B ⊗ B).hom (spMap (algebraMap k₀ R)) := by
        rw [← Category.assoc, hδfR]; exact Over.w _
      rw [Category.assoc, hcond, ← Category.assoc, e1, Category.assoc, Category.assoc, e2]
      erw [pullback.lift_fst_assoc]
      rw [Category.assoc, hcond, ← Category.assoc, ← Category.assoc, Category.assoc _ _ (pullback.snd _ _), e3]
    · try simp only [Category.assoc]
      rw [reassoc_of% hbcμ, hψ2, ← hδμK]
      try simp only [Category.assoc]
      rw [reassoc_of% hfμ, pullback_mu_fst_eq]
      try simp only [← Category.assoc]
      congr 1
      apply pullback.hom_ext
      · try simp only [Category.assoc]
        erw [pullback.lift_fst, pullback.lift_fst]
        rw [reassoc_of% hffst, reassoc_of% hδfK, reassoc_of% hδfR, reassoc_of% hbcfst, hψ2]
      · try simp only [Category.assoc]
        erw [pullback.lift_snd, pullback.lift_snd]
        rw [reassoc_of% hfsnd, reassoc_of% hδsK, reassoc_of% hδsR, reassoc_of% hbcsnd, hψ2]
  have hΨmul : μ[((Over.pullback (spMap (algebraMap k₀ R))).obj B)] ≫ Ψ = (Ψ ⊗ₘ Ψ) ≫ μ[((Over.pullback (spMap (algebraMap k₀ R))).obj B)] := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · show (μ[((Over.pullback (spMap (algebraMap k₀ R))).obj B)].left ≫ Ψl) ≫ _ = ((Ψ ⊗ₘ Ψ).left ≫ μ[((Over.pullback (spMap (algebraMap k₀ R))).obj B)].left) ≫ _
      rw [Category.assoc, hΨfst, hμψ, Category.assoc, pullback_mu_fst_eq, ← Category.assoc (Ψ ⊗ₘ Ψ).left]
      congr 1
      apply pullback.hom_ext
      · erw [pullback.lift_fst, Category.assoc, pullback.lift_fst]
        rw [← Category.assoc, ← Over.comp_left, tensorHom_fst, Over.comp_left, Category.assoc]
        show _ = _ ≫ Ψl ≫ _
        rw [hΨfst]
      · erw [pullback.lift_snd, Category.assoc, pullback.lift_snd]
        rw [← Category.assoc, ← Over.comp_left, tensorHom_snd, Over.comp_left, Category.assoc]
        show _ = _ ≫ Ψl ≫ _
        rw [hΨfst]
    · exact (Over.w (μ[((Over.pullback (spMap (algebraMap k₀ R))).obj B)] ≫ Ψ)).trans (Over.w ((Ψ ⊗ₘ Ψ) ≫ μ[((Over.pullback (spMap (algebraMap k₀ R))).obj B)])).symm
  have hΨmon : IsMonHom Ψ := ⟨hΨone, hΨmul⟩
  refine ⟨R, g, Ψ, f₀, σ, hΨmon, ?_, ?_, hσfst, hσsnd, rfl⟩

  have hf0l : f₀.left = σ ≫ ψ := by
    show σ ≫ Ψl ≫ _ = _
    rw [hΨfst]
  have hησ : η[B].left ≫ σ = spMap g.toRingHom ≫ η[((Over.pullback (spMap (algebraMap k₀ R))).obj B)].left := by
    apply pullback.hom_ext
    · rw [Category.assoc, hσfst, Category.comp_id, Category.assoc, hηR, ← Category.assoc, hgc]
      first | exact (Category.id_comp _).symm | simp
    · rw [Category.assoc, hσsnd, ← Category.assoc, eta_left_hom, Category.id_comp, Category.assoc, hηRs,
        Category.comp_id]
  have hf0one : η[B] ≫ f₀ = η[B] := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hf0l, ← Category.assoc, hησ, Category.assoc, hone, hηR, ← Category.assoc, hgc]
    first | exact Category.id_comp _ | simp
  have hτc : (pullback.fst B.hom B.hom ≫ σ) ≫ pullback.snd B.hom (spMap (algebraMap k₀ R)) =
      (pullback.snd B.hom B.hom ≫ σ) ≫ pullback.snd B.hom (spMap (algebraMap k₀ R)) := by
    rw [Category.assoc, Category.assoc, hσsnd, ← Category.assoc, ← Category.assoc, pullback.condition]
  let τ : (B ⊗ B).left ⟶ (((Over.pullback (spMap (algebraMap k₀ R))).obj B) ⊗ ((Over.pullback (spMap (algebraMap k₀ R))).obj B)).left := pullback.lift _ _ hτc
  have hτ1 : τ ≫ (fst ((Over.pullback (spMap (algebraMap k₀ R))).obj B) ((Over.pullback (spMap (algebraMap k₀ R))).obj B)).left = pullback.fst B.hom B.hom ≫ σ := pullback.lift_fst _ _ _
  have hτ2 : τ ≫ (snd ((Over.pullback (spMap (algebraMap k₀ R))).obj B) ((Over.pullback (spMap (algebraMap k₀ R))).obj B)).left = pullback.snd B.hom B.hom ≫ σ := pullback.lift_snd _ _ _
  have e2 : μ[B].left ≫ B.hom = pullback.fst B.hom B.hom ≫ B.hom := Over.w μ[B]
  have e4 : μ[((Over.pullback (spMap (algebraMap k₀ R))).obj B)].left ≫ pullback.snd B.hom (spMap (algebraMap k₀ R)) = (fst ((Over.pullback (spMap (algebraMap k₀ R))).obj B) ((Over.pullback (spMap (algebraMap k₀ R))).obj B)).left ≫ pullback.snd B.hom (spMap (algebraMap k₀ R)) :=
    Over.w μ[((Over.pullback (spMap (algebraMap k₀ R))).obj B)]
  have hτl : τ ≫ pullback.lift ((fst ((Over.pullback (spMap (algebraMap k₀ R))).obj B) ((Over.pullback (spMap (algebraMap k₀ R))).obj B)).left ≫ pullback.fst B.hom (spMap (algebraMap k₀ R)))
      ((snd ((Over.pullback (spMap (algebraMap k₀ R))).obj B) ((Over.pullback (spMap (algebraMap k₀ R))).obj B)).left ≫ pullback.fst B.hom (spMap (algebraMap k₀ R))) (by
          rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc]
          congr 1
          exact (Over.w (fst ((Over.pullback (spMap (algebraMap k₀ R))).obj B) ((Over.pullback (spMap (algebraMap k₀ R))).obj B))).trans (Over.w (snd ((Over.pullback (spMap (algebraMap k₀ R))).obj B) ((Over.pullback (spMap (algebraMap k₀ R))).obj B))).symm) = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      erw [pullback.lift_fst]
      rw [← Category.assoc, hτ1, Category.assoc, hσfst, Category.comp_id]
      first | exact (Category.id_comp _).symm | simp
    · rw [Category.assoc]
      erw [pullback.lift_snd]
      rw [← Category.assoc, hτ2, Category.assoc, hσfst, Category.comp_id]
      first | exact (Category.id_comp _).symm | simp
  have hμσ : μ[B].left ≫ σ = τ ≫ μ[((Over.pullback (spMap (algebraMap k₀ R))).obj B)].left := by
    apply pullback.hom_ext
    · rw [Category.assoc, hσfst, Category.comp_id, Category.assoc, pullback_mu_fst_eq, ← Category.assoc, hτl]
      first | exact (Category.id_comp _).symm | simp
    · rw [Category.assoc, hσsnd, ← Category.assoc, e2, Category.assoc, Category.assoc τ, e4,
        ← Category.assoc τ, hτ1, Category.assoc (pullback.fst B.hom B.hom) σ, hσsnd]
  have hf0fst : (f₀ ⊗ₘ f₀).left ≫ (fst B B).left = (fst B B).left ≫ f₀.left := by
    rw [← Over.comp_left, ← Over.comp_left, tensorHom_fst]
  have hf0snd : (f₀ ⊗ₘ f₀).left ≫ (snd B B).left = (snd B B).left ≫ f₀.left := by
    rw [← Over.comp_left, ← Over.comp_left, tensorHom_snd]
  have hf0mul : μ[B] ≫ f₀ = (f₀ ⊗ₘ f₀) ≫ μ[B] := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, hf0l, ← Category.assoc, hμσ, Category.assoc, hμψ, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc]
      erw [pullback.lift_fst, hf0fst]
      rw [← Category.assoc, hτ1, Category.assoc, hf0l]
      rfl
    · rw [Category.assoc]
      erw [pullback.lift_snd, hf0snd]
      rw [← Category.assoc, hτ2, Category.assoc, hf0l]
      rfl
  · exact ⟨hf0one, hf0mul⟩
  · show bcMap B.hom R.val ≫ Ψl ≫ _ = _
    rw [hΨfst, hψ2]

end GlobalTheory.Spread
