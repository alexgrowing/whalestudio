import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordMapOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBaseChangeOfKernelInGeneratingOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoTransOfSelfPt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.PullComplete

theorem main : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (L : LB G₀.left) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (ξ : Sp R ⟶ Z) [IsCommMonObj ((Over.pullback ξ).obj G₀)] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A ((Over.pullback ξ).obj G₀)), LBIso U.LG.L (L.pull (pullback.fst G₀.hom ξ)) → (∀ y, PsiUnitOn D.toPre y (ξ ⁻¹' abLocus G₀)) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ ψ : R →+* V, IsLocalHom ψ → (∀ w, (jK V ≫ spMap ψ ≫ ξ) w ∈ abLocus G₀) → ∃ (G' : Over (Sp V)) (_ : GrpObj G') (_ : IsCommMonObj G') (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (gm : G'.left ⟶ G₀.left) (ι : D.toPre.X ≃+ D'.toPre.X), IsSemiAbelian G' ∧ IsGrpPullback G' G₀ (spMap ψ ≫ ξ) gm ∧ LBIso U'.LG.L (L.pull gm) ∧ CoordMap D.toPre D'.toPre ψ ι.toAddMonoidHom ∧ ∀ f : G₀ ⟶ G₀, IsMonHom f → ∃ f' : G' ⟶ G', IsMonHom f' ∧ f'.left ≫ gm = gm ≫ f.left ∧ ∀ m m', EndChar U ((Over.pullback ξ).map f) m → EndChar U' f' m' → ∀ y, ι (m y) = m' (ι y) := by
  intro Z G₀ _ _ hG₀ L R _ _ _ hR ξ _ D A U hL hψ V _ _ _ hV ψ hloc hgen
  have hG : IsSemiAbelian ((Over.pullback ξ).obj G₀) := IsSemiAbelian.pullback ξ G₀ hG₀
  have hpb := isGrpPullback_pullback G₀ ξ
  have hab : ξ ⁻¹' abLocus G₀ = abLocus ((Over.pullback ξ).obj G₀) :=
    Set.ext fun x => abLocus_pullback abLocusOne hG₀ hpb.1 x
  let W : (Sp R).Opens := ⟨ξ ⁻¹' abLocus G₀, by rw [hab]; exact GlobalTheory.AbLocusOpen.isOpen_abLocus_local _ hG⟩
  have hz : (jK V).base (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V)) = genericPoint (Sp V) := by
    rw [genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap V (FractionRing V)) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V))
  have hW : spMap ψ (genericPoint (Sp V)) ∈ W := by
    show ξ (spMap ψ (genericPoint (Sp V))) ∈ abLocus G₀
    rw [← hz]
    have := hgen (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
    exact this
  let G := (Over.pullback ξ).obj G₀
  let G' := (Over.pullback (specOf ψ)).obj G
  have hbc : IsMonHom (Iso.refl G').hom := by show IsMonHom (𝟙 G'); infer_instance
  obtain ⟨D', A', hD, U', hP⟩ := GlobalTheory.Mum.unif_baseChange_of_psiUnitOn R hR D A G hG U V hV.1 ψ hloc W hψ hW
    G' (Iso.refl G') hbc
  have hG' : IsSemiAbelian G' := IsSemiAbelian.pullback (specOf ψ) G hG
  let β : G'.left ⟶ G.left := (Iso.refl G').hom.left ≫ pullback.fst G.hom (specOf ψ)
  obtain ⟨hLB, hC, hE⟩ := GlobalTheory.Poinc.Eq8.PullUnif.main R hR G hG D A U V hV G' hG' D' A' U' ψ β hloc (Iso.refl G')
    hbc rfl hD hP
  let gm : G'.left ⟶ G₀.left := β ≫ pullback.fst G₀.hom ξ
  have hβ : IsGrpPullback G' G (specOf ψ) β :=
    ((isGrpPullback_of_iso (Iso.refl G')).comp (isGrpPullback_pullback G (specOf ψ))).congr (Category.id_comp _) rfl
  refine ⟨G', inferInstance, inferInstance, D', A', U', gm, hD.xe.symm, hG', hβ.comp hpb, ?_, hC, ?_⟩
  · exact GlobalTheory.LBIsoEnd.lbIso_trans_end _ _ _ _ U'.LG.isLB (pull_isLB U.LG.isLB β) hLB
      (LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_of_lbIso hL β rfl))
  · intro f hf
    haveI := hf
    have e1 : ((Over.pullback (specOf ψ)).map ((Over.pullback ξ).map f)).left ≫ β =
        β ≫ ((Over.pullback ξ).map f).left := by
      show _ ≫ 𝟙 _ ≫ _ = (𝟙 _ ≫ _) ≫ _
      exact pullback.lift_fst _ _ _
    have e2 : ((Over.pullback ξ).map f).left ≫ pullback.fst G₀.hom ξ = pullback.fst G₀.hom ξ ≫ f.left :=
      pullback.lift_fst _ _ _
    refine ⟨(Over.pullback (specOf ψ)).map ((Over.pullback ξ).map f), inferInstance, ?_, ?_⟩
    · show _ ≫ β ≫ _ = (β ≫ _) ≫ _
      calc _ = (((Over.pullback (specOf ψ)).map ((Over.pullback ξ).map f)).left ≫ β) ≫ pullback.fst G₀.hom ξ :=
            (Category.assoc _ _ _).symm
        _ = (β ≫ ((Over.pullback ξ).map f).left) ≫ pullback.fst G₀.hom ξ := by rw [e1]
        _ = β ≫ (((Over.pullback ξ).map f).left ≫ pullback.fst G₀.hom ξ) := Category.assoc _ _ _
        _ = β ≫ (pullback.fst G₀.hom ξ ≫ f.left) := by rw [e2]
        _ = _ := (Category.assoc _ _ _).symm
    · intro m m' hm hm' y
      exact hE _ _ inferInstance inferInstance e1 m m' hm hm' y

end GlobalTheory.Poinc.Eq8.PullComplete
