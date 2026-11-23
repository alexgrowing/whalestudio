import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreKilled
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalPullbackBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KernelFiniteFlatHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.KernelRepFinite

theorem isClosedImmersion_pullback_map {S S' : Scheme.{0}} (f : S' ⟶ S) {A B : Over S} (k : A ⟶ B)
    [IsClosedImmersion k.left] : IsClosedImmersion ((Over.pullback f).map k).left := by
  exact MorphismProperty.overPullbackMap (P := @IsClosedImmersion) f k inferInstance

theorem lbIso_diag {S T : Scheme.{0}} (A : Over S) (B : Over T) (β : B.left ⟶ A.left)
    (β₂ : (G2 B).left ⟶ (G2 A).left) (hs : IsSquare β β₂) {P : LB (G2 A).left} (hP : P.IsLB) :
    LBIso ((P.pull β₂).pull (lift (𝟙 B) (𝟙 B)).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull β) := by
  have e₁ : LBIso ((P.pull β₂).pull (lift (𝟙 B) (𝟙 B)).left) (P.pull ((lift (𝟙 B) (𝟙 B)).left ≫ β₂)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP β₂)) _
  have e₂ : LBIso ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull β) (P.pull (β ≫ (lift (𝟙 A) (𝟙 A)).left)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _
  rw [GlobalTheory.DiagAmpleBC.diag_comp A B β β₂ hs] at e₁
  exact LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁ e₂.symm

theorem isFinite_restrict : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → ∀ V₀ : S'.Opens, IsAffineOpen V₀ → Out.RelAmple ((Over.pullback V₀.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V₀.ι G)).pull (lift (𝟙 ((Over.pullback V₀.ι).obj G)) (𝟙 ((Over.pullback V₀.ι).obj G))).left) → ∀ (Z : Over S') (i : Z ⟶ G), IsClosedImmersion i.left → (∀ (T : Over S') (z : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → GlobalTheory.MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) (z ≫ i)) → IsFinite (Z.hom ∣_ V₀) := by
  intro S' _ G _ _ P hA hP V₀ hV hRel Z i hi hZ
  haveI : IsNoetherianRing Γ(S', V₀) := IsLocallyNoetherian.component_noetherian ⟨V₀, hV⟩
  let t : Sp Γ(S', V₀) ⟶ V₀.toScheme := hV.isoSpec.inv
  let GV := (Over.pullback V₀.ι).obj G
  let B := (Over.pullback t).obj GV
  have hAV : IsAbelianScheme GV := GlobalTheory.isAbelianScheme_pullback_obj _ G hA
  have hAB : IsAbelianScheme B := GlobalTheory.isAbelianScheme_pullback_obj _ GV hAV
  let PV := P.pull (Pdiv.PullbackComparison.pφ₂ V₀.ι G)
  have hPV : PV.IsLB := pull_isLB hP _
  have h₁ := Pdiv.PullbackComparison.isGrpPullback V₀.ι G
  have h₂ := Pdiv.PullbackComparison.isGrpPullback t GV
  have hRelB : Out.RelAmple B ((PV.pull (Pdiv.PullbackComparison.pφ₂ t GV)).pull (lift (𝟙 B) (𝟙 B)).left) :=
    GlobalTheory.DiagAmpleBC.relAmple_diag_pull _ _ GV hAV PV hPV hRel t B (Pdiv.PullbackComparison.pφ t GV)
      (Pdiv.PullbackComparison.pφ₂ t GV) h₂.1 (Pdiv.PullbackComparison.isSquare t GV)
  obtain ⟨ZL, iL, hiL, hfinL, -, hrep⟩ := GlobalTheory.kernelFiniteFlat_holds _ B hAB _
    (pull_isLB (pull_isLB hPV _) _) hRelB
  let ZV := (Over.pullback V₀.ι).obj Z
  let ZB := (Over.pullback t).obj ZV
  let iV : ZV ⟶ GV := (Over.pullback V₀.ι).map i
  let iB : ZB ⟶ B := (Over.pullback t).map iV
  have hmem : GlobalTheory.MemKL B ((PV.pull (Pdiv.PullbackComparison.pφ₂ t GV)).pull (lift (𝟙 B) (𝟙 B)).left) iB := by
    refine GlobalTheory.memKL_of_push h₂ (pull_isLB hPV _) (pull_isLB (pull_isLB hPV _) _)
      (lbIso_diag GV B _ _ (Pdiv.PullbackComparison.isSquare t GV) hPV) iB ?_
    refine GlobalTheory.memKL_of_push h₁ (pull_isLB hP _) (pull_isLB hPV _)
      (lbIso_diag G GV _ _ (Pdiv.PullbackComparison.isSquare V₀.ι G) hP) _ ?_
    let zz : Over.mk ((ZB.hom ≫ t) ≫ V₀.ι) ⟶ Z :=
      Over.homMk (pullback.fst ZV.hom t ≫ pullback.fst Z.hom V₀.ι) (by
        show (pullback.fst ZV.hom t ≫ pullback.fst Z.hom V₀.ι) ≫ Z.hom = (pullback.snd ZV.hom t ≫ t) ≫ V₀.ι
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        congr 1
        exact pullback.condition)
    have e : ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushPt h₁.1.w (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushPt h₂.1.w iB) = zz ≫ i := by
      apply Over.OverMorphism.ext
      show (iB.left ≫ Pdiv.PullbackComparison.pφ t GV) ≫ Pdiv.PullbackComparison.pφ V₀.ι G =
        (pullback.fst ZV.hom t ≫ pullback.fst Z.hom V₀.ι) ≫ i.left
      simp only [Pdiv.PullbackComparison.pφ]
      rw [Pdiv.PullbackComparison.pullback_map_left_fst' t iV, Category.assoc,
        Pdiv.PullbackComparison.pullback_map_left_fst' V₀.ι i, Category.assoc]
    rw [e]
    apply hZ
    rintro _ ⟨y, rfl⟩
    show (((ZB.hom ≫ t) ≫ V₀.ι).base y) ∈ V₀
    exact (Scheme.Opens.range_ι V₀).subset ⟨(ZB.hom ≫ t).base y, rfl⟩
  obtain ⟨z, hz⟩ := (hrep ZB iB).1 hmem
  haveI : IsClosedImmersion iV.left := isClosedImmersion_pullback_map _ i
  haveI : IsClosedImmersion iB.left := isClosedImmersion_pullback_map _ iV
  have hz' : z.left ≫ iL.left = iB.left := congrArg (fun q => q.left) hz
  haveI : IsClosedImmersion (z.left ≫ iL.left) := by rw [hz']; infer_instance
  haveI : IsClosedImmersion z.left := IsClosedImmersion.of_comp z.left iL.left
  have hZB : IsFinite ZB.hom := by
    rw [← Over.w z]; infer_instance
  have hV' : IsFinite ZV.hom := by
    have ec : ZV.hom = inv (pullback.fst ZV.hom t) ≫ pullback.snd ZV.hom t ≫ t := by
      rw [← pullback.condition, IsIso.inv_hom_id_assoc]
    rw [ec]
    haveI : IsFinite (pullback.snd ZV.hom t) := hZB
    infer_instance
  rw [← (isPullback_morphismRestrict Z.hom V₀).flip.isoPullback_hom_snd]
  haveI : IsFinite (pullback.snd Z.hom V₀.ι) := hV'
  infer_instance

end GlobalTheory.KernelRepFinite
