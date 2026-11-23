import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendLineBundleFactorialStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothProjectiveStalkFactorialStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSabExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetryHypothesisSpreadFromGenericFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section
open MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegTripleBundle
open GlobalTheory.CechPic

theorem exists_bundle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g : ℕ) (φ : InvFun ℤ) (n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S) (d N : ℕ) (U Y : Scheme.{0}) (f : U ⟶ Y) (π : Y ⟶ S) (G' : Over Y) [GrpObj G'] [IsCommMonObj G'] (μ : G'.left ⟶ G.left) (act : OAct (𝓞 E) G') (t₀ : SAB H U) (y : U ⟶ F.X) (α : t₀.G.left ⟶ F.univ.A.left) (α₂ : (G2 t₀.G).left ⟶ (G2 F.univ.A).left) (ψ : t₀.G.left ⟶ G'.left), SiegData g φ n F S s j G e BD d N → f ≫ π = y ≫ j → IsGrpPullback G' G π μ → IsGrpPullback t₀.G G' f ψ → ψ ≫ μ = α ≫ e → (∀ a, (t₀.act.act a).left ≫ ψ = ψ ≫ (act.act a).left) → IsGrpPullback t₀.G F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ t₀.G t₀.PP.L) (F.univ.P.pull α₂) → ∃ M : LB G'.left, M.IsLB ∧ LBIso (M.pull ψ) t₀.PP.L := by
  intro E _ _ _ H g φ n F S s j _ G _ e BD d N U Y f π G' _ _ μ act t₀ y α α₂ ψ hSD hfπ hμ hψ hψμ hact hα hsq hlb
  have hG : IsSemiAbelian G := hSD.2.2.2.2.1
  haveI : IsCommMonObj G := hG.comm
  have hAG : IsGrpPullback F.univ.A G j e := hSD.2.2.2.2.2.2.1
  have hpb := GlobalTheory.SymSpread.isPullback_square hAG
  have he₂ : IsOpenImmersion (lift (pushPt hAG.1.w (fst F.univ.A F.univ.A)) (pushPt hAG.1.w (snd F.univ.A F.univ.A))).left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb.flip (inferInstanceAs (IsOpenImmersion j))
  have hs : Smooth s := hSD.2.1.smooth
  have : Smooth G.hom := hG.smooth
  have : QuasiCompact G.hom := hG.quasiCompact
  have hsm2 : Smooth (G ⊗ G).hom := by
    show Smooth (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  have hqc2 : QuasiCompact (G ⊗ G).hom := by
    show QuasiCompact (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.smooth_projective_stalk_factorial n S s (G ⊗ G).left (G ⊗ G).hom hSD.1 hs hsm2 hqc2
  have hP := F.univ.isLB
  obtain ⟨P', hP', hP'e⟩ := GlobalTheory.T.extend_line_bundle_factorial (G ⊗ G).left _ _ he₂ (fun x => (h3 x).1) (fun x => (h3 x).2) F.univ.P hP
  have hsqe : IsSquare e (lift (pushPt hAG.1.w (fst F.univ.A F.univ.A)) (pushPt hAG.1.w (snd F.univ.A F.univ.A))).left :=
    ⟨congrArg (fun z => z.left) (lift_fst (pushPt hAG.1.w (fst F.univ.A F.univ.A)) (pushPt hAG.1.w (snd F.univ.A F.univ.A))),
      congrArg (fun z => z.left) (lift_snd (pushPt hAG.1.w (fst F.univ.A F.univ.A)) (pushPt hAG.1.w (snd F.univ.A F.univ.A)))⟩
  have hsqμ : IsSquare μ (lift (pushPt hμ.1.w (fst G' G')) (pushPt hμ.1.w (snd G' G'))).left :=
    ⟨congrArg (fun z => z.left) (lift_fst (pushPt hμ.1.w (fst G' G')) (pushPt hμ.1.w (snd G' G'))),
      congrArg (fun z => z.left) (lift_snd (pushPt hμ.1.w (fst G' G')) (pushPt hμ.1.w (snd G' G')))⟩
  have key : ψ ≫ (lift (𝟙 G') (act.act H.w0)).left ≫ (lift (pushPt hμ.1.w (fst G' G')) (pushPt hμ.1.w (snd G' G'))).left =
      (lift (𝟙 t₀.G) (t₀.act.act H.w0)).left ≫ α₂ ≫
        (lift (pushPt hAG.1.w (fst F.univ.A F.univ.A)) (pushPt hAG.1.w (snd F.univ.A F.univ.A))).left := by
    have k1 : (lift (𝟙 t₀.G) (t₀.act.act H.w0)).left ≫ (fst t₀.G t₀.G).left = 𝟙 _ := by
      rw [← Over.comp_left, lift_fst, Over.id_left]
    have k2 : (lift (𝟙 t₀.G) (t₀.act.act H.w0)).left ≫ (snd t₀.G t₀.G).left = (t₀.act.act H.w0).left := by
      rw [← Over.comp_left, lift_snd]
    have a1 : (lift (𝟙 G') (act.act H.w0)).left ≫ (fst G' G').left = 𝟙 _ := by
      rw [← Over.comp_left, lift_fst, Over.id_left]
    have a2 : (lift (𝟙 G') (act.act H.w0)).left ≫ (snd G' G').left = (act.act H.w0).left := by
      rw [← Over.comp_left, lift_snd]
    apply pullback.hom_ext
    · change _ ≫ (fst G G).left = _ ≫ (fst G G).left
      simp only [Category.assoc, hsqμ.1, hsqe.1]
      rw [reassoc_of% a1, hψμ, reassoc_of% hsq.1, reassoc_of% k1]
    · change _ ≫ (snd G G).left = _ ≫ (snd G G).left
      simp only [Category.assoc, hsqμ.2, hsqe.2]
      rw [reassoc_of% a2, reassoc_of% hsq.2, reassoc_of% k2, ← hψμ, reassoc_of% (hact H.w0)]
  refine ⟨P'.pull ((lift (𝟙 G') (act.act H.w0)).left ≫ (lift (pushPt hμ.1.w (fst G' G')) (pushPt hμ.1.w (snd G' G'))).left),
    pull_isLB hP' _, ?_⟩
  refine (cls_eq_iff (pull_isLB (pull_isLB hP' _) ψ) t₀.PP.isLB).1 ?_
  rw [cls_pull (pull_isLB hP' _) ψ, cls_pull hP' _, ← pull_comp, key, pull_comp, pull_comp]
  have hPe : pull (lift (pushPt hAG.1.w (fst F.univ.A F.univ.A)) (pushPt hAG.1.w (snd F.univ.A F.univ.A))).left (cls P' hP') = cls F.univ.P hP := by
    rw [← cls_pull hP' _ (pull_isLB hP' _)]
    exact (cls_eq_iff _ _).2 hP'e
  rw [hPe, ← cls_pull hP α₂ (pull_isLB hP α₂), ← (cls_eq_iff (TripleExt.isLB_cube _ t₀.PP.isLB) (pull_isLB hP α₂)).2 hlb]
  refine (congrArg (CechPic.pull _) (TripleExt.cls_cube (x2 t₀.G) t₀.PP.isLB)).trans ?_
  rw [TripleExt.pull_cubeCls_pre]
  refine Eq.trans ?_ ((cls_eq_iff t₀.PP.isLB (TripleExt.isLB_cube _ t₀.PP.isLB)).2 t₀.prim).symm
  rw [TripleExt.cls_cube _ t₀.PP.isLB]
  congr 1
  funext i
  fin_cases i <;> simp [x2]
end GlobalTheory.SiegTripleBundle
