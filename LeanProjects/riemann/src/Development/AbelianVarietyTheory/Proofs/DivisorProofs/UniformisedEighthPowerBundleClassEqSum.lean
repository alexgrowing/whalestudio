import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationLineBundleUnifIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

noncomputable section

namespace GlobalTheory.SharpBundle

open GlobalTheory.ZH.EndoExtend GlobalTheory.SquareOfGeneric

theorem prod_left_ext {S : Scheme.{0}} {X Y : Over S} {Z : Scheme.{0}} (f g : Z ⟶ (X ⊗ Y).left)
    (h₁ : f ≫ (fst X Y).left = g ≫ (fst X Y).left) (h₂ : f ≫ (snd X Y).left = g ≫ (snd X Y).left) : f = g := by
  apply pullback.hom_ext
  · simpa using h₁
  · simpa using h₂

theorem cls_eq_sum_lam : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : GlobalTheory.ZM.SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀) (y : Sp (FractionRing R) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left) (φ₂ : (G2 c.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback c.A F.univ.A y φc → IsSquare φc φ₂ → LBIso c.P (F.univ.P.pull φ₂) → ∀ pr : Fin 8 → (A.A ⟶ c.A), LBIso A.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ q : Fin 8 → (G ⟶ G₀), (∀ u, IsMonHom (q u)) → (∀ u, ((Over.pullback (jK R)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → cls U.LG.L U.LG.isLB = ∑ a, ∑ b, W a b • lam (cls U₀.LG.L U₀.LG.isLB) (q a) (q b) := by
  intro g n o _ ζ F W R _ _ _ hR D D₀ A A₀ G G₀ _ _ _ _ hG U U₀ y α α₂ hα hαs hαL c φc φ₂ hφ hφs hφL pr hP q hq hqg
  obtain ⟨hno, -, hic, -⟩ := hR.1
  have hS : IsSemiAbelian G := hG
  have := hS.smooth
  have := hS.geomConnected
  have := geometricallyIntegral_of_smooth G.hom
  have := U₀.gen_hom
  have hL := U.LG.isLB
  have hL₀ := U₀.LG.isLB
  have hA := A.isLB
  have hA₀ := A₀.isLB
  have hcP := c.isLB
  have hUP := F.univ.isLB
  have h₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h₂ : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  have h₃ : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have hn : Geo.Tor.IsNormalScheme (Sp R) := (GlobalTheory.isNormalScheme_iff_pred _).1 inferInstance

  have key : ∀ a b, CechPic.pull U.gen.hom.left (CechPic.pull (lift (pr a) (pr b)).left (cls c.P hcP)) =
      CechPic.pull (pullback.fst G.hom (jK R)) (lam (cls U₀.LG.L hL₀) (q a) (q b)) := by
    intro a b
    have eP : cls c.P hcP = CechPic.pull φ₂ (cls F.univ.P hUP) := (cls_eq_iff hcP (pull_isLB hUP _)).2 hφL
    have eΛ : CechPic.pull α₂ (cls F.univ.P hUP) = lam (cls A₀.L hA₀) (fst A₀.A A₀.A) (snd A₀.A A₀.A) :=
      ((cls_eq_iff (LB.isLB_linComb hA₀ _ _) (pull_isLB hUP _)).2 hαL).symm.trans (cls_cube_two hA₀ _ _ _)
    have eK : (U.gen.hom ≫ lift (pr a) (pr b)).left ≫ φ₂ =
        (lift ((Over.pullback (jK R)).map (q a) ≫ U₀.gen.hom) ((Over.pullback (jK R)).map (q b) ≫ U₀.gen.hom)).left ≫ α₂ := by
      apply GlobalTheory.SharpBundle.prod_left_ext
      · rw [Category.assoc, hφs.1, Category.assoc, hαs.1, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
          ← Over.comp_left, Category.assoc, lift_fst, lift_fst]
        exact (hqg a).symm
      · rw [Category.assoc, hφs.2, Category.assoc, hαs.2, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
          ← Over.comp_left, Category.assoc, lift_snd, lift_snd]
        exact (hqg b).symm
    have hext₀ : CechPic.pull U₀.gen.hom.left (cls A₀.L hA₀) =
        CechPic.pull (pullback.fst G₀.hom (jK R)) (cls U₀.LG.L hL₀) := by
      obtain ⟨w, hw⟩ := U₀.ext
      rw [← cls_pull hL₀ _ (pull_isLB hL₀ _), ← cls_pull hA₀ _ (pull_isLB hA₀ _)]
      exact (cls_eq_iff _ _).2 ⟨w, hw⟩
    rw [← pull_comp, ← Over.comp_left, eP, ← pull_comp, eK, pull_comp, eΛ, pull_lam, lift_fst, lift_snd, ← lam_pull,
      hext₀, lam_pull_fst]
    let hh : Over.mk (((Over.pullback (jK R)).obj G).hom ≫ jK R) ⟶ G :=
      Over.homMk (pullback.fst G.hom (jK R)) pullback.condition
    show _ = CechPic.pull hh.left _
    rw [pull_lam]
    congr 1 <;> ext1 <;> exact pullback.lift_fst _ _ _
  refine pic_ext (jK R) hn G (eSec G) (Over.w η[G]) ?_ ?_
  · have h0 : CechPic.pull (eSec G) (cls U.LG.L hL) = 0 :=
      (cls_eq_zero_iff (pull_isLB hL _)).2 ⟨U.LG.rig, U.LG.rigGen⟩
    rw [h0, map_sum]
    symm
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    have := hq a
    have := hq b
    have e₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ G₀) = η[G₀] := by rw [Hom.one_def]; simp
    rw [map_zsmul]
    show _ • CechPic.pull η[G].left _ = 0
    rw [pull_lam, IsMonHom.one_hom, IsMonHom.one_hom, ← e₁, lam_one_left, smul_zero]
  · have hc' : CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL) =
        CechPic.pull U.gen.hom.left (cls A.L hA) := by
      obtain ⟨w, hw⟩ := U.ext
      rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hA _ (pull_isLB hA _)]
      exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm
    rw [hc', (cls_eq_iff hA (LB.isLB_linComb hcP _ _)).2 hP, cls_linComb hcP, map_sum, map_sum,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_zsmul, map_zsmul, key]

end GlobalTheory.SharpBundle
