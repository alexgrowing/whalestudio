import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonOfFibres
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearIsIsoOfIsProperOfFinitePresentation

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.CatCoh GlobalTheory.Cris
open GlobalTheory.DeRham GlobalTheory.Published GlobalTheory.Published.AbelianDeRham GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase GlobalTheory.DeRhamSheaf
open Limits (pullback)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PrincipalPolPairing

theorem exists_affine_pairings : GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.CubeTheorem → GlobalTheory.CovTop.Hypotheses2 →
    GlobalTheory.Published.PoincareDeRhamDuality → ∀ {T : Scheme.{0}} (A : Over T) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → (∃ c, GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.IsPrincipalPol A c) → ∀ (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)), IsDRIso A H e →
    ∃ b : ∀ (V : T.Opens), IsAffineOpen V → (Γ(H, V) →ₗ[Γ(T, V)] Γ(H, V) →ₗ[Γ(T, V)] Γ(T, V)),
      (∀ (V V' : T.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V) (s t : Γ(H, V)),
        b V' hV' (GlobalTheory.Twist.resM H h s) (GlobalTheory.Twist.resM H h t) = resG T h (b V hV s t)) ∧
      (∀ (V : T.Opens) (hV : IsAffineOpen V), (b V hV).IsPerfPair) ∧
      ∀ (V : T.Opens) (hV : IsAffineOpen V), ∃ P : LB ((onAff A hV) ⊗ (onAff A hV)).left,
        GlobalTheory.AbDual.IsDual (onAff A hV) (onAff A hV) P ∧
        ∃ φ : HdR (onAff A hV) →ₗ[Γ(T, V)] HdR (onAff A hV) →ₗ[Γ(T, V)] Γ(T, V),
          GlobalTheory.AbDual.IsCorrForm (GlobalTheory.Cris.dp0 Γ(T, V)) (𝟙 _) (onAff A hV) (onAff A hV) P φ ∧
          ∀ (x y : HdR (onAff A hV)) (u v : Γ(H, V)), (∀ w, x (e V hV w) = b V hV w u) →
            (∀ w, y (e V hV w) = b V hV w v) → φ x y = b V hV u v := by
  intro hDu hC hP2 _ T A _ g hA hg ⟨c, hc⟩ H e he
  have hD : AbelianDeRham := hP2.p5
  have hπ (V : T.Opens) (hV : IsAffineOpen V) :
      IsGrpPullback (onAff A hV) A hV.fromSpec (pullback.fst A.hom hV.fromSpec) := isGrpPullback_pullback A _
  choose P hP eP dP using fun (V : T.Opens) (hV : IsAffineOpen V) ↦
    principalPol_selfDual hDu hC _ (onAff A hV) (DeRhamSheaf.VB.isAbelianScheme_onAff A hA hV) _
      (PPAS.isPrincipalPol_pull (hπ V hV) hc)
  choose φ b hφ pφ pb k iso using fun (V : T.Opens) (hV : IsAffineOpen V) ↦
    exists_pairing hD (DeRhamSheaf.VB.isAbelianScheme_onAff A hA hV) (DeRhamSheaf.VB.smooth_onAff A hg hV)
      (hP V hV) (eP V hV ▸ PPAS.isPrincipalPol_pull (hπ V hV) hc)
  refine ⟨fun V hV ↦ (b V hV).flip.compl₁₂ (e V hV).toLinearMap (e V hV).toLinearMap,
    fun V V' hV hV' h s t ↦ ?_, fun V hV ↦ ?_, fun V hV ↦ ⟨P V hV, dP V hV, φ V hV, hφ V hV, ?_⟩⟩
  · letI := resAlg h
    obtain ⟨π, hπ', eπ⟩ := DeRhamSheaf.VB.exists_transition A hV hV' h
    have hAV := DeRhamSheaf.VB.isAbelianScheme_onAff A hA hV
    have hgV := DeRhamSheaf.VB.smooth_onAff A hg hV
    obtain ⟨_, _, -⟩ := Free.prim hD.1 hAV hgV
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearMap.flip_apply]
    rw [he V V' hV hV' h π hπ' eπ, he V V' hV hV' h π hπ' eπ]
    refine inverse_bc (hD.2.2.1 _ _ g hAV hgV _ _ π hπ').1 (pφ V' hV') (corr_bc hD.1
      (DeRhamSheaf.VB.isAbelianScheme_onAff A hA hV') (DeRhamSheaf.VB.smooth_onAff A hg hV') hπ' (hP V hV)
      (hP V' hV') ?_ (hφ V hV) (hφ V' hV')) (k V hV) (k V' hV') _ _
    rw [eP, eP, ← CechPic.pull_comp]
    congr 2
    apply pullback.hom_ext
    · simp only [sqMap, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, eπ]
    · simp only [sqMap, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, eπ]
  · have := pb V hV
    have : (b V hV).flip.IsPerfPair := inferInstance
    exact LinearMap.IsPerfPair.congr (b V hV).flip (e V hV) (e V hV) _ (by ext; simp)
  · intro x y u v hx hy
    have ex : x = b V hV (e V hV u) := LinearMap.ext fun w ↦ by
      obtain ⟨w, rfl⟩ := (e V hV).surjective w
      exact hx w
    rw [ex, k, hy]

end GlobalTheory.PrincipalPolPairing
