import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SquareUnits
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfMemChart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemNonzeroLocusIffChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisationSectionNonemptyNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointMemTranslatesStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TwistFibre

variable {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ S)

theorem unitAt_square (x₁ x₂ : Over.mk t ⟶ P.A) (y : (Over.mk t ⊗ P.A).left) :
    UnitAt P.L ![(translPt P.A (x₁ * x₂)).left, (snd (Over.mk t) P.A).left,
      (translPt P.A x₁).left, (translPt P.A x₂).left] ![1, 1, -1, -1] y := by
  obtain ⟨V, hpV, c, hc⟩ := (GlobalTheory.AbSquare.square_of_cube GlobalTheory.AbLaw.CubeAssembly.cube_gen).1 S P (Over.mk t) x₁ x₂
    (IsLocalRing.closedPoint K)
  have hV : V = ⊤ := eq_top_iff.2 fun q _ => by
    rw [spec_pt_eq (k := K) q (IsLocalRing.closedPoint K)]; exact hpV
  subst hV
  obtain ⟨s, hs⟩ := exists_sec_of_pullGen (Z := (Over.mk t ⊗ P.A).left)
    ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι c hc
  let e := IsOpenImmersion.lift ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι (𝟙 _)
    (by rintro _ ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; trivial)
  have he : e ≫ ((fst (Over.mk t) P.A).left ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    IsOpenImmersion.lift_fac _ _ _
  refine UnitAt.congr P.isLB ?_ ⟨pullSec s e, fun J hJ => ?_⟩
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Category.assoc, he, Category.id_comp]
  · rw [sval_pullSec s e (𝟙 _) y hJ]
    exact hs _ y J hJ

theorem isIntegral_fibre : IsIntegral (Over.mk t ⊗ P.A).left := by
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have : GeometricallyIntegral P.A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance
  exact GeometricallyIntegral.geometrically_isIntegral (f := P.A.hom) t (pullback.snd t P.A.hom)
    (pullback.fst t P.A.hom) (IsPullback.of_hasPullback t P.A.hom).flip

def trY (w : Over.mk t ⟶ P.A) : Over.mk t ⊗ P.A ⟶ Over.mk t ⊗ P.A := lift (fst _ _) (translPt P.A w)

theorem trY_snd (w : Over.mk t ⟶ P.A) :
    (trY P t w).left ≫ (snd (Over.mk t) P.A).left = (translPt P.A w).left := by
  rw [← Over.comp_left, trY, lift_snd]

theorem lift_trY (a w : Over.mk t ⟶ P.A) : lift (𝟙 (Over.mk t)) a ≫ trY P t w = lift (𝟙 (Over.mk t)) (w * a) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [trY]
  · rw [Category.assoc, trY, lift_snd, lift_snd, translPt, comp_lift_assoc, lift_fst_assoc, Category.id_comp,
      lift_snd, Hom.mul_def]

theorem isUnit_sval_of_mem {X Y Z : Scheme.{0}} {L : LB X} {I : Type} [Fintype I] {φ : I → (Y ⟶ X)} {ε : I → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (h : r z ∈ nonzeroLocus s) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : IsUnit (sval s r z J) := by
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.isUnit_sval s r z hJ k hk

theorem exists_sec_twist_mem_nonzeroLocus : ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (c : Over.mk t ⟶ P.A) (a : Over.mk t ⟶ P.A) (p : Spec (CommRingCat.of K)), ∃ s : LB.Sec (twistLB P.A P.L 2 c), (lift (𝟙 (Over.mk t)) a).left p ∈ nonzeroLocus s := by
  intro S P K _ _ t c a p
  have hI := isIntegral_fibre P t
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_polarisation_section_nonempty_nonvanishing S P K t hI
  obtain ⟨u, h₁, h₂⟩ := GlobalTheory.T.exists_point_mem_translates' S P K t inferInstance (nonzeroLocus θ) hθ a c p
  obtain ⟨g, hg⟩ := unitAt_square P t (c * u) u⁻¹ ((lift (𝟙 (Over.mk t)) a).left p)
  have hF : FormEq (Sum.elim (Sum.elim (fun k => (trY P t (c * u)).left ≫ ![(snd (Over.mk t) P.A).left] k)
      (fun k => (trY P t u⁻¹).left ≫ ![(snd (Over.mk t) P.A).left] k))
      ![(translPt P.A (c * u * u⁻¹)).left, (snd (Over.mk t) P.A).left,
        (translPt P.A (c * u)).left, (translPt P.A u⁻¹).left])
      (Sum.elim (Sum.elim ![1] ![1]) ![1, 1, -1, -1])
      ![(snd (Over.mk t) P.A).left, (translPt P.A c).left] ![((2 : ℕ) : ℤ) - 1, 1] := by
    refine formEq_of_add fun U _ h => ?_
    simp only [Fintype.sum_sum_type, Fin.sum_univ_succ, Fin.sum_univ_zero, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons]
    rw [trY_snd, trY_snd, mul_inv_cancel_right]
    simp
    abel
  obtain ⟨σ, hσ⟩ := exists_sec P.isLB hF (mulSec (mulSec (pullSec θ (trY P t (c * u)).left)
    (pullSec θ (trY P t u⁻¹).left)) g)
  refine ⟨σ, ?_⟩
  choose J hJ using fun χ : (Over.mk t ⊗ P.A).left ⟶ P.A.left => exists_chart P.isLB (χ ((lift (𝟙 (Over.mk t)) a).left p))
  have hJ' : Good P.L ((lift (𝟙 (Over.mk t)) a).left p) J := hJ
  refine (GlobalTheory.AbVarProj.mem_nonzeroLocus_iff_sval σ _ hJ').2 ?_
  rw [hσ _ _ _ J hJ', sval_mulSec _ _ _ _ hJ',
    sval_mulSec _ _ _ _ hJ', sval_pullSec _ _ _ _ hJ', sval_pullSec _ _ _ _ hJ']
  refine ((isUnit_sval_of_mem θ _ _ ?_ hJ').mul (isUnit_sval_of_mem θ _ _ ?_ hJ')).mul (hg J hJ')
  · rw [Category.id_comp, ← Scheme.Hom.comp_apply, ← Over.comp_left, lift_trY]
    exact h₁
  · rw [Category.id_comp, ← Scheme.Hom.comp_apply, ← Over.comp_left, lift_trY]
    exact h₂

end GlobalTheory.TwistFibre
