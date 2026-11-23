import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDerivAt0CompLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismDescendsToAlgebraic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.ExpKernel

theorem fderiv_apply_eq_zero {g : ℕ} (h : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) (hc : ∀ t : ℂ, h (t • w) = h 0) :
    fderiv ℂ h 0 w = 0 := by
  by_cases hd : DifferentiableAt ℂ h 0
  · have hl : HasFDerivAt (fun t : ℂ => t • w) ((ContinuousLinearMap.id ℂ ℂ).smulRight w) 0 :=
      ((ContinuousLinearMap.id ℂ ℂ).smulRight w).hasFDerivAt
    have h0 : HasFDerivAt h (fderiv ℂ h 0) ((0 : ℂ) • w) := by rw [zero_smul]; exact hd.hasFDerivAt
    have h1 := h0.comp (0 : ℂ) hl
    have h2 : HasFDerivAt (fun t : ℂ => h (t • w)) (0 : ℂ →L[ℂ] ℂ) 0 := by
      simp only [hc]; exact hasFDerivAt_const _ _
    have := congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) (h1.unique h2)
    simpa using this
  · rw [fderiv_zero_of_not_differentiableAt hd]; rfl

theorem kernel_isFullLattice : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G →
    SmoothOfRelativeDimension g G.hom → ∀ (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsExp y e →
    ∃ Λ : Submodule ℤ (Fin g → ℂ), DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ ∧
      ∀ z, e z = 1 ↔ z ∈ Λ := by
  intro X G _ _ g hG hg y e he
  obtain ⟨hadd, hsurj, hhol, hd1, hd2⟩ := he
  let A : Over (Sp ℂ) := (Over.pullback y).obj G
  letI : GrpObj A := Functor.grpObjObj
  let φ : A.left ⟶ G.left := pullback.fst G.hom y
  have hp : IsGrpPullback A G y φ := isGrpPullback_pullback G y
  have hA : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG hp
  have hgA : SmoothOfRelativeDimension g A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hp.1 hg
  obtain ⟨L, ⟨u⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif A g hA hgA
  obtain ⟨ht₁, ht₂⟩ := GlobalTheory.TorusTransfer.tangent_bijective u hgA
  have inj : ∀ x x' : 𝟙_ (Over (Sp ℂ)) ⟶ A, x.left ≫ φ = x'.left ≫ φ → x = x' := fun x x' h =>
    Over.OverMorphism.ext (hp.1.hom_ext h (by rw [Over.w x, Over.w x']))
  have lift : ∀ x₀ : Over.mk y ⟶ G, ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x.left ≫ φ = x₀.left := fun x₀ =>
    ⟨Over.homMk (hp.1.lift x₀.left (𝟙 _) ((Over.w x₀).trans (Category.id_comp _).symm)) (hp.1.lift_snd _ _ _),
      hp.1.lift_fst _ _ _⟩
  choose Φ hΦ using lift
  have Φmul : ∀ x x', Φ (x * x') = Φ x * Φ x' := fun x x' => inj _ _ (by
    rw [hΦ, ← hp.2 _ (Φ x) (Φ x') (pushPt hp.1.w (Φ x)) (pushPt hp.1.w (Φ x')) rfl rfl]
    exact mul_left_congr (Category.id_comp _).symm _ _ _ _ (hΦ x).symm (hΦ x').symm)
  have Φinj : Function.Injective Φ := fun x x' h => Over.OverMorphism.ext (by rw [← hΦ, ← hΦ, h])
  have Φone : Φ 1 = 1 := by
    have := Φmul 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have hol : IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun z => (Φ (e z)).left) :=
    FibreUnif.isHolTo_of_isPullback hp.1 (e := fun z => (Φ (e z)).left) (fun z => Over.w (Φ (e z)))
      (by simpa only [hΦ] using hhol)
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hA L g g u ht₁ ht₂ (fun z => Φ (e z))
    (fun z z' => by rw [hadd, Φmul]) hol
  have Finj : Function.Injective F := (injective_iff_map_eq_zero F).2 fun w hw => by
    have hconst : ∀ t : ℂ, e (t • w) = e 0 := fun t => Φinj (by
      rw [← hF, ← hF, map_smul, hw, smul_zero, map_zero])
    have hiff : ∀ v, IsDerivAt0 (fun z => (e z).left) w v ↔ IsDerivAt0 (fun z => (e z).left) 0 v := by
      intro v
      unfold IsDerivAt0
      refine and_congr_right fun _ => forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => ?_
      rw [map_zero, fderiv_apply_eq_zero _ w (fun t => by simp only [hconst t, zero_smul])]
    obtain ⟨v, hv, -⟩ := hd1 w
    exact (hd2 v hv.1).unique hv ((hiff _).1 hv)
  let F' : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofInjectiveEndo F Finj
  have hF' : ∀ z, F' z = F z := fun _ => rfl
  have hker : ∀ z, e z = 1 ↔ F z ∈ u.Λ := fun z => by
    rw [← u.ker, hF, ← Φone, Φinj.eq_iff]
  let Λ : Submodule ℤ (Fin g → ℂ) := u.Λ.comap F.toAddMonoidHom.toIntLinearMap
  have hmem : ∀ z, z ∈ Λ ↔ F z ∈ u.Λ := fun _ => Iff.rfl
  refine ⟨Λ, ?_, ?_, fun z => (hker z).trans (hmem z).symm⟩
  · have := u.discrete
    let c : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) := F'.toContinuousLinearEquiv
    let f : Λ → u.Λ := fun x => ⟨F x, (hmem x).1 x.2⟩
    have hcomp : (Subtype.val ∘ f) = c ∘ (Subtype.val : Λ → Fin g → ℂ) := rfl
    have hemb : Topology.IsEmbedding f := by
      rw [← Topology.IsEmbedding.subtypeVal.of_comp_iff, hcomp]
      exact c.toHomeomorph.isEmbedding.comp Topology.IsEmbedding.subtypeVal
    exact hemb.discreteTopology
  · let Fr : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) := F'.restrictScalars ℝ
    have hset : (Λ : Set (Fin g → ℂ)) = Fr.symm '' (u.Λ : Set (Fin g → ℂ)) := by
      rw [LinearEquiv.image_symm_eq_preimage]
      ext z
      exact hmem z
    rw [hset, ← LinearEquiv.coe_coe, Submodule.span_image, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact Fr.symm.surjective

end GlobalTheory.ExpKernel
