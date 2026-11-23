import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeDescentSmoothDimension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFieldExtensionBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedSymmetricKernelTrivialDescendFieldExt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedRingActionDescendOfGenerators
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

private theorem lb_descends (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (X X₀ : Scheme.{0}) (f : X ⟶ Sp Ω)
    (f₀ : X₀ ⟶ Sp K) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] (L : LB X)
    (H : IsPullback π f f₀ (spMap (algebraMap K Ω))) (hL : L.IsLB) :
    ∃ S : Finset Ω, ∀ (F : IntermediateField K Ω), (S : Set Ω) ⊆ F → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp F)
      (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (algebraMap K F)) → j ≫ π₁ = π →
      j ≫ f₁ = f ≫ spMap (algebraMap F Ω) → ∃ L₁ : LB X₁, L₁.IsLB ∧ LBIso L (L₁.pull j) := by
  classical
  let ρ : ∀ s : (Finset Ω)ᵒᵖ, X ⟶ (Spread.bcDiagram f₀ Ω).obj s := fun s =>
    H.isoPullback.hom ≫ (Spread.bcCone f₀ Ω).π.app s
  have w : ∀ {s t} (g : s ⟶ t), ρ s ≫ (Spread.bcDiagram f₀ Ω).map g = ρ t := fun g =>
    (Category.assoc _ _ _).trans (congrArg _ ((Spread.bcCone f₀ Ω).w g))
  have hc : IsLimit (schemeConeOfFamily _ ρ w) :=
    (Spread.isLimitBcCone f₀ Ω).ofIsoLimit (Cone.ext H.isoPullback fun _ => rfl).symm
  obtain ⟨s, M, hM, -, h⟩ := LBLimit.exists_lb_of_isLimit _ ρ w hc L hL
  refine ⟨s.unop, fun F hS X₁ f₁ π₁ j H₁ hj₁ hj₂ => ?_⟩
  have hsub : Algebra.adjoin K (s.unop : Set Ω) ≤ F.toSubalgebra := Algebra.adjoin_le hS
  let φ : Algebra.adjoin K (s.unop : Set Ω) →+* F :=
    (Algebra.adjoin K (s.unop : Set Ω)).val.toRingHom.codRestrict F (fun x => hsub x.2)
  let q : X₁ ⟶ pullback f₀ (spMap (algebraMap K (Algebra.adjoin K (s.unop : Set Ω)))) :=
    pullback.lift π₁ (f₁ ≫ spMap φ) (by
      rw [H₁.w, Category.assoc, ← spMap_comp]
      rfl)
  refine ⟨M.pull q, pull_isLB hM _, h X₁ j q ?_⟩
  show j ≫ q = H.isoPullback.hom ≫ Spread.bcMap f₀ (Algebra.adjoin K (s.unop : Set Ω)).val
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hj₁, Category.assoc, Spread.bcMap_fst,
      IsPullback.isoPullback_hom_fst]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hj₂, Category.assoc, ← spMap_comp,
      Category.assoc, Spread.bcMap_snd, IsPullback.isoPullback_hom_snd_assoc]
    rfl

theorem UpperTheory.rosati_polarised_descends_finite_field :
    ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] (c : O →+* O) (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
        [Algebra.IsAlgebraic K Ω] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (j₀ : OAct O B) (P : Out.PolAV (Sp Ω))
        (j : OAct O P.A) (ψ : P.A.left ⟶ B.left), IsActPull j j₀ (spMap (algebraMap K Ω)) ψ → IsRosati c P j →
        ∃ F : IntermediateField K Ω, FiniteDimensional K F ∧ ∃ (P₁ : Out.PolAV (Sp F)) (j₁ : OAct O P₁.A)
          (ψ₁ : P₁.A.left ⟶ B.left), IsActPull j₁ j₀ (spMap (algebraMap K F)) ψ₁ ∧ IsRosati c P₁ j₁ := by
  intro O _ _ c K Ω _ _ _ _ B _ hB j₀ P j ψ hψ hR
  have := hB.proper
  have := hB.comm
  obtain ⟨S, hS⟩ := lb_descends K Ω P.A.left B.left P.A.hom B.hom ψ P.L hψ.1.1 P.isLB
  let F : IntermediateField K Ω := IntermediateField.adjoin K (S : Set Ω)
  have hF : FiniteDimensional K F :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨F, hF, ?_⟩
  have e : spMap (algebraMap K Ω) = spMap (algebraMap F Ω) ≫ spMap (algebraMap K F) :=
    spMap_comp (algebraMap K F) (algebraMap F Ω)
  have hp := exists_isActPull (spMap (algebraMap K F)) j₀
  let χ : P.A.left ⟶ ((Over.pullback (spMap (algebraMap K F))).obj B).left :=
    hp.1.1.lift ψ (P.A.hom ≫ spMap (algebraMap F Ω)) (by rw [hψ.1.1.w, e, Category.assoc])
  have h₁ : χ ≫ pullback.fst B.hom (spMap (algebraMap K F)) = ψ := hp.1.1.lift_fst _ _ _
  have h₂ : χ ≫ ((Over.pullback (spMap (algebraMap K F))).obj B).hom = P.A.hom ≫ spMap (algebraMap F Ω) :=
    hp.1.1.lift_snd _ _ _
  have hG : IsGrpPullback P.A ((Over.pullback (spMap (algebraMap K F))).obj B) (spMap (algebraMap F Ω)) χ :=
    IsGrpPullback.cancel hp.1 (hψ.1.congr e h₁.symm) h₂
  obtain ⟨L₁, hL₁, hL⟩ := hS F (IntermediateField.subset_adjoin _ _) _ _ _ χ hp.1.1 h₁ h₂
  obtain ⟨hab, hdim⟩ := FieldDescentAb.isAbelianScheme_and_relDim_descend _ Ω (algebraMap F Ω) _ P.A χ hG P.isAb
  obtain ⟨hr, hs, hk⟩ :=
    PolDescent.rigidified_sym_kTriv_descend _ Ω (algebraMap F Ω) _ P.A χ L₁ P.L hab hG hL₁ P.isLB hL
  have hamp := AmpleDescent.relAmple_of_fieldExtension _ Ω (algebraMap F Ω) _ P.A χ L₁ P.L hab hG hL₁ P.isLB hL P.ample
  have hact : ∀ a, (j.act a).left ≫ χ = χ ≫ ((OAct.pullback (spMap (algebraMap K F)) B j₀).act a).left := fun a => by
    apply hp.1.1.hom_ext
    · rw [Category.assoc, h₁, Category.assoc, hp.2, ← Category.assoc, h₁, hψ.2]
    · rw [Category.assoc, h₂, ← Category.assoc, Over.w, Category.assoc, Over.w, h₂]
  refine ⟨⟨_, hab, P.g, hdim _ P.smoothDim, L₁, hL₁, hr P.rigid, hs P.sym, hamp, hk P.ktriv⟩,
    OAct.pullback (spMap (algebraMap K F)) B j₀, _, hp, fun a => ?_⟩
  have := P.isAb.comm
  exact RosatiDescent.rosatiAdj_descend (algebraMap F Ω) hab hG hL₁ P.isLB hL (hact a) (hact (c a)) (hR a)
