import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLawOfHasTestsOfIndep
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitAllAndIsSemiAbelian
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoExtendOfNormalBaseStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedCubicalSymmetricExtensionNormalB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleExtensionThetaSectionSemiAbelianStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianTorsionFiniteAndMulNSurjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ.Assembly

theorem exists_sec_of_lbIso_pull {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB)
    (hL' : L'.IsLB) (H : LBIso L' (L.pull F)) (s : LB.Sec L) :
    ∃ s' : LB.Sec L', ∀ y : X', F y ∈ Out.nonzeroLocus s → y ∈ Out.nonzeroLocus s' := by
  obtain ⟨W, hW⟩ := H
  obtain ⟨s', hs'⟩ := sec_pull_down ((isGen_iff W).1 hW) hL hL' s
  refine ⟨s', fun y hy => ?_⟩
  obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ _).1 hy
  obtain ⟨k, hk⟩ := exists_chart hL' y
  have e := hs' _ (𝟙 _) y j k hj hk
  rw [Category.id_comp, gs_stalkMap F y _ hj] at e
  refine (mem_nonzeroLocus _ _).2 ⟨k, hk, ?_⟩
  exact isUnit_of_mul_isUnit_right ((congrArg IsUnit e).mp (u.map (F.stalkMap y).hom))

theorem mulN_eq_pow' {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) : mulN G n = (𝟙 G) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

theorem mulN_comm_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G]
    [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (n : ℕ) :
    (mulN G' n).left ≫ φ = φ ≫ (mulN G n).left := by
  have e := congrArg (fun q => q.left) (map_pow (pushHom h G') (𝟙 G') n)
  have e₂ : pushHom h G' (𝟙 G') ≫ mulN G n = pushHom h G' (𝟙 G') ^ n := by
    rw [mulN_eq_pow', MonObj.comp_pow, Category.comp_id]
  rw [← e₂, ← mulN_eq_pow'] at e
  refine Eq.trans e ?_
  change (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem exists_sec_fibres {H S : Scheme.{0}} (p : H ⟶ S) {L M : LB H} (hL : L.IsLB) (hM : M.IsLB) (z : S)
    (h₁ : ∃ N : S.Opens, z ∈ N ∧ LBIso (L.pull (p ⁻¹ᵁ N).ι) (M.pull (p ⁻¹ᵁ N).ι))
    (h₂ : ∃ (N : S.Opens) (σ : LB.Sec (M.pull (p ⁻¹ᵁ N).ι)), z ∈ N ∧
      ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, p ((p ⁻¹ᵁ N).ι x) = z') :
    ∃ (N : S.Opens) (σ : LB.Sec (L.pull (p ⁻¹ᵁ N).ι)), z ∈ N ∧
      ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, p ((p ⁻¹ᵁ N).ι x) = z' := by
  obtain ⟨N₁, hz₁, H₁⟩ := h₁
  obtain ⟨N₂, σ, hz₂, H₂⟩ := h₂
  have l₁ : p ⁻¹ᵁ (N₁ ⊓ N₂) ≤ p ⁻¹ᵁ N₁ := fun _ hx => hx.1
  have l₂ : p ⁻¹ᵁ (N₁ ⊓ N₂) ≤ p ⁻¹ᵁ N₂ := fun _ hx => hx.2
  have I : LBIso (L.pull (p ⁻¹ᵁ (N₁ ⊓ N₂)).ι) ((M.pull (p ⁻¹ᵁ N₂).ι).pull (H.homOfLE l₂)) :=
    H₁.chartPull (h := H.homOfLE l₁)
      (chartPullSame L _ _ _ _ fun _ => (H.homOfLE_ι l₁).symm)
      (chartPullLinComb M _ _ _ _ _ fun _ => (H.homOfLE_ι l₂).trans (H.homOfLE_ι l₁).symm)
  obtain ⟨σ', hσ'⟩ := exists_sec_of_lbIso_pull (pull_isLB hM _) (pull_isLB hL _) I σ
  refine ⟨N₁ ⊓ N₂, σ', ⟨hz₁, hz₂⟩, fun z' hz' => ?_⟩
  obtain ⟨x, hx, e⟩ := H₂ z' hz'.2
  have hm : x.1 ∈ p ⁻¹ᵁ (N₁ ⊓ N₂) := by
    change p x.1 ∈ N₁ ⊓ N₂
    exact (show p x.1 = z' from e) ▸ hz'
  refine ⟨⟨x.1, hm⟩, hσ' _ ?_, e⟩
  have : H.homOfLE l₂ ⟨x.1, hm⟩ = x := Subtype.ext (Scheme.homOfLE_apply l₂ _)
  rwa [this]

theorem exists_law_splitAll_cubical : Out.Laws → ∀ (C : Core) (T : C.Theta) (n : ℕ), C.HasTests → C.Indep → C.HasCharts → C.TorsSec n → T.Few n → ∃ L : C.Law, letI := L.grp; letI := L.comm; SplitAll C.GG ∧ IsSemiAbelian C.GG ∧ ∃ (PP : RigLB C.GG) (cub : CubicalStr C.GG PP) (m : CubeMap C.A C.GG), m.F = C.a ∧ m.e = C.U.ι ∧ m.IsPullCubical T.cub cub ∧ (T.L.IsSymmetric → PP.IsSymmetric) ∧ (∀ z : C.Z, ∃ (N : C.Z.Opens) (σ : LB.Sec (PP.L.pull (C.GG.hom ⁻¹ᵁ N).ι)), z ∈ N ∧ ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, C.GG.hom ((C.GG.hom ⁻¹ᵁ N).ι x) = z') ∧ ∀ z : C.Z, ∃ N : C.Z.Opens, z ∈ N ∧ LBIso (T.O₁.pull (C.GG.hom ⁻¹ᵁ N).ι) ((PP.L.pull (mulN C.GG T.m).left).pull (C.GG.hom ⁻¹ᵁ N).ι) := by
  intro hL C T n hT hI hC hS hF
  obtain ⟨L⟩ := Core.nonempty_law_of_hasTests_of_indep C hT hI
  refine ⟨L, ?_⟩
  letI := L.grp
  letI := L.comm
  obtain ⟨h₁, h₂⟩ := GlobalTheory.ZJ.FibreSplit.splitAll_and_isSemiAbelian C L hT hC
  obtain ⟨M, hM, hMa, hσ⟩ := GlobalTheory.T.exists_lineBundle_extension_thetaSection_semiAbelian hL.extend hL.mulN
    GlobalTheory.abelian_torsion_finite_and_mulN_surjective.2 C L T n h₂ hT hS hF
  obtain ⟨-, -, -, -, -, -, -, hcart, -, hN, -⟩ := GlobalTheory.ZJ.core_basic C
  have : Nonempty C.U.toScheme := C.ne.to_subtype
  have := h₂.smooth
  have := h₂.geomConnected
  have hgi : GeometricallyIntegral C.GG.hom := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ C.GG
  obtain ⟨PP, cub, m, hF, he, hp, hsym⟩ :=
    GlobalTheory.NormalCubeExt.exists_cubical_extension C.Z C.normal C.U.toScheme C.U.ι C.GG C.A C.a L.pull T.L T.cub M hM hMa
  have iso := GlobalTheory.T.lineBundleIso_extend_of_normal_base C.Z C.normal C.U.toScheme C.G.toScheme C.A.left C.U.ι C.GG.hom C.e C.a C.A.hom
    h₂.smooth hgi C.e_sec hcart
  have hw : LBIso T.L.L (PP.L.pull C.a) := by
    obtain ⟨w, hw, -⟩ := hp
    exact hF ▸ ⟨w, hw⟩
  refine ⟨h₁, h₂, PP, cub, m, hF, he, hp, hsym, fun z => ?_, fun z => ?_⟩
  · refine exists_sec_fibres C.GG.hom PP.isLB hM z ((iso PP.L M PP.isLB hM ?_).2 z) (hσ z)
    exact (LBIso.trans (pull_isLB hM _) T.L.isLB (pull_isLB PP.isLB _) hMa hw).symm
  · refine (iso T.O₁ (PP.L.pull (mulN C.GG T.m).left) T.isLB (pull_isLB PP.isLB _) ?_).2 z
    have i₁ : LBIso (T.L.L.pull (mulN C.A T.m).left) ((PP.L.pull (mulN C.GG T.m).left).pull C.a) :=
      hw.chartPull (h := (mulN C.A T.m).left) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl)
        (chartPullLinComb PP.L _ _ _ _ _ fun _ => (mulN_comm_of_isGrpPullback L.pull T.m).symm)
    exact LBIso.trans (pull_isLB T.isLB _) (pull_isLB T.L.isLB _) (pull_isLB (pull_isLB PP.isLB _) _)
      (LBIso.symm ⟨T.w, T.w_gen⟩) i₁

end GlobalTheory.ZJ.Assembly
