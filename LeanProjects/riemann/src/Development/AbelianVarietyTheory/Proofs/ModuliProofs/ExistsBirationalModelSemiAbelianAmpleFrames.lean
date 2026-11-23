import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfLbIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperHomOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOnOfPowOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Laws3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
open Classical

namespace GlobalTheory.ModelOfOutput

theorem exists_openImmersion_section {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {U : Scheme.{0}} [IsIntegral U] (g : U ⟶ Sp R) [IsSeparated g] [LocallyOfFiniteType g]
    (x : Sp K ⟶ U) [IsDominant x] (hx : x ≫ g = spMap (algebraMap R K)) :
    ∃ (W : (Sp R).Opens) (j : W.toScheme ⟶ U), Dense (W : Set (Sp R)) ∧ IsOpenImmersion j ∧ IsDominant j ∧
      j ≫ g = W.ι := by
  obtain ⟨e, he⟩ := IsGenericPointHom.fractionField R K
  obtain ⟨W, hW, j, h₁, h₂⟩ := spread_out_of_isGermInjective' (𝟙 (Sp R)) g (x := genericPoint (Sp R)) (e.inv ≫ x)
    (by rw [Category.assoc, hx, Category.comp_id, Iso.inv_comp_eq]; exact he.symm)
  rw [Category.comp_id] at h₂
  have hd : IsDominant j := by
    have : IsDominant (W.fromSpecStalkOfMem _ hW ≫ j) := h₁ ▸ inferInstance
    exact IsDominant.of_comp (W.fromSpecStalkOfMem _ hW) j
  have hr : Set.range j ⊆ Set.range (g ⁻¹ᵁ W).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    show g (j w) ∈ W
    rw [← Scheme.Hom.comp_apply, h₂]
    exact w.2
  have e₁ := IsOpenImmersion.lift_fac (g ⁻¹ᵁ W).ι j hr
  set j' := IsOpenImmersion.lift (g ⁻¹ᵁ W).ι j hr
  have : IsDominant (j' ≫ (g ⁻¹ᵁ W).ι) := e₁.symm ▸ hd
  have : IsDominant j' := IsDominant.of_comp_of_isOpenImmersion _ (g ⁻¹ᵁ W).ι
  have e₂ : j' ≫ g ∣_ W = 𝟙 _ := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, e₁, h₂, Category.id_comp]
  have e₃ : g ∣_ W ≫ j = (g ⁻¹ᵁ W).ι :=
    ext_of_isDominant_of_isSeparated g (by rw [Category.assoc, h₂, morphismRestrict_ι]) j'
      (by rw [← Category.assoc, e₂, Category.id_comp, e₁])
  have : IsIso j' := ⟨g ∣_ W, e₂, by
    rw [← cancel_mono (g ⁻¹ᵁ W).ι, Category.assoc, e₁, e₃, Category.id_comp]⟩
  refine ⟨W, j, W.isOpen.dense ⟨_, hW⟩, ?_, hd, h₂⟩
  rw [← e₁]
  infer_instance

theorem flat_ratModel {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [h : GlobalTheory.ZH.ArithBase o Ω]
    (M : GlobalTheory.ZH.RatModel o Ω) : Flat M.s := by
  have := h.ded
  have := M.sep
  have : IsSchemeTheoreticallyDominant M.pt := .of_isDominant _
  have : QuasiCompact M.pt := ⟨fun U _ _ => (Set.toFinite _).isCompact⟩
  have : Flat (M.pt ≫ M.s) := by
    rw [M.pt_s]
    refine Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 ?_)
    have : FaithfulSMul o Ω := (faithfulSMul_iff_algebraMap_injective o Ω).2 h.inj
    infer_instance
  exact flat_of_schemeDominant_of_isDedekindDomain (O := CommRingCat.of o) M.pt M.s

theorem exists_zOn : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R : Subalgebra o Ω) (t₀ : SAB H (Sp R)) (S : GlobalTheory.ZH.ThetaSys o Ω) (ρ : S.Real) (h : R ≤ S.R) (φ : ρ.P.A.left ⟶ t₀.G.left) (act : OAct (𝓞 E) ρ.P.A) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : GlobalTheory.ZH.ZHOut ρ M U₀ EE) (m : ℕ) (r₀ : ℤ), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) → S.Over₀ M U₀ → IsOpen (abLocus Z.G) → IsGrpPullback ρ.P.A t₀.G (spMap (Subalgebra.inclusion h).toRingHom) φ → LBIso ρ.P.L (t₀.PP.L.pull φ) → (∀ a, (act.act a).left ≫ φ = φ ≫ (t₀.act.act a).left) → (letI := ρ.P.isAb.comm; ∀ a, LBIso (cubeLB ρ.P.A ![fst _ _ ≫ act.act a, snd _ _] ρ.P.L) (cubeLB ρ.P.A ![fst _ _, snd _ _ ≫ act.act (H.bar a)] ρ.P.L)) → (letI := ρ.P.isAb.comm; LBIso ρ.P.L (cubeLB ρ.P.A ![𝟙 _, act.act H.w0] ρ.P.L)) → (∀ r : ℤ, r₀ ≤ r → ∃ A : GlobalTheory.LN.AmpFrames Z.G Z.L.L (m ^ 2), A.r = r ∧ A.s = 1) → ∃ C : ZOn (spMap (algebraMap o R)) t₀ m, IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L (m ^ 2), A.r = r ∧ A.s = 1 := by
  intro _ _ E _ _ _ H o Ω _ _ _ hb R t₀ S ρ h φ act M U₀ EE Z m r₀ _ hfr hO hop hφ hL hact hadj hprim hamp
  obtain ⟨act', h₂, h₃, hact', hgood⟩ := GlobalTheory.TripleOut.exists_triple GlobalTheory.homExtension_semiAbelian_dvr o Ω S ρ M U₀ EE Z
    E H act hO hadj hprim
  let t : SAB H M.Z := SAB.mk (H := H) Z.G Z.semi act' Z.L Z.cub Z.sym h₂ h₃
  have : IsFractionRing R Ω := IsFractionRing.of_field R Ω fun y => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hfr y
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩
  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    exact (GlobalTheory.ZH.top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hO.ne)
  have ex := IsOpenImmersion.lift_fac U₀.ι M.pt hr
  set x := IsOpenImmersion.lift U₀.ι M.pt hr
  have : IsDominant (x ≫ U₀.ι) := ex.symm ▸ inferInstance
  have : IsDominant x := IsDominant.of_comp_of_isOpenImmersion _ U₀.ι
  have : Nonempty U₀.toScheme := ⟨⟨_, hO.ne.some_mem⟩⟩
  have : IsIntegral U₀.toScheme := isIntegral_of_isOpenImmersion U₀.ι
  let g : U₀.toScheme ⟶ Sp R := Z.u₀ ≫ spMap (Subalgebra.inclusion h).toRingHom
  have hx : x ≫ g = spMap (algebraMap R Ω) := by
    rw [← Category.assoc, Z.u₀_gen x ex, ← Spec.map_comp]
    rfl
  have hg : g ≫ spMap (algebraMap o R) = U₀.ι ≫ M.s := by
    refine ext_of_isDominant x ?_
    rw [← Category.assoc, hx, ← Category.assoc, ex, M.pt_s, ← Spec.map_comp]
    rfl
  have := M.sep
  have := M.lft
  have : IsSeparated (g ≫ spMap (algebraMap o R)) := hg ▸ inferInstance
  have : IsSeparated g := IsSeparated.of_comp g (spMap (algebraMap o R))
  have : LocallyOfFiniteType (g ≫ spMap (algebraMap o R)) := hg ▸ inferInstance
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (spMap (algebraMap o R))
  obtain ⟨W, j, hW, hj₁, hj₂, hj⟩ := exists_openImmersion_section g x hx
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull GlobalTheory.laws3.cubePull W.ι t₀
  set tW : SAB H W.toScheme := ⟨(Over.pullback W.ι).obj t₀.G, IsSemiAbelian.pullback W.ι t₀.G t₀.semi,
    OAct.pullback W.ι t₀.G t₀.act, PP', cub, sym, adj, prim⟩
  clear_value tW
  have hP := (isGrpPullback_pullback ρ.P.A Z.u₀).comp hφ
  let ψ : tW.G.left ⟶ pullback ρ.P.A.hom Z.u₀ :=
    hP.1.lift m₁.φ (tW.G.hom ≫ j) (by rw [m₁.cart.1.w, Category.assoc, hj])
  have ψ₁ : ψ ≫ pullback.fst ρ.P.A.hom Z.u₀ ≫ φ = m₁.φ := hP.1.lift_fst _ _ _
  have ψ₂ : ψ ≫ pullback.snd ρ.P.A.hom Z.u₀ = tW.G.hom ≫ j := hP.1.lift_snd _ _ _
  have hψ : IsGrpPullback tW.G ((Over.pullback Z.u₀).obj ρ.P.A) j ψ :=
    hP.cancel (m₁.cart.congr hj.symm ψ₁.symm) ψ₂
  have hA : IsProper ρ.P.A.hom := GlobalTheory.ZH.isProper_hom_of_relAmple ρ.P.ample
  have hA' : IsProper tW.G.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) hψ.1 (inferInstanceAs (IsProper (pullback.snd ρ.P.A.hom Z.u₀)))
  have hψa : ∀ a, (tW.act.act a).left ≫ ψ = ψ ≫ ((Over.pullback Z.u₀).map (act.act a)).left := fun a => by
    have A : ((Over.pullback Z.u₀).map (act.act a)).left ≫ pullback.fst ρ.P.A.hom Z.u₀ =
      pullback.fst ρ.P.A.hom Z.u₀ ≫ (act.act a).left := pullback.lift_fst _ _ _
    have B : ((Over.pullback Z.u₀).map (act.act a)).left ≫ pullback.snd ρ.P.A.hom Z.u₀ =
      pullback.snd ρ.P.A.hom Z.u₀ := Over.w ((Over.pullback Z.u₀).map (act.act a))
    apply hP.1.hom_ext
    · calc ((tW.act.act a).left ≫ ψ) ≫ pullback.fst ρ.P.A.hom Z.u₀ ≫ φ
          = m₁.φ ≫ (t₀.act.act a).left := by rw [Category.assoc, ψ₁]; exact m₁.act a
        _ = ψ ≫ (pullback.fst ρ.P.A.hom Z.u₀ ≫ (act.act a).left) ≫ φ := by
          rw [← ψ₁]; simp only [Category.assoc, hact]
        _ = _ := by rw [← A]; simp only [Category.assoc]
    · calc ((tW.act.act a).left ≫ ψ) ≫ pullback.snd ρ.P.A.hom Z.u₀
          = tW.G.hom ≫ j := by rw [Category.assoc, ψ₂, ← Category.assoc, Over.w]
        _ = ψ ≫ ((Over.pullback Z.u₀).map (act.act a)).left ≫ pullback.snd ρ.P.A.hom Z.u₀ := by rw [B, ψ₂]
        _ = _ := (Category.assoc _ _ _).symm
  have hLW : LBIso tW.PP.L (t.PP.L.pull (ψ ≫ Z.φ)) := by
    have a₁ : LBIso tW.PP.L (t₀.PP.L.pull m₁.φ) := by
      obtain ⟨w, hw, -⟩ := m₁.lin
      exact ⟨w, hw⟩
    have a₂ : LBIso (ρ.P.L.pull (ψ ≫ pullback.fst ρ.P.A.hom Z.u₀)) (t₀.PP.L.pull m₁.φ) :=
      GenSpread.lbIso_pull_of_lbIso hL _ (by rw [Category.assoc, ψ₁])
    have a₃ : LBIso (Z.L.L.pull (ψ ≫ Z.φ)) (ρ.P.L.pull (ψ ≫ pullback.fst ρ.P.A.hom Z.u₀)) :=
      GenSpread.lbIso_pull_comp ψ rfl rfl ⟨Z.w, Z.w_gen⟩
    exact LBIso.trans tW.PP.isLB (pull_isLB t₀.PP.isLB _) (pull_isLB Z.L.isLB _) a₁
      (LBIso.trans (pull_isLB Z.L.isLB _) (pull_isLB ρ.P.isLB _) (pull_isLB t₀.PP.isLB _) a₃ a₂).symm
  obtain ⟨m₂, -⟩ := GlobalTheory.exists_sabMap_of_lbIso E H M.Z W.toScheme t tW (j ≫ U₀.ι) (ψ ≫ Z.φ)
    ⟨inferInstance, fun y _ K _ _ p _ => inferInstance⟩ (hψ.comp Z.cart)
    (fun a => by
      rw [← Category.assoc, hψa, Category.assoc, Category.assoc]
      exact congrArg (ψ ≫ ·) (hact' a)) hLW
  obtain ⟨A, hA₁, hA₂⟩ := hamp r₀ le_rfl
  have : IsDominant U₀.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact U₀.isOpen.dense hO.ne⟩
  exact ⟨⟨M.Z, M.s, hO.normal, hO.proj, flat_ratModel M, t, Z.qproj,
    hgood (GlobalTheory.ZH.abOpen_of_isOpen_abLocus o Ω S ρ M U₀ EE Z hO hop), W, hW, j ≫ U₀.ι, inferInstance, inferInstance,
    by rw [Category.assoc, ← hg, ← Category.assoc, hj], tW, m₁, m₂, A⟩, M.integral, hA₂,
    fun r hr => hamp r (hA₁ ▸ hr)⟩

end GlobalTheory.ModelOfOutput
