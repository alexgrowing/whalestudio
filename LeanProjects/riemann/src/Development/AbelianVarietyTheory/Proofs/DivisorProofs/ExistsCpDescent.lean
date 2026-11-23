import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralOfTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppBijectiveOfFlatBaseChangeGlobalFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackPowersCartesianGroupSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportedGeneratorDescendBijectiveAppStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalStructureOfPushedPointValuesCubeFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeSymmCompatDescendsFromPushedPointsStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.CPDesc

theorem cancel_of_surjective {X Y : Scheme.{0}} (π : X ⟶ Y) [Surjective π]
    (h : ∀ W, Function.Injective (π.app W)) {Z : Scheme.{0}} (a b : Y ⟶ Z) (hab : π ≫ a = π ≫ b) : a = b := by
  have hb : a.base = b.base := by
    ext y
    obtain ⟨x, rfl⟩ := π.surjective y
    exact congr($hab x)
  refine Scheme.Hom.ext hb fun U ↦ ?_
  have : Mono (π.app (b ⁻¹ᵁ U)) := ConcreteCategory.mono_of_injective _ (h _)
  rw [← cancel_mono (π.app _)]
  simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE, hab]

end GlobalTheory.Mum.CPDesc

namespace GlobalTheory.Mum
open CPDesc

theorem flat_tensor {S : Scheme.{0}} (G H : Over S) [Flat G.hom] [Flat H.hom] : Flat (G ⊗ H).hom := by
  show Flat (pullback.fst G.hom H.hom ≫ G.hom); infer_instance

theorem exists_cp_descent : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G')
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G →
    IsGrpPullback G' G M.π β → ∀ L : LB G.left, L.IsLB → LBIso P'.L.L (L.pull β) → ∃ P : GlobalTheory.UU.CP G, P.L.L = L := by
  intro R _ _ _ hR M G' _ _ _ P' G _ _ β hG h L hL hLw
  obtain ⟨w, hw⟩ := hLw
  obtain ⟨_, -, _, -⟩ := hR
  have hp := (isGen_iff w).1 hw
  obtain ⟨hbijπ, hsurjπ⟩ := GlobalTheory.T.appTop_bijective_and_surjective_normalDomain R M
  have := M.proper
  have hf1 : Flat G.hom := by have := hG.smooth; infer_instance
  have hf2 : Flat (G2 G).hom := flat_tensor _ _
  have hf3 : Flat (G3 G).hom := by have := hf2; exact flat_tensor _ _
  have hf4 : Flat (G4 G).hom := by have := hf3; exact flat_tensor _ _
  have key : ∀ {Y Z : Scheme.{0}} (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ M.S), Flat y → IsPullback p q y M.π →
      (∀ V, Function.Bijective (p.app V).hom) ∧ (∀ {X : Scheme.{0}} (a b : Y ⟶ X), p ≫ a = p ≫ b → a = b) := by
    intro Y Z y p q hy hpb
    have hb := GlobalTheory.T.app_bijective_of_flat_baseChange_globalFunctions R M.S Y Z M.π y p q inferInstance inferInstance hbijπ hy hpb
    have : Surjective p := MorphismProperty.of_isPullback hpb.flip hsurjπ
    exact ⟨hb, fun a b e => cancel_of_surjective p (fun V => (hb V).1) a b e⟩
  obtain ⟨A2, A3, A4⟩ := GlobalTheory.T.isPullback_powers_cartesian_group_square h
  have k0 := key (𝟙 (Sp R)) M.π (𝟙 M.S) inferInstance (IsPullback.id_vert M.π)
  have k1 := key G.hom β G'.hom hf1 h.1
  have k2 := key _ _ _ hf2 A2
  have k3 := key _ _ _ hf3 A3
  have k4 := key _ _ _ hf4 A4

  obtain ⟨rig, hr, -⟩ := GlobalTheory.T.exists_transported_generator_descend_bijective_app hp hL P'.L.isLB M.π k0.1 (K := PUnit) (φ' := fun _ => eSec G')
    (φ := fun _ => eSec G) (fun _ => (cubeMapOf h).e_comm) P'.L.rig P'.L.rigGen

  have hι : (ι[G']).left ≫ β = β ≫ (ι[G]).left := by
    have e := congrArg (fun q => q.left) (map_inv (pushHom h G') (𝟙 G'))
    simp only [Hom.inv_def, Category.id_comp] at e
    refine e.trans ?_
    show (𝟙 _ ≫ β) ≫ _ = _
    rw [Category.id_comp]
  have hc₂ : ∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ β = β ≫ ![(ι[G]).left, 𝟙 G.left] k := fun k => by
    fin_cases k
    · exact hι
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨s, hs, vs⟩ := GlobalTheory.T.exists_transported_generator_descend_bijective_app hp hL P'.L.isLB β k1.1 hc₂ P'.sym P'.sym_gen

  have hc : ∀ I : thK.{0}, thφ G' (x3 G') I ≫ β = (cubeMapOf h).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf h).psum_comm I.down
  obtain ⟨t, ht, vt⟩ := GlobalTheory.T.exists_transported_generator_descend_bijective_app hp hL P'.L.isLB (cubeMapOf h).F3 k3.1 hc P'.c.t P'.c.isGen
  let L₁ : RigLB G := ⟨L, rig, hL, hr⟩
  let Wf : ∀ {T : Over M.S} (z : T.left), ((T.left ⟶ G.left) → L.ι) → ((T.left ⟶ G'.left) → P'.L.L.ι) →
      (T ⟶ G') → (T.left.presheaf.stalk z)ˣ := fun z I J x => gw w x.left z (I (x.left ≫ β)) (J x.left)
  have vcub : ∀ (T : Over M.S) (z : T.left) (I J), Good L z I → Good P'.L.L z J → ∀ a b d : T ⟶ G',
      GlobalTheory.CubTransport.thV (L := L₁) t z I (pushHom h T a) (pushHom h T b) (pushHom h T d) =
        Wf z I J (a * b * d) * (Wf z I J (a * b))⁻¹ * (Wf z I J (a * d))⁻¹ * (Wf z I J (b * d))⁻¹ * Wf z I J a *
          Wf z I J b * Wf z I J d * (Wf z I J 1)⁻¹ * cubV P'.c z J a b d := by
    intro T z I J hI hJ a b d
    have q : (lift a (lift b d)).left ≫ (cubeMapOf h).F3 =
        (lift (pushHom h T a) (lift (pushHom h T b) (pushHom h T d))).left := hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3] <;> rfl
    have e := vt _ (lift a (lift b d)).left z I J hI hJ
    rw [q] at e
    exact e.trans (congrArg₂ (· * ·) (prod_cub a b d (fun q => gw w q z (I (q ≫ β)) (J q))) rfl)
  have vsym : ∀ (T : Over M.S) (z : T.left) (I J), Good L z I → Good P'.L.L z J → ∀ a : T ⟶ G',
      val s (pushHom h T a).left z I = Wf z I J a⁻¹ * (Wf z I J a)⁻¹ * val P'.sym a.left z J := by
    intro T z I J hI hJ a
    exact (vs _ a.left z I J hI hJ).trans
      (congrArg₂ (· * ·) (GlobalTheory.UU.prod_sym a (fun q => gw w q z (I (q ≫ β)) (J q))) rfl)
  obtain ⟨c, hct⟩ := GlobalTheory.T.cubicalStructure_of_pushed_point_values_cube_function h L₁ t ht (fun U => (k2.1 U).1) k2.2 (fun U => (k3.1 U).1) k3.2
    (fun U => (k4.1 U).1) k4.2 fun T z I hI => by
      obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt P'.L.isLB z
      refine GlobalTheory.CubTransport.isCub_of_twist (isCub_cubV P'.c hJ) (MonoidHom.id _) (fun a => (Wf z I J a)⁻¹)
        fun a b d => ?_
      rw [MonoidHom.id_apply, MonoidHom.id_apply, MonoidHom.id_apply, vcub T z I J hI hJ]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, inv_inv]
      abel
  subst hct
  have symCub := GlobalTheory.T.cubeSymm_compat_descends_from_pushed_points h L₁ c s hs (fun U => (k3.1 U).1) k3.2 fun T z I hI x y u => by
    obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt P'.L.isLB z
    refine GlobalTheory.UU.sym_cub_alg (MonoidHom.id _) (fun a => (Wf z I J a)⁻¹) (θ := cubV P'.c z J)
      (θ' := fun a b d => cubV c z I (pushHom h T a) (pushHom h T b) (pushHom h T d))
      (σ := fun a => val P'.sym a.left z J) (σ' := fun a => val s (pushHom h T a).left z I) (fun a b d => ?_)
      (fun a => ?_) (P'.sym_cub T x y u z J hJ)
    · have := vcub T z I J hI hJ a b d
      show cubV P'.c z J a b d = _
      rw [show cubV c z I (pushHom h T a) (pushHom h T b) (pushHom h T d) =
        GlobalTheory.CubTransport.thV (L := L₁) c.t z I (pushHom h T a) (pushHom h T b) (pushHom h T d) from rfl, this]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, inv_inv]
      abel
    · show val P'.sym a.left z J = _
      rw [vsym T z I J hI hJ a]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, inv_inv]
      abel
  have symRig : LB.Gen.Corr L₁.L _ _ _ _ (LB.pullGen L₁.L _ _ s (eSec G)) (LB.oneGen L₁.L) := by
    refine GlobalTheory.GtTorsionPoints.corr_of_val_pull hL M.π (fun U => (k0.1 U).1) (fun a b e => k0.2 a b e)
      fun z I hI => ?_
    obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt P'.L.isLB z
    have e₁ : M.π ≫ eSec G = eSec G' ≫ β := (cubeMapOf h).e_comm.symm
    have e₂ : eSec G' ≫ (ι[G']).left = eSec G' := by
      rw [eSec, ← Over.comp_left, GrpObj.one_inv]
    have e₃ := vs _ (eSec G') z I J hI hJ
    have e₄ : val P'.sym (eSec G') z J = 1 := by
      have := (val_pull hJ P'.sym (eSec G') (𝟙 _)).symm.trans ((val_corr hJ P'.sym_rig (𝟙 _)).trans (val_one _))
      rwa [Category.id_comp] at this
    rw [val_pull hI, e₁, e₃, e₄, Fin.prod_univ_two, val_one]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e₂, Category.comp_id, zpow_one, zpow_neg,
      mul_inv_cancel, _root_.one_mul]
  exact ⟨⟨L₁, c, s, hs, symRig, fun T x y u z J hJ => symCub T x y u z J hJ⟩, rfl⟩

end GlobalTheory.Mum
