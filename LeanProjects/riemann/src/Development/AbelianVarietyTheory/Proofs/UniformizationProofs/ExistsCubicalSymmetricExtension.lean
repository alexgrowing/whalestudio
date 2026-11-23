import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueGeneratorExtendDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalExtendsAndExtendGen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CorrOfGenericOfIsSeparated
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubicalSymmetryTransport

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolExtension

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CubTransport

theorem isCub_of_surjective {A A' U : Type} [CommGroup A] [CommGroup A'] [CommGroup U] {θ : A → A → A → U}
    (β : A' →* A) (hβ : Function.Surjective β) (h : IsCub (fun a b c => θ (β a) (β b) (β c))) : IsCub θ := by
  refine ⟨fun x y => ?_, fun x y z => ?_, fun x y z => ?_, fun x x' x'' y => ?_⟩
  · obtain ⟨x, rfl⟩ := hβ x; obtain ⟨y, rfl⟩ := hβ y
    simpa only [map_one] using h.face x y
  · obtain ⟨x, rfl⟩ := hβ x; obtain ⟨y, rfl⟩ := hβ y; obtain ⟨z, rfl⟩ := hβ z
    exact h.s01 x y z
  · obtain ⟨x, rfl⟩ := hβ x; obtain ⟨y, rfl⟩ := hβ y; obtain ⟨z, rfl⟩ := hβ z
    exact h.s12 x y z
  · obtain ⟨x, rfl⟩ := hβ x; obtain ⟨x', rfl⟩ := hβ x'; obtain ⟨x'', rfl⟩ := hβ x''; obtain ⟨y, rfl⟩ := hβ y
    simpa only [map_mul] using h.coc x x' x'' y

theorem isCub_mul_diff {A U : Type} [CommGroup A] [CommGroup U] {θ θ' : A → A → A → U} (hθ : IsCub θ) (Ω : A → U)
    (h : ∀ a b c, θ' a b c = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b *
      Ω c * (Ω 1)⁻¹ * θ a b c) : IsCub θ' :=
  isCub_of_twist hθ (MonoidHom.id A) (fun a => (Ω a)⁻¹) fun a b c => by
    rw [h]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, MonoidHom.id_apply]
    abel

section DVR

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K] {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

omit [IsDomain V] [IsDiscreteValuationRing V] [GrpObj G] [IsCommMonObj G] in

theorem corr_of_generic_val [IsSeparated G.hom] (T : Over (Spec (CommRingCat.of V))) [Flat T.hom]
    {L : LB G.left} (hL : L.IsLB) {I I' : Type} [Fintype I] [Fintype I']
    {φ : I → (T.left ⟶ G.left)} {ε : I → ℤ} {φ' : I' → (T.left ⟶ G.left)} {ε' : I' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (H : ∀ (y : (pullback T.hom (etaK V K) :)) J, Good L y J →
      val t (pullback.fst T.hom (etaK V K)) y J = val t' (pullback.fst T.hom (etaK V K)) y J) :
    LB.Gen.Corr L _ _ _ _ t t' :=
  corr_of_generic_of_isSeparated V K G T L φ ε φ' ε' t t' (corr_of_val hL fun y J hJ => by
    rw [val_pull hJ, val_pull hJ, Category.id_comp]
    exact H y J hJ)

theorem nonempty_cubical_of_generic [IsSeparated G.hom] [Flat G.hom] (L : RigLB G) (t : LB.Gen (Theta G L.L))
    (ht : t.IsGen)
    (h : ∀ (T : Over (Spec (CommRingCat.of K))) (z : T.left) (J), Good L.L z J →
      IsCub (thV t (T := Over.mk (T.hom ≫ etaK V K)) z J)) : Nonempty (CubicalStr G L) := by
  have f₂ : Flat (G2 G).hom := by
    show Flat (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  have f₃ : Flat (G3 G).hom := by
    show Flat (pullback.fst G.hom (G2 G).hom ≫ G.hom)
    infer_instance
  have f₄ : Flat (G4 G).hom := by
    show Flat (pullback.fst G.hom (G3 G).hom ≫ G.hom)
    infer_instance
  let ρ : ∀ T : Over (Spec (CommRingCat.of V)), Over.mk (pullback.snd T.hom (etaK V K) ≫ etaK V K) ⟶ T := fun T =>
    Over.homMk (pullback.fst T.hom (etaK V K)) pullback.condition
  have v : ∀ (T : Over (Spec (CommRingCat.of V))) (y : (pullback T.hom (etaK V K) :)) J, Good L.L y J →
      ∀ a b c : T ⟶ G, val (LB.pullGen L.L (thφ G (x3 G)) thε t (lift a (lift b c)).left)
        (pullback.fst T.hom (etaK V K)) y J =
        thV t (T := Over.mk (pullback.snd T.hom (etaK V K) ≫ etaK V K)) y J (ρ T ≫ a) (ρ T ≫ b) (ρ T ≫ c) := by
    intro T y J hJ a b c
    refine (val_pull hJ _ _ _).trans ?_
    rw [thV, ← comp_lift, ← comp_lift]; rfl
  have v' : ∀ (y : (pullback (G3 G).hom (etaK V K) :)) J,
      val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) t (pullback.fst (G3 G).hom (etaK V K)) y J =
        thV t (T := Over.mk (pullback.snd (G3 G).hom (etaK V K) ≫ etaK V K)) y J
          (ρ _ ≫ x3 G 0) (ρ _ ≫ x3 G 1) (ρ _ ≫ x3 G 2) := by
    intro y J
    have e : lift (x3 G 0) (lift (x3 G 1) (x3 G 2)) = 𝟙 (G3 G) := by
      ext <;> simp [x3]
    rw [thV, ← comp_lift, ← comp_lift, e, Category.comp_id]; rfl
  refine ⟨⟨t, ht, fun i => corr_of_generic_val (K := K) (G2 G) L.isLB fun y J hJ => ?_,
    corr_of_generic_val (K := K) (G3 G) L.isLB fun y J hJ => ?_,
    corr_of_generic_val (K := K) (G3 G) L.isLB fun y J hJ => ?_,
    corr_of_generic_val (K := K) (G4 G) L.isLB fun y J hJ => ?_⟩⟩
  · refine Eq.trans ?_ (val_one _).symm
    have C := h (Over.mk (pullback.snd (G2 G).hom (etaK V K))) y J hJ
    have o : ρ (G2 G) ≫ pzero G _ = 1 := map_one (preHom (ρ (G2 G)))
    fin_cases i
    · exact (v _ y J hJ _ _ _).trans (by rw [o]; exact C.face _ _)
    · exact (v _ y J hJ _ _ _).trans (by rw [o]; exact C.face₂ _ _)
    · exact (v _ y J hJ _ _ _).trans (by rw [o]; exact C.face₃ _ _)
  · exact (v' y J).trans (((h (Over.mk (pullback.snd (G3 G).hom (etaK V K))) y J hJ).s01 _ _ _).trans
      (v _ y J hJ _ _ _).symm)
  · exact (v' y J).trans (((h (Over.mk (pullback.snd (G3 G).hom (etaK V K))) y J hJ).s12 _ _ _).trans
      (v _ y J hJ _ _ _).symm)
  · have C := h (Over.mk (pullback.snd (G4 G).hom (etaK V K))) y J hJ
    have m : ∀ a b : G4 G ⟶ G, ρ (G4 G) ≫ padd G a b = (ρ (G4 G) ≫ a) * (ρ (G4 G) ≫ b) := fun a b =>
      MonObj.comp_mul _ _ _
    refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v _ y J hJ _ _ _) (v _ y J hJ _ _ _))).trans
      (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v _ y J hJ _ _ _) (v _ y J hJ _ _ _))).symm)
    rw [m, m]
    exact C.coc _ _ _ _

variable [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom]
  {A : Over (Spec (CommRingCat.of K))} [GrpObj A] [IsCommMonObj A] {F : A.left ⟶ G.left}

theorem nonempty_cubical (hE : cubical_extendsSt.{0}) (gp : IsGrpPullback A G (etaK V K) F) (L : RigLB G)
    {M : RigLB A} (c : CubicalStr A M) (w : LB.Iso M.L (L.L.pull F)) (hw : w.IsGen) :
    Nonempty (CubicalStr G L) := by
  have hp := gp.1
  obtain ⟨t₁, ht₁, v₁⟩ := exists_up ((isGen_iff w).1 hw) L.isLB M.isLB (φ' := thφ A (x3 A)) (ε := thε) c.t c.isGen
  let P : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd (G3 G).hom (etaK V K))
  let x : Fin 3 → (P ⟶ A) := fun i => Over.homMk
    (hp.lift (pullback.fst _ _ ≫ (x3 G i).left) P.hom (by
      rw [Category.assoc, Over.w]; exact pullback.condition)) (hp.lift_snd _ _ _)
  have hx : ∀ i, (x i).left ≫ F = pullback.fst _ _ ≫ (x3 G i).left := fun i => hp.lift_fst _ _ _
  let l : P ⟶ G3 A := lift (x 0) (lift (x 1) (x 2))
  have lx : ∀ i, l ≫ x3 A i = x i := fun i => by fin_cases i <;> simp [l, x3]
  have f3 : ∀ i, (cubeMapOf gp).F3 ≫ (x3 G i).left = (x3 A i).left ≫ F := cubeMap_comp_proj_three (cubeMapOf gp)
  have hl : l.left ≫ (cubeMapOf gp).F3 = genericFiberCubeInclusion V K G := hom_ext_triple _ fun i => by
    rw [Category.assoc, f3, ← Category.assoc, ← Over.comp_left, lx, hx]
  let κ : (G3 A).left ⟶ pullback (G3 G).hom (etaK V K) := pullback.lift (cubeMapOf gp).F3 (G3 A).hom
    (Over.w (lift (pushPt hp.w (x3 A 0)) (lift (pushPt hp.w (x3 A 1)) (pushPt hp.w (x3 A 2)))))
  have κ₁ : κ ≫ genericFiberCubeInclusion V K G = (cubeMapOf gp).F3 := pullback.lift_fst _ _ _
  have κ₂ : κ ≫ l.left = 𝟙 _ := hom_ext_triple _ fun i => by
    rw [Category.assoc, ← Over.comp_left, lx, Category.id_comp]
    refine hp.hom_ext ?_ ?_
    · rw [Category.assoc, hx, ← Category.assoc]
      exact (congrArg (· ≫ _) κ₁).trans (f3 i)
    · rw [Category.assoc, Over.w, Over.w]
      exact pullback.lift_snd _ _ _
  obtain ⟨t₂, ht₂, v₂⟩ := exists_gen L.isLB (φ' := fun I => genericFiberCubeInclusion V K G ≫ thφ G (x3 G) I) (ε' := thε)
    (fun U _ k => Finset.prod_congr rfl fun I _ => congrArg (fun q => k q ^ thε I) (by
      show _ = genericFiberCubeInclusion V K G ≫ _
      rw [← hl, Category.assoc]
      exact congrArg (l.left ≫ ·) ((cubeMapOf gp).psum_comm I.down)))
    (LB.pullGen L.L _ _ t₁ l.left) (DVR.pullGen_isGen _ _ _ _ ht₁ _)
  have C : ∀ (T : Over (Spec (CommRingCat.of K))) (z : T.left) (J), Good L.L z J →
      IsCub (fun a b d : T ⟶ A => val t₂ ((lift a (lift b d)).left ≫ κ) z J) := by
    intro T z J hJ
    choose J' hJ' using fun χ : T.left ⟶ A.left => exists_chart M.isLB (χ z)
    refine isCub_mul_diff (isCub_cubV c hJ') (fun q => gw w q.left z (J (q.left ≫ F)) (J' q.left)) fun a b d => ?_
    refine (v₂ _ _ z J hJ).trans ((val_pull hJ _ _ _).trans ?_)
    rw [Category.assoc, κ₂, Category.comp_id]
    refine (v₁ _ _ z _ _ (hJ.mem _ _) (Good.mem hJ' _ _)).trans (congrArg₂ (· * ·) (Eq.trans ?_
      (prod_cub a b d (fun q => gw w q z (J (q ≫ F)) (J' q)))) rfl)
    exact Finset.prod_congr rfl fun I _ => by rw [Category.assoc]
  have q : ∀ (T : Over (Spec (CommRingCat.of K))) (a b d : T ⟶ A), (lift a (lift b d)).left ≫ (cubeMapOf gp).F3 =
      (lift (pushHom gp T a) (lift (pushHom gp T b) (pushHom gp T d))).left := fun T a b d => hom_ext_triple _ fun i => by
    rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i <;> simp [x3] <;> rfl
  obtain ⟨t, ⟨ht, htt⟩, -⟩ := hE V K G ((lift (1 : 𝟙_ _ ⟶ A) (lift 1 1)).left ≫ κ) (by
      rw [Category.assoc, κ₁, q, map_one, CubeExtension.eSec_three]
      refine hom_ext_triple _ fun i => ?_
      rw [Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3, Hom.one_def]) L t₂ (corr_of_val L.isLB fun y J hJ => by
      refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_one _).symm)
      rw [Category.id_comp]
      exact (C (𝟙_ _) y J hJ).face 1 1) ht₂
  refine nonempty_cubical_of_generic (K := K) L t ht fun T z J hJ => isCub_of_surjective (pushHom gp T) (fun a => ?_) ?_
  · exact ⟨Over.homMk (hp.lift a.left T.hom (Over.w a)) (hp.lift_snd _ _ _), Over.OverMorphism.ext (hp.lift_fst _ _ _)⟩
  · refine (congrArg IsCub (funext fun a => funext fun b => funext fun d => ?_)).mpr (C T z J hJ)
    rw [← htt]
    refine Eq.trans ?_ (val_pull hJ _ _ _).symm
    rw [Category.assoc, κ₁, q]
    rfl

omit [IsCommMonObj A] [QuasiCompact G.hom] in

theorem exists_symmetry (gp : IsGrpPullback A G (etaK V K) F) {L : LB G.left} (hL : L.IsLB)
    {M : LB A.left} (hM : M.IsLB) (hs : Out.Sym A M) (w : LB.Iso M (L.pull F)) (hw : w.IsGen) :
    ∃ s : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]), s.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ s (eSec G)) (LB.oneGen L) := by
  have hp := gp.1
  obtain ⟨U, hU, t, ht⟩ := hs (IsLocalRing.closedPoint K)
  obtain ⟨n, hn⟩ : ∃ n : pullback G.hom (etaK V K) ⟶ (A.hom ⁻¹ᵁ U).toScheme, n ≫ (A.hom ⁻¹ᵁ U).ι = hp.isoPullback.inv :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      have : A.hom (hp.isoPullback.inv y) = IsLocalRing.closedPoint K :=
        Subsingleton.elim (α := PrimeSpectrum K) _ _
      exact (congrArg (· ∈ U) this).mpr hU), IsOpenImmersion.lift_fac _ _ _⟩
  have hι : (ι[A]).left ≫ F = F ≫ (ι[G]).left := by
    have e := congrArg (fun q => q.left) (map_inv (pushHom gp A) (𝟙 A))
    simp only [Hom.inv_def, Category.id_comp] at e
    refine e.trans ?_
    show (𝟙 _ ≫ F) ≫ _ = _
    rw [Category.id_comp]
  obtain ⟨t₁, ht₁, -⟩ := exists_up ((isGen_iff w).1 hw) hL hM _ (DVR.pullGen_isGen _ _ _ _ ht n)
  obtain ⟨t₂, ht₂, -⟩ := exists_gen hL
    (φ' := fun k : Fin 2 => pullback.fst G.hom (etaK V K) ≫ ![(ι[G]).left, 𝟙 G.left] k) (ε' := ![1, -1])
    (fun _ _ k => Finset.prod_congr rfl fun i _ => congrArg (fun q => k q ^ (![1, -1] : Fin 2 → ℤ) i) (by
      fin_cases i
      · show (n ≫ _ ≫ (ι[A]).left) ≫ F = _ ≫ (ι[G]).left
        rw [← Category.assoc, hn, Category.assoc, hι, ← Category.assoc, hp.isoPullback_inv_fst]
      · show (n ≫ (A.hom ⁻¹ᵁ U).ι) ≫ F = _ ≫ 𝟙 _
        rw [hn, hp.isoPullback_inv_fst, Category.comp_id])) t₁ ht₁
  have a₁ : eSec G ≫ G.hom = 𝟙 _ := Over.w η[G]
  have e₂ : eSec G ≫ (ι[G]).left = eSec G := by
    rw [eSec, ← Over.comp_left, GrpObj.one_inv]
  let e : Spec (CommRingCat.of K) ⟶ pullback G.hom (etaK V K) := pullback.lift (etaK V K ≫ eSec G) (𝟙 _) (by
    rw [Category.assoc, a₁, Category.id_comp]; exact Category.comp_id _)
  have he : e ≫ pullback.fst G.hom (etaK V K) = etaK V K ≫ eSec G := pullback.lift_fst _ _ _
  obtain ⟨u, hu, cu⟩ := DVR.exists_normalized_to hL _ _ t₂ ht₂ (pullback.snd G.hom (etaK V K)) e
    (pullback.lift_snd _ _ _) _ _ (LB.oneGen L) (LB.isGen_oneGen L) (by
      have : e ≫ pullback.fst G.hom (etaK V K) ≫ (ι[G]).left = e ≫ pullback.fst G.hom (etaK V K) := by
        rw [← Category.assoc, he, Category.assoc]
        exact congrArg (etaK V K ≫ ·) e₂
      simp [DVR.fsum, Fin.sum_univ_two, this, Finsupp.single_neg])
  obtain ⟨ρ, hρ, vρ⟩ := exists_gen hL (φ' := fun k : Fin 2 => eSec G ≫ ![(ι[G]).left, 𝟙 G.left] k) (ε' := ![1, -1])
    (fun U _ k => by simp [Fin.prod_univ_two, e₂]) (LB.oneGen L) (LB.isGen_oneGen L)
  obtain ⟨s, ⟨hs₁, hs₂⟩, -⟩ := GenExtend.existsUnique_gen_extend V K G.left G.left G.hom (eSec G) inferInstance
    (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance) a₁ e he L hL
    (Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1] u ρ hu hρ (corr_of_val hL fun y J hJ =>
      (val_corr hJ cu _).trans ((val_one _).trans
        ((val_pull hJ ρ _ _).trans ((vρ _ _ y J hJ).trans (val_one _))).symm))
  have : Flat (𝟙_ (Over (Spec (CommRingCat.of V)))).hom := inferInstanceAs (Flat (𝟙 _))
  refine ⟨s, hs₁, corr_of_generic_val (K := K) (𝟙_ _) hL fun y J hJ => ?_⟩
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_corr hJ cu (pullback.snd _ _)).trans
    ((val_one _).trans (val_one _).symm)))
  rw [← hs₂]
  refine Eq.trans ?_ ((val_pull hJ _ _ _).trans (val_pull hJ _ _ _)).symm
  rw [Category.assoc, he, ← Category.assoc, ← pullback.condition]
  exact congrArg (fun q => val s (q ≫ eSec G) y J) (Category.comp_id _).symm

end DVR

theorem exists_cubical_symmetric_extension : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (eA : (Over.pullback (jK V)).obj G ≅ A.A), IsMonHom eA.hom → ∃ (LG : RigLB G) (_c : CubicalStr G LG) (s : LB.Gen (LB.LinComb LG.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), s.IsGen ∧ LB.Gen.Corr LG.L _ _ _ _ (LB.pullGen LG.L _ _ s (eSec G)) (LB.oneGen LG.L) ∧ (∃ w : LB.Iso (A.L.pull eA.hom.left) (LG.L.pull (pullback.fst G.hom (jK V))), w.IsGen) := by
  intro laws V _ _ _ G _ _ hG A eA hA
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have : IsMonHom eA.symm.hom := inferInstanceAs (IsMonHom eA.inv)
  have gp : IsGrpPullback A.A G (jK V) (eA.inv.left ≫ pullback.fst G.hom (jK V)) :=
    ((isGrpPullback_of_iso eA.symm).comp (isGrpPullback_pullback G (jK V))).congr (Category.id_comp _) rfl
  have hi : eA.inv.left ≫ eA.hom.left = 𝟙 _ := by rw [← Over.comp_left, eA.inv_hom_id, Over.id_left]
  obtain ⟨r, hr⟩ := A.rigid
  obtain ⟨ρ, hρ⟩ := gen_chartPull (chartPullLinComb A.L eA.hom.left (K := PUnit) (fun _ => eSec A.A ≫ eA.inv.left)
    (fun _ => eSec A.A) (fun _ => 1) (𝟙 _) fun _ => by
      rw [Category.assoc, hi, Category.comp_id, Category.id_comp]) r hr
  obtain ⟨L, hφ⟩ := laws.extend V (FractionRing V) G (eSec A.A ≫ eA.inv.left)
    ((Category.assoc _ _ _).trans (cubeMapOf gp).e_comm) (A.L.pull eA.hom.left) (pull_isLB A.isLB _) ρ hρ
  have h₁ : LBIso (A.L.pull eA.hom.left) (L.L.pull (pullback.fst G.hom (jK V))) := LBIso.symm hφ
  obtain ⟨w, hw⟩ : LBIso A.L (L.L.pull (eA.inv.left ≫ pullback.fst G.hom (jK V))) :=
    LBIso.chartPull (chartPullSec A.L _ eA.inv.left hi) (chartPullSame L.L _ _ _ eA.inv.left fun _ => rfl) h₁
  obtain ⟨c⟩ := (laws.cube _ A ⟨A.L, r, A.isLB, hr⟩ rfl).1
  obtain ⟨c'⟩ := nonempty_cubical laws.cubicalExtends gp L c w hw
  obtain ⟨s, hs, hs'⟩ := exists_symmetry gp L.isLB A.isLB A.sym w hw
  exact ⟨L, c', s, hs, hs', h₁⟩

end GlobalTheory.PolExtension
