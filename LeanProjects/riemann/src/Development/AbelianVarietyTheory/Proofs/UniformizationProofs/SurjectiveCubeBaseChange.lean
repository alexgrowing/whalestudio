import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.SameB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CompatAlongOfSquare
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.ValueForm

theorem gen_unique_of_injective {X Y Y' S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K]
    [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ' ε' φ ε)
    (ρ : Y' ⟶ Y) (hρ : ∀ U : Y.Opens, Function.Injective (ρ.app U).hom)
    (p : Y' ⟶ S₀) (e : S₀ ⟶ Y') (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u (e ≫ ρ) y J = val u' (e ≫ ρ) y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J)
    (hJ : Good M z J) : val u r z J = val u' r z J := by
  obtain ⟨t, ht, hv⟩ := exists_gen hM hF u' hu'
  have key := gen_unique hM p e he hp (DVR.pullGen_isGen _ _ _ _ hu ρ) (DVR.pullGen_isGen _ _ _ _ ht ρ)
    (fun y J hJ => (val_pull hJ _ _ _).trans (((h y J hJ).trans (hv _ _ y J hJ).symm).trans (val_pull hJ _ _ _).symm))
  have e₁ : ∀ j, u.s j = t.s j := fun j => by
    apply Units.map_injective (f := (ρ.app (LB.wchart M φ j)).hom.toMonoidHom) (hρ _)
    refine unit_ext fun y hy => ?_
    choose I hI using fun χ : Y' ⟶ X => exists_chart hM (χ y)
    have hy' : ρ y ∈ LB.wchart M φ j := hy
    have k := (val_pull hI _ _ _).symm.trans ((key _ (𝟙 Y') y I hI).trans (val_pull hI _ _ _))
    rw [Category.id_comp] at k
    refine (gm_pull (𝟙 Y') ρ y _ hy' _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') ρ y _ hy' _).symm)
    rw [Category.id_comp]
    exact (gen_trans hu ρ y hy' (Good.mem hI φ ρ)).trans ((congrArg _ k).trans
      (gen_trans ht ρ y hy' (Good.mem hI φ ρ)).symm)
  exact (congrArg (gm r z _) (e₁ _)).trans (hv Z r z J hJ)

theorem sym_cub_of_baseChange {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (f : S' ⟶ S)
    (hi : ∀ U, Function.Injective ((pullback.fst (G3 G).hom f).app U).hom)
    (h3 : Function.Surjective (pullback.snd (G3 G).hom f).appTop.hom) {L : RigLB G} (c : CubicalStr G L)
    (sym : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hs : sym.IsGen)
    (hr : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sym (eSec G)) (LB.oneGen L.L))
    (T : Over S) (x y u : T ⟶ G) (z : T.left) (J) (hJ : Good L.L z J) :
    cubV c z J x⁻¹ y⁻¹ u⁻¹ * val sym (x * y).left z J * val sym (x * u).left z J * val sym (y * u).left z J =
      cubV c z J x y u * val sym (x * y * u).left z J * val sym x.left z J * val sym y.left z J *
        val sym u.left z J := by
  let a := x3 G 0
  let b := x3 G 1
  let d := x3 G 2
  let sy := fun p : G3 G ⟶ G => LB.pullGen L.L _ _ sym p.left
  let cu := fun p q r : G3 G ⟶ G => LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift p (lift q r)).left
  have gs : ∀ p, (sy p).IsGen := fun p => DVR.pullGen_isGen _ _ _ _ hs _
  have gc : ∀ p q r, (cu p q r).IsGen := fun p q r => DVR.pullGen_isGen _ _ _ _ c.isGen _
  have vs : ∀ {T' : Over S} (σ : T' ⟶ G3 G) {z : T'.left} {J}, Good L.L z J → ∀ p,
      val (sy p) σ.left z J = val sym (σ ≫ p).left z J := fun σ z J hJ p => val_pull hJ _ _ _
  let t₁ := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (cu a⁻¹ b⁻¹ d⁻¹) (sy (a * b)))
    (sy (a * d))) (sy (b * d))
  let t₂ := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (cu a b d)
    (sy (a * b * d))) (sy a)) (sy b)) (sy d)
  have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 G) {z : T'.left} {J}, Good L.L z J →
      val t₁ σ.left z J = cubV c z J (σ ≫ a)⁻¹ (σ ≫ b)⁻¹ (σ ≫ d)⁻¹ * val sym ((σ ≫ a) * (σ ≫ b)).left z J *
        val sym ((σ ≫ a) * (σ ≫ d)).left z J * val sym ((σ ≫ b) * (σ ≫ d)).left z J ∧
      val t₂ σ.left z J = cubV c z J (σ ≫ a) (σ ≫ b) (σ ≫ d) * val sym ((σ ≫ a) * (σ ≫ b) * (σ ≫ d)).left z J *
        val sym (σ ≫ a).left z J * val sym (σ ≫ b).left z J * val sym (σ ≫ d).left z J := fun σ z J hJ => by
    constructor
    · rw [← MonObj.comp_mul, ← MonObj.comp_mul, ← MonObj.comp_mul, ← GrpObj.comp_inv, ← GrpObj.comp_inv,
        ← GrpObj.comp_inv]
      exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c σ hJ _ _ _) (vs σ hJ _))) (vs σ hJ _))) (vs σ hJ _))
    · rw [← MonObj.comp_mul, ← MonObj.comp_mul]
      exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
          (val_cub c σ hJ _ _ _) (vs σ hJ _))) (vs σ hJ _))) (vs σ hJ _))) (vs σ hJ _))
  let e : Over.mk f ⟶ G3 G := lift 1 (lift 1 1)
  have e₀ : e ≫ a = 1 := by simp [e, a, x3]
  have e₁ : e ≫ b = 1 := by simp [e, b, x3]
  have e₂ : e ≫ d = 1 := by simp [e, d, x3]
  let ρ : T ⟶ G3 G := lift x (lift y u)
  have r₀ : ρ ≫ a = x := by simp [ρ, a, x3]
  have r₁ : ρ ≫ b = y := by simp [ρ, b, x3]
  have r₂ : ρ ≫ d = u := by simp [ρ, d, x3]
  have key : val t₁ ρ.left z J = val t₂ ρ.left z J := by
    refine gen_unique_of_injective L.isLB (fun V _ k => ?_) (pullback.fst (G3 G).hom f) hi (pullback.snd _ _)
      (pullback.lift e.left (𝟙 _) ((Over.w e).trans (Category.id_comp f).symm)) (pullback.lift_snd _ _ _) h3
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (gc _ _ _) (gs _))
        (gs _)) (gs _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (gc _ _ _) (gs _)) (gs _)) (gs _)) (gs _)) (fun y I hI => ?_) _ ρ.left z J hJ
    · refine (DVR.prod_sum₂ (K := ((thK ⊕ Fin 2) ⊕ Fin 2) ⊕ Fin 2) (K' := Fin 2) (U := V) _
        (DVR.prod_sum₂ (K := (thK ⊕ Fin 2) ⊕ Fin 2) (K' := Fin 2) (U := V) _
          (DVR.prod_sum₂ (K := thK ⊕ Fin 2) (K' := Fin 2) (U := V) _
            (DVR.prod_sum₂ (K := thK) (K' := Fin 2) (U := V) _ (prod_cub a b d k) (prod_sym (a * b * d) k))
            (prod_sym a k)) (prod_sym b k)) (prod_sym d k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := (thK ⊕ Fin 2) ⊕ Fin 2) (K' := Fin 2) (U := V) _
          (DVR.prod_sum₂ (K := thK ⊕ Fin 2) (K' := Fin 2) (U := V) _
            (DVR.prod_sum₂ (K := thK) (K' := Fin 2) (U := V) _ (prod_cub a⁻¹ b⁻¹ d⁻¹ k) (prod_sym (a * b) k))
            (prod_sym (a * d) k)) (prod_sym (b * d) k)).symm)
      simp only [← mul_inv]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · have s1 : val sym (1 : Over.mk f ⟶ G).left y I = 1 := by
        rw [one_left]
        exact (val_pull hI sym (eSec G) _).symm.trans ((val_corr hI hr _).trans (val_one _))
      rw [pullback.lift_fst]
      refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
      rw [e₀, e₁, e₂]
      simp only [inv_one, _root_.mul_one, s1]
  have := (ev ρ hJ).1.symm.trans (key.trans (ev ρ hJ).2)
  rwa [r₀, r₁, r₂] at this

theorem app_generic_injective {R : Type} [CommRing R] [IsDomain R] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of R)) [Flat p] (U : Y.Opens) :
    Function.Injective ((pullback.fst p (jK R)).app U).hom := by
  have hd : IsSchemeTheoreticallyDominant (jK R) := by
    refine ⟨Scheme.IdealSheafData.ext_of_isAffine ?_⟩
    rw [Scheme.Hom.ker_apply]
    simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
    rw [← RingHom.injective_iff_ker_eq_bot]
    have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    have i : Function.Injective ((jK R).appTop ≫ (Scheme.ΓSpecIso _).hom).hom := by
      rw [e, CommRingCat.hom_comp, RingHom.coe_comp]
      exact (IsFractionRing.injective R (FractionRing R)).comp
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
    rw [CommRingCat.hom_comp, RingHom.coe_comp] at i
    exact i.of_comp
  have pb := (IsPullback.of_hasPullback p (jK R)).flip
  have : IsSchemeTheoreticallyDominant (pullback.fst p (jK R)) := .of_isPullback pb
  have : QuasiCompact (pullback.fst p (jK R)) := inferInstance
  exact (pullback.fst p (jK R)).app_injective U

theorem surjective_cube_baseChange (hG : GlobalFnsSt) {S S' : Scheme.{0}} {G : Over S} (f : S' ⟶ S) {A : Over S'}
    [GrpObj A] (hA : IsAbelianScheme A) (gen : (Over.pullback f).obj G ≅ A) :
    Function.Surjective (pullback.snd (G3 G).hom f).appTop.hom := by
  have := hA.comm
  let e : (Over.pullback f).obj (G3 G) ≅ G3 A := (Functor.Monoidal.μIso (Over.pullback f) G (G ⊗ G)).symm ≪≫
    (gen ⊗ᵢ ((Functor.Monoidal.μIso (Over.pullback f) G G).symm ≪≫ (gen ⊗ᵢ gen)))
  have hw : e.hom.left ≫ (G3 A).hom = pullback.snd (G3 G).hom f := Over.w e.hom
  have : IsIso e.hom.left := ((Over.forget _).mapIso e).isIso_hom
  have : IsIso e.hom.left.appTop := inferInstanceAs (IsIso (e.hom.left.app ⊤))
  rw [← hw]
  exact surj_comp (ConcreteCategory.bijective_of_isIso e.hom.left.appTop).2 (surjective_cube hG hA)

section Clauses

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G)

def modelCP (hG : GlobalFnsSt) : CP G where
  L := U.LG
  c := U.cubG
  sym := U.symG
  sym_gen := U.symG_gen
  sym_rig := U.symG_rig
  sym_cub := by
    have := U.smooth
    have : Flat (G3 G).hom := by
      show Flat (pullback.fst G.hom (pullback.fst G.hom G.hom ≫ G.hom) ≫ G.hom)
      infer_instance
    exact sym_cub_of_baseChange (jK R) (app_generic_injective _) (surjective_cube_baseChange hG _ A.isAb U.gen)
      U.cubG U.symG U.symG_gen U.symG_rig

theorem rig_val (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) {z : T.left}
    {N : (T.left ⟶ G.left) → U.LG.L.ι} {J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    (hN : Good U.LG.L z N) (hJ : Good D.toPre.P.L z J) :
    val (L := D.toPre.P.L) (φ := fun _ : PUnit => eSec D.toPre.P.A) (ε := fun _ => 1) D.toPre.rig
        (T.hom ≫ thick R I e) z J =
      TorusInvariance.wVal U e z J N (1 : T ⟶ thickObj R I e G).left *
        val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (T.hom ≫ thick R I e) z N := by
  have hp : (T.hom ≫ eSec (thickObj R I e G)) ≫ (U.gt e).pG.left = (T.hom ≫ thick R I e) ≫ eSec D.toPre.P.A :=
    (Category.assoc _ _ _).trans ((congrArg (T.hom ≫ ·) (UnifPullRig.eSec_pG I (U.gt e))).trans
      (Category.assoc _ _ _).symm)
  have hf : (T.hom ≫ eSec (thickObj R I e G)) ≫ (fstG I e G).left = (T.hom ≫ thick R I e) ≫ eSec G :=
    (Category.assoc _ _ _).trans ((congrArg (T.hom ≫ ·) (UnifPullRig.eSec_fstG I e G)).trans
      (Category.assoc _ _ _).symm)
  rw [one_left, TorusInvariance.wVal, hp, hf]
  obtain ⟨j, hj⟩ : ∃ j, J ((T.hom ≫ thick R I e) ≫ eSec D.toPre.P.A) = j := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, N ((T.hom ≫ thick R I e) ≫ eSec G) = k := ⟨_, rfl⟩
  have mj : ((T.hom ≫ thick R I e) ≫ eSec D.toPre.P.A) z ∈ D.toPre.P.L.U j := hj ▸ hJ _
  have mk : ((T.hom ≫ thick R I e) ≫ eSec G) z ∈ U.LG.L.U k := hk ▸ hN _
  rw [val_of _ _ z J (fun _ => j) (fun _ => hj), val_of _ _ z N (fun _ => k) (fun _ => hk), hj, hk]
  have m₁ : T.hom z ∈ eSec (thickObj R I e G) ⁻¹ᵁ
      ((D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => j) ⊓ (U.LG.L.pull (fstG I e G).left).U (fun _ => k)) :=
    ⟨mem_pull.2 ((congrArg (fun q => q z ∈ D.toPre.P.L.U j) hp).mpr mj),
      mem_pull.2 ((congrArg (fun q => q z ∈ U.LG.L.U k) hf).mpr mk)⟩
  have m₂ : T.hom z ∈ thick R I e ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => k) := mem_pull.2 mk
  have m₃ : T.hom z ∈ thick R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => j) := mem_pull.2 mj
  have W := congrArg (gm T.hom z _) (U.w_rig e (fun _ => j, fun _ => k) (_ ⊓ _ ⊓ _) (inf_le_left.trans inf_le_left)
    (inf_le_left.trans inf_le_right) inf_le_right)
  exact ((gm_res _ z _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _).trans (gm_pull _ _ z _ m₃ _)).symm.trans (W.symm.trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ z _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _).trans (gm_pull _ _ z _ m₁ _))
      ((gm_res _ z _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _).trans (gm_pull _ _ z _ m₂ _)))))

theorem compat_val (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (z : Z) (j : D.toPre.P.L.ι)
    (k : U.LG.L.ι) (hj : (U.gt e).pG.left (x z) ∈ D.toPre.P.L.U j) (hk : (fstG I e G).left (x z) ∈ U.LG.L.U k) :
    gw (U.w (e + 1)) (x ≫ thickMap R I e G) z j (fun _ => k) = gw (U.w e) x z j (fun _ => k) := by
  have m₁ : x z ∈ thickMap R I e G ⁻¹ᵁ ((D.toPre.P.L.pull (U.gt (e + 1)).pG.left).U (fun _ => j) ⊓
      (U.LG.L.pull (fstG I (e + 1) G).left).U (fun _ => k)) :=
    ⟨mem_pull.2 ((congrArg (fun g => g (x z) ∈ D.toPre.P.L.U j) (U.gt_q e)).mpr hj),
      mem_pull.2 ((congrArg (fun g => g (x z) ∈ U.LG.L.U k) (UnifPullRig.thickMap_fstG I e G)).mpr hk)⟩
  have m₂ : x z ∈ (D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => j) ⊓
      (U.LG.L.pull (fstG I e G).left).U (fun _ => k) := ⟨mem_pull.2 hj, mem_pull.2 hk⟩
  have W := congrArg (gm x z _) (U.w_compat e (fun _ => j, fun _ => k) (_ ⊓ _) inf_le_left inf_le_right)
  exact ((gm_res _ z _ (by exact ⟨m₁, m₂⟩) _).trans (gm_pull _ _ z _ m₁ _)).symm.trans
    (W.trans (gm_res _ z _ (by exact ⟨m₁, m₂⟩) _))

def toPreU (hG : GlobalFnsSt) (hS : IsSemiAbelian G)
    (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))) (hw : w.IsGen) :
    PreU I D.toPre A G where
  semi := hS
  gen := U.gen
  gen_hom := U.gen_hom
  P := modelCP U hG
  wA := w
  wA_gen := hw
  gt := U.gt
  gt_q := U.gt_q
  gt_t := U.gt_t
  w := U.w
  w_gen := U.w_gen
  w_vals e T z N J hN hJ W hW := by
    obtain rfl : W = fun x => TorusInvariance.wVal U e z J N x.left := funext hW
    refine ⟨rig_val U e T hN hJ, fun x => TorusInvariance.even_val U x.left hJ hN, fun x y u => ?_⟩
    exact cub_alg ((TorusInvariance.cube_val U ![x, y, u] hJ hN).trans (congrArg₂ (· * ·)
      (TorusInvariance.prod_psum x y u (TorusInvariance.wVal U e z J N)) rfl))
  w_compat := compat_val U

end Clauses

theorem exists_preU_match :
    GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U' : UnifPre I D A G), IsSemiAbelian G → ∀ w : LB.Iso (A.L.pull U'.gen.hom.left) (U'.LG.L.pull (pullback.fst G.hom (jK R))), w.IsGen → ∃ U : PreU I D.toPre A G, Match U U' ∧ HEq U.wA w :=
  fun hG _ _ _ _ _ _ _ _ _ U' hS w hw =>
    ⟨toPreU U' hG hS w hw, ⟨rfl, rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl⟩, HEq.rfl⟩

end GlobalTheory.ValueForm

end
