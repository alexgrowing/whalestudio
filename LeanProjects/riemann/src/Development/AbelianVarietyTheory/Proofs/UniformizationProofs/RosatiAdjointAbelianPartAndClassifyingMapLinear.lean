import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocGenOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceThickening
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGenRosati
import Development.AbelianVarietyTheory.Definitions.Jets.SurjectiveAppTopSqCube

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.EndRosati

open GlobalTheory.CechPic

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G)

section Level

variable (e : ℕ) {f g : G ⟶ G} [IsMonHom f] [IsMonHom g] {a b : D.toPre.P.A ⟶ D.toPre.P.A} [IsMonHom a] [IsMonHom b]
  (hf : (Over.pullback (thick R I e)).map f ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R I e)).map a)
  (hg : (Over.pullback (thick R I e)).map g ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R I e)).map b)
include hf hg

set_option maxHeartbeats 800000 in

theorem exists_gen_invariant [ConnectedSpace (thickObj R I e G).left]
    (sj : Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom)
    (u : LB.Gen (LB.LinComb U.LG.L (rosatiφ G f g) rosatiε)) (hu : u.IsGen)
    (h₀ : LB.Gen.Corr U.LG.L _ _ _ _ (LB.pullGen U.LG.L _ _ u (zero2 G)) (LB.oneGen U.LG.L)) :
    ∃ v : LB.Gen (LB.LinComb D.toPre.P.L (fun k => rosatiφ (thickObj R I e G) ((Over.pullback (thick R I e)).map f)
        ((Over.pullback (thick R I e)).map g) k ≫ (U.gt e).pG.left) rosatiε), v.IsGen ∧
      ∀ (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (z : T.left) (J), Good D.toPre.P.L z J →
        ∀ x x' y y' : T ⟶ thickObj R I e G, x ≫ (U.gt e).q = x' ≫ (U.gt e).q → y ≫ (U.gt e).q = y' ≫ (U.gt e).q →
          val v (lift x y).left z J = val v (lift x' y').left z J := by
  obtain ⟨v, hv, hm⟩ := exists_gen_mul U e hf hg sj u hu h₀
  have := (U.gt e).q_hom
  have := (U.gt e).i_hom
  have hM := D.toPre.P.isLB
  have ti : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (t : Z ⟶ splitTorus _ D.toPre.X),
      push (U.gt e).pG (t ≫ (U.gt e).i) = 1 := fun t =>
    (TorusCoord.im_congr (U.gt e) (x' := 1) (by
      rw [Category.assoc, (U.gt e).isKernel.w, MonObj.one_comp, comp_toUnit_assoc, Hom.one_def])).trans
      (TorusCoord.im_one (U.gt e))
  have unit : ∀ {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x y : T ⟶ thickObj R I e G),
      push (U.gt e).pG x = 1 ∨ push (U.gt e).pG y = 1 → ∃ ρ : Γ(T.left, ⊤)ˣ,
        ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (r : Z ⟶ T) (z : Z.left) (J), Good D.toPre.P.L z J →
          gm r.left z ⊤ ρ = val v (lift (r ≫ x) (r ≫ y)).left z J := fun x y hxy => by
    obtain ⟨ρ, hρ⟩ := exists_unit_of_formal hM (fun V _ h => by
      refine (Finset.prod_congr rfl fun k _ => congrArg (h · ^ rosatiε k) (ros_push (U.gt e).pG
        (TorusCoord.im_mul (U.gt e)) (push_pG U e hf) (push_pG U e hg) x y k).symm).trans
        ((prod_ros a b (push (U.gt e).pG x) (push (U.gt e).pG y) h).trans ?_)
      apply Additive.ofMul.injective
      rcases hxy with h | h
      · rw [h, MonObj.one_comp, _root_.one_mul, _root_.one_mul]
        simp only [ofMul_mul, ofMul_inv, ofMul_one]
        abel
      · rw [h, MonObj.one_comp, _root_.mul_one, _root_.mul_one]
        simp only [ofMul_mul, ofMul_inv, ofMul_one]
        abel) (LB.pullGen D.toPre.P.L _ _ v (lift x y).left) (DVR.pullGen_isGen _ _ _ _ hv _)
    refine ⟨ρ, fun Z r z J hJ => (hρ _ r.left z J hJ).symm.trans ((val_pull hJ _ _ _).trans ?_)⟩
    rw [← Over.comp_left, comp_lift]
  have one : ∀ (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (z : T.left) (J), Good D.toPre.P.L z J →
      ∀ y : T ⟶ thickObj R I e G, val v (lift 1 y).left z J = 1 ∧ val v (lift y 1).left z J = 1 :=
    fun T z J hJ y => by
      have := hm T z J hJ 1 1 y (TorusCoord.im_one (U.gt e))
      rw [_root_.mul_one] at this
      exact ⟨left_eq_mul.1 this.1, left_eq_mul.1 this.2⟩
  have gd : ∀ {Z : Scheme.{0}} (z : Z), ∃ J, Good D.toPre.P.L z J := fun {Z} z => by
    choose J hJ using fun χ : Z ⟶ D.toPre.P.A.left => Geo.Tor.exists_chart hM (χ z)
    exact ⟨J, hJ⟩
  obtain ⟨ρ₁, h₁⟩ := unit (fst (splitTorus _ D.toPre.X) (thickObj R I e G) ≫ (U.gt e).i) (snd _ _) (Or.inl (ti _))
  obtain ⟨ρ₂, h₂⟩ := unit (snd _ _) (fst (splitTorus _ D.toPre.X) (thickObj R I e G) ≫ (U.gt e).i) (Or.inr (ti _))
  have e₁ := fun Z t y z J hJ => h₁ Z (lift t y) z J hJ
  have e₂ := fun Z t y z J hJ => h₂ Z (lift t y) z J hJ
  simp only [lift_fst_assoc, lift_snd] at e₁ e₂
  have k₁ := fun Z t y z => unit_eq_one ρ₁ (fun Z t t' y z => by
      obtain ⟨J, hJ⟩ := gd z
      rw [e₁ Z _ y z J hJ, e₁ Z _ y z J hJ, e₁ Z _ y z J hJ, MonObj.mul_comp]
      exact (hm Z z J hJ _ _ y (ti t)).1) (fun Z t z => by
      obtain ⟨J, hJ⟩ := gd z
      exact (e₁ Z t 1 z J hJ).trans (one Z z J hJ _).2) (Z := Z) t y z
  have k₂ := fun Z t y z => unit_eq_one ρ₂ (fun Z t t' y z => by
      obtain ⟨J, hJ⟩ := gd z
      rw [e₂ Z _ y z J hJ, e₂ Z _ y z J hJ, e₂ Z _ y z J hJ, MonObj.mul_comp]
      exact (hm Z z J hJ _ _ y (ti t)).2) (fun Z t z => by
      obtain ⟨J, hJ⟩ := gd z
      exact (e₂ Z t 1 z J hJ).trans (one Z z J hJ _).1) (Z := Z) t y z
  refine ⟨v, hv, fun T z J hJ x x' y y' hx hy => ?_⟩
  obtain ⟨t, rfl⟩ := TorusCoord.exists_torus (U.gt e) x x' hx
  obtain ⟨t', rfl⟩ := TorusCoord.exists_torus (U.gt e) y y' hy
  rw [(hm T z J hJ _ x' _ (ti t)).1, (hm T z J hJ _ y' x' (ti t')).2, ← e₁ T t _ z J hJ, ← e₂ T t' _ z J hJ, k₁, k₂,
    _root_.one_mul, _root_.one_mul]

theorem exists_gen_thick [ConnectedSpace (thickObj R I e G).left]
    (sj : Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom)
    (u : LB.Gen (LB.LinComb U.LG.L (rosatiφ G f g) rosatiε)) (hu : u.IsGen)
    (h₀ : LB.Gen.Corr U.LG.L _ _ _ _ (LB.pullGen U.LG.L _ _ u (zero2 G)) (LB.oneGen U.LG.L)) :
    ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun k => pullback.fst (D.toPre.P.A ⊗ D.toPre.P.A).hom (thick R I e) ≫
      rosatiφ D.toPre.P.A a b k) rosatiε), t.IsGen := by
  obtain ⟨v, hv, hi⟩ := exists_gen_invariant U e hf hg sj u hu h₀
  have hM := D.toPre.P.isLB
  have := (U.gt e).q_affine
  let m := (U.gt e).q ⊗ₘ (U.gt e).q
  have : Flat m.left := MorphismProperty.pullbackMap (P := @Flat) (U.gt e).q_flat (U.gt e).q_flat
    (Over.w (U.gt e).q).symm (Over.w (U.gt e).q).symm
  have : Surjective m.left :=
    have : MorphismProperty.IsStableUnderComposition @Surjective.{0} := ⟨fun _ _ _ _ => inferInstance⟩
    MorphismProperty.pullbackMap (P := @Surjective) (U.gt e).q_surj (U.gt e).q_surj
      (Over.w (U.gt e).q).symm (Over.w (U.gt e).q).symm
  have qc : QuasiCompact (U.gt e).q.left := inferInstance
  have : QuasiCompact m.left := MorphismProperty.pullbackMap (P := @QuasiCompact) qc qc
    (Over.w (U.gt e).q).symm (Over.w (U.gt e).q).symm
  let Be := thickObj R I e D.toPre.P.A
  let π := lift (push (fstG I e D.toPre.P.A) (fst Be Be)) (push (fstG I e D.toPre.P.A) (snd Be Be))
  have hπ : m.left ≫ π.left = (lift (push (U.gt e).pG (fst _ _)) (push (U.gt e).pG (snd _ _))).left := by
    refine (lift_push (fstG I e D.toPre.P.A) (fst _ _ ≫ (U.gt e).q) (snd _ _ ≫ (U.gt e).q)).trans ?_
    simp only [push, Functor.map_comp, Category.assoc]
    rfl
  obtain ⟨v', hv', vv⟩ := exists_gen hM (φ' := fun k => m.left ≫ π.left ≫ rosatiφ D.toPre.P.A a b k) (ε' := rosatiε)
    (fun V _ h => Finset.prod_congr rfl fun k _ => congrArg (h · ^ rosatiε k)
      ((ros_push' (U.gt e).pG (TorusCoord.im_mul (U.gt e)) (push_pG U e hf) (push_pG U e hg) k).symm.trans
        ((congrArg (· ≫ _) hπ.symm).trans (Category.assoc _ _ _)))) v hv
  obtain ⟨t, ht, -⟩ := CoordCompare.exists_gen_of_val_eq hM _ _ m.left v' hv' fun Z r r' z J hJ h => by
    have hw : r ≫ (thickObj R I e G ⊗ thickObj R I e G).hom = r' ≫ (thickObj R I e G ⊗ thickObj R I e G).hom := by
      rw [← Over.w m, reassoc_of% h]
    let T := Over.mk (r' ≫ (thickObj R I e G ⊗ thickObj R I e G).hom)
    let s : T ⟶ thickObj R I e G ⊗ thickObj R I e G := Over.homMk r hw
    let s' : T ⟶ thickObj R I e G ⊗ thickObj R I e G := Over.homMk r' rfl
    have hs : s ≫ m = s' ≫ m := Over.OverMorphism.ext h
    have := hi T z J hJ (s ≫ fst _ _) (s' ≫ fst _ _) (s ≫ snd _ _) (s' ≫ snd _ _)
      (by simpa [m] using congrArg (· ≫ fst _ _) hs) (by simpa [m] using congrArg (· ≫ snd _ _) hs)
    rw [lift_comp_fst_snd, lift_comp_fst_snd] at this
    exact (vv _ r z J hJ).trans (this.trans (vv _ r' z J hJ).symm)
  have hn : (lift ((Over.pullback (thick R I e)).map (fst D.toPre.P.A D.toPre.P.A))
      ((Over.pullback (thick R I e)).map (snd D.toPre.P.A D.toPre.P.A))).left ≫ π.left =
      pullback.fst (D.toPre.P.A ⊗ D.toPre.P.A).hom (thick R I e) := by
    refine (lift_push (fstG I e D.toPre.P.A) _ _).trans ?_
    rw [push_fstG, push_fstG, lift_comp_fst_snd]
    rfl
  have := (gen_iff_sum hM _ _).1 ⟨_, DVR.pullGen_isGen _ _ _ _ ht (lift ((Over.pullback (thick R I e)).map
    (fst D.toPre.P.A D.toPre.P.A)) ((Over.pullback (thick R I e)).map (snd D.toPre.P.A D.toPre.P.A))).left⟩
  refine (gen_iff_sum hM _ _).2 (Eq.trans (Finset.sum_congr rfl fun k _ => ?_) this)
  rw [← hn, Category.assoc]

end Level

theorem rosatiAdj_generic {f g : G ⟶ G} {a b : A.A ⟶ A.A}
    (hf : (Over.pullback (jK R)).map f ≫ U.gen.hom = U.gen.hom ≫ a)
    (hg : (Over.pullback (jK R)).map g ≫ U.gen.hom = U.gen.hom ≫ b)
    (u : LB.Gen (LB.LinComb U.LG.L (rosatiφ G f g) rosatiε)) (hu : u.IsGen) : RosatiAdj A.A A.L a b := by
  have := U.gen_hom
  let κ : (Over.map (jK R)).obj ((Over.pullback (jK R)).obj G) ⟶ G :=
    Over.homMk (pullback.fst G.hom (jK R)) pullback.condition
  let p : (Over.map (jK R)).obj A.A ⟶ G := push κ U.gen.inv
  have hp : ∀ {f : G ⟶ G} {a : A.A ⟶ A.A}, (Over.pullback (jK R)).map f ≫ U.gen.hom = U.gen.hom ≫ a →
      push p a = p ≫ f := fun {f a} h => by
    have e : a ≫ U.gen.inv = U.gen.inv ≫ (Over.pullback (jK R)).map f := by
      rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]
    have e' : push κ ((Over.pullback (jK R)).map f) = κ ≫ f := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    exact (Functor.map_comp_assoc _ _ _ _).symm.trans ((congrArg (push κ) e).trans (push_comp κ e' _))
  have hc : pull p.left (cls _ U.LG.isLB) = cls _ A.isLB := by
    have e := (cls_eq_iff (LB.isLB_pull A.isLB _) (LB.isLB_pull U.LG.isLB _)).2 U.ext
    refine (pull_comp U.gen.inv.left (pullback.fst G.hom (jK R)) _).trans ((congrArg _ e.symm).trans ?_)
    rw [cls_pull A.isLB, ← pull_comp, ← Over.comp_left, Iso.inv_hom_id]
    exact pull_id _
  have := (gen_iff_sum U.LG.isLB _ _).1 ⟨_, DVR.pullGen_isGen _ _ _ _ hu
    (lift (push p (fst A.A A.A)) (push p (snd A.A A.A))).left⟩
  obtain ⟨t, ht⟩ := (gen_iff_sum A.isLB (rosatiφ A.A a b) rosatiε).2
    (Eq.trans (Finset.sum_congr rfl fun k _ => congrArg (rosatiε k • ·) (by
      refine Eq.trans ?_ (congrArg (pull · _) (ros_push' p (push_mul p U.gen.inv rfl) (hp hf) (hp hg) k).symm)
      exact (congrArg _ hc.symm).trans (pull_comp _ _ _).symm)) this)
  exact fun _ => ⟨⊤, trivial, LB.pullGen _ _ _ t _, DVR.pullGen_isGen _ _ _ _ ht _⟩

theorem cls_of_gen (D : DegPre R) (a : D.P.A ⟶ D.P.A) (χ χ' : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) χ') (D.Oφ a χ)) (Sum.elim Oε Oinvε))) (hu : u.IsGen) :
    pull (𝟙 D.P.A * (toUnit _ ≫ D.c χ')).left (cls _ D.P.isLB) - pull (toUnit D.P.A ≫ D.c χ').left (cls _ D.P.isLB) -
      pull (𝟙 D.P.A : D.P.A ⟶ D.P.A).left (cls _ D.P.isLB) =
    pull (a * (toUnit _ ≫ D.c χ)).left (cls _ D.P.isLB) - pull (toUnit D.P.A ≫ D.c χ).left (cls _ D.P.isLB) -
      pull a.left (cls _ D.P.isLB) := by
  have e : ∀ (p : D.P.A ⟶ D.P.A) (χ : D.X), D.Oφ p χ = ![(p * (toUnit _ ≫ D.c χ)).left,
      (toUnit D.P.A ≫ D.c χ).left, p.left, (toUnit D.P.A ≫ η[D.P.A]).left] := fun _ _ => rfl
  have key : ∀ (V : Type 1) [AddCommGroup V] (F : (D.P.A.left ⟶ D.P.A.left) → V),
      ∑ k, Sum.elim Oε Oinvε k • F (Sum.elim (D.Oφ (𝟙 _) χ') (D.Oφ a χ) k) = 0 →
      F (𝟙 D.P.A * (toUnit _ ≫ D.c χ')).left - F (toUnit D.P.A ≫ D.c χ').left - F (𝟙 D.P.A : D.P.A ⟶ D.P.A).left =
        F (a * (toUnit _ ≫ D.c χ)).left - F (toUnit D.P.A ≫ D.c χ).left - F a.left := fun V _ F h => by
    rw [Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_four] at h
    simp only [Sum.elim_inl, Sum.elim_inr, e, Oε, Oinvε, Matrix.cons_val] at h
    linear_combination (norm := abel) h
  exact key _ (fun ψ => pull ψ (cls _ D.P.isLB)) ((gen_iff_sum D.P.isLB _ _).1 ⟨u, hu⟩)

theorem cls_of_rosati {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {M : LB B.left} (hM : M.IsLB)
    {a b : B ⟶ B} (u : LB.Gen (LB.LinComb M (rosatiφ B a b) rosatiε)) (hu : u.IsGen) {T : Over S} (x y : T ⟶ B) :
    pull ((x ≫ a) * y).left (cls _ hM) - pull (x ≫ a).left (cls _ hM) - pull y.left (cls _ hM) =
      pull (x * (y ≫ b)).left (cls _ hM) - pull x.left (cls _ hM) - pull (y ≫ b).left (cls _ hM) := by
  have h := (gen_iff_sum hM _ _).1 ⟨_, DVR.pullGen_isGen _ _ _ _ hu (lift x y).left⟩
  simp only [ros_comp] at h
  rw [Fin.sum_univ_six] at h
  change (1 : ℤ) • pull ((x ≫ a) * y).left (cls _ hM) + (-1 : ℤ) • pull (x ≫ a).left (cls _ hM) +
    (-1 : ℤ) • pull y.left (cls _ hM) + (-1 : ℤ) • pull (x * (y ≫ b)).left (cls _ hM) +
    (1 : ℤ) • pull x.left (cls _ hM) + (1 : ℤ) • pull (y ≫ b).left (cls _ hM) = 0 at h
  linear_combination (norm := abel) h

end GlobalTheory.EndRosati

open GlobalTheory.EndRosati in

theorem GlobalTheory.UT.rosatiAdj_and_c_linear_of_endU : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ E E' : EndU U.toUnifPre, LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) → RosatiAdj A.A A.L E.aA E'.aA ∧ RosatiAdj D.toPre.P.A D.toPre.P.L E.aB E'.aB ∧ (∀ χ, D.toPre.c (E.h χ) = D.toPre.c χ ≫ E'.aB) ∧ ∀ χ, D.toPre.c (E'.h χ) = D.toPre.c χ ≫ E.aB := by
  intro hLL R _ _ _ I hR D A G _ _ hG U E E' H
  have hGF := hLL.1.globalFns
  obtain ⟨-, -, -, hC⟩ := hR
  have := E.homG
  have := E'.homG
  have := E.homB
  have := E'.homB
  have := hG.geomConnected
  obtain ⟨u, hu, h₀⟩ := (NormRos.normRos_of_lbIso _ G U.LG.L U.LG.isLB E.aG E'.aG H).1
  have hP : AbLaw.IsProjBy D.toPre.P.A.hom := AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)
  have hB : RosatiAdj D.toPre.P.A D.toPre.P.L E.aB E'.aB :=
    loc_gen_of_thickenings hGF I _ (AbelianSchemeGerms.isAbelianScheme_tensor _ _ D.toPre.P.isAb D.toPre.P.isAb)
      (AbLaw.isProjBy_tensor R _ _ hP hP) D.toPre.P.isLB _ _ fun e => by
      have := EndTorus.connectedSpace_thickening I e
      have : GeometricallyConnected (thickObj R I e G).hom :=
        inferInstanceAs (GeometricallyConnected (pullback.snd G.hom (thick R I e)))
      have : ConnectedSpace (thickObj R I e G).left :=
        GroupConn.connectedSpace_of_section (thickObj R I e G).hom (η : 𝟙_ _ ⟶ thickObj R I e G).left (Over.w _)
      exact exists_gen_thick U.toUnifPre e (E.q_lin e) (E'.q_lin e)
        (FamGerm.surjective_appTop_sq_cube U.toUnifPre).2 u hu h₀
  obtain ⟨r, hr, -⟩ := exists_ros hGF D.toPre.P.isAb D.toPre.P.isLB E.aB E'.aB hB
  refine ⟨rosatiAdj_generic U.toUnifPre E.ext E'.ext u hu, hB, fun χ => ?_, fun χ => ?_⟩
  · have h₁ := cls_of_gen D.toPre E.aB χ _ (E.u χ) (E.u_norm χ).1
    have h₂ := cls_of_rosati D.toPre.P.isLB r hr (𝟙 _) (toUnit _ ≫ D.toPre.c χ)
    rw [Category.id_comp, Category.assoc] at h₂
    refine eq_of_translate_cls D.toPre.P.isLB D.toPre.P.ktriv _ _ ?_
    linear_combination (norm := abel) h₁ + h₂
  · have h₁ := cls_of_gen D.toPre E'.aB χ _ (E'.u χ) (E'.u_norm χ).1
    have h₂ := cls_of_rosati D.toPre.P.isLB r hr (toUnit _ ≫ D.toPre.c χ) (𝟙 _)
    rw [Category.id_comp, Category.assoc, mul_comm _ (𝟙 D.toPre.P.A), mul_comm _ E'.aB] at h₂
    refine eq_of_translate_cls D.toPre.P.isLB D.toPre.P.ktriv _ _ ?_
    linear_combination (norm := abel) h₁ - h₂

end
