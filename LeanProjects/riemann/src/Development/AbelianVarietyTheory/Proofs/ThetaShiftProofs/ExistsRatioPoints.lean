import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ESecStruct
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusCoord

theorem indep_fst {S : Scheme.{0}} {H B T : Over S} (q : H ⟶ B) [Flat q.left] [Surjective q.left]
    [QuasiCompact q.left] (hB : Function.Surjective (snd B T).left.appTop.hom)
    (ρ : Γ((H ⊗ T).left, ⊤))
    (hinv : ∀ (Z : Over S) (a a' : Z ⟶ H) (b : Z ⟶ T), a ≫ q = a' ≫ q →
      (lift a b).left.appTop.hom ρ = (lift a' b).left.appTop.hom ρ)
    {Z : Over S} (a a' : Z ⟶ H) (b : Z ⟶ T) :
    (lift a b).left.appTop.hom ρ = (lift a' b).left.appTop.hom ρ := by
  have hp : IsPullback (q ▷ T).left (pullback.fst H.hom T.hom) (pullback.fst B.hom T.hom) q.left := by
    refine IsPullback.of_right ?_ (Over.whiskerRight_left_fst q)
      (IsPullback.of_hasPullback B.hom T.hom).flip
    rw [Over.whiskerRight_left_snd, Over.w q]
    exact (IsPullback.of_hasPullback H.hom T.hom).flip
  have h1 : Flat (q ▷ T).left := MorphismProperty.of_isPullback (P := @Flat) hp.flip ‹_›
  have h2 : Surjective (q ▷ T).left := MorphismProperty.of_isPullback (P := @Surjective) hp.flip ‹_›
  have h3 : QuasiCompact (q ▷ T).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hp.flip ‹_›
  have hc : ∀ {Y : Scheme.{0}} (y₁ y₂ : Y ⟶ (H ⊗ T).left), y₁ ≫ (q ▷ T).left = y₂ ≫ (q ▷ T).left →
      y₁ ≫ TLinPf.mOf ρ = y₂ ≫ TLinPf.mOf ρ := by
    intro Y y₁ y₂ h
    have hw : y₁ ≫ (H ⊗ T).hom = y₂ ≫ (H ⊗ T).hom := by
      rw [← Over.w (q ▷ T), ← Category.assoc, h, Category.assoc]
    let Yo : Over S := Over.mk (y₂ ≫ (H ⊗ T).hom)
    let z₁ : Yo ⟶ H ⊗ T := Over.homMk y₁ hw
    let z₂ : Yo ⟶ H ⊗ T := Over.homMk y₂ rfl
    have hz : z₁ ≫ q ▷ T = z₂ ≫ q ▷ T := Over.OverMorphism.ext h
    have e₁ : z₁ ≫ snd H T = z₂ ≫ snd H T := by
      simpa using congrArg (· ≫ snd B T) hz
    have e₂ : (z₁ ≫ fst H T) ≫ q = (z₂ ≫ fst H T) ≫ q := by
      simpa using congrArg (· ≫ fst B T) hz
    have := hinv Yo _ _ (z₂ ≫ snd H T) e₂
    rw [lift_comp_fst_snd, ← e₁, lift_comp_fst_snd] at this
    rw [TLinPf.comp_mOf, TLinPf.comp_mOf]
    exact congrArg TLinPf.mOf this
  have hfac := EffectiveEpi.fac (q ▷ T).left (TLinPf.mOf ρ) hc
  obtain ⟨κ, hκ⟩ := hB (TLinPf.fnOf (EffectiveEpi.desc (q ▷ T).left (TLinPf.mOf ρ) hc))
  have hρ : ρ = (q ▷ T).left.appTop.hom ((snd B T).left.appTop.hom κ) := by
    rw [hκ, ← TLinPf.fnOf_comp, hfac, TLinPf.fnOf_mOf]
  have key : ∀ a : Z ⟶ H, (lift a b).left.appTop.hom ρ = b.left.appTop.hom κ := fun a => by
    have e : (lift a b).left ≫ (q ▷ T).left ≫ (snd B T).left = b.left := by
      rw [← Over.comp_left, ← Over.comp_left, whiskerRight_snd, lift_snd]
    rw [hρ, ← e, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
    rfl
  rw [key, key]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

abbrev im {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x : T ⟶ thickObj R I e G) :
    (Over.map (thick R I e)).obj T ⟶ D.P.A :=
  (Over.map (thick R I e)).map x ≫ g.pG

theorem im_mul {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x x' : T ⟶ thickObj R I e G) :
    im g (x * x') = im g x * im g x' := by
  have := g.q_hom
  have key : ∀ y : T ⟶ thickObj R I e G,
      im g y = pushHom (isGrpPullback_pullback D.P.A (thick R I e)) T (y ≫ g.q) := fun y =>
    Over.OverMorphism.ext (Category.assoc _ _ _).symm
  rw [key, key, key, MonObj.mul_comp]
  exact map_mul _ _ _

theorem im_one {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} :
    im g (1 : T ⟶ thickObj R I e G) = 1 := by
  have := im_mul g (1 : T ⟶ thickObj R I e G) 1
  rw [_root_.mul_one] at this
  exact left_eq_mul.1 this

theorem im_congr {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} {x x' : T ⟶ thickObj R I e G}
    (h : x ≫ g.q = x' ≫ g.q) : im g x = im g x' := by
  simp only [im, GtCoord.pG, ← Category.assoc, ← Functor.map_comp, h]

abbrev cPt (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (χ : D.X) :
    (Over.map (thick R I e)).obj T ⟶ D.P.A :=
  DegPre.cT D ((Over.map (thick R I e)).obj T) χ

abbrev lhs {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x x' : T ⟶ thickObj R I e G)
    (χ : D.X) :=
  LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) (x * x').left)
    (DegPre.cubAtT D ((Over.map (thick R I e)).obj T) (cPt T χ) (im g x) (im g x'))

abbrev rhs {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x x' : T ⟶ thickObj R I e G)
    (χ : D.X) :=
  LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) x.left) (LB.pullGen D.P.L _ _ (g.t χ) x'.left)

def cubeVal {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (χ : D.X) (z : Z.left)
    (J : (Z.left ⟶ D.P.A.left) → D.P.L.ι) (a b : Z ⟶ thickObj R I e G) :
    (Z.left.presheaf.stalk z)ˣ :=
  cubV D.cub (T := (Over.map (thick R I e)).obj Z) z J (cPt Z χ) (im g a) (im g b)

section Val

variable {T Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (χ : D.X) {z : Z.left}
  {J : (Z.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
include hJ

theorem val_lhs (x x' : T ⟶ thickObj R I e G) (r : Z ⟶ T) :
    val (lhs g x x' χ) r.left z J = val (g.t χ) ((r ≫ x) * (r ≫ x')).left z J *
      cubeVal g χ z J (r ≫ x) (r ≫ x') := by
  refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_pull hJ _ _ _).trans ?_)
    ((val_cub D.cub ((Over.map (thick R I e)).map r) hJ _ _ _).trans ?_))
  · rw [← Over.comp_left, MonObj.comp_mul]
  · unfold cubeVal
    congr 1 <;> simp [im]

theorem val_rhs (x x' : T ⟶ thickObj R I e G) (r : Z ⟶ T) :
    val (rhs g x x' χ) r.left z J =
      val (g.t χ) (r ≫ x).left z J * val (g.t χ) (r ≫ x').left z J :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _) (val_pull hJ _ _ _))

theorem val_unit : val (g.t χ) (1 : Z ⟶ thickObj R I e G).left z J = 1 :=
  (val_pull hJ (g.t χ) (eSec (thickObj R I e G)) (toUnit Z).left).symm.trans
    ((val_corr hJ (g.t_unit χ) _).trans (val_one _))

theorem val_torus (τ : Z ⟶ WeightPf.Te D I e) (a : Z ⟶ thickObj R I e G) :
    val (g.t χ) ((τ ≫ g.i) * a).left z J =
      gm τ.left z ⊤ (charUnit _ D.X χ) * val (g.t χ) a.left z J := by
  have h := val_corr hJ (g.t_weight χ) (lift τ a).left
  rw [val_pull hJ, val_mul hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, lift_snd] at h
  have e1 : lift τ a ≫ lift (fst (WeightPf.Te D I e) (thickObj R I e G) ≫ g.i) (snd _ _) ≫
      μ[thickObj R I e G] = (τ ≫ g.i) * a := by
    rw [← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]; rfl
  rw [e1] at h
  refine h.trans (congrArg (· * _) ?_)
  refine (gm_res _ z _ (hJ.mem (K := PEmpty) PEmpty.elim (lift τ a).left) _).trans
    ((gm_pull _ _ z ⊤ trivial _).trans ?_)
  rw [← Over.comp_left, lift_fst]

end Val

theorem exists_ratio_points {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (x x' : T ⟶ thickObj R I e G) (χ : D.X) :
    ∃ ρ : Γ(T.left, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good D.P.L z J →
      val (lhs g x x' χ) r z J = gm r z ⊤ ρ * val (rhs g x x' χ) r z J := by
  have hO : ∀ (y : T ⟶ thickObj R I e G) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U),
      ∏ k, h (y.left ≫ D.Oφ g.pG χ k) ^ Oinvε k =
        (h (cPt T χ * im g y).left)⁻¹ * h (cPt T χ).left * h (im g y).left *
          (h (1 : (Over.map (thick R I e)).obj T ⟶ D.P.A).left)⁻¹ := by
    intro y U _ h
    have e0 : ∀ k, y.left ≫ D.Oφ g.pG χ k = D.Oφ (im g y) χ k := fun k =>
      WeightPf.Oφ_comp ((Over.map (thick R I e)).map y) g.pG χ k
    simp only [e0]
    rw [Fin.prod_univ_four, mul_comm (cPt T χ)]
    show h _ ^ (-1 : ℤ) * h _ ^ (1 : ℤ) * h _ ^ (1 : ℤ) * h _ ^ (-1 : ℤ) = _
    rw [zpow_neg_one, zpow_neg_one, zpow_one, zpow_one]
    rfl
  obtain ⟨t, -, hv⟩ := exists_gen D.P.isLB (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [mul_inv_eq_one]
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_sum_type _).symm)
      refine (congrArg₂ (· * ·) (hO (x * x') h) (prod_cub (cPt T χ) (im g x) (im g x') h)).trans
        (Eq.trans ?_ (congrArg₂ (· * ·) (hO x h) (hO x' h)).symm)
      rw [im_mul, _root_.mul_assoc (cPt T χ)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen D.P.L _ _ _ _ (lhs g x x' χ) (LB.invGen D.P.L _ _ (rhs g x x' χ)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (g.t_gen χ) _)
        (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))
      (DVR.invGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.pullGen_isGen _ _ _ _ (g.t_gen χ) _) (DVR.pullGen_isGen _ _ _ _ (g.t_gen χ) _))))
  have le : (⊤ : T.left.Opens) ≤ LB.wchart D.P.L (PEmpty.elim : PEmpty → (T.left ⟶ D.P.A.left))
      PEmpty.elim := fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  have h := hv Z r z J hJ
  rw [val_mul hJ, val_inv, val_of t r z J PEmpty.elim (fun k => k.elim)] at h
  exact mul_inv_eq_iff_eq_mul.1 ((gm_res r z le trivial _).trans h).symm

theorem appTop_eq_of_gm {Y Z : Scheme.{0}} (r r' : Z ⟶ Y) (ρ : Γ(Y, ⊤)ˣ)
    (h : ∀ z, gm r z ⊤ ρ = gm r' z ⊤ ρ) : r.appTop.hom ρ.val = r'.appTop.hom ρ.val := by
  apply TopCat.Presheaf.section_ext Z.sheaf ⊤
  intro z hz
  have := congrArg Units.val (h z)
  rw [gm_val r z ⊤ trivial, gm_val r' z ⊤ trivial] at this
  exact this

theorem gm_eq_of_appTop {Y Z : Scheme.{0}} (r r' : Z ⟶ Y) (ρ : Γ(Y, ⊤)ˣ)
    (h : r.appTop.hom ρ.val = r'.appTop.hom ρ.val) (z : Z) : gm r z ⊤ ρ = gm r' z ⊤ ρ := by
  apply Units.ext
  rw [gm_val r z ⊤ trivial, gm_val r' z ⊤ trivial]
  exact congrArg (Z.presheaf.germ ⊤ z trivial).hom h

theorem snd_surj (hGF : GlobalFnsSt) {S : Scheme.{0}} (B T : Over S) [GrpObj B]
    (hB : IsAbelianScheme B) : Function.Surjective (snd B T).left.appTop.hom :=
  fun v => TLinPf.const_pullback hGF T.hom B hB v

theorem exists_torus {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (a a' : Z ⟶ thickObj R I e G) (h : a ≫ g.q = a' ≫ g.q) :
    ∃ τ : Z ⟶ WeightPf.Te D I e, a = (τ ≫ g.i) * a' := by
  have := g.q_hom
  have hinv : a'⁻¹ ≫ g.q = (a' ≫ g.q)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← MonObj.mul_comp, inv_mul_cancel, MonObj.one_comp]
  have hd : (a * a'⁻¹) ≫ g.q = toUnit Z ≫ η[thickObj R I e D.P.A] := by
    rw [MonObj.mul_comp, hinv, h, mul_inv_cancel, Hom.one_def]
  refine ⟨g.isKernel.lift (a * a'⁻¹) (toUnit Z) hd, ?_⟩
  rw [g.isKernel.lift_fst, inv_mul_cancel_right]

theorem exists_univ_ratio (χ : D.X) :
    ∃ ρ : Γ((thickObj R I e G ⊗ thickObj R I e G).left, ⊤)ˣ,
      ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (a b : Z ⟶ thickObj R I e G)
      (z : Z.left) (J : (Z.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
      val (g.t χ) (a * b).left z J * cubeVal g χ z J a b =
        gm (lift a b).left z ⊤ ρ * (val (g.t χ) a.left z J * val (g.t χ) b.left z J) := by
  obtain ⟨ρ, hρ⟩ := exists_ratio_points g (fst (thickObj R I e G) (thickObj R I e G)) (snd _ _) χ
  refine ⟨ρ, fun Z a b z J hJ => ?_⟩
  have := ((val_lhs g χ hJ _ _ (lift a b)).symm.trans (hρ _ (lift a b).left z J hJ)).trans
    (congrArg (_ * ·) (val_rhs g χ hJ _ _ (lift a b)))
  rwa [lift_fst, lift_snd] at this

theorem cancel_torus {U : Type} [CommGroup U] {ab ab' a a' b c c' ρ ρ' τ : U}
    (k₁ : ab * c = ρ * (a * b)) (k₂ : ab' * c' = ρ' * (a' * b)) (t₁ : a = τ * a') (t₂ : ab = τ * ab')
    (hc : c = c') : ρ = ρ' := by
  rw [t₁, t₂, hc, _root_.mul_assoc, k₂, mul_left_comm, _root_.mul_assoc] at k₁
  exact (mul_right_cancel k₁).symm

theorem cancel_unit {U : Type} [CommGroup U] {ab o b c ρ : U}
    (k : ab * c = ρ * (o * b)) (h₁ : ab = b) (h₂ : c = 1) (h₃ : o = 1) : ρ = 1 := by
  rw [h₁, h₂, h₃, _root_.one_mul, _root_.mul_one] at k
  exact right_eq_mul.1 k

theorem val_congr {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (χ : D.X)
    {a a' : Z ⟶ thickObj R I e G} (h : a = a') (z : Z.left)
    (J : (Z.left ⟶ D.P.A.left) → D.P.L.ι) :
    val (g.t χ) a.left z J = val (g.t χ) a'.left z J := by rw [h]

theorem val_t_mul_points (hGF : GlobalFnsSt) {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (χ : D.X) (a b : Z ⟶ thickObj R I e G) (z : Z.left) (J : (Z.left ⟶ D.P.A.left) → D.P.L.ι)
    (hJ : Good D.P.L z J) :
    val (g.t χ) (a * b).left z J * cubeVal g χ z J a b =
      val (g.t χ) a.left z J * val (g.t χ) b.left z J := by
  obtain ⟨ρ, key⟩ := exists_univ_ratio g χ
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have hinv : ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (a a' b : Z ⟶ thickObj R I e G), a ≫ g.q = a' ≫ g.q →
      (lift a b).left.appTop.hom ρ.val = (lift a' b).left.appTop.hom ρ.val := by
    intro Z a a' b h
    obtain ⟨τ, ha⟩ := exists_torus g a a' h
    have hab : a * b = (τ ≫ g.i) * (a' * b) := by rw [← _root_.mul_assoc, ← ha]
    refine appTop_eq_of_gm _ _ ρ fun z => ?_
    obtain ⟨J, hJ'⟩ := TLinPf.idx_exists D.P.L D.P.isLB z
    have hJ : Good D.P.L z J := hJ'
    have k₁ := key Z a b z J hJ
    have k₂ := key Z a' b z J hJ
    have t₁ := val_torus g χ hJ τ a'
    have t₂ := val_torus g χ hJ τ (a' * b)
    have c : cubeVal g χ z J a b = cubeVal g χ z J a' b := by
      unfold cubeVal
      rw [im_congr g h]
    exact cancel_torus k₁ k₂ ((val_congr g χ ha z J).trans t₁)
      ((val_congr g χ hab z J).trans t₂) c
  have hind := indep_fst g.q (snd_surj hGF _ _ (TLinPf.isAb_pullback _ _ D.P.isAb)) ρ.val hinv a 1 b
  have k₁ := key Z 1 b z J hJ
  have c : cubeVal g χ z J 1 b = 1 := by
    unfold cubeVal
    rw [im_one]
    exact (isCub_cubV D.cub (T := (Over.map (thick R I e)).obj Z) hJ).face₂ _ _
  have h1 := cancel_unit k₁
    (val_congr g χ (_root_.one_mul b) z J) c (val_unit g χ hJ)
  exact (key Z a b z J hJ).trans ((congrArg (· * _)
    ((gm_eq_of_appTop _ _ ρ hind z).trans h1)).trans (_root_.one_mul _))

theorem t_mul_points (hGF : GlobalFnsSt) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (x x' : T ⟶ thickObj R I e G) (χ : D.X) :
    LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) (x * x').left)
        (DegPre.cubAtT D ((Over.map (thick R I e)).obj T)
          (DegPre.cT D ((Over.map (thick R I e)).obj T) χ)
          ((Over.map (thick R I e)).map x ≫ g.pG) ((Over.map (thick R I e)).map x' ≫ g.pG)))
      (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) x.left)
        (LB.pullGen D.P.L _ _ (g.t χ) x'.left)) := by
  refine corr_of_val D.P.isLB fun y J hJ => ?_
  refine (val_lhs g χ hJ x x' (𝟙 T)).trans (Eq.trans ?_ (val_rhs g χ hJ x x' (𝟙 T)).symm)
  exact val_t_mul_points g hGF χ _ _ y J hJ

theorem isAdd_of_points (hGF : GlobalFnsSt) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (x x' : T ⟶ thickObj R I e G) (p p' p'' : GtPt D ((Over.map (thick R I e)).obj T))
    (hb : p.b = (Over.map (thick R I e)).map x ≫ g.pG)
    (hs : ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (p.s χ) (LB.pullGen D.P.L _ _ (g.t χ) x.left))
    (hb' : p'.b = (Over.map (thick R I e)).map x' ≫ g.pG)
    (hs' : ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (p'.s χ) (LB.pullGen D.P.L _ _ (g.t χ) x'.left))
    (hb'' : p''.b = (Over.map (thick R I e)).map (x * x') ≫ g.pG)
    (hs'' : ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (p''.s χ) (LB.pullGen D.P.L _ _ (g.t χ) (x * x').left)) :
    GtPt.IsAdd p p' p'' := by
  refine ⟨?_, fun χ => ?_⟩
  · rw [hb, hb', hb'']
    exact im_mul g x x'
  · refine DVR.corr_trans D.P.isLB (DVR.corr_mulGen (hs'' χ)
      (DVR.corr_pullGen_of_eq (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t D.cub.isGen _ _ ?_))
      (DVR.corr_trans D.P.isLB (t_mul_points g hGF x x' χ)
        (DVR.corr_symm (DVR.corr_mulGen (hs χ) (hs' χ))))
    rw [hb, hb']

theorem isAdd_pointsEquiv (hGF : GlobalFnsSt) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (x x' : T ⟶ thickObj R I e G) :
    GtPt.IsAdd (pointsEquiv g T x) (pointsEquiv g T x') (pointsEquiv g T (x * x')) :=
  isAdd_of_points g hGF x x' _ _ _ (toGtPt_b g x) (thickenedPointToTorusExtension_generator g x) (toGtPt_b g x') (thickenedPointToTorusExtension_generator g x')
    (toGtPt_b g (x * x')) (thickenedPointToTorusExtension_generator g (x * x'))

end GlobalTheory.TorusCoord
