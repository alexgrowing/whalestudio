import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqTopOfThick

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.PullDescent

section Level
open TorusInvariance WCub

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) {K : Type} [Fintype K] {ε : K → ℤ}

open RigidIsoCube in
include U in

theorem surj_base (hG : GlobalFnsSt) : Function.Surjective G.hom.appTop.hom ∧
    Function.Surjective ((snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom).appTop.hom := by
  have := U.smooth
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hg : IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) A.A.hom G.hom (jK R) := by
    have : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
    have s : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK R)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w U.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))
  have s₁ : Function.Surjective G.hom.appTop.hom :=
    surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ A.isAb).2
  have : Flat (G ⊗ G).hom := by rw [Over.tensorObj_hom]; infer_instance
  exact ⟨s₁, surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _)
    (surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _) s₁)⟩

def cube3 (a : G ⟶ G) : G3 G ⟶ G3 G := lift (x3 G 0 ≫ a) (lift (x3 G 1 ≫ a) (x3 G 2 ≫ a))

theorem psum_comp {S : Scheme.{0}} {T H H' : Over S} [GrpObj H] [IsCommMonObj H] [GrpObj H'] [IsCommMonObj H']
    (a : H ⟶ H') [IsMonHom a] (x : Fin 3 → (T ⟶ H)) (s : Finset (Fin 3)) :
    psum H x s ≫ a = psum H' (fun i => x i ≫ a) s :=
  psum_hom (MonoidHom.mk' (fun z : T ⟶ H => z ≫ a) fun b c => MonObj.mul_comp b c a) x s

theorem val_cub_one (y : (𝟙_ (Over (Spec (CommRingCat.of R)))).left) (J) (hJ : Good U.LG.L y J) :
    val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t
      (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G) (lift 1 1) : _ ⟶ G3 G).left y J = 1 :=
  (isCub_cubV U.cubG hJ).face 1 1

variable (a : K → (G ⟶ G)) [∀ k, IsMonHom (a k)] (β : LB.Gen (LB.LinComb U.LG.L (fun k => (a k).left) ε))
  (hβ : β.IsGen) (nβ : ∀ y J, Good U.LG.L y J → val β (eSec G) y J = 1)
include hβ nβ

theorem gen_cube (hG : GlobalFnsSt) (Z : Scheme.{0}) (r : Z ⟶ (G3 G).left) (z : Z) (J) (hJ : Good U.LG.L z J) :
    ∏ i, val β (r ≫ thφ G (x3 G) i) z J ^ thε i =
      ∏ k, val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t (r ≫ (cube3 (a k)).left) z J ^ ε k := by
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 G := lift 1 (lift 1 1)
  have he : e.left ≫ (snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  refine prod_comm_val U.LG.isLB (θ := thφ G (x3 G)) (δ := thε) β hβ U.cubG.t U.cubG.isGen (thφ G (x3 G))
    (fun k => (cube3 (a k)).left) (fun i k => ?_) _ e.left he (surj_base U hG).2 (fun i y J hJ => ?_)
    (fun k y J hJ => ?_) Z r z J hJ
  · refine congrArg (fun q => q.left) ((psum_comp (a k) (x3 G) i.down).trans (Eq.trans (congrArg
      (fun q => psum G q i.down) (funext fun j => ?_)) (psum_hom (preHom (cube3 (a k))) (x3 G) i.down).symm))
    fin_cases j <;> simp [preHom, x3, cube3]
  · have : e ≫ psum G (x3 G) i.down = η[G] := by
      refine (psum_hom (preHom e) (x3 G) i.down).trans (Eq.trans (congrArg (fun q => psum G q i.down)
        (funext fun j => ?_)) ((psum_hom (1 : (G3 G ⟶ G) →* (𝟙_ _ ⟶ G)) (x3 G) i.down).symm.trans ?_))
      · fin_cases j <;> simp [preHom, x3, e]
      · simp [Hom.one_def]
    have t : e.left ≫ thφ G (x3 G) i = eSec G := congrArg (fun q => q.left) this
    show val β (e.left ≫ thφ G (x3 G) i) y J = 1
    rw [t]
    exact nβ y J hJ
  · have : e ≫ cube3 (a k) = e := by
      simp only [cube3, comp_lift, ← Category.assoc]
      simp [x3, e, MonObj.one_comp]
    have t : e.left ≫ (cube3 (a k)).left = e.left := congrArg (fun q => q.left) this
    show val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t (e.left ≫ (cube3 (a k)).left) y J = 1
    rw [t]
    exact val_cub_one U y J hJ

theorem gen_even (hG : GlobalFnsSt) (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J) (hJ : Good U.LG.L z J) :
    val β (r ≫ (ι[G]).left) z J = val β r z J * ∏ k, val U.symG (r ≫ (a k).left) z J ^ ε k := by
  have := prod_comm_val U.LG.isLB β hβ U.symG U.symG_gen ![(ι[G]).left, 𝟙 G.left] (fun k => (a k).left)
    (fun i k => by
      fin_cases i
      · exact EvenPull.inv_left_comp (a k)
      · exact (Category.id_comp _).trans (Category.comp_id _).symm)
    G.hom (eSec G) (Over.w η[G]) (surj_base U hG).1 (fun i y J hJ => by
      fin_cases i
      · exact (congrArg (fun q => val β q y J) (EvenPull.eSec_inv G)).trans (nβ y J hJ)
      · exact (congrArg (fun q => val β q y J) (Category.comp_id _)).trans (nβ y J hJ))
    (fun k y J hJ => by
      have b := val_corr hJ U.symG_rig (𝟙 _)
      rw [val_pull hJ, val_one, Category.id_comp] at b
      have : eSec G ≫ (a k).left = eSec G := congrArg (fun q => q.left) (IsMonHom.one_hom (a k))
      rw [this, b]) Z r z J hJ
  rw [Fin.prod_univ_two] at this
  rw [← this]
  show _ = _ * (val β (r ≫ (ι[G]).left) z J ^ (1 : ℤ) * val β (r ≫ 𝟙 _) z J ^ (-1 : ℤ))
  rw [Category.comp_id, zpow_one, zpow_neg_one, mul_comm, inv_mul_cancel_right]

omit hβ nβ

theorem prod_swap {V K K' : Type} [CommGroup V] [Fintype K] [Fintype K'] (ε : K → ℤ) (δ : K' → ℤ) (b : K' → V)
    (W : K' → K → V) (c m : K → V) (h₁ : ∏ i, b i ^ δ i = ∏ k, c k ^ ε k) (h₂ : ∀ k, m k = (∏ i, W i k ^ δ i) * c k) :
    ∏ i, (b i * ∏ k, W i k ^ ε k) ^ δ i = ∏ k, m k ^ ε k := by
  simp only [h₂, mul_zpow, Finset.prod_mul_distrib, h₁, ← Finset.prod_zpow, ← zpow_mul]
  rw [mul_comm, Finset.prod_comm]
  simp only [mul_comm]

omit [IsDomain R] in
theorem map_fstG (e : ℕ) {H H' : Over (Spec (CommRingCat.of R))} (b : H ⟶ H') :
    ((Over.pullback (thick R I e)).map b).left ≫ (fstG I e H').left = (fstG I e H).left ≫ b.left :=
  pullback.lift_fst _ _ _

omit [IsDomain R] in
theorem eSec_fstG (e : ℕ) (H : Over (Spec (CommRingCat.of R))) [GrpObj H] :
    eSec (thickObj R I e H) ≫ (fstG I e H).left = thick R I e ≫ eSec H := by
  show eSec (thickObj R I e H) ≫ pullback.fst H.hom (thick R I e) = _
  simp [eSec]
  rw [pullback.lift_fst, ← Category.assoc, ← pullback.condition, Category.comp_id]

def aV (e : ℕ) {Z : Scheme.{0}} (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
    (N : (Z ⟶ G.left) → U.LG.L.ι) (x : Z ⟶ (thickObj R I e G).left) : (Z.presheaf.stalk z)ˣ :=
  val β (x ≫ (fstG I e G).left) z N *
    ∏ k, wVal U e z J N (x ≫ ((Over.pullback (thick R I e)).map (a k)).left) ^ ε k

include hβ nβ in
theorem aV_cube (hG : GlobalFnsSt) (e : ℕ) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (x : Fin 3 → (T ⟶ thickObj R I e G)) {z : T.left} {J} {N} (hJ : Good D.toPre.P.L z J) (hN : Good U.LG.L z N) :
    ∏ i : thK.{0}, aV U a β e z J N (psum (thickObj R I e G) x i.down).left ^ thε i =
      ∏ k, val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
        (tri (thick R I e) (U.gt e).pG fun i => x i ≫ (Over.pullback (thick R I e)).map (a k)) z J ^ ε k := by
  have c₁ := gen_cube U a β hβ nβ hG _ (tri (thick R I e) (fstG I e G) x) z N hN
  have f₃ := tri_thφ (thick R I e) (fstG I e G) x (𝟙 _) (Category.id_comp _).symm
  refine prod_swap ε thε _ _ _ _ ((Finset.prod_congr rfl fun i _ =>
    congrArg (fun q => val β q z N ^ thε i) (f₃ i).symm).trans c₁) fun k => ?_
  refine (cube_val U (fun i => x i ≫ (Over.pullback (thick R I e)).map (a k)) hJ hN).trans
    (congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => ?_) ?_)
  · rw [← psum_comp, Over.comp_left]
  · have m : ∀ y : T ⟶ thickObj R I e G,
        (Over.map (thick R I e)).map (y ≫ (Over.pullback (thick R I e)).map (a k)) ≫ fstG I e G =
          ((Over.map (thick R I e)).map y ≫ fstG I e G) ≫ a k := fun y => Over.OverMorphism.ext
      ((Category.assoc _ _ _).trans ((congrArg (y.left ≫ ·) (map_fstG e (a k))).trans (Category.assoc _ _ _).symm))
    have t : tri (thick R I e) (fstG I e G) (fun i => x i ≫ (Over.pullback (thick R I e)).map (a k)) =
        tri (thick R I e) (fstG I e G) x ≫ (cube3 (a k)).left := by
      rw [← Over.comp_left]
      refine congrArg (fun q : (Over.map (thick R I e)).obj T ⟶ G3 G => q.left) ?_
      simp only [m, cube3, comp_lift]
      simp [x3]
    rw [t]

include hβ nβ in
theorem aV_even (hG : GlobalFnsSt) (e : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (thickObj R I e G).left) {z : Z} {J} {N}
    (hJ : Good D.toPre.P.L z J) (hN : Good U.LG.L z N) :
    aV U a β e z J N (r ≫ (ι[thickObj R I e G]).left) = aV U a β e z J N r *
      ∏ k, val D.toPre.sym ((r ≫ ((Over.pullback (thick R I e)).map (a k)).left) ≫ (U.gt e).pG.left) z J ^ ε k := by
  have iF : (ι[thickObj R I e G]).left ≫ (fstG I e G).left = (fstG I e G).left ≫ (ι[G]).left :=
    EvenPull.inv_fst _ G
  have e₁ : (r ≫ (ι[thickObj R I e G]).left) ≫ (fstG I e G).left = (r ≫ (fstG I e G).left) ≫ (ι[G]).left :=
    (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) iF).trans (Category.assoc _ _ _).symm)
  rw [aV, aV, e₁, gen_even U a β hβ nβ hG _ _ z N hN, _root_.mul_assoc, _root_.mul_assoc, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine congrArg (_ * ·) (Finset.prod_congr rfl fun k _ => ?_)
  rw [← mul_zpow, ← mul_zpow]
  refine congrArg (· ^ ε k) ?_
  have e₂ : (r ≫ (ι[thickObj R I e G]).left) ≫ ((Over.pullback (thick R I e)).map (a k)).left =
      (r ≫ ((Over.pullback (thick R I e)).map (a k)).left) ≫ (ι[thickObj R I e G]).left :=
    (Category.assoc _ _ _).trans ((congrArg (r ≫ ·)
      (EvenPull.inv_left_comp ((Over.pullback (thick R I e)).map (a k)))).trans (Category.assoc _ _ _).symm)
  have e₃ : (r ≫ (fstG I e G).left) ≫ (a k).left =
      (r ≫ ((Over.pullback (thick R I e)).map (a k)).left) ≫ (fstG I e G).left :=
    (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (map_fstG e (a k)).symm).trans (Category.assoc _ _ _).symm)
  rw [e₂, e₃]
  exact (mul_comm _ _).trans ((even_val U _ hJ hN).symm.trans (mul_comm _ _))

variable (b : K → (D.toPre.P.A ⟶ D.toPre.P.A))
  (hq : ∀ e k, (Over.pullback (thick R I e)).map (a k) ≫ (U.gt e).q =
    (U.gt e).q ≫ (Over.pullback (thick R I e)).map (b k))

set_option maxHeartbeats 800000 in
include hβ nβ hq in

theorem exists_level (hG : GlobalFnsSt) (hS : IsSemiAbelian G) [IsAdicComplete I R] (e : ℕ) :
    ∃ s : LB.Gen (LB.LinComb D.toPre.P.L (fun k => (fstG I e D.toPre.P.A).left ≫ (b k).left) ε), s.IsGen ∧
      ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (z : Z) (J) (N), Good D.toPre.P.L z J →
        Good U.LG.L z N → val s (x ≫ (U.gt e).q.left) z J = aV U a β e z J N x := by
  have := (U.gt e).q_hom
  have := (U.gt e).i_hom
  have := (U.gt e).q_flat
  have := (U.gt e).q_surj
  have := (U.gt e).q_affine
  have := hS.geomConnected
  have := EndTorus.connectedSpace_thickening I e
  have : GeometricallyConnected (thickObj R I e G).hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd G.hom (thick R I e)))
  have : ConnectedSpace (thickObj R I e G).left :=
    GroupConn.connectedSpace_of_section (thickObj R I e G).hom (η : 𝟙_ _ ⟶ thickObj R I e G).left (Over.w _)
  obtain ⟨t, ht, hv⟩ := exists_transport U.LG.isLB D.toPre.P.isLB (U.w_gen e) (Y := (thickObj R I e G).left)
    (fun k => ((Over.pullback (thick R I e)).map (a k)).left)
    (φf := fun k => (fstG I e G).left ≫ (a k).left)
    (φp := fun k => (U.gt e).q.left ≫ (fstG I e D.toPre.P.A).left ≫ (b k).left) (fun k => map_fstG e (a k))
    (fun k => (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ (fstG I e D.toPre.P.A).left)
      (hq e k)).trans ((Category.assoc _ _ _).trans (congrArg ((U.gt e).q.left ≫ ·) (map_fstG e (b k))))))
    (LB.pullGen U.LG.L _ _ β (fstG I e G).left) (pullGen_isGen _ _ _ _ hβ _)
  have hv' : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (z : Z) (J) (N), Good D.toPre.P.L z J →
      Good U.LG.L z N → val t x z J = aV U a β e z J N x := fun Z x z J N hJ hN =>
    (hv Z x z N J hN hJ).trans (congrArg (· * _) (val_pull hN _ _ _))
  have h1 : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.toPre.X),
      (τ ≫ (U.gt e).i) ≫ (U.gt e).q = (1 : Z ⟶ thickObj R I e G) ≫ (U.gt e).q := fun τ => by
    rw [Category.assoc, (U.gt e).isKernel.w, MonObj.one_comp, ← Category.assoc, comp_toUnit, Hom.one_def]
  have h2 : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.toPre.X) k,
      ((τ ≫ (U.gt e).i) ≫ (Over.pullback (thick R I e)).map (a k)) ≫ (U.gt e).q =
        ((1 : Z ⟶ thickObj R I e G) ≫ (Over.pullback (thick R I e)).map (a k)) ≫ (U.gt e).q := fun τ k => by
    rw [Category.assoc, hq, ← Category.assoc, h1, Category.assoc, Category.assoc, hq]
  obtain ⟨ρ, hρ⟩ := exists_ratio D.toPre.P.isLB t ht
    ((fst (splitTorus _ D.toPre.X) (thickObj R I e G) ≫ (U.gt e).i) * snd _ _).left (snd _ (thickObj R I e G)).left
    (fun k => by
      have : ((fst (splitTorus _ D.toPre.X) (thickObj R I e G) ≫ (U.gt e).i) * snd _ _) ≫ (U.gt e).q =
          snd _ _ ≫ (U.gt e).q := by rw [MonObj.mul_comp, h1, ← MonObj.mul_comp, _root_.one_mul]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ (fstG I e D.toPre.P.A).left ≫ (b k).left)
        this).trans (Category.assoc _ _ _)))
  have key : ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (τ : Z ⟶ splitTorus _ D.toPre.X)
      (y : Z ⟶ thickObj R I e G) (z : Z.left) (J), Good D.toPre.P.L z J → val t ((τ ≫ (U.gt e).i) * y).left z J =
        gm (𝟙 Z.left) z ⊤ (pullTop (lift τ y) ρ) * val t y.left z J := fun Z τ y z J hJ => by
    have := hρ _ (lift τ y).left z J hJ
    rwa [← Over.comp_left, ← Over.comp_left, lift_snd, MonObj.comp_mul, lift_fst_assoc, lift_snd,
      ← gm_pullTop] at this
  have triv := ratio_eq_one (U.gt e).i ρ (fun Z z => by
    choose J hJ using fun χ : Z.left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ z)
    choose N hN using fun χ : Z.left ⟶ G.left => exists_chart U.LG.isLB (χ z)
    refine ⟨aV U a β e z J N, fun τ y => ?_, fun τ τ' y => ?_, fun τ => ?_⟩
    · rw [← hv' _ _ z J N hJ hN, ← hv' _ _ z J N hJ hN]
      exact key Z τ y z J hJ
    · rw [aV_cube U a β hβ nβ hG e _ hJ hN, aV_cube U a β hβ nβ hG e _ hJ hN]
      refine Finset.prod_congr rfl fun k _ => ?_
      exact congrArg (fun q => val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε)
        D.toPre.cub.t q z J ^ ε k) (tri_congr (U.gt e) (y ≫ (Over.pullback (thick R I e)).map (a k)) (h2 τ k) (h2 τ' k))
    · rw [aV_even U a β hβ nβ hG e _ hJ hN, aV_even U a β hβ nβ hG e _ hJ hN, mul_right_comm, ← _root_.mul_assoc]
      refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun k _ => ?_)
      exact congrArg (fun q => val D.toPre.sym q z J ^ ε k) (pG_congr (U.gt e) (h2 τ k)))
  obtain ⟨s, hs, vs⟩ := exists_descend D.toPre.P.isLB (U.gt e).q.left
    (fun k => (fstG I e D.toPre.P.A).left ≫ (b k).left) t ht (fun Z g₁ g₂ z J hJ h => by
      let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (g₂ ≫ (thickObj R I e G).hom)
      let k₂ : Z' ⟶ thickObj R I e G := Over.homMk g₂ rfl
      let k₁ : Z' ⟶ thickObj R I e G := Over.homMk g₁ (by
        change g₁ ≫ (thickObj R I e G).hom = g₂ ≫ (thickObj R I e G).hom
        rw [← Over.w (U.gt e).q, reassoc_of% h])
      have e' : k₁ ≫ (U.gt e).q = k₂ ≫ (U.gt e).q := Over.OverMorphism.ext h
      have w : (k₁ * k₂⁻¹) ≫ (U.gt e).q = toUnit Z' ≫ η[thickObj R I e D.toPre.P.A] := by
        rw [MonObj.mul_comp, GrpObj.inv_comp, e', mul_inv_cancel]
        rfl
      have ht : ((U.gt e).isKernel.lift _ _ w ≫ (U.gt e).i) * k₂ = k₁ := by
        rw [(U.gt e).isKernel.lift_fst, inv_mul_cancel_right]
      have := key Z' ((U.gt e).isKernel.lift _ _ w) k₂ z J hJ
      rw [ht, triv, map_one, _root_.one_mul] at this
      exact this)
  exact ⟨s, hs, fun Z x z J N hJ hN => (vs Z x z J hJ).trans (hv' Z x z J N hJ hN)⟩

end Level

section Main
open TorusInvariance

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) {K : Type} [Fintype K] {ε : K → ℤ}

theorem exists_descent (hG : GlobalFnsSt) (hS : IsSemiAbelian G) [IsAdicComplete I R]
    (hε : ∀ (V : Type) [CommGroup V] (c : V), ∏ k, c ^ ε k = 1)
    (a : K → (G ⟶ G)) [∀ k, IsMonHom (a k)] (b : K → (D.toPre.P.A ⟶ D.toPre.P.A)) [∀ k, IsMonHom (b k)]
    (hq : ∀ e k, (Over.pullback (thick R I e)).map (a k) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (b k))
    {φ : K → (G.left ⟶ G.left)} (hφ : ∀ k, (a k).left = φ k)
    {ψ : K → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)} (hψ : ∀ k, (b k).left = ψ k)
    (β : LB.Gen (LB.LinComb U.LG.L φ ε)) (hβ : β.IsGen)
    (hn : LB.Gen.Corr U.LG.L _ _ _ _ (LB.pullGen U.LG.L _ _ β (eSec G)) (LB.oneGen U.LG.L)) :
    ∃ κ : LB.Gen (LB.LinComb D.toPre.P.L ψ ε), Normd κ ∧
      ∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (z : Z) (N) (J), Good U.LG.L z N →
        Good D.toPre.P.L z J → val κ (x ≫ (U.gt e).pG.left) z J = val β (x ≫ (fstG I e G).left) z N *
          ∏ k, wVal U e z J N (x ≫ ((Over.pullback (thick R I e)).map (a k)).left) ^ ε k := by
  obtain rfl : (fun k => (a k).left) = φ := funext hφ
  obtain rfl : (fun k => (b k).left) = ψ := funext hψ
  have hM := D.toPre.P.isLB
  have nβ : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left) (z : Z) (N),
      Good U.LG.L z N → val β (r ≫ eSec G) z N = 1 := fun Z r z N hN =>
    (val_pull hN _ _ _).symm.trans ((val_corr hN hn r).trans (val_one _))
  choose s hs vs using exists_level U a β hβ (fun y N hN => by
    have := nβ _ (𝟙 _) y N hN
    rwa [Category.id_comp] at this) b hq hG hS
  have ob : ∀ k, eSec D.toPre.P.A ≫ (b k).left = eSec D.toPre.P.A := fun k =>
    congrArg (fun q => q.left) (IsMonHom.one_hom (b k))
  obtain ⟨t₀, ht₀, -⟩ := exists_gen hM (φ' := fun k => eSec D.toPre.P.A ≫ (b k).left) (ε' := ε)
    (fun V _ h => (Fintype.prod_empty _).trans (by simp only [ob, hε])) (LB.oneGen D.toPre.P.L)
    (fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)).symm)
  have proj : AbLaw.IsProjBy D.toPre.P.A.hom := by
    obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R D.toPre.P.A D.toPre.P.L hM).1 D.toPre.P.ample
    exact ⟨_, AbLaw.isLB_pw hM _, n, s, hs⟩
  obtain ⟨κ₀, h₀⟩ := triv_of_thick hG I D.toPre.P.A D.toPre.P.isAb proj _
    (LB.isLB_linComb hM (fun k => (b k).left) ε) (triv_pull _ t₀ ht₀) (fun e => triv_pull _ (s e) (hs e))
  let n := (1 : D.toPre.P.A ⟶ D.toPre.P.A).left
  have nb : ∀ k, n ≫ (b k).left = n := fun k =>
    congrArg (fun q : D.toPre.P.A ⟶ D.toPre.P.A => q.left) (MonObj.one_comp (b k))
  have on : eSec D.toPre.P.A ≫ n = eSec D.toPre.P.A := by
    have : η[D.toPre.P.A] ≫ (1 : D.toPre.P.A ⟶ D.toPre.P.A) = η[D.toPre.P.A] := by simp [Hom.one_def]
    exact congrArg (fun q => q.left) this
  obtain ⟨κ, hκ, vκ⟩ := exists_gen hM (φ' := fun k => (b k).left) (ε' := ε) (fun V _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, nb, hε, inv_one, _root_.mul_one])
    (LB.mulGen D.toPre.P.L _ _ _ _ κ₀ (LB.invGen D.toPre.P.L _ _ (LB.pullGen D.toPre.P.L _ _ κ₀ n)))
    (mulGen_isGen _ _ _ _ _ _ _ h₀ (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ h₀ _)))
  have nκ : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left) (z : Z) (J),
      Good D.toPre.P.L z J → val κ (r ≫ eSec D.toPre.P.A) z J = 1 := fun Z r z J hJ => by
    rw [vκ _ _ z J hJ, val_mul hJ, val_inv, val_pull hJ, Category.assoc, on, mul_inv_cancel]
  refine ⟨κ, ⟨hκ, corr_of_val hM fun y J hJ => (val_pull hJ _ _ _).trans ((nκ _ _ y J hJ).trans (val_one _).symm)⟩,
    fun e Z x z N J hN hJ => ?_⟩
  have := (U.gt e).q_hom
  have key := gen_unique hM (thickObj R I e D.toPre.P.A).hom (eSec (thickObj R I e D.toPre.P.A)) (Over.w _)
    (hG _ _ (TLinPf.isAb_pullback (thick R I e) _ D.toPre.P.isAb)).2
    (pullGen_isGen _ _ _ _ hκ (fstG I e D.toPre.P.A).left) (hs e) (fun y J hJ => by
      choose N hN using fun χ : _ ⟶ G.left => exists_chart U.LG.isLB (χ y)
      have q₀ : eSec (thickObj R I e G) ≫ (U.gt e).q.left = eSec (thickObj R I e D.toPre.P.A) :=
        congrArg (fun q => q.left) (IsMonHom.one_hom (U.gt e).q)
      have a₀ : ∀ k, eSec (thickObj R I e G) ≫ ((Over.pullback (thick R I e)).map (a k)).left =
          eSec (thickObj R I e G) := fun k =>
        congrArg (fun q => q.left) (IsMonHom.one_hom ((Over.pullback (thick R I e)).map (a k)))
      have v := vs e _ (eSec (thickObj R I e G)) y J N hJ hN
      rw [q₀, aV] at v
      simp only [a₀, hε, _root_.mul_one] at v
      refine (val_pull hJ _ _ _).trans (Eq.trans ?_ v.symm)
      exact ((congrArg (fun q => val κ q y J) (eSec_fstG e D.toPre.P.A)).trans (nκ _ _ y J hJ)).trans
        ((congrArg (fun q => val β q y N) (eSec_fstG e G)).trans (nβ _ _ y N hN)).symm)
    Z (x ≫ (U.gt e).q.left) z J hJ
  exact ((congrArg (fun q => val κ q z J) (Category.assoc _ _ _).symm).trans (val_pull hJ _ _ _).symm).trans
    (key.trans (vs e Z x z J N hJ hN))

end Main

theorem main : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (E : EndU U.toUnifPre) (k' k : ℕ) (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 3) ![𝟙 _, E.aG.left, (1 : G ⟶ G).left] ![(k' : ℤ), -(k : ℤ), (k : ℤ) - k'])), β.IsGen → LB.Gen.Corr U.LG.L _ _ _ _ (LB.pullGen U.LG.L _ _ β (eSec G)) (LB.oneGen U.LG.L) → ∃ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ ∧ ∀ (e : ℕ) (Z : Scheme.{0}) (x o : Z ⟶ (thickObj R I e G).left) (z : Z) (JG) (J), Good U.LG.L z JG → Good D.toPre.P.L z J → o = x ≫ (1 : thickObj R I e G ⟶ thickObj R I e G).left → ∀ W : (Z ⟶ (thickObj R I e G).left) → (Z.presheaf.stalk z)ˣ, (∀ y, W y = gw (U.w e) y z (J (y ≫ (U.gt e).pG.left)) (fun _ => JG (y ≫ (fstG I e G).left))) → val κ (x ≫ (U.gt e).pG.left) z J = val β (x ≫ (fstG I e G).left) z JG * W x ^ (k' : ℤ) * W (x ≫ ((Over.pullback (thick R I e)).map E.aG).left) ^ (-(k : ℤ)) * W o ^ ((k : ℤ) - k') := by
  intro hL R _ _ _ I hI D A G _ _ hS U E k' k β hβ hn
  have := hI.2.2.2
  have := E.homG
  have := E.homB
  have : ∀ i, IsMonHom ((![𝟙 G, E.aG, 1] : Fin 3 → (G ⟶ G)) i) := fun i => by
    fin_cases i
    exacts [inferInstanceAs (IsMonHom (𝟙 G)), E.homG, inferInstanceAs (IsMonHom (toUnit G ≫ η[G]))]
  have : ∀ i, IsMonHom ((![𝟙 _, E.aB, 1] : Fin 3 → (D.toPre.P.A ⟶ D.toPre.P.A)) i) := fun i => by
    fin_cases i
    exacts [inferInstanceAs (IsMonHom (𝟙 _)), E.homB, inferInstanceAs (IsMonHom (toUnit _ ≫ η[D.toPre.P.A]))]
  obtain ⟨κ, hκ, hv⟩ := exists_descent U.toUnifPre hL.1.globalFns hS (fun V _ c => by
      rw [Fin.prod_univ_three]
      show c ^ (k' : ℤ) * c ^ (-(k : ℤ)) * c ^ ((k : ℤ) - k') = 1
      rw [← zpow_add, ← zpow_add, show (k' : ℤ) + -(k : ℤ) + ((k : ℤ) - k') = 0 by ring, zpow_zero])
    ![𝟙 G, E.aG, 1] ![𝟙 _, E.aB, 1] (fun e i => by
      have := (U.gt e).q_hom
      fin_cases i
      · show (Over.pullback (thick R I e)).map (𝟙 G) ≫ _ = _ ≫ (Over.pullback (thick R I e)).map (𝟙 _)
        rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      · exact E.q_lin e
      · show (Over.pullback (thick R I e)).map (1 : G ⟶ G) ≫ _ =
          _ ≫ (Over.pullback (thick R I e)).map (1 : D.toPre.P.A ⟶ D.toPre.P.A)
        rw [CategoryTheory.Functor.map_one, CategoryTheory.Functor.map_one, MonObj.one_comp, MonObj.comp_one])
    (fun i => by fin_cases i <;> rfl)
    (ψ := ![𝟙 _, E.aB.left, (1 : D.toPre.P.A ⟶ D.toPre.P.A).left]) (fun i => by fin_cases i <;> rfl) β hβ hn
  refine ⟨κ, hκ, fun e Z x o z JG J hG hJ ho W hW => ?_⟩
  obtain rfl : W = TorusInvariance.wVal U.toUnifPre e z J JG := funext hW
  rw [hv e Z x z JG J hG hJ, Fin.prod_univ_three, ← _root_.mul_assoc, ← _root_.mul_assoc, ho]
  have e₀ : x ≫ ((Over.pullback (thick R I e)).map (𝟙 G)).left = x := by
    rw [CategoryTheory.Functor.map_id]; exact Category.comp_id _
  have e₂ : ((Over.pullback (thick R I e)).map (1 : G ⟶ G)) = (1 : thickObj R I e G ⟶ thickObj R I e G) :=
    CategoryTheory.Functor.map_one _
  rw [← e₂]
  exact congrArg (fun q => _ * TorusInvariance.wVal U.toUnifPre e z J JG q ^ (k' : ℤ) * _ * _) e₀

end GlobalTheory.UT.PullDescent
end
