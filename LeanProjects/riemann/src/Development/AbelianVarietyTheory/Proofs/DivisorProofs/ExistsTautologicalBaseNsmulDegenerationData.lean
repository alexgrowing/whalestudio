import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToUnitTKLeft

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TInjBase

theorem val_eq_of_injective {X Y Y₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    (e : Y₀ ⟶ Y) (he : Function.Injective e.appTop.hom)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u e y J = val u' e y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J) (hJ : Good M z J) :
    val u r z J = val u' r z J := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, hF U h, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ : ∃ a, a = (res le (t.s PEmpty.elim)).val := ⟨_, rfl⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J * (val u' r z J)⁻¹).val = gs r z ⊤ a := by
    intro Z r z J hJ
    rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
    exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
      (congrArg (gs r z ⊤) ha.symm))
  have a1 : a = 1 := he ((fn_ext (V := ⊤) fun y _ => by
    choose I hI using fun χ : Y₀ ⟶ X => exists_chart hM (χ y)
    have := key _ e y I hI
    rw [h y I hI, mul_inv_cancel] at this
    refine (gs_pull (𝟙 Y₀) e y ⊤ trivial a).trans ?_
    rw [Category.id_comp, ← this, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]).trans (map_one _).symm)
  have := key Z r z J hJ
  rw [a1, gs_eq _ z ⊤ trivial, map_one, map_one] at this
  exact mul_inv_eq_one.1 (Units.ext this)

theorem exists_gens {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult)
    (hU : ∀ y, PsiUnitOn D y Set.univ) :
    ∃ τ : ∀ a b : D.X, LB.Gen (LB.LinComb D.P.L (lamPts (D.c a) (D.c b)) negε), (∀ a b, (τ a b).IsGen) ∧
      (∀ a b z J, Good D.P.L z J → val (τ a b) (𝟙 _) z J = val (τ b a) (𝟙 _) z J) ∧
      (∀ a a' b z J, Good D.P.L z J → val (τ (a + a') b) (𝟙 _) z J * cubV D.cub z J (D.c a) (D.c a') (D.c b) =
        val (τ a b) (𝟙 _) z J * val (τ a' b) (𝟙 _) z J) ∧
      ∀ a b z J, Good D.P.L z J → val (D.tau a b) (𝟙 _) z J = val (τ a b) (toUnit (TK R)).left z J := by
  obtain ⟨τ₀, h₀⟩ := GlobalTheory.DDataGens.main R D hB hU
  have cadd : ∀ a b, D.c (a + b) = D.c a * D.c b := D.c_add
  have c0 : D.c 0 = 1 := mul_eq_left.1 ((cadd 0 0).symm.trans (by rw [add_zero]))
  have ex : ∀ a b : D.X, ∃ t : LB.Gen (LB.LinComb D.P.L (lamPts (D.c a) (D.c b)) negε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ _) (z : Z) (J), Good D.P.L z J → val t r z J = val (τ₀ a b) r z J := fun a b =>
    exists_gen D.P.isLB (fun U _ h => by
      simp [lamPts, negε, Fin.prod_univ_four, cadd, c0]) (τ₀ a b) (h₀ a b).1
  choose τ hτ hv using ex
  have hK : ∀ a b z J, Good D.P.L z J → val (D.tau a b) (𝟙 _) z J = val (τ a b) (toUnit (TK R)).left z J :=
    fun a b z J hJ => ((h₀ a b).2 z J hJ).trans (hv a b _ _ z J hJ).symm
  have inj : Function.Injective (toUnit (TK R)).left.appTop.hom := by
    rw [GlobalTheory.DDataGens.toUnit_TK_left]
    have nat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    intro x y hxy
    refine (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
      (IsFractionRing.injective R (FractionRing R) ?_)
    exact (congrArg (fun g => g.hom x) nat).symm.trans
      ((congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom hxy).trans (congrArg (fun g => g.hom y) nat))
  refine ⟨τ, hτ, fun a b z J hJ => ?_, fun a a' b z J hJ => ?_, hK⟩
  · refine val_eq_of_injective D.P.isLB (fun U _ h => ?_) _ inj (hτ a b) (hτ b a) (fun y J hJ => ?_) _ _ z J hJ
    · simp only [Fin.prod_univ_four, lamPts, negε, mul_comm (D.c b) (D.c a)]
      simp [mul_right_comm]
    · exact (hK a b y J hJ).symm.trans ((GlobalTheory.TauTwist.val_tau_symm (𝟙 (TK R)) hJ a b).trans (hK b a y J hJ))
  · have key := val_eq_of_injective D.P.isLB (fun U _ h => ?_) _ inj
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hτ (a + a') b)
        (DVR.pullGen_isGen _ _ _ _ D.cub.isGen (lift (D.c a) (lift (D.c a') (D.c b))).left))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hτ a b) (hτ a' b)) (fun y J hJ => ?_) _ (𝟙 _) z J hJ
    · refine Eq.trans ?_ (key.trans (val_mul hJ _ _ _))
      refine Eq.trans ?_ (val_mul hJ _ _ _).symm
      refine congrArg (_ * ·) ?_
      have := val_cub D.cub (𝟙 (𝟙_ (Over (Sp R)))) hJ (D.c a) (D.c a') (D.c b)
      simp only [Category.id_comp] at this
      exact this.symm
    · refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) rfl (prod_cub (D.c a) (D.c a') (D.c b) h))).trans ?_
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, lamPts, negε, cadd]
      apply Additive.ofMul.injective
      simp [ofMul_mul, ofMul_inv]
      abel
    · refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
      rw [← hK _ _ y J hJ, ← hK _ _ y J hJ, ← hK _ _ y J hJ]
      exact (congrArg (_ * ·) (val_cub D.cub (toUnit (TK R)) hJ _ _ _)).trans
        (GlobalTheory.TauTwist.val_tau_add (𝟙 (TK R)) hJ hB a a' b)

theorem val_trans {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {L : LB B.left} (hL : L.IsLB) {T T' : Over S}
    (ρ : T' ⟶ T) (x y : T ⟶ B) {t : LB.Gen (LB.LinComb L (lamPts x y) negε)} (ht : t.IsGen) (z : T'.left) {J J'}
    (hJ : Good L z J) (hJ' : Good L z J') :
    val t ρ.left z J' = lamVal (Wit.idPull (abelian₂ B L)) (lift (ρ ≫ x) (ρ ≫ y)).left z J J' * val t ρ.left z J := by
  refine (gen_trans ht ρ.left z (hJ'.mem _ _) (hJ.mem _ _)).trans (congrArg (· * _) ?_)
  have hm : ∀ {J}, Good L z J → (lift (ρ ≫ x) (ρ ≫ y)).left z ∈ (abelian₂ B L).U
    (fun I => J ((lift (ρ ≫ x) (ρ ≫ y)).left ≫ (psum B (x2 B) I.down).left)) := fun hJ => hJ.mem _ _
  refine Eq.trans ?_ (Wit.gw_idPull (abelian₂ B L) _ z _ _ (hm hJ) (hm hJ')).symm
  refine Eq.trans ?_ (gm_linComb L _ _ _ z _ _ (hm hJ) (hm hJ')).symm
  refine Eq.trans ?_ (GlobalTheory.PrimCocycle.prod_lam (ρ ≫ x) (ρ ≫ y) (fun q => gm q z _ (L.g (J q) (J' q)))).symm
  have inv : ∀ q, gm q z _ (L.g (J' q) (J q)) = (gm q z _ (L.g (J q) (J' q)))⁻¹ := fun q =>
    eq_inv_of_mul_eq_one_left ((gm_cocycle hL q z (hJ' q) (hJ q) (hJ' q)).trans (gm_self hL q z (hJ' q)))
  refine (Finset.prod_congr rfl fun k _ => congrArg (· ^ negε k) (inv (_ ≫ _))).trans ?_
  refine Eq.trans (Finset.prod_congr rfl fun k _ => ?_)
    (Wit.prod_neg_lamPts _ _ (fun q => gm q z _ (L.g (J q) (J' q))))
  have : ρ.left ≫ lamPts x y k = 𝟙 _ ≫ lamPts (ρ ≫ x) (ρ ≫ y) k := by
    rw [Category.id_comp]
    fin_cases k
    · exact congrArg (fun q : T' ⟶ B => q.left) (MonObj.comp_mul ρ _ _)
    · rfl
    · rfl
    · exact congrArg (fun q : T' ⟶ B => q.left) (MonObj.comp_one ρ)
  exact congrArg (fun q => (gm q z _ (L.g (J q) (J' q)))⁻¹ ^ negε k) this

theorem main : ∀ {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (b : o →+* W) (D : DegPre W), D.TauBimult → (∀ y, PsiUnitOn D y Set.univ) → ∀ n : ℕ, ∃ (T : TautBase o W) (ib : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), From T (RingHom.id W) (fun _ : Empty => (1 : W)) (fun _ => 0) n (mulDeg D n) ib β ββ w := by
  intro o W _ _ _ _ b D hB hU n
  obtain ⟨τ, hg, hs, ha, hK⟩ := exists_gens D hB hU
  obtain ⟨ib⟩ : Nonempty (D.X ≃+ (Fin (Module.finrank ℤ D.X) → ℤ)) := ⟨(Module.finBasis ℤ D.X).equivFun.toAddEquiv⟩
  have hid : spMap (RingHom.id W) = 𝟙 (Sp W) := Spec.map_id _
  have hn : ∀ a : D.X, ib.symm ((n : ℤ) • ib a) = n • a := fun a => by
    rw [map_zsmul, ib.symm_apply_apply, natCast_zsmul]
  let T : TautBase o W :=
    { b := b
      B := D.P.A
      comm := D.P.isAb.comm
      isAb := D.P.isAb
      g := D.P.g
      smoothDim := D.P.smoothDim
      M := ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩
      cub := D.cub
      ample := D.P.ample
      ktriv := D.P.ktriv
      r := Module.finrank ℤ D.X
      c₀ := fun a => D.c (ib.symm a)
      c₀_add := fun a a' => by rw [map_add]; exact D.c_add _ _
      τ₀ := fun a a' => τ (ib.symm a) (ib.symm a')
      τ₀_gen := fun a a' => hg _ _
      τ₀_symm := fun a a' => hs _ _
      τ₀_add := fun a a' a'' z J hJ => (congrArg (fun x => val (τ x (ib.symm a'')) (𝟙 _) z J * _) (map_add ib.symm a a')).trans
        (ha _ _ _ z J hJ) }
  refine ⟨T, ib, 𝟙 _, 𝟙 _, Wit.idPull _, ?_, ⟨(Category.id_comp _).trans (Category.comp_id _).symm,
    (Category.id_comp _).trans (Category.comp_id _).symm⟩, Wit.idPull_isGen (DVR.linComb_isLB _ D.P.isLB _ _), fun a => ?_,
    fun (a b : D.X) => ⟨1, by simp, fun z J J' hJ hJ' => ?_⟩⟩
  · rw [hid]
    exact Wit.grpPullback_id D.P.A
  · rw [hid]
    exact (Category.comp_id _).trans ((congrArg (fun x => (D.c x).left) (hn a).symm).trans (Category.id_comp _).symm)
  · have e₁ : val ((mulDeg D n).tau a b) (𝟙 _) z J' = val (D.tau (n • a) (n • b)) (𝟙 _) z J' := by
      refine (GlobalTheory.TauTwist.val_tau (mulDeg D n) a b _ hJ').trans (Eq.trans ?_ (GlobalTheory.TauTwist.val_tau D _ _ _ hJ').symm)
      rw [← nsmul_add]
      rfl
    have e₂ : val (T.τ₀ ((n : ℤ) • ib a) ((n : ℤ) • ib b)) ((TK W).hom ≫ spMap (RingHom.id W)) z J =
        val (τ (n • a) (n • b)) (toUnit (TK W)).left z J := by
      rw [hid, Category.comp_id, GlobalTheory.DDataGens.toUnit_TK_left]
      exact congrArg₂ (fun x y => val (τ x y) (jK W) z J) (hn a) (hn b)
    have e₃ : gm (𝟙 (TK W).left) z ⊤ (unitOn (1 : (FractionRing W)ˣ)) = 1 := (congrArg (gm (𝟙 (TK W).left) z ⊤) (map_one _)).trans (map_one _)
    refine e₁.trans ((hK _ _ z J' hJ').trans (Eq.trans ?_ (congrArg₂ (· * ·) e₃ (congrArg (_ * ·) e₂)).symm))
    rw [_root_.one_mul]
    exact val_trans D.P.isLB (toUnit (TK W)) _ _ (hg (n • a) (n • b)) z hJ hJ'

end GlobalTheory.TInjBase
