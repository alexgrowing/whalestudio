import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompletePoint

section Units

variable {R : Type} [CommRing R] (I : Ideal R)

theorem iso_appTop {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : Γ(Spec (CommRingCat.of A), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((Spec.map (CommRingCat.ofHom f)).appTop.hom a) =
      f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom a) :=
  congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)).hom a)

theorem iso_injective (A : Type) [CommRing A] :
    Function.Injective (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective

theorem fn_eq_of_thick [IsHausdorff I R] {a b : Γ(Spec (CommRingCat.of R), ⊤)}
    (h : ∀ e, (thick R I e).appTop.hom a = (thick R I e).appTop.hom b) : a = b := by
  apply iso_injective R
  refine IsHausdorff.eq_iff_smodEq (I := I) |>.2 fun n => ?_
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (n + 1)))).hom.hom (h n)
  rw [iso_appTop, iso_appTop, Ideal.Quotient.eq] at this
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  exact Ideal.pow_le_pow_right n.le_succ this

theorem exists_fn_of_thick [IsPrecomplete I R] (a : ∀ e, Γ(Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ⊤))
    (h : ∀ e, (thickTrans R I e).appTop.hom (a (e + 1)) = a e) :
    ∃ b : Γ(Spec (CommRingCat.of R), ⊤), ∀ e, (thick R I e).appTop.hom b = a e := by
  choose r hr using fun e => Ideal.Quotient.mk_surjective
    ((Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (e + 1)))).hom.hom (a e))
  have hs : ∀ e, r e - r (e + 1) ∈ I ^ (e + 1) := fun e => by
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (e + 1)))).hom.hom (h e)
    rw [iso_appTop, ← hr, ← hr, Ideal.Quotient.factor_mk] at this
    exact Ideal.Quotient.eq.1 this.symm
  have hle : ∀ {m n : ℕ}, m ≤ n → r m - r n ∈ I ^ (m + 1) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := add_mem ih (Ideal.pow_le_pow_right (Nat.succ_le_succ hmn) (hs n))
      simpa using this
  obtain ⟨l, hl⟩ := IsPrecomplete.prec (I := I) (M := R) inferInstance (f := r) fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    exact Ideal.pow_le_pow_right m.le_succ (hle hmn)
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom l, fun e => iso_injective _ ?_⟩
  have h1 := hl (e + 1)
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  rw [iso_appTop, ← hr, Iso.inv_hom_id_apply, eq_comm, Ideal.Quotient.eq]
  simpa using add_mem (hs e) h1

theorem exists_unit_of_thick [IsAdicComplete I R] (a : ∀ e, Γ(Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ⊤)ˣ)
    (h : ∀ e, pullU (thickTrans R I e) ⊤ (a (e + 1)) = a e) :
    ∃ b : Γ(Spec (CommRingCat.of R), ⊤)ˣ, ∀ e, pullU (thick R I e) ⊤ b = a e := by
  obtain ⟨b, hb⟩ := exists_fn_of_thick I (fun e => (a e).val) fun e => congrArg Units.val (h e)
  obtain ⟨c, hc⟩ := exists_fn_of_thick I (fun e => (a e)⁻¹.val) fun e =>
    congrArg Units.val ((map_inv _ _).trans (congrArg (·⁻¹) (h e)))
  have hbc : b * c = 1 := fn_eq_of_thick I fun e => by
    rw [map_mul, hb, hc, map_one]; exact (a e).mul_inv
  exact ⟨⟨b, c, hbc, (mul_comm _ _).trans hbc⟩, fun e => Units.ext (hb e)⟩

end Units

section Gens

variable {R : Type} [CommRing R] (I : Ideal R) {X : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Spec (CommRingCat.of R) ⟶ X)} {ε : K → ℤ} {φ' : K' → (Spec (CommRingCat.of R) ⟶ X)} {ε' : K' → ℤ}

theorem corr_of_thick [IsHausdorff I R] (hL : L.IsLB) (h : FormEq φ ε φ' ε') {u : LB.Gen (LB.LinComb L φ ε)}
    (hu : u.IsGen) {u' : LB.Gen (LB.LinComb L φ' ε')} (hu' : u'.IsGen)
    (hv : ∀ e z J, Good L z J → val u (thick R I e) z J = val u' (thick R I e) z J) :
    LB.Gen.Corr L φ ε φ' ε' u u' := by
  obtain ⟨a, ha⟩ := TorusCoord.exists_ratio hL h u hu u' hu'
  have h1 : ∀ e, pullU (thick R I e) ⊤ a = 1 := fun e => unit_ext fun z _ => by
    obtain ⟨J, hJ⟩ := TorusCoord.exists_good' hL z
    have := ha _ (thick R I e) z J hJ
    rw [hv e z J hJ] at this
    rw [gm_pull (𝟙 _) (thick R I e) z ⊤ trivial, Category.id_comp, map_one]
    exact (mul_eq_right.1 this.symm)
  have h2 : a = 1 := Units.ext (fn_eq_of_thick I fun e =>
    (congrArg Units.val (h1 e)).trans (map_one _).symm)
  exact corr_of_val hL fun y J hJ => by rw [ha _ _ y J hJ, h2, map_one, _root_.one_mul]

theorem exists_gen_of_thick [IsLocalRing R] [IsAdicComplete I R] (hL : L.IsLB)
    {ψ : ∀ e, K' → (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ X)}
    (h : ∀ e, FormEq (fun k => thick R I e ≫ φ k) ε (ψ e) ε') (t : ∀ e, LB.Gen (LB.LinComb L (ψ e) ε'))
    (ht : ∀ e, (t e).IsGen)
    (hc : ∀ e z J, Good L z J → val (t (e + 1)) (thickTrans R I e) z J = val (t e) (𝟙 _) z J) :
    ∃ s : LB.Gen (LB.LinComb L φ ε), s.IsGen ∧
      ∀ e z J, Good L z J → val s (thick R I e) z J = val (t e) (𝟙 _) z J := by
  obtain ⟨g, hg⟩ := DVR.exists_gen_of_local L hL φ ε
  choose a ha using fun e => TorusCoord.exists_ratio hL (fun U _ f => (h e U f).symm) (t e) (ht e)
    (LB.pullGen L _ _ g (thick R I e)) (DVR.pullGen_isGen _ _ _ _ hg _)
  obtain ⟨b, hb⟩ := exists_unit_of_thick I a fun e => unit_ext fun z _ => by
    obtain ⟨J, hJ⟩ := TorusCoord.exists_good' hL z
    have e₁ := hc e z J hJ
    rw [ha _ _ _ z J hJ, ha _ _ _ z J hJ, val_pull hJ, val_pull hJ, thickTrans_comp, Category.id_comp] at e₁
    rw [gm_pull (𝟙 _) (thickTrans R I e) z ⊤ trivial, Category.id_comp]
    exact mul_right_cancel e₁
  refine ⟨DVR.scaleGen b g, DVR.scaleGen_isGen b g hg, fun e z J hJ => ?_⟩
  rw [ha _ _ _ z J hJ, val_pull hJ, Category.id_comp, ← hb e]
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ z le_top (hJ.mem φ _) b).trans ?_) rfl)
  refine Eq.trans ?_ (gm_pull (𝟙 _) (thick R I e) z ⊤ trivial b).symm
  rw [Category.id_comp]

end Gens

section Main

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}

theorem prod_gtφT {D : DegPre R} {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X)
    {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k, h (DegPre.gtφT D T b χ k) ^ DegPre.gtε k =
      (h (DegPre.cT D T χ * b).left)⁻¹ * h (DegPre.cT D T χ).left * h b.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four]
  show h (DegPre.cT D T χ * b).left ^ (-1 : ℤ) * h (DegPre.cT D T χ).left ^ (1 : ℤ) * h b.left ^ (1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem formEq_mult {D : DegPre R} {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ χ' : D.X) :
    FormEq (Sum.elim (DegPre.gtφT D T b (χ + χ')) fun k =>
        (lift (DegPre.cT D T χ) (lift (DegPre.cT D T χ') b)).left ≫ thφ D.P.A (x3 D.P.A) k)
      (Sum.elim DegPre.gtε thε) (Sum.elim (DegPre.gtφT D T b χ) (DegPre.gtφT D T b χ'))
      (Sum.elim DegPre.gtε DegPre.gtε) := by
  intro U _ h
  refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (prod_gtφT b _ h)
    (prod_cub (DegPre.cT D T χ) (DegPre.cT D T χ') b h))).trans (Eq.trans ?_
    ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (prod_gtφT b χ h) (prod_gtφT b χ' h))).symm)
  have : DegPre.cT D T (χ + χ') = DegPre.cT D T χ * DegPre.cT D T χ' := DVR.cPoint_add D T χ χ'
  rw [this]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

variable [IsLocalRing R] [IsAdicComplete I R] {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem existsUnique_gtPt (y : ∀ e, Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left)
    (hw : ∀ e, y e ≫ (thickObj R I e G).hom = 𝟙 _)
    (hy : ∀ e, thickTrans R I e ≫ y (e + 1) = y e ≫ thickMap R I e G) :
    ∃! gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R)))), ∀ e,
      thick R I e ≫ gp.b.left = y e ≫ (U.gt e).pG.left ∧ ∀ χ z J, Good D.toPre.P.L z J →
        val (Y := Spec (CommRingCat.of R)) (gp.s χ) (thick R I e) z J = val ((U.gt e).t χ) (y e) z J := by
  have hL := D.toPre.P.isLB
  obtain ⟨b₀, ⟨hb₀, hb⟩, hbu⟩ := existsUnique_over_of_isAdicFamily (I := I) (𝟙 _) D.toPre.P.A.hom
    (f := fun e => y e ≫ (U.gt e).pG.left)
    (fun e => by
      show thickTrans R I e ≫ y (e + 1) ≫ _ = _
      rw [← Category.assoc, hy, Category.assoc, U.gt_q])
    (fun e => by
      rw [Category.assoc, Over.w (U.gt e).pG, Category.comp_id]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ thick R I e) (hw e)).trans (Category.id_comp _)))
  let b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.toPre.P.A := Over.homMk b₀ hb₀
  have hb' : ∀ e, thick R I e ≫ b.left = y e ≫ (U.gt e).pG.left := hb
  choose s hs vs using fun χ => exists_gen_of_thick I hL
    (fun e => TorusCoord.formEq_of_left b (U.gt e).pG (thick R I e) (y e) (hb' e) χ)
    (fun e => LB.pullGen _ _ _ ((U.gt e).t χ) (y e))
    (fun e => DVR.pullGen_isGen _ _ _ _ ((U.gt e).t_gen χ) _) (fun e z J hJ => by
      refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
      rw [hy, Category.id_comp]
      exact (val_pull hJ _ _ _).symm.trans (val_corr hJ (U.gt_t e χ) (y e)))
  have vs' : ∀ χ e z J, Good D.toPre.P.L z J →
      val (s χ) (thick R I e) z J = val ((U.gt e).t χ) (y e) z J := fun χ e z J hJ => by
    refine (vs χ e z J hJ).trans ((val_pull hJ _ _ _).trans ?_)
    rw [Category.id_comp]
  have hm : ∀ χ χ', LB.Gen.Corr D.toPre.P.L _ _ _ _
      (LB.mulGen D.toPre.P.L _ _ _ _ (s (χ + χ'))
        (DegPre.cubAtT D.toPre _ (DegPre.cT D.toPre _ χ) (DegPre.cT D.toPre _ χ') b))
      (LB.mulGen D.toPre.P.L _ _ _ _ (s χ) (s χ')) := fun χ χ' =>
    corr_of_thick I hL (formEq_mult b χ χ')
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hs _) (DVR.pullGen_isGen _ _ _ _ D.toPre.cub.isGen _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hs _) (hs _)) fun e z J hJ => by
        refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
        refine Eq.trans (congrArg₂ (· * ·) (vs' _ e z J hJ) ((val_pull hJ _ _ _).trans ?_))
          ((TorusCoord.val_t_mul (U.gt e) (y e) χ χ' z J hJ).trans
            (congrArg₂ (· * ·) (vs' _ e z J hJ) (vs' _ e z J hJ)).symm)
        exact congrArg (fun q => TorusCoord.cubVal q z J)
          ((TorusCoord.comp_eq_of_left b (U.gt e).pG (thick R I e) (y e) (hb' e)).2 χ χ')
  have h0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (s 0) (LB.oneGen D.toPre.P.L) := corr_of_val hL fun z J hJ => by
    have h := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
      ((val_corr hJ (hm 0 0) (𝟙 _)).trans (val_mul hJ _ _ _))
    have c0 : DegPre.cT D.toPre (𝟙_ (Over (Spec (CommRingCat.of R)))) 0 = 1 := cPoint_zero _
    have c1 : TorusCoord.cubVal (𝟙 _ ≫ (lift (DegPre.cT D.toPre _ 0) (lift (DegPre.cT D.toPre _ 0) b)).left) z J
        = 1 := by
      rw [Category.id_comp, c0]
      exact (isCub_cubV D.toPre.cub hJ).face 1 b
    have key : ∀ {V : Type} [CommGroup V] (a c : V), c = 1 → a * c = a * a → a = 1 := fun a c hc h => by
      rw [hc] at h
      exact (mul_left_cancel h).symm
    rw [add_zero] at h
    exact (key _ _ c1 h).trans (val_one _).symm
  refine ⟨⟨b, s, hs, h0, hm⟩, fun e => ⟨hb' e, fun χ z J hJ => vs' χ e z J hJ⟩, ?_⟩
  rintro ⟨b', s', hs', _, _⟩ h
  obtain rfl : b' = b := Over.OverMorphism.ext (hbu b'.left ⟨Over.w b', fun e => (h e).1⟩)
  obtain rfl : s' = s := funext fun χ => TorusCoord.gen_eq_of_corr hL (hs' χ) (hs χ)
    (corr_of_thick I hL (fun _ _ _ => rfl) (hs' χ) (hs χ) fun e z J hJ =>
      ((h e).2 χ z J hJ).trans (vs' χ e z J hJ).symm)
  rfl

end Main

end GlobalTheory.CompletePoint

theorem GlobalTheory.existsUnique_gtPt_of_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (x : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G), ∃! gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R)))), (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) := by
  intro R _ _ _ I hR _ D A G _ _ U x
  have := hR.2.2.2
  have hx : x.left ≫ G.hom = 𝟙 _ := Over.w x
  have w : ∀ e, (thick R I e ≫ x.left) ≫ G.hom = 𝟙 _ ≫ thick R I e := fun e => by
    rw [Category.assoc, hx, Category.id_comp]; exact Category.comp_id _
  let y : ∀ e, Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left := fun e =>
    pullback.lift (thick R I e ≫ x.left) (𝟙 _) (w e)
  have y₁ : ∀ e, y e ≫ pullback.fst G.hom (thick R I e) = thick R I e ≫ x.left := fun e => pullback.lift_fst _ _ _
  have y₂ : ∀ e, y e ≫ (thickObj R I e G).hom = 𝟙 _ := fun e => pullback.lift_snd _ _ _
  have hy : ∀ e, thickTrans R I e ≫ y (e + 1) = y e ≫ thickMap R I e G := fun e => by
    have tf : thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) = pullback.fst G.hom (thick R I e) :=
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    refine (cancel_mono (pullback.fst G.hom (thick R I (e + 1)))).1 ?_
    exact ((Category.assoc _ _ _).trans ((congrArg (thickTrans R I e ≫ ·) (y₁ (e + 1))).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ x.left) (thickTrans_comp R I e))))).trans
      ((Category.assoc _ _ _).trans ((congrArg (y e ≫ ·) tf).trans (y₁ e))).symm
  refine (existsUnique_congr fun gp => forall_congr' fun e => ⟨fun h => ?_, ?_⟩).1
    (GlobalTheory.CompletePoint.existsUnique_gtPt U y y₂ hy)
  · refine ⟨Over.homMk (y e) ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ thick R I e) (y₂ e)).trans (Category.id_comp _))), Over.OverMorphism.ext (y₁ e),
      Over.OverMorphism.ext h.1.symm, fun χ => corr_of_val D.toPre.P.isLB fun z J hJ => ?_⟩
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    exact (congrArg (fun q => val _ q z J) (Category.id_comp _)).trans ((h.2 χ z J hJ).symm.trans
      (congrArg (fun q => val _ q z J) (Category.id_comp _)).symm)
  · rintro ⟨xe, h₁, h₂, h₃⟩
    have hxe : y e = xe.left := (cancel_mono (pullback.fst G.hom (thick R I e))).1
      ((y₁ e).trans (congrArg (·.left) h₁).symm)
    rw [hxe]
    refine ⟨(congrArg (·.left) h₂).symm, fun χ z J hJ => ?_⟩
    have := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (h₃ χ) (𝟙 _)).trans (val_pull hJ _ _ _))
    rw [Category.id_comp, Category.id_comp] at this
    exact this.symm
