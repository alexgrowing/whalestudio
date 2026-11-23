import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceThickening
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniformizationEndomorphismOfLinear
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.EndCalc

variable {R : Type} [CommRing R] [IsDomain R]

section Rep

open FreeAbelianGroup

variable {D : DegPre R} {T₀ : Over (Spec (CommRingCat.of R))}

abbrev Vals (D : DegPre R) (T₀ : Over (Spec (CommRingCat.of R))) :=
  ∀ (T : Over (Spec (CommRingCat.of R))) (_ : T ⟶ T₀) (z : T.left) (_ : (T.left ⟶ D.P.A.left) → D.P.L.ι),
    (T.left.presheaf.stalk z)ˣ

def Rep (s : FreeAbelianGroup (T₀ ⟶ D.P.A)) (v : Vals D T₀) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (T₀.left ⟶ D.P.A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb D.P.L φ ε)),
    t.IsGen ∧ (∀ (U : Type) [CommGroup U] (h : (T₀.left ⟶ D.P.A.left) → U),
      ∏ k, h (φ k) ^ ε k = (FreeAbelianGroup.lift (fun q : T₀ ⟶ D.P.A => Additive.ofMul (h q.left)) s).toMul) ∧
    ∀ T (ρ : T ⟶ T₀) z J, Good D.P.L z J → val t ρ.left z J = v T ρ z J

theorem Rep.one : Rep (D := D) (T₀ := T₀) 0 fun _ _ _ _ => 1 :=
  ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, LB.oneGen D.P.L,
    fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm,
    fun U _ h => by simp, fun _ _ _ _ _ => val_one _⟩

theorem Rep.mul {s s' : FreeAbelianGroup (T₀ ⟶ D.P.A)} {v v' : Vals D T₀} (h : Rep s v) (h' : Rep s' v') :
    Rep (s + s') fun T ρ z J => v T ρ z J * v' T ρ z J := by
  obtain ⟨K, _, φ, ε, t, ht, f, e⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', f', e'⟩ := h'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen D.P.L _ _ _ _ t t', mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ h => ?_, fun T ρ z J hJ => (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (e T ρ z J hJ) (e' T ρ z J hJ))⟩
  rw [map_add, toMul_add]
  exact prod_sum₂ (K := K) (K' := K') (U := U) _ (f U h) (f' U h)

theorem Rep.cub (x x' y : T₀ ⟶ D.P.A) :
    Rep (of (x * x' * y) - of (x * x') - of (x * y) - of (x' * y) + of x + of x' + of y - of 1)
      fun _ ρ z J => th D z J (ρ ≫ x) (ρ ≫ x') (ρ ≫ y) := by
  refine ⟨thK, inferInstance, _, _, LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift x (lift x' y)).left,
    pullGen_isGen _ _ _ _ D.cub.isGen _, fun U _ h => (prod_cub x x' y h).trans ?_,
    fun T ρ z J hJ => val_cub D.cub ρ hJ _ _ _⟩
  simp only [map_add, map_sub, lift_apply_of, toMul_add, toMul_sub, toMul_ofMul, div_eq_mul_inv]

abbrev CmpGen (D : DegPre R) (a : D.P.A ⟶ D.P.A) (p χ : D.X) : Type :=
  LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) p) (D.Oφ a χ)) (Sum.elim Oε Oinvε))

theorem Rep.cmp {a : D.P.A ⟶ D.P.A} {p χ : D.X} {u : CmpGen D a p χ} (hu : Normd u) (x : T₀ ⟶ D.P.A) :
    Rep (of (cP D T₀ p * x) - of (cP D T₀ p) - of x - of (cP D T₀ χ * (x ≫ a)) + of (cP D T₀ χ) + of (x ≫ a))
      fun _ ρ z J => val u (ρ ≫ x).left z J := by
  refine ⟨Fin 4 ⊕ Fin 4, inferInstance, _, _, LB.pullGen D.P.L _ _ u x.left, pullGen_isGen _ _ _ _ hu.1 _,
    fun U _ h => ?_, fun T ρ z J hJ => val_pull hJ _ _ _⟩
  refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
    ((Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ Oε k) (WeightPf.Oφ_comp x (𝟙 _) p k)).trans
      (OLinEnd.prod_Oφ D _ p h))
    ((Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ Oinvε k) (WeightPf.Oφ_comp x a χ k)).trans
      (OLinEnd.prod_Oφ_inv D _ χ h))).trans ?_
  rw [Category.comp_id]
  apply Additive.ofMul.injective
  simp only [map_add, map_sub, lift_apply_of, ofMul_mul, ofMul_inv, ofMul_toMul]
  abel

theorem Rep.unique {s s' : FreeAbelianGroup (T₀ ⟶ D.P.A)} {v v' : Vals D T₀} (h : Rep s v) (h' : Rep s' v')
    (hs : Function.Surjective T₀.hom.appTop.hom) (e : 𝟙_ _ ⟶ T₀) (hF : s = s')
    (h₀ : ∀ y J, Good D.P.L y J → v _ e y J = v' _ e y J) {T} (ρ : T ⟶ T₀) {z J} (hJ : Good D.P.L z J) :
    v T ρ z J = v' T ρ z J := by
  obtain ⟨K, _, φ, ε, t, ht, f, c⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', f', c'⟩ := h'
  subst hF
  exact (c T ρ z J hJ).symm.trans ((gen_unique' D.P.isLB (fun U _ h => (f' U h).trans (f U h).symm) T₀.hom e.left
    (Over.w e) hs ht ht' (fun y I hI => (c _ e y I hI).trans ((h₀ y I hI).trans (c' _ e y I hI).symm))
    _ ρ.left z J hJ).trans (c' T ρ z J hJ))

end Rep

section Cmp

variable {D : DegPre R} {a a' a'' : D.P.A ⟶ D.P.A} {p p' p'' χ χ' χ'' : D.X} {T : Over (Spec (CommRingCat.of R))}
  {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι}

theorem cmp_one {u : CmpGen D a p χ} (hu : Normd u) (hJ : Good D.P.L z J) : val u (1 : T ⟶ D.P.A).left z J = 1 :=
  (val_pull hJ u (eSec D.P.A) (toUnit T).left).symm.trans ((val_corr hJ hu.2 _).trans (val_one _))

theorem cmp_zero (hG : GlobalFnsSt) {u : CmpGen D a p χ} (hu : Normd u) (hp : p = 0) (hχ : χ = 0)
    (hJ : Good D.P.L z J) (x : T ⟶ D.P.A) : val u x.left z J = 1 := by
  have h := (Rep.cmp hu (𝟙 _)).unique Rep.one (hG _ _ D.P.isAb).2 1 (by
    rw [hp, hχ, cPoint_zero, _root_.one_mul, _root_.one_mul]; abel)
    (fun y I hI => by rw [Category.comp_id, cmp_one hu hI]) x hJ
  rwa [Category.comp_id] at h

theorem cmp_congr (hG : GlobalFnsSt) {u : CmpGen D a p χ} (hu : Normd u) {u' : CmpGen D a' p' χ} (hu' : Normd u')
    (ha : a = a') (hp : p = p') (hJ : Good D.P.L z J) (x : T ⟶ D.P.A) : val u x.left z J = val u' x.left z J := by
  have h := (Rep.cmp hu (𝟙 _)).unique (Rep.cmp hu' (𝟙 _)) (hG _ _ D.P.isAb).2 1 (by rw [ha, hp])
    (fun y I hI => by rw [Category.comp_id, cmp_one hu hI, cmp_one hu' hI]) x hJ
  rwa [Category.comp_id] at h

theorem cmp_add_char (hG : GlobalFnsSt) [IsMonHom a] {u : CmpGen D a p χ} (hu : Normd u) {u' : CmpGen D a p' χ'}
    (hu' : Normd u') {u'' : CmpGen D a p'' (χ + χ')} (hu'' : Normd u'') (hp : p'' = p + p')
    (hJ : Good D.P.L z J) (x : T ⟶ D.P.A) :
    val u'' x.left z J * th D z J (cP D T χ) (cP D T χ') (x ≫ a) =
      th D z J (cP D T p) (cP D T p') x * (val u x.left z J * val u' x.left z J) := by
  have h := ((Rep.cmp hu'' (𝟙 _)).mul (Rep.cub (cP D _ χ) (cP D _ χ') a)).unique
    ((Rep.cub (cP D _ p) (cP D _ p') (𝟙 _)).mul ((Rep.cmp hu (𝟙 _)).mul (Rep.cmp hu' (𝟙 _))))
    (hG _ _ D.P.isAb).2 1 (by rw [hp, cPoint_add, cPoint_add, Category.id_comp]; abel)
    (fun y I hI => by
      have C : IsCub (th D (T := 𝟙_ _) y I) := isCub_cubV D.cub hI
      rw [Category.comp_id, cmp_one hu hI, cmp_one hu' hI, cmp_one hu'' hI, MonObj.one_comp a, C.face₃, C.face₃]
      simp) x hJ
  simpa only [Category.comp_id, comp_cP] using h

theorem cmp_add_end (hG : GlobalFnsSt) [IsMonHom a] {u : CmpGen D a p χ} (hu : Normd u) {u' : CmpGen D a' p' χ}
    (hu' : Normd u') {u'' : CmpGen D a'' p'' χ} (hu'' : Normd u'') (ha : a'' = a * a') (hp : p'' = p + p')
    (hJ : Good D.P.L z J) (x : T ⟶ D.P.A) :
    val u'' x.left z J * th D z J (cP D T χ) (x ≫ a) (x ≫ a') =
      th D z J (cP D T p) (cP D T p') x * (val u x.left z J * val u' x.left z J) := by
  have h := ((Rep.cmp hu'' (𝟙 _)).mul (Rep.cub (cP D _ χ) a a')).unique
    ((Rep.cub (cP D _ p) (cP D _ p') (𝟙 _)).mul ((Rep.cmp hu (𝟙 _)).mul (Rep.cmp hu' (𝟙 _))))
    (hG _ _ D.P.isAb).2 1 (by
      rw [hp, ha, cPoint_add, Category.id_comp, Category.id_comp, Category.id_comp, _root_.mul_assoc _ a a']; abel)
    (fun y I hI => by
      have C : IsCub (th D (T := 𝟙_ _) y I) := isCub_cubV D.cub hI
      rw [Category.comp_id, cmp_one hu hI, cmp_one hu' hI, cmp_one hu'' hI, MonObj.one_comp a, C.face₂, C.face₃]
      simp) x hJ
  simpa only [Category.comp_id, comp_cP] using h

theorem cmp_comp (hG : GlobalFnsSt) [IsMonHom a] {u : CmpGen D a p p'} (hu : Normd u) {u' : CmpGen D a' p' χ}
    (hu' : Normd u') {u'' : CmpGen D a'' p'' χ} (hu'' : Normd u'') (ha : a'' = a ≫ a') (hp : p'' = p)
    (hJ : Good D.P.L z J) (x : T ⟶ D.P.A) :
    val u'' x.left z J = val u x.left z J * val u' (x ≫ a).left z J := by
  have h := (Rep.cmp hu'' (𝟙 _)).unique ((Rep.cmp hu (𝟙 _)).mul (Rep.cmp hu' a))
    (hG _ _ D.P.isAb).2 1 (by rw [hp, ha, Category.id_comp, Category.id_comp]; abel)
    (fun y I hI => by
      rw [Category.comp_id, MonObj.one_comp, cmp_one hu hI, cmp_one hu' hI, cmp_one hu'' hI, _root_.mul_one]) x hJ
  simpa only [Category.comp_id] using h

theorem cmp_add_pt (hG : GlobalFnsSt) [IsMonHom a] {u : CmpGen D a p χ} (hu : Normd u)
    (hJ : Good D.P.L z J) (x y : T ⟶ D.P.A) :
    val u (x * y).left z J * th D z J (cP D T χ) (x ≫ a) (y ≫ a) =
      th D z J (cP D T p) x y * (val u x.left z J * val u y.left z J) := by
  have sj : Function.Surjective (D.P.A ⊗ D.P.A).hom.appTop.hom := by
    rw [← Over.w (snd D.P.A D.P.A)]
    exact surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2
  have h := ((Rep.cmp hu (fst _ _ * snd _ _)).mul (Rep.cub (cP D _ χ) (fst _ _ ≫ a) (snd _ _ ≫ a))).unique
    ((Rep.cub (cP D _ p) (fst _ _) (snd _ _)).mul ((Rep.cmp hu (fst _ _)).mul (Rep.cmp hu (snd _ _))))
    sj (lift 1 1) (by
      rw [MonObj.mul_comp, _root_.mul_assoc (cP D _ χ), _root_.mul_assoc (cP D _ p)]; abel)
    (fun y I hI => by
      have C : IsCub (th D (T := 𝟙_ _) y I) := isCub_cubV D.cub hI
      rw [MonObj.comp_mul, lift_fst_assoc, lift_fst, lift_snd, _root_.mul_one, cmp_one hu hI, MonObj.one_comp,
        C.face₂, C.face₂]
      simp) (lift x y) hJ
  simpa only [MonObj.comp_mul, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, comp_cP] using h

end Cmp

section End

open GlobalTheory.TorusExt

variable {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G}

theorem end_base_ext (hR : AdmBase R I) (U : UnifPre I D A G) {b b' : D.toPre.P.A ⟶ D.toPre.P.A}
    (h : ∀ e, (U.gt e).q ≫ (Over.pullback (thick R I e)).map b = (U.gt e).q ≫ (Over.pullback (thick R I e)).map b') :
    b = b' := by
  obtain ⟨_, -, -, _⟩ := hR
  have := D.toPre.P.isAb.smooth
  have := D.toPre.P.isAb.geomConnected
  have := D.toPre.P.isAb.proper
  refine (sec_eq_zero_and_hom_eq_of_thickenings R I (IsAdicComplete.le_jacobson_bot I) D.toPre.P.A).2 _ b b' fun e => ?_
  have := (U.gt e).q_flat
  have := (U.gt e).q_surj
  have := (U.gt e).q_affine
  have := FlatQuotient.epi_of_flat_surjective (U.gt e).q
  have k := congrArg (fun q => q.left ≫ pullback.fst D.toPre.P.A.hom (thick R I e)) ((cancel_epi _).1 (h e))
  exact (pullback.lift_fst _ _ _).symm.trans (k.trans (pullback.lift_fst _ _ _))

theorem end_char_ext (hR : AdmBase R I) (U : UnifPre I D A G) {h h' : D.toPre.X → D.toPre.X}
    {t t' : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (0 + 1)))) D.toPre.X ⟶ splitTorus _ D.toPre.X}
    (ht : TorusEndOf D.toPre.X h t) (ht' : TorusEndOf D.toPre.X h' t')
    (e : t ≫ (U.gt 0).i = t' ≫ (U.gt 0).i) (χ : D.toPre.X) : h χ = h' χ := by
  have := hR.2.2.2
  have := EndTorus.connectedSpace_thickening I 0
  have : Mono (U.gt 0).i := by
    have : Mono (η[thickObj R I 0 D.toPre.P.A]) := ⟨fun _ _ _ => toUnit_unique _ _⟩
    exact (MorphismProperty.monomorphisms _).of_isPullback (U.gt 0).isKernel.flip (.infer_property _)
  obtain rfl : t = t' := (cancel_mono _).1 e
  exact SplitTorusHom.charUnit_injective (S := Spec (CommRingCat.of (R ⧸ I ^ (0 + 1))))
    (congrArg Units.val ((ht χ).symm.trans (ht' χ)))

theorem pullback_map_mul {S S' : Scheme.{0}} (f : S' ⟶ S) {H : Over S} [GrpObj H] (a a' : H ⟶ H) :
    (Over.pullback f).map (a * a') = (Over.pullback f).map a * (Over.pullback f).map a' :=
  map_mul ((Over.pullback f).homMonoidHom (X := H) (M := H)) a a'

theorem congr_data (hR : AdmBase R I) (E E' : EndU U) (h : E.aG = E'.aG) : E.aB = E'.aB ∧ E.h = E'.h := by
  refine ⟨end_base_ext hR U fun e => by rw [← E.q_lin, ← E'.q_lin, h], AddMonoidHom.ext fun χ => ?_⟩
  obtain ⟨t, ht, e⟩ := E.i_lin 0
  obtain ⟨t', ht', e'⟩ := E'.i_lin 0
  exact end_char_ext hR U ht ht' (by rw [← e, ← e', h]) χ

theorem add_data (hR : AdmBase R I) (E E' E'' : EndU U) (h : E''.aG = E.aG * E'.aG) :
    E''.aB = E.aB * E'.aB ∧ E''.h = E.h + E'.h := by
  refine ⟨end_base_ext hR U fun e => ?_, AddMonoidHom.ext fun χ => ?_⟩
  · have := (U.gt e).q_hom
    rw [← E''.q_lin, h, pullback_map_mul, pullback_map_mul, MonObj.mul_comp, MonObj.comp_mul, E.q_lin, E'.q_lin]
  · obtain ⟨t, ht, e⟩ := E.i_lin 0
    obtain ⟨t', ht', e'⟩ := E'.i_lin 0
    obtain ⟨t'', ht'', e''⟩ := E''.i_lin 0
    have := (U.gt 0).i_hom
    refine end_char_ext hR U (h' := fun χ => E.h χ + E'.h χ) (t' := t * t') ht''
      ((EndTorus.torusEndOf_iff_appTop _ _).2 fun χ => ?_) ?_ χ
    · rw [SplitTorusHom.appTop_mul_charUnit, SplitTorusHom.charUnit_add,
        (EndTorus.torusEndOf_iff_appTop _ _).1 ht, (EndTorus.torusEndOf_iff_appTop _ _).1 ht']
    · rw [← e'', h, pullback_map_mul, MonObj.mul_comp, MonObj.comp_mul, e, e']

theorem comp_data (hR : AdmBase R I) (E E' E'' : EndU U) (h : E''.aG = E.aG ≫ E'.aG) :
    E''.aB = E.aB ≫ E'.aB ∧ E''.h = E.h.comp E'.h := by
  refine ⟨end_base_ext hR U fun e => ?_, AddMonoidHom.ext fun χ => ?_⟩
  · rw [← E''.q_lin, h, Functor.map_comp, Functor.map_comp, Category.assoc, E'.q_lin, ← Category.assoc, E.q_lin,
      Category.assoc]
  · obtain ⟨t, ht, e⟩ := E.i_lin 0
    obtain ⟨t', ht', e'⟩ := E'.i_lin 0
    obtain ⟨t'', ht'', e''⟩ := E''.i_lin 0
    refine end_char_ext hR U (h' := fun χ => E.h (E'.h χ)) (t' := t ≫ t') ht''
      ((EndTorus.torusEndOf_iff_appTop _ _).2 fun χ => ?_) ?_ χ
    · rw [SplitTorusHom.appTop_comp, (EndTorus.torusEndOf_iff_appTop _ _).1 ht',
        (EndTorus.torusEndOf_iff_appTop _ _).1 ht]
    · rw [← e'', h, Functor.map_comp, ← Category.assoc, e, Category.assoc, e', Category.assoc]

variable {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem act_val {E : EndU U} {g g' : GtPtF D.toPre F} (h : E.Act g g') (χ : D.toPre.X) {y J}
    (hJ : Good D.toPre.P.L y J) : charVal g' χ y J = charVal g (E.h χ) y J * val (E.u χ) g.b.left y J :=
  h.2 χ y J hJ

theorem exists_act (hG : GlobalFnsSt) (E : EndU U) (g : GtPtF D.toPre F) : ∃ g', E.Act g g' := by
  have := E.homB
  have vv : ∀ χ y J, Good D.toPre.P.L y J → val (LB.mulGen D.toPre.P.L _ _ _ _ (g.s (E.h χ))
      (LB.pullGen D.toPre.P.L _ _ (E.u χ) g.b.left)) (𝟙 (TF (R := R) F).left) y J =
      charVal g (E.h χ) y J * val (E.u χ) g.b.left y J := fun χ y J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (by rw [Category.id_comp])))
  obtain ⟨g', hb, hv⟩ := exists_gt (g.b ≫ E.aB) (fun χ => LB.mulGen D.toPre.P.L _ _ _ _ (g.s (E.h χ))
      (LB.pullGen D.toPre.P.L _ _ (E.u χ) g.b.left))
    (fun χ => mulGen_isGen _ _ _ _ _ _ _ (g.isGen _) (pullGen_isGen _ _ _ _ (E.u_norm χ).1 _)) (fun χ V _ h => by
      refine (prod_sum₂ (K := Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := V) _ (prod_gt g.b (E.h χ) h)
        (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := V) _
          ((Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ Oε k)
            (WeightPf.Oφ_comp g.b (𝟙 _) (E.h χ) k)).trans (OLinEnd.prod_Oφ D.toPre _ (E.h χ) h))
          ((Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ Oinvε k)
            (WeightPf.Oφ_comp g.b E.aB χ k)).trans (OLinEnd.prod_Oφ_inv D.toPre _ χ h)))).trans ?_
      rw [prod_gt, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (fun y J hJ => by
      refine (vv 0 y J hJ).trans ?_
      rw [cmp_zero hG (E.u_norm 0) (map_zero _) rfl hJ, map_zero, charVal_zero g hJ, _root_.mul_one])
    (fun χ χ' y J hJ => by
      have e₁ := congrArg Additive.ofMul
        (cmp_add_char hG (E.u_norm χ) (E.u_norm χ') (E.u_norm (χ + χ')) (map_add _ _ _) hJ g.b)
      have e₂ := charVal_add g hJ (E.h χ) (E.h χ')
      rw [← map_add] at e₂
      have e₃ := congrArg Additive.ofMul e₂
      refine (congrArg₂ (· * ·) (vv _ y J hJ) rfl).trans (Eq.trans ?_ (congrArg₂ (· * ·) (vv _ y J hJ) (vv _ y J hJ)).symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul] at e₁ e₃ ⊢
      linear_combination (norm := abel) e₁ + e₃)
  exact ⟨g', hb, fun χ y J hJ => (hv χ y J hJ).trans (vv χ y J hJ)⟩

theorem act_unique {E : EndU U} {g g' g'' : GtPtF D.toPre F} (h : E.Act g g') (h' : E.Act g g'') : g' = g'' :=
  gt_ext_val (h.1.trans h'.1.symm) fun χ _ _ hJ => (act_val h χ hJ).trans (act_val h' χ hJ).symm

theorem act_isAdd (hG : GlobalFnsSt) {E : EndU U} {g₁ g₂ g₃ g₁' g₂' g₃' : GtPtF D.toPre F} (h : g₁.IsAdd g₂ g₃)
    (h₁ : E.Act g₁ g₁') (h₂ : E.Act g₂ g₂') (h₃ : E.Act g₃ g₃') : g₁'.IsAdd g₂' g₃' := by
  have := E.homB
  obtain ⟨b, v⟩ := (isAdd_iff_val _ _ _).1 h
  refine (isAdd_iff_val _ _ _).2 ⟨by rw [h₁.1, h₂.1, h₃.1, b, MonObj.mul_comp], fun χ y J hJ => ?_⟩
  have e₁ := cmp_add_pt hG (E.u_norm χ) hJ g₁.b g₂.b
  rw [← b, ← h₁.1, ← h₂.1] at e₁
  have e₂ := congrArg Additive.ofMul e₁
  have e₃ := congrArg Additive.ofMul (v (E.h χ) y J hJ)
  rw [act_val h₁ χ hJ, act_val h₂ χ hJ, act_val h₃ χ hJ]
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at e₂ e₃ ⊢
  linear_combination (norm := abel) e₂ + e₃

theorem act_isTor {E : EndU U} {t : Multiplicative D.toPre.X →* Fˣ} {g g' : GtPtF D.toPre F} (ht : IsTor t g)
    (h : E.Act g g') : IsTor (t.comp (AddMonoidHom.toMultiplicative E.h)) g' := by
  have := E.homB
  refine ⟨by rw [h.1, ht.1, MonObj.one_comp], fun χ y J hJ => ?_⟩
  have e : val (E.u χ) g.b.left y J = 1 :=
    (congrArg (fun b : TF (R := R) F ⟶ D.toPre.P.A => val (E.u χ) b.left y J) ht.1).trans (cmp_one (E.u_norm χ) hJ)
  have e' := act_val h χ hJ
  rw [e, _root_.mul_one] at e'
  exact (congrArg Units.val e').trans (ht.2 (E.h χ) y J hJ)

theorem act_congr (hG : GlobalFnsSt) {E E' : EndU U} (hb : E.aB = E'.aB) (hh : E.h = E'.h)
    {g g' : GtPtF D.toPre F} (h : E.Act g g') : E'.Act g g' :=
  ⟨hb ▸ h.1, fun χ y J hJ => (act_val h χ hJ).trans (congrArg₂ (· * ·)
    (congrArg (fun k : D.toPre.X →+ D.toPre.X => charVal g (k χ) y J) hh)
    (cmp_congr hG (E.u_norm χ) (E'.u_norm χ) hb (by rw [hh]) hJ g.b))⟩

theorem act_add_end (hG : GlobalFnsSt) {E E' E'' : EndU U} (hb : E''.aB = E.aB * E'.aB) (hh : E''.h = E.h + E'.h)
    {g g₁ g₂ g₃ : GtPtF D.toPre F} (h₁ : E.Act g g₁) (h₂ : E'.Act g g₂) (h : g₁.IsAdd g₂ g₃) : E''.Act g g₃ := by
  have := E.homB
  obtain ⟨b, v⟩ := (isAdd_iff_val _ _ _).1 h
  refine ⟨by rw [b, h₁.1, h₂.1, hb, MonObj.comp_mul], fun χ y J hJ => ?_⟩
  have hp : E''.h χ = E.h χ + E'.h χ := by rw [hh, AddMonoidHom.add_apply]
  have e₁ := cmp_add_end hG (E.u_norm χ) (E'.u_norm χ) (E''.u_norm χ) hb hp hJ g.b
  rw [← h₁.1, ← h₂.1] at e₁
  have e₂ := charVal_add g hJ (E.h χ) (E'.h χ)
  rw [← hp] at e₂
  have e₃ := v χ y J hJ
  rw [act_val h₁ χ hJ, act_val h₂ χ hJ] at e₃
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  have a₃ := congrArg Additive.ofMul e₃
  change charVal g₃ χ y J = charVal g (E''.h χ) y J * val (E''.u χ) g.b.left y J
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at a₁ a₂ a₃ ⊢
  linear_combination (norm := abel) a₃ - a₁ - a₂

theorem act_comp_end (hG : GlobalFnsSt) {E E' E'' : EndU U} (hb : E''.aB = E.aB ≫ E'.aB) (hh : E''.h = E.h.comp E'.h)
    {g g₁ g₂ : GtPtF D.toPre F} (h₁ : E.Act g g₁) (h₂ : E'.Act g₁ g₂) : E''.Act g g₂ := by
  have := E.homB
  refine ⟨by rw [h₂.1, h₁.1, hb, Category.assoc], fun χ y J hJ => ?_⟩
  have hp : E''.h χ = E.h (E'.h χ) := by rw [hh, AddMonoidHom.comp_apply]
  have e₁ := cmp_comp hG (E.u_norm (E'.h χ)) (E'.u_norm χ) (E''.u_norm χ) hb hp hJ g.b
  rw [← h₁.1] at e₁
  change charVal g₂ χ y J = charVal g (E''.h χ) y J * val (E''.u χ) g.b.left y J
  rw [act_val h₂ χ hJ, act_val h₁ _ hJ, e₁, _root_.mul_assoc]
  exact congrArg (fun k => charVal g k y J * _) hp.symm

end End

theorem end_calculus : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ E E' E'' : EndU U.toUnifPre, (∀ g : GtPtF D.toPre F, ∃! g', E.Act g g') ∧ (∀ g₁ g₂ g₃ g₁' g₂' g₃' : GtPtF D.toPre F, g₁.IsAdd g₂ g₃ → E.Act g₁ g₁' → E.Act g₂ g₂' → E.Act g₃ g₃' → g₁'.IsAdd g₂' g₃') ∧ (∀ t (g g' : GtPtF D.toPre F), IsTor t g → E.Act g g' → IsTor (t.comp (AddMonoidHom.toMultiplicative E.h)) g') ∧ (E.aG = E'.aG → E.aB = E'.aB ∧ E.h = E'.h ∧ ∀ g g' : GtPtF D.toPre F, E.Act g g' ↔ E'.Act g g') ∧ (E''.aG = E.aG * E'.aG → E''.aB = E.aB * E'.aB ∧ E''.h = E.h + E'.h ∧ ∀ g g₁ g₂ g₃ : GtPtF D.toPre F, E.Act g g₁ → E'.Act g g₂ → g₁.IsAdd g₂ g₃ → E''.Act g g₃) ∧ (E''.aG = E.aG ≫ E'.aG → E''.aB = E.aB ≫ E'.aB ∧ E''.h = E.h.comp E'.h ∧ ∀ g g₁ g₂ : GtPtF D.toPre F, E.Act g g₁ → E'.Act g₁ g₂ → E''.Act g g₂) := by
  intro hL R _ _ _ I hR D A G _ _ _ U F _ _ _ E E' E''
  have hG := hL.1.globalFns
  refine ⟨fun g => ?_, fun _ _ _ _ _ _ => act_isAdd hG, fun _ _ _ => act_isTor, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨g', hg⟩ := exists_act hG E g
    exact ⟨g', hg, fun _ h => act_unique h hg⟩
  · obtain ⟨hb, hh⟩ := congr_data hR E E' h
    exact ⟨hb, hh, fun _ _ => ⟨act_congr hG hb hh, act_congr hG hb.symm hh.symm⟩⟩
  · obtain ⟨hb, hh⟩ := add_data hR E E' E'' h
    exact ⟨hb, hh, fun _ _ _ _ => act_add_end hG hb hh⟩
  · obtain ⟨hb, hh⟩ := comp_data hR E E' E'' h
    exact ⟨hb, hh, fun _ _ _ => act_comp_end hG hb hh⟩

end GlobalTheory.EndCalc
