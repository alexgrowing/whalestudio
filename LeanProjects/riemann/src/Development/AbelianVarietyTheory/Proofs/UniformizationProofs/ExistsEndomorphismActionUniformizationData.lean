import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceThickening
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisedAbelianSchemesIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartIsoIsMonHomAndRigidified
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSec
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianProjectiveBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismCharacterMapConstantStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordEndRatioDescendsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGeneratorOfCompatibleThickeningGeneratorsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEndomorphismAlgebraisingThickeningsStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.EndData

theorem val_eq_of_flat {X Y Y' Y₁ Y₂ : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ₁ : K → (Y₁ ⟶ X)} {φ₂ : K → (Y₂ ⟶ X)} {ε : K → ℤ} (t₁ : LB.Gen (LB.LinComb L φ₁ ε))
    (t₂ : LB.Gen (LB.LinComb L φ₂ ε)) (m₁ : Y ⟶ Y₁) (m₂ : Y ⟶ Y₂) (hm : ∀ k, m₁ ≫ φ₁ k = m₂ ≫ φ₂ k)
    (π : Y' ⟶ Y) [Flat π] [Surjective π]
    (h : ∀ x J, Good L x J → val t₁ (π ≫ m₁) x J = val t₂ (π ≫ m₂) x J) (y : Y) (J) (hJ : Good L y J) :
    val t₁ m₁ y J = val t₂ m₂ y J := by
  have : Epi π := Flat.epi_of_flat_of_surjective _
  let j : K → L.ι := fun k => J (m₁ ≫ φ₁ k)
  have h₁ : m₁ y ∈ LB.wchart L φ₁ j := hJ.mem φ₁ m₁
  have e₂ : ∀ k, J (m₂ ≫ φ₂ k) = j k := fun k => congrArg J (hm k).symm
  have h₂ : m₂ y ∈ LB.wchart L φ₂ j := (funext e₂ : _ = j) ▸ hJ.mem φ₂ m₂
  have key := UnifCompare.gm_eq_of_flat_surjective π (pullU m₁ (LB.wchart L φ₁ j) (t₁.s j))
    (pullU m₂ (LB.wchart L φ₂ j) (t₂.s j)) (fun x hx₁ hx₂ => by
      obtain ⟨J', hJ', e⟩ := exists_good L hL x (fun k => (π ≫ m₁) ≫ φ₁ k) j
        (fun a b e => congrArg J (by simpa only [Category.assoc, cancel_epi] using e))
        (fun k => Set.mem_iInter.1 hx₁ k)
      have := h x J' hJ'
      rw [val_of t₁ _ x J' j e, val_of t₂ _ x J' j (fun k => by
        rw [Category.assoc, ← hm, ← Category.assoc]; exact e k)] at this
      exact (gm_pull π m₁ x _ hx₁ _).trans (this.trans (gm_pull π m₂ x _ hx₂ _).symm)) (𝟙 Y) y h₁ h₂
  have k₁ := gm_pull (𝟙 Y) m₁ y _ h₁ (t₁.s j)
  have k₂ := gm_pull (𝟙 Y) m₂ y _ h₂ (t₂.s j)
  rw [Category.id_comp] at k₁ k₂
  rw [val_of t₂ m₂ y J j e₂]
  exact k₁.symm.trans (key.trans k₂)

theorem val_eq_one {R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R] {X : Scheme.{0}} {L : LB X}
    (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Spec (CommRingCat.of R) ⟶ X)} {ε : K → ℤ}
    (hf : FormEq (K' := PEmpty) φ ε PEmpty.elim PEmpty.elim) (c : LB.Gen (LB.LinComb L φ ε)) (hc : c.IsGen)
    (h : ∀ e z J, Good L z J → val c (thick R I e) z J = 1) (y) (J) (hJ : Good L y J) :
    val c (𝟙 _) y J = 1 := by
  obtain ⟨c', -, hv⟩ := exists_gen hL hf c hc
  have le : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ LB.wchart L (K := PEmpty) PEmpty.elim PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  have ev : ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (J), Good L z J →
      val c r z J = gm r z ⊤ (res le (c'.s PEmpty.elim)) := fun Z r z J hJ =>
    (hv Z r z J hJ).symm.trans ((val_of c' r z J PEmpty.elim (fun k => k.elim)).trans
      (gm_res r z le trivial _).symm)
  have one : res le (c'.s PEmpty.elim) = 1 := by
    refine Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
      (SecAlg.eq_of_forall_mk I fun e => ?_))
    have key : ((thick R I e).app ⊤).hom (res le (c'.s PEmpty.elim)).val = ((thick R I e).app ⊤).hom 1 := by
      refine fn_ext fun z hz => ?_
      choose J hJ using fun ψ : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ X => exists_chart hL (ψ z)
      rw [gs_pull _ _ z ⊤ trivial, gs_pull _ _ z ⊤ trivial, Category.id_comp, gs_unit _ z ⊤ trivial,
        ← ev _ _ z J hJ, h e z J hJ, gs_eq _ z ⊤ trivial, map_one, map_one, Units.val_one]
    have nat := fun x => congrArg (fun φ => φ.hom x)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
    exact (nat _).symm.trans ((congrArg _ key).trans (nat 1))
  rw [ev _ _ y J hJ, one, map_one]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}

theorem prod_unit (D : DegPre R) (p : D.P.A ⟶ D.P.A) [IsMonHom p] (χ : D.X) {U : Type} [CommGroup U]
    (h : (Spec (CommRingCat.of R) ⟶ D.P.A.left) → U) :
    ∏ k, h (eSec D.P.A ≫ D.Oφ p χ k) ^ Oε k = 1 ∧ ∏ k, h (eSec D.P.A ≫ D.Oφ p χ k) ^ Oinvε k = 1 := by
  let T := 𝟙_ (Over (Spec (CommRingCat.of R)))
  have o : η[D.P.A] ≫ p = (1 : T ⟶ D.P.A) := by simp [Hom.one_def, T]
  have e0 : ∀ k, eSec D.P.A ≫ D.Oφ p χ k = D.Oφ (1 : T ⟶ D.P.A) χ k :=
    fun k => (WeightPf.Oφ_comp η[D.P.A] p χ k).trans (congrArg (D.Oφ · χ k) o)
  simp only [e0]
  rw [Fin.prod_univ_four, Fin.prod_univ_four]
  constructor
  · show h ((1 : T ⟶ D.P.A) * (toUnit T ≫ D.c χ)).left ^ (1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (-1 : ℤ) *
      h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (1 : ℤ) = 1
    rw [_root_.one_mul]
    simp
  · show h ((1 : T ⟶ D.P.A) * (toUnit T ≫ D.c χ)).left ^ (-1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (1 : ℤ) *
      h (1 : T ⟶ D.P.A).left ^ (1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = 1
    rw [_root_.one_mul]
    simp

omit [IsDomain R] in
theorem map_fst (e : ℕ) {G G' : Over (Spec (CommRingCat.of R))} (a : G ⟶ G') :
    ((Over.pullback (thick R I e)).map a).left ≫ pullback.fst G'.hom (thick R I e) =
      pullback.fst G.hom (thick R I e) ≫ a.left := pullback.lift_fst _ _ _

omit [IsDomain R] in
theorem trans_fst (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) = pullback.fst G.hom (thick R I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

omit [IsDomain R] in

theorem trans_map (e : ℕ) {G G' : Over (Spec (CommRingCat.of R))} (a : G ⟶ G') :
    thickMap R I e G ≫ ((Over.pullback (thick R I (e + 1))).map a).left =
      ((Over.pullback (thick R I e)).map a).left ≫ thickMap R I e G' := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, map_fst, trans_fst, map_fst, ← Category.assoc, trans_fst]
  · have k : ∀ B : Over (Spec (CommRingCat.of R)), thickMap R I e B ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ thickTrans R I e := fun B => pullback.lift_snd _ _ _
    have l : ∀ n, ((Over.pullback (thick R I n)).map a).left ≫ pullback.snd _ _ = pullback.snd _ _ :=
      fun n => pullback.lift_snd _ _ _
    rw [Category.assoc, Category.assoc, l, k, k, ← Category.assoc, l]

variable {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem exists_abelian (hL : LL) (hR : AdmBase R I) (U : UnifPre I D A G) (aG : G ⟶ G) [IsMonHom aG] :
    ∃ aB : D.toPre.P.A ⟶ D.toPre.P.A, IsMonHom aB ∧ ∀ e,
      (Over.pullback (thick R I e)).map aG ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R I e)).map aB := by
  have hN := hR.1
  have hC := hR.2.2.2
  choose b hb hq using fun e => (gtCoord_end_torus_abelian hL R I hR D.toPre e G (U.gt e)
    ((Over.pullback (thick R I e)).map aG) inferInstance).2.exists
  have hql : ∀ e, (U.gt e).q.left ≫ (b e).left = ((Over.pullback (thick R I e)).map aG).left ≫ (U.gt e).q.left :=
    fun e => (congrArg (·.left) (hq e)).symm
  obtain ⟨aB, haB⟩ := T.exists_endomorphism_algebraising_thickenings R I hC D.toPre.P.A D.toPre.P.isAb.smooth
    (AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _))
    (fun e => (b e).left ≫ pullback.fst D.toPre.P.A.hom (thick R I e))
    (fun e => by
      have w : (b e).left ≫ pullback.snd D.toPre.P.A.hom (thick R I e) = pullback.snd _ _ := Over.w (b e)
      rw [Category.assoc, pullback.condition, ← Category.assoc, w])
    (fun e => by
      have := (U.gt e).q_flat
      have := (U.gt e).q_surj
      have : Epi (U.gt e).q.left := Flat.epi_of_flat_of_surjective _
      rw [← cancel_epi (U.gt e).q.left, ← Category.assoc, ← UnifCompare.trans_comp_q, Category.assoc,
        ← Category.assoc (U.gt (e + 1)).q.left, hql, ← Category.assoc (U.gt e).q.left, hql, ← Category.assoc,
        ← Category.assoc, trans_map, Category.assoc _ (thickMap R I e G), UnifCompare.trans_comp_q,
        Category.assoc, Category.assoc, trans_fst, Category.assoc])
  have hm : ∀ e, (Over.pullback (thick R I e)).map aB = b e := fun e =>
    Over.OverMorphism.ext (pullback.hom_ext ((map_fst e aB).trans (haB e)) ((Over.w _).trans (Over.w (b e)).symm))
  refine ⟨aB, AbelianPartIso.isMonHom_of_thickenings (IsAdicComplete.le_jacobson_bot I) D.toPre.P.isAb
    D.toPre.P.isAb aB fun e => ?_, fun e => ?_⟩
  · rw [hm]; exact hb e
  · rw [hm]; exact hq e

theorem exists_endU : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (aG : G ⟶ G) (aA : A.A ⟶ A.A), IsMonHom aG → IsMonHom aA → (Over.pullback (jK R)).map aG ≫ U.gen.hom = U.gen.hom ≫ aA → ∃ E : EndU U.toUnifPre, E.aG = aG ∧ E.aA = aA := by
  intro hL R _ _ _ I hR D A G _ _ _ U aG aA hG hA hext
  have hC := hR.2.2.2
  have hB := D.toPre.P.isLB
  obtain ⟨aB, haB, hq⟩ := exists_abelian hL hR U.toUnifPre aG
  obtain ⟨h, hh⟩ := T.uniformisation_endomorphism_character_map_constant hL R I hR D A G U.toUnifPre aG hG
  choose t ht hi using hh
  choose v hv vv using fun χ e => T.exists_gen_of_torusEnd_compat R I D.toPre e G (U.gt e) ((Over.pullback (thick R I e)).map aG) aB h (t e)
    inferInstance (ht e) (hi e) (hq e) χ
  have down : ∀ χ e (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.toPre.P.L z J →
      val ((U.gt (e + 1)).t χ) (r ≫ thickMap R I e G) z J = val ((U.gt e).t χ) r z J :=
    fun χ e Z r z J hJ => (val_pull hJ _ _ _).symm.trans (val_corr hJ (U.gt_t e χ) r)
  choose u hu uv using fun χ => T.exists_generator_of_compatible_thickening_generators R I hC D.toPre.P.A D.toPre.P.isAb.smooth
    (AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)) _ D.toPre.P.L _ _ _ _ hB (fun _ _ => rfl)
    (v χ) (hv χ) (fun e z J hJ => by
      have := (U.gt e).q_flat
      have := (U.gt e).q_surj
      refine val_eq_of_flat hB _ _ _ _ (fun k => ?_) (U.gt e).q.left (fun x J hJ => ?_) z J hJ
      · rw [← Category.assoc, trans_fst, Category.id_comp]
      · have k₁ := vv χ (e + 1) _ (𝟙 _ ≫ thickMap R I e G) x J hJ
        have k₀ := vv χ e _ (𝟙 _) x J hJ
        rw [down _ _ _ _ _ _ hJ, Category.assoc, trans_map, ← Category.assoc, down _ _ _ _ _ _ hJ, k₀,
          Category.id_comp, Category.id_comp, UnifCompare.trans_comp_q] at k₁
        rw [Category.comp_id]
        exact (mul_left_cancel k₁).symm)
  refine ⟨⟨aG, aA, aB, hG, hA, haB, h, hext, hq, fun e => ⟨t e, ht e, hi e⟩, u, fun χ => ⟨hu χ, ?_⟩,
    fun e χ Z x z J hJ => ?_⟩, rfl, rfl⟩
  · refine corr_of_val hB fun y J hJ => Eq.trans ?_ (val_one _).symm
    refine val_eq_one I hB (fun V _ k => ?_) _ (pullGen_isGen _ _ _ _ (hu χ) _) (fun e z J hJ => ?_) y J hJ
    · refine (Fintype.prod_sum_type _).trans ((congrArg₂ (· * ·) (prod_unit D.toPre (𝟙 _) (h χ) k).1
        (prod_unit D.toPre aB χ k).2).trans ((_root_.mul_one _).trans (Fintype.prod_empty _).symm))
    · have := (U.gt e).q_hom
      have k := vv χ e _ (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left z J hJ
      rw [← Over.comp_left, ← Over.comp_left, MonObj.one_comp, MonObj.one_comp, TorusCoord.val_unit _ _ hJ,
        TorusCoord.val_unit _ _ hJ, _root_.one_mul, ← uv χ e _ _ z J hJ] at k
      have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e D.toPre.P.A) =
        η[thickObj R I e D.toPre.P.A] := by simp [Hom.one_def]
      rw [o] at k
      exact (val_pull hJ _ _ _).trans ((congrArg (fun p => val (u χ) p z J)
        (UnitValue.eSec_pullback_fst (thick R I e) D.toPre.P.A).symm).trans k.symm)
  · refine (vv χ e Z x z J hJ).trans (congrArg (_ * ·) ((uv χ e Z _ z J hJ).symm.trans ?_))
    exact congrArg (fun p => val (u χ) p z J) (Category.assoc _ _ _)

end GlobalTheory.EndData
