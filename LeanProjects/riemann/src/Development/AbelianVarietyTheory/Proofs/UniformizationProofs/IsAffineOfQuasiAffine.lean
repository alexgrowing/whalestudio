import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.AmpleStabFinite
open GlobalTheory.CechPic

theorem eq_pull_of_local {Y S : Scheme.{0}} (p : Y ⟶ S) (e : S ⟶ Y) (he : e ≫ p = 𝟙 S)
    (hp : ∀ V : S.Opens, Function.Surjective (pullback.snd p V.ι).appTop.hom) (c : CechPic.Pic Y)
    (h : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ CechPic.pull (p ⁻¹ᵁ U).ι c = 0) : c = CechPic.pull (p ≫ e) c := by
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  have key := exists_gen_of_local_on_base hM (K := Fin 2) ![𝟙 Y, p ≫ e] ![1, -1] p e he hp
    (fun U _ k => by
      rw [Fin.prod_univ_two]
      show k (e ≫ 𝟙 Y) ^ (1 : ℤ) * k (e ≫ p ≫ e) ^ (-1 : ℤ) = 1
      rw [← Category.assoc e, he, Category.comp_id, Category.id_comp]; simp)
    (fun s => by
      obtain ⟨U, hs, hU⟩ := h s
      refine ⟨U, hs, (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).1 ?_⟩
      obtain ⟨n, n₁⟩ : ∃ n : (p ⁻¹ᵁ U).toScheme ⟶ (p ⁻¹ᵁ U).toScheme,
          n ≫ (p ⁻¹ᵁ U).ι = (p ⁻¹ᵁ U).ι ≫ p ≫ e :=
        ⟨IsOpenImmersion.lift (p ⁻¹ᵁ U).ι ((p ⁻¹ᵁ U).ι ≫ p ≫ e) (by
          rintro _ ⟨y, rfl⟩
          rw [Scheme.Opens.range_ι]
          have e' := congrArg (fun q => q (p y.1)) he
          exact (congrArg (· ∈ U) e').mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
      rw [cls_linComb hM, Fin.sum_univ_two]
      show (1 : ℤ) • CechPic.pull ((p ⁻¹ᵁ U).ι ≫ 𝟙 Y) (cls M hM) +
        (-1 : ℤ) • CechPic.pull ((p ⁻¹ᵁ U).ι ≫ p ≫ e) (cls M hM) = 0
      rw [← n₁, Category.comp_id, pull_comp, hU, map_zero]; simp)
  have k2 := (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).2 key
  rw [cls_linComb hM, Fin.sum_univ_two] at k2
  have k3 : (1 : ℤ) • CechPic.pull (𝟙 Y) (cls M hM) + (-1 : ℤ) • CechPic.pull (p ≫ e) (cls M hM) = 0 := k2
  rw [pull_id, one_zsmul, neg_one_zsmul, ← sub_eq_add_neg, sub_eq_zero] at k3
  exact k3

theorem surj_of_isPullback (hG : GlobalFnsSt) {S : Scheme.{0}} {B : Over S} [GrpObj B] (hB : IsAbelianScheme B)
    {Y T : Scheme.{0}} {a : Y ⟶ B.left} {q : Y ⟶ T} {b : T ⟶ S} (h : IsPullback a q B.hom b) :
    Function.Surjective q.appTop.hom := by
  rw [← h.isoPullback_hom_snd]
  exact surj_comp (ConcreteCategory.bijective_of_isIso (h.isoPullback.hom.app ⊤)).2 (surj_snd hG hB (Over.mk b))

theorem cls_pw {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (d : ℤ) : cls (pw L d) (isLB_pw hL d) = d • cls L hL := by
  have h := LB.isLB_linComb hL (fun _ : PUnit => 𝟙 X) (fun _ => d)
  have e := cls_linComb hL _ _ h
  rw [Fintype.sum_unique, pull_id] at e
  rw [← e]
  refine (cls_eq_iff _ h).2 (iso_of_chart h ⟨fun i _ => i, fun _ _ hy => Set.mem_iInter.2 fun _ => hy, ?_⟩)
  intro y i j hi hj
  refine Eq.trans (map_zpow _ _ _) (Eq.symm ((gm_linComb L (fun _ : PUnit => 𝟙 X) (fun _ => d) (𝟙 X) y (fun _ => i) (fun _ => j)
    (Set.mem_iInter.2 fun _ => hi) (Set.mem_iInter.2 fun _ => hj)).trans ?_))
  rw [Fintype.prod_unique, Category.id_comp]
  rfl

theorem pull_spec_local {K : Type} [CommRing K] [IsLocalRing K] {X : Scheme.{0}} (y : Spec (CommRingCat.of K) ⟶ X)
    (c : CechPic.Pic X) : CechPic.pull y c = 0 := by
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  exact (cls_eq_zero_iff (pull_isLB hM y)).2 (DVR.exists_gen_of_local M hM _ _)

theorem isAffine_of_quasiAffine {X S : Scheme.{0}} [IsAffine S] [X.IsQuasiAffine] (f : X ⟶ S) [UniversallyClosed f] :
    IsAffine X := by
  have : UniversallyClosed (X.toSpecΓ ≫ Spec.map f.appTop) := by
    rw [← Scheme.toSpecΓ_naturality]; infer_instance
  have : UniversallyClosed X.toSpecΓ := .of_comp_of_isSeparated _ (Spec.map f.appTop)
  have : Surjective X.toSpecΓ := inferInstance
  exact ⟨isIso_of_isOpenImmersion_of_opensRange_eq_top _
    (top_unique fun x _ => X.toSpecΓ.surjective x)⟩

theorem quasiAffine_of_pull_add {X Y : Scheme.{0}} [CompactSpace X] (f g : X ⟶ Y) [IsAffineHom f] {M : LB Y}
    (hM : M.IsLB) {I : Type} (s : I → M.Sec) (hc : ⨆ i, nonzeroLocus (s i) = ⊤)
    (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (h : CechPic.pull f (cls M hM) + CechPic.pull g (cls M hM) = 0) : X.IsQuasiAffine := by
  refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen X fun x => ?_
  obtain ⟨a, hxa⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge (Set.mem_univ (f x)))
  obtain ⟨b, hxb⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge (Set.mem_univ (g x)))
  have hN := LB.isLB_linComb hM (Sum.elim (fun _ : PUnit => g) (fun _ : PUnit => f))
    (Sum.elim (fun _ => 1) (fun _ => 1))
  have h0 : cls _ hN = 0 := by
    rw [cls_linComb hM, Fintype.sum_sum_type]
    simpa [add_comm] using h
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_triv X) hN
    ((cls_eq_iff _ _).1 h0.symm)
    (DVR.mulSec M _ _ _ _ (secPull (s b) g) (secPull (s a) f))
  rw [nonzeroLocus_mulSec, nonzeroLocus_secPull (s a)] at ht
  have e : nonzeroLocus t = X.basicOpen (show Γ(X, ⊤) from t.f PUnit.unit) :=
    le_antisymm (iSup_le fun _ => le_rfl) (basicOpen_le_nonzeroLocus t PUnit.unit)
  refine ⟨t.f PUnit.unit, ?_, ?_⟩
  · rw [← e, ht]
    exact isAffineOpen_nonzeroLocus_inf (pull_isLB hM g) _ ((ha a).preimage f)
  · rw [← e, ht, nonzeroLocus_secPull]
    exact ⟨hxb, hxa⟩

section Points

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {L O : LB B.left}

theorem transl_const (hG : GlobalFnsSt) (hB : IsAbelianScheme B) (hL : L.IsLB) (hO : O.IsLB) {T : Over S} (x : T ⟶ B)
    (h : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) (b : T ⟶ B) :
    CechPic.pull (x * b).left (cls L hL) - CechPic.pull b.left (cls L hL) - CechPic.pull b.left (cls O hO) =
      CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ B).left (cls L hL) -
        CechPic.pull (1 : T ⟶ B).left (cls O hO) := by
  have h₁ : (translDiff B L x).IsLB := LB.isLB_linComb hL _ _
  have h₂ := pull_isLB hO (snd T B).left
  have hM := LB.isLB_div h₁ h₂
  have val : ∀ b : T ⟶ B, CechPic.pull (lift (𝟙 T) b).left (cls _ hM) =
      CechPic.pull (x * b).left (cls L hL) - CechPic.pull b.left (cls L hL) - CechPic.pull b.left (cls O hO) := by
    intro b
    have e₁ : cls _ h₁ = CechPic.pull (lift (fst T B ≫ x) (snd T B) ≫ μ[B]).left (cls L hL) -
        CechPic.pull (snd T B).left (cls L hL) := by
      refine (cls_linComb hL _ _ h₁).trans ?_
      rw [Fin.sum_univ_two, sub_eq_add_neg]
      exact congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)
    have a₁ : lift (𝟙 T) b ≫ (lift (fst T B ≫ x) (snd T B) ≫ μ[B]) = x * b := by
      rw [comp_lift_assoc, lift_fst_assoc, lift_snd, Category.id_comp]; rfl
    rw [cls_div h₁ h₂, e₁, cls_pull hO, map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp,
      ← Over.comp_left, ← Over.comp_left, a₁, lift_snd]
  have sec : ∀ b : T ⟶ B, (lift (𝟙 T) b).left ≫ (fst T B).left = 𝟙 _ := fun b => by
    rw [← Over.comp_left, lift_fst]; rfl
  have key := eq_pull_of_local (fst T B).left (lift (𝟙 T) (1 : T ⟶ B)).left (sec 1)
    (fun V => surj_of_isPullback hG hB
      ((IsPullback.of_hasPullback (fst T B).left V.ι).paste_horiz
        (IsPullback.of_hasPullback T.hom B.hom).flip)) (cls _ hM)
    (fun p => by
      obtain ⟨U, hU, ht⟩ := h p
      exact ⟨U, hU, (cls_eq_zero_iff (pull_isLB hM _)).2 ht⟩)
  have k := congrArg (CechPic.pull (lift (𝟙 T) b).left) key
  rw [← pull_comp, ← Category.assoc, sec, Category.id_comp, val, val, _root_.mul_one] at k
  exact k

theorem add_inv_eq [IsCommMonObj B] (hG : GlobalFnsSt) (hB : IsAbelianScheme B) (hL : L.IsLB) (hO : O.IsLB)
    {T : Over S} (x y : T ⟶ B)
    (hx : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι))
    (hy : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L y) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) :
    CechPic.pull x.left (cls L hL) + CechPic.pull (x⁻¹).left (cls L hL) =
      CechPic.pull y.left (cls L hL) + CechPic.pull (y⁻¹).left (cls L hL) := by
  have a := transl_const hG hB hL hO x hx (x⁻¹ * y⁻¹)
  have b := transl_const hG hB hL hO y hy (x⁻¹ * y⁻¹)
  rw [mul_inv_cancel_left] at a
  rw [mul_comm x⁻¹ y⁻¹, mul_inv_cancel_left, mul_comm y⁻¹ x⁻¹] at b
  linear_combination (norm := abel) b - a

end Points

theorem isFinite_of_relAmple : GlobalFnsSt → ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ L O : LB B.left, L.IsLB → O.IsLB → RelAmple B L → ∀ (H : Over (Spec (CommRingCat.of R))) (j : H ⟶ B), IsClosedImmersion j.left → (∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ B), (∀ p : (T).left, ∃ U : (T).left.Opens, p ∈ U ∧ Triv ((LB.div (translDiff B L x) (O.pull (snd (T) B).left)).pull ((fst (T) B).left ⁻¹ᵁ U).ι)) ↔ ∃ y : T ⟶ H, y ≫ j = x) → IsFinite H.hom := by
  intro hG R _ B _ _ hB L O hL hO hA H j hj hH
  obtain ⟨d, -, n, s, hc, ha⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B L hL).1 hA
  have := hB.proper
  have : IsProper H.hom := by rw [← Over.w j]; infer_instance
  suffices LocallyQuasiFinite H.hom from .of_isProper_of_locallyQuasiFinite _
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun z => ?_
  rcases Set.eq_empty_or_nonempty (H.hom ⁻¹' {z}) with h0 | ⟨h, hh⟩
  · rw [h0]; exact Set.finite_empty
  let K : Type := H.left.residueField h
  let y₀ : Spec (CommRingCat.of K) ⟶ H.left := H.left.fromSpecResidueField h
  let P : Over (Spec (CommRingCat.of R)) := Over.mk (y₀ ≫ H.hom)
  let y : P ⟶ H := Over.homMk y₀ rfl
  let π : (H ⊗ P).left ⟶ H.left := (fst H P).left
  let q : (H ⊗ P).left ⟶ Spec (CommRingCat.of K) := (snd H P).left
  have hpb : IsPullback π q H.hom (y₀ ≫ H.hom) := IsPullback.of_hasPullback H.hom P.hom
  have : IsProper q := MorphismProperty.of_isPullback hpb inferInstance
  have : IsAffineHom π := MorphismProperty.of_isPullback hpb.flip inferInstance
  have key := add_inv_eq hG hB hL hO (fst H P ≫ j) (snd H P ≫ y ≫ j) ((hH _ _).2 ⟨_, rfl⟩)
    ((hH _ _).2 ⟨snd H P ≫ y, Category.assoc _ _ _⟩)
  rw [← GrpObj.comp_inv (snd H P), Over.comp_left _ _ _ (snd H P), Over.comp_left _ _ _ (snd H P), pull_comp (snd H P).left,
    pull_comp (snd H P).left, pull_spec_local (K := K) (y ≫ j).left, pull_spec_local (K := K) (y ≫ j)⁻¹.left,
    map_zero, add_zero] at key
  have : CompactSpace (H ⊗ P).left := QuasiCompact.compactSpace_of_compactSpace q
  have : IsAffineHom (fst H P ≫ j).left := inferInstanceAs (IsAffineHom (π ≫ j.left))
  have : (H ⊗ P).left.IsQuasiAffine := quasiAffine_of_pull_add (fst H P ≫ j).left ((fst H P ≫ j)⁻¹).left
    (isLB_pw hL d) s hc (fun i => (ha i).1) (by
      rw [cls_pw hL, map_zsmul, map_zsmul, ← zsmul_add, key, zsmul_zero])
  have : IsAffine (H ⊗ P).left := isAffine_of_quasiAffine q
  have : IsFinite q := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hfin : (Set.univ : Set (H ⊗ P).left).Finite := by
    have := q.finite_preimage_singleton (IsLocalRing.closedPoint K)
    refine this.subset fun t _ => Subsingleton.elim _ _
  refine (hfin.image π).subset fun w hw => ?_
  have e : H.hom w = (y₀ ≫ H.hom) (IsLocalRing.closedPoint K) := by
    have e₀ : y₀ (IsLocalRing.closedPoint K) = h := Scheme.fromSpecResidueField_apply h _
    exact (show H.hom w = z from hw).trans ((show H.hom h = z from hh).symm.trans (congrArg H.hom e₀).symm)
  obtain ⟨t, ht, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := H.hom) (g := y₀ ≫ H.hom) w _ e
  exact ⟨t, trivial, ht⟩

end GlobalTheory.AmpleStabFinite
