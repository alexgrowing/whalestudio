import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KfBijective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MemBasicOpenIffGs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

noncomputable section
namespace GlobalTheory.ZH.SecProp
open GlobalTheory.ZH.CrdCalc

section
variable {F : Type} [Field F] [IsAlgClosed F] {Y : Scheme.{0}} (p : Y ⟶ Sp F) [LocallyOfFiniteType p]

theorem exists_point {Z : Set Y} (hZ : IsLocallyClosed Z) (hn : Z.Nonempty) :
    ∃ r : Sp F ⟶ Y, r ≫ p = 𝟙 _ ∧ ∀ z, r z ∈ Z := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨c, hcW, hc⟩ := nonempty_inter_closedPoints hn hZ
  exact ⟨pointOfClosedPoint p c hc, pointOfClosedPoint_comp p c hc,
    fun z => (congrArg (· ∈ Z) (pointOfClosedPoint_apply p c hc z)).mpr hcW⟩

theorem fn_ext_valR [IsReduced Y] {U : Y.Opens} {a b : Γ(Y, U)}
    (h : ∀ r : Sp F ⟶ Y, r ≫ p = 𝟙 _ → ⊤ ≤ r ⁻¹ᵁ U → valR r U a = valR r U b) : a = b := by
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  by_contra hne
  have hn : ((Y.basicOpen (a - b) : Y.Opens) : Set Y).Nonempty :=
    Set.nonempty_iff_ne_empty.2 fun e => hne (SetLike.coe_injective e)
  obtain ⟨r, hr, hz⟩ := exists_point p (Y.basicOpen (a - b)).isOpen.isLocallyClosed hn
  have hU : ⊤ ≤ r ⁻¹ᵁ U := fun z _ => Y.basicOpen_le _ (hz z)
  have hu := (isUnit_valR_iff r U hU (a - b)).2 fun z _ => hz z
  have e := h r hr hU
  rw [valR_eq r U hU, valR_eq r U hU, ← sub_eq_zero, ← map_sub] at e
  rw [valR_eq r U hU, e] at hu
  exact not_isUnit_zero hu

variable {H : LB Y} {I : Type} {a b : I → H.Sec}

theorem exists_mem_basicOpen (h : ∀ r : Sp F ⟶ Y, r ≫ p = 𝟙 _ → ∃ w, w ≠ 0 ∧ Crd H b r w) (l : H.ι) (y : Y)
    (hy : y ∈ H.U l) : ∃ i, y ∈ Y.basicOpen ((b i).f l) := by
  by_contra hne
  let V : Y.Opens := ⨆ i, Y.basicOpen ((b i).f l)
  have hyV : y ∉ V := fun e => hne (TopologicalSpace.Opens.mem_iSup.1 e)
  obtain ⟨r, hr, hz⟩ := exists_point p
    ((H.U l).isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed) ⟨y, hy, hyV⟩
  obtain ⟨w, hw, hc⟩ := h r hr
  have hU : ⊤ ≤ r ⁻¹ᵁ H.U l := fun z _ => (hz z).1
  obtain ⟨c, hc'⟩ := crd_unique hc
    (⟨l, 1, hU, fun j => by simp⟩ : Crd H b r (fun i => valR r (H.U l) ((b i).f l)))
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
  have hu : IsUnit (valR r (H.U l) ((b i).f l)) := by
    rw [hc' i]
    exact c.isUnit.mul (Ne.isUnit hi)
  have z : Sp F := IsLocalRing.closedPoint F
  exact (hz z).2 (TopologicalSpace.Opens.mem_iSup.2 ⟨i, (isUnit_valR_iff r _ hU _).1 hu (Set.mem_univ z)⟩)

theorem cross_eq [IsReduced Y] (h : ∀ r : Sp F ⟶ Y, r ≫ p = 𝟙 _ → ∃ w, Crd H a r w ∧ Crd H b r w) (l : H.ι)
    (i i' : I) : (a i).f l * (b i').f l = (a i').f l * (b i).f l := by
  refine fn_ext_valR p fun r hr hU => ?_
  obtain ⟨w, ha, hb⟩ := h r hr
  obtain ⟨c, hc⟩ := crd_unique ha
    (⟨l, 1, hU, fun j => by simp⟩ : Crd H a r (fun i => valR r (H.U l) ((a i).f l)))
  obtain ⟨d, hd⟩ := crd_unique hb
    (⟨l, 1, hU, fun j => by simp⟩ : Crd H b r (fun i => valR r (H.U l) ((b i).f l)))
  rw [valR_mul r _ hU, valR_mul r _ hU, hc i, hc i', hd i, hd i']
  ring

end

theorem valR_const {F : Type} [Field F] {Y : Scheme.{0}} (p : Y ⟶ Sp F) (r : Sp F ⟶ Y) (hr : r ≫ p = 𝟙 _)
    (U : Y.Opens) (hU : ⊤ ≤ r ⁻¹ᵁ U) (a : F) :
    valR r U (resG Y le_top (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom a))) = a := by
  rw [valR_res r le_top hU, valR_eq r ⊤ le_rfl]
  have e : r.appLE ⊤ ⊤ le_rfl = r.appTop := (Scheme.Hom.app_eq_appLE r).symm
  have e₂ : p.appTop ≫ r.appTop = 𝟙 _ := by rw [← Scheme.Hom.comp_appTop, hr, Scheme.Hom.id_appTop]
  change (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom ((p.appTop ≫ r.appLE ⊤ ⊤ le_rfl).hom _) = a
  rw [e, e₂]
  exact (Scheme.ΓSpecIso (CommRingCat.of F)).inv_hom_id_apply a

theorem proportional_of_crd : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ) (I J : Type) [Fintype J] (t : I → SecA A F k) (s : J → SecA A F k) (b : Matrix I J F), (∀ x : TFK (R := R) F ⟶ A.A, ∃ v : J → F, b.mulVec v ≠ 0 ∧ Crd (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) s (show Sp F ⟶ _ from (ptSecT A.A x).left) v ∧ Crd (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) t (show Sp F ⟶ _ from (ptSecT A.A x).left) (b.mulVec v)) → ∃ c : F, ∀ i, ∑ j, kf R F (b i j) • SecM.ofSec A.A (s j) = kf R F c • SecM.ofSec A.A (t i) := by
  intro hG R _ _ A F _ _ _ k I J _ t s b H
  have hsm := A.isAb.smooth
  let T : Over (Spec (CommRingCat.of (FractionRing R))) := TFK (R := R) F
  let p : (T ⊗ A.A).left ⟶ Sp F := (fst T A.A).left
  have hp : Smooth p := inferInstanceAs (Smooth (pullback.fst T.hom A.A.hom))
  have : IsReduced (T ⊗ A.A).left := GlobalTheory.isReduced_of_smooth_of_isReduced p
  let m : I → SecM A.A A.L (k : ℤ) T := fun i => ∑ j, kf R F (b i j) • SecM.ofSec A.A (s j)
  let t' : I → SecA A F k := fun i => SecM.toSec A.A (m i)
  have key : ∀ r : Sp F ⟶ (T ⊗ A.A).left, r ≫ p = 𝟙 _ →
      ∃ w, w ≠ 0 ∧ Crd (LPow A.A A.L (k : ℤ) T) t' r w ∧ Crd (LPow A.A A.L (k : ℤ) T) t r w := by
    intro r hr
    let r' : T ⟶ T ⊗ A.A := Over.homMk r (by
      rw [← Over.w (fst T A.A), ← Category.assoc]
      exact (congrArg (· ≫ T.hom) hr).trans (Category.id_comp _))
    have er : ptSecT A.A (r' ≫ snd _ _) = r' := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ (lift_snd _ _)
      rw [ptSecT, lift_fst]
      exact Over.OverMorphism.ext hr.symm
    obtain ⟨v, hv, hs, ht⟩ := H (r' ≫ snd _ _)
    have er' : (ptSecT A.A (r' ≫ snd _ _)).left = r := congrArg (·.left) er
    replace hs : Crd (LPow A.A A.L (k : ℤ) T) s r v := er' ▸ hs
    replace ht : Crd (LPow A.A A.L (k : ℤ) T) t r (b.mulVec v) := er' ▸ ht
    refine ⟨_, hv, ?_, ht⟩
    obtain ⟨l, c, hl, hc⟩ := hs
    refine ⟨l, c, hl, fun i => ?_⟩
    have e : (t' i).f l = ∑ j, resG _ le_top (p.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (b i j))) * (s j).f l := by
      change (m i).1 l = _
      simp only [m, Submodule.coe_sum, Finset.sum_apply]
      rfl
    rw [e, valR_eq r _ hl, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← valR_eq r _ hl, valR_mul r _ hl, valR_const p r hr _ hl, hc j, mul_left_comm]
  obtain ⟨c₀, hc₀⟩ := SectionRatio.exists_ratio A.isLB (φ := fun _ : Fin 1 => (snd T A.A).left)
    (ε := fun _ => (k : ℤ)) t' t
    (fun y J hJ => by
      have hm := hJ.mem (fun _ : Fin 1 => (snd T A.A).left) (𝟙 _)
      obtain ⟨i, hi⟩ := exists_mem_basicOpen p (H := LPow A.A A.L (k : ℤ) T) (b := t)
        (fun r hr => (key r hr).imp fun w hw => ⟨hw.1, hw.2.2⟩) _ y hm
      exact ⟨i, (SectionRatio.mem_basicOpen_iff_gs _ y hm).1 hi⟩)
    (fun i i' y J hJ => by
      have hm := hJ.mem (fun _ : Fin 1 => (snd T A.A).left) (𝟙 _)
      have e := cross_eq p (H := LPow A.A A.L (k : ℤ) T) (a := t') (b := t)
        (fun r hr => (key r hr).imp fun w hw => hw.2) (fun _ => J (𝟙 _ ≫ (snd T A.A).left)) i i'
      exact (gs_mul _ y _ hm _ _).symm.trans ((congrArg (gs (𝟙 _) y _) e).trans (gs_mul _ y _ hm _ _)))
  obtain ⟨d, hd⟩ := CommPairing.surj_fst hG A.isAb T c₀
  obtain ⟨c, rfl⟩ := (kf_bijective R F).2 d
  refine ⟨c, fun i => ThetaAct.sv_ext A.isLB fun y J hJ => ?_⟩
  refine (hc₀ i y J hJ).trans (Eq.trans ?_ (ThetaAct.sv_smul _ _ _ _ hJ).symm)
  exact congrArg (· * _) ((congrArg (gs (𝟙 _) y ⊤) hd.symm).trans (gs_pull (𝟙 _) _ y ⊤ trivial _))

end GlobalTheory.ZH.SecProp
end
