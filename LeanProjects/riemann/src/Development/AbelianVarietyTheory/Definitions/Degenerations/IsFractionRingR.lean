import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoreOfIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH.PreModel
open ReciprocityTheory.ChartRestriction.G.Out Classical GlobalTheory.Points GlobalTheory.TuplePoint
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem isFractionRing_R (S : ThetaSys o Ω) : IsFractionRing S.R Ω :=
  IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, ha, b, hb, h⟩ := S.frac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, h⟩

def affModel (S : ThetaSys o Ω) : RatModel o Ω :=
  haveI := isFractionRing_R S
  haveI : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType _).1 S.fg
  RatModel.ofAffine o Ω S.R

def idIso {X : Scheme.{0}} (L : LB X) : LB.Iso L L := ⟨fun p => L.g p.1 p.2⟩

theorem idIso_isGen {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : (idIso L).IsGen := by
  refine fun p q => unit_ext fun y hy => ?_
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem valR_gen {X Y : Scheme.{0}} (L : LB X) (e : Y ⟶ X) (t : LB.Gen (L.pull e)) (ht : t.IsGen)
    {K : Type} [Field K] (y : Sp K ⟶ Y) (i j : L.ι) (hi : Set.range (y ≫ e) ⊆ L.U i) (hj : Set.range (y ≫ e) ⊆ L.U j) :
    valR y _ (t.s fun _ => i).val = valR (y ≫ e) _ (L.g i j).val * valR y _ (t.s fun _ => j).val := by
  have h : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L (K := PUnit) (fun _ => e) (fun _ => i) ⊓ LB.wchart L (K := PUnit) (fun _ => e) (fun _ => j)) :=
    fun z _ => ⟨Set.mem_iInter.2 fun _ => hi ⟨z, rfl⟩, Set.mem_iInter.2 fun _ => hj ⟨z, rfl⟩⟩
  have e1 := congrArg (fun u => valR y _ u.val) (ht (fun _ => i) (fun _ => j))
  refine (valR_res_unit y inf_le_left h _).symm.trans (e1.trans ((valR_mul_unit y h _ _).trans ?_))
  exact congrArg₂ (· * ·) ((valR_linComb_g y L e 1 _ _ h).trans (zpow_one _)) (valR_res_unit y inf_le_right h _)

def pre {S : ThetaSys o Ω} (ρ : S.Real) (c : CubicalStr ρ.P.A ⟨ρ.P.L, ρ.rig, ρ.P.isLB, ρ.rig_gen⟩) :
    ZHPre ρ (affModel S) ⊤ where
  u₀ := (⊤ : (Sp S.R).Opens).ι
  u₀_gen := fun _ h => h
  G := ρ.P.A
  grp := ρ.P.grp
  comm := ρ.P.isAb.comm
  semi := GlobalTheory.isSemiAbelian_of_isAbelianScheme (S := Sp S.R) _ ρ.P.isAb
  dim := ρ.g_eq ▸ ρ.P.smoothDim
  qproj := by
    have := ρ.P.isAb.proper
    have h : LocallyOfFiniteType (spMap (algebraMap o S.R)) := (affModel S).lft
    show IsQProjOver (ρ.P.A.hom ≫ spMap (algebraMap o S.R))
    exact (isAmpleLB_of_relAmple_of_isAffine ρ.P.A ρ.P.isLB ρ.P.ample).isQProjOver _
  φ := pullback.fst _ _
  cart := isGrpPullback_pullback (S := Sp S.R) ρ.P.A _
  L := (⟨ρ.P.L, ρ.rig, ρ.P.isLB, ρ.rig_gen⟩ : RigLB ρ.P.A)
  cub := c
  sym := by
    have := ρ.P.isAb.comm
    exact GlobalTheory.PrimNorm.isSymmetric_of_hasGen (B := ρ.P.A) _ (exists_gen_neg_of_sym globalFns_holds ρ.P.isAb ρ.P.isLB ρ.P.sym)
  w := idIso _
  w_gen := idIso_isGen (LB.isLB_pull ρ.P.isLB _)
  w_rig := by
    intro K _ g x y jP jL hx hy hP hL
    have hs : eSec ρ.P.A ≫ ρ.P.A.hom = 𝟙 _ := Over.w η[ρ.P.A]
    have hxy : x = y := by
      have h : (x ≫ eSec ρ.P.A) ≫ ρ.P.A.hom = (y ≫ eSec ρ.P.A) ≫ ρ.P.A.hom :=
        congrArg (· ≫ ρ.P.A.hom) (hx.symm.trans hy)
      have k : ∀ v : Sp K ⟶ Sp S.R, (v ≫ eSec ρ.P.A) ≫ ρ.P.A.hom = v := fun v =>
        (Category.assoc _ _ _).trans ((congrArg (v ≫ ·) hs).trans (Category.comp_id _))
      exact (k x).symm.trans (h.trans (k y))
    subst hxy
    have h : ⊤ ≤ g ⁻¹ᵁ (LB.wchart ρ.P.L (K := PUnit) (fun _ => pullback.fst ρ.P.A.hom (⊤ : (Sp S.R).Opens).ι) (fun _ => jP) ⊓
        LB.wchart ρ.P.L (K := PUnit) (fun _ => pullback.fst ρ.P.A.hom (⊤ : (Sp S.R).Opens).ι) (fun _ => jL)) :=
      fun z _ => ⟨Set.mem_iInter.2 fun _ => hP ⟨z, rfl⟩, Set.mem_iInter.2 fun _ => hL ⟨z, rfl⟩⟩
    refine (valR_gen ρ.P.L (eSec ρ.P.A) ρ.rig ρ.rig_gen x jP jL (hy ▸ hP) (hy ▸ hL)).trans (congrArg₂ (· * ·) ?_ rfl)
    refine Eq.trans ?_ ((valR_linComb_g g ρ.P.L _ 1 _ _ h).trans (zpow_one _)).symm
    exact congrArg (fun v => valR v (ρ.P.L.U jP ⊓ ρ.P.L.U jL) (ρ.P.L.g jP jL).val) hy.symm
  split := fun z => ⟨_, GlobalTheory.ZJ.isGt_splitExtOfAbelian _ (isAbelianScheme_pullback_obj (S := Sp S.R) _ _ ρ.P.isAb)⟩

theorem pre_sec {S : ThetaSys o Ω} (ρ : S.Real) (c : CubicalStr ρ.P.A ⟨ρ.P.L, ρ.rig, ρ.P.isLB, ρ.rig_gen⟩) :
    (pre ρ c).Sec ∧ abLocus (pre ρ c).G = Set.univ ∧
      ∀ W : (affModel S).Z.Opens, IsProper (pullback.snd (pre ρ c).G.hom W.ι) := by
  have hp : IsProper (pre ρ c).G.hom := ρ.P.isAb.proper
  refine ⟨fun z a _ => ⟨⊤, (⊤ : (Sp S.R).Opens).ι ≫ (ρ.pt a).left, trivial, ?_, fun x x' hx _ h => ?_⟩,
    Set.eq_univ_of_forall fun z K _ _ t _ => inferInstance, fun W => inferInstance⟩
  · have h : (ρ.pt a).left ≫ ρ.P.A.hom = 𝟙 _ := Over.w (ρ.pt a)
    show ((⊤ : (Sp S.R).Opens).ι ≫ (ρ.pt a).left) ≫ ρ.P.A.hom = _
    exact (Category.assoc _ _ _).trans ((congrArg ((⊤ : (Sp S.R).Opens).ι ≫ ·) h).trans (Category.comp_id _))
  · refine Eq.trans ?_ h.symm
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (ρ.pt a).left) hx)

theorem exists_pre (hC : CubeSt) [IsNoetherianRing o] (S : ThetaSys o Ω) (ρ : S.Real) :
    ∃ (M : RatModel o Ω) (Q : ZHPre ρ M ⊤), Q.Sec ∧ abLocus Q.G = Set.univ ∧
      ∀ W : M.Z.Opens, IsProper (pullback.snd Q.G.hom W.ι) := by
  have : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType _).1 S.fg
  have : IsNoetherianRing S.R := Algebra.FiniteType.isNoetherianRing o S.R
  obtain ⟨c⟩ := (hC (Sp S.R) ρ.P ⟨ρ.P.L, ρ.rig, ρ.P.isLB, ρ.rig_gen⟩ rfl).1
  exact ⟨_, pre ρ c, pre_sec ρ c⟩

end GlobalTheory.ZH.PreModel
end
