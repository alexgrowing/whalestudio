import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.PullCochMemCoboundaries
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Cech

open GroundTheory.Arith.SchemeCoh

variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type} (U : ι → X.Opens) (a : ℕ)

def toOm (W : X.Opens) : GlobalTheory.CechDR.OmU q W a →+ (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj.obj (op W) where
  toFun x := (GlobalTheory.HodgeCoh.toOmega q a).app (op W) x
  map_zero' := map_zero _
  map_add' x y := map_add _ x y

theorem toOm_formRes {W W' : X.Opens} (h : W' ≤ W) (x : GlobalTheory.CechDR.OmU q W a) :
    toOm q a W' (GlobalTheory.HodgeCoh.formRes q h a x) = res (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj h (toOm q a W x) :=
  PresheafOfModules.naturality_apply (GlobalTheory.HodgeCoh.toOmega q a) (homOfLE h).op x

theorem inter_le_capO {n : ℕ} (i : Fin n → ι) : inter U i ≤ Pb.capO U i := by
  intro x hx
  rw [mem_inter_iff] at hx
  unfold Pb.capO
  rw [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  exact hx

def formCoch (n : ℕ) : (Glob.formCos q U a).X n →+ Cochain (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj U n where
  toFun c i := res _ (inter_le_capO U i) (toOm q a (Pb.capO U i) (c i))
  map_zero' := by
    funext i
    rw [show (0 : (Glob.formCos q U a).X n) i = 0 from rfl, map_zero, map_zero]
    rfl
  map_add' c c' := by
    funext i
    rw [show (c + c') i = c i + c' i from rfl, map_add, map_add]
    rfl

theorem formCoch_d (n : ℕ) (c : (Glob.formCos q U a).X n) :
    formCoch q U a (n + 1) (CrystallineSemistableComparison.Cos.d (Glob.formCos q U a) n c) =
      d (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj U n (formCoch q U a n c) := by
  rw [CrystallineSemistableComparison.Cos.d_apply, map_sum]
  funext i
  rw [GroundTheory.Arith.SchemeCoh.d_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, Pi.smul_apply]
  congr 1
  change res _ (inter_le_capO U i) (toOm q a (Pb.capO U i)
      (GlobalTheory.HodgeCoh.formRes q (Pb.capO_comp U i k.succAbove) a (c (i ∘ k.succAbove)))) =
    res _ (inter_le_comp U i k.succAbove) (res _ (inter_le_capO U (i ∘ k.succAbove))
      (toOm q a (Pb.capO U (i ∘ k.succAbove)) (c (i ∘ k.succAbove))))
  rw [toOm_formRes, res_res, res_res]

def formZ (n : ℕ) : (Glob.formCos q U a).cx.Z n →+ cocycles (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj U n :=
  AddMonoidHom.codRestrict ((formCoch q U a n).comp ((Glob.formCos q U a).cx.Z n).subtype.toAddMonoidHom) _
    fun z => by
      rw [mem_cocycles]
      change d (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj U n (formCoch q U a n z.1) = 0
      rw [← formCoch_d]
      change formCoch q U a (n + 1) ((Glob.formCos q U a).cx.d n z.1) = 0
      rw [z.2, map_zero]

def formToCO (n : ℕ) : (Glob.formCos q U a).cx.H n →+ CO q U a n :=
  QuotientAddGroup.lift (((Glob.formCos q U a).cx.B n).submoduleOf ((Glob.formCos q U a).cx.Z n)).toAddSubgroup
    ((QuotientAddGroup.mk' _).comp (formZ q U a n)) fun z hz => by
      change (QuotientAddGroup.mk' ((coboundaries (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj U n).addSubgroupOf
        (cocycles (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj U n)) (formZ q U a n z) : cechH _ U n) = 0
      rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      have hz' : z.1 ∈ (Glob.formCos q U a).cx.B n := hz
      change formCoch q U a n z.1 ∈ coboundaries (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj U n
      cases n with
      | zero =>
        have h0 : z.1 = 0 := hz'
        rw [h0, map_zero]
        exact zero_mem _
      | succ n =>
        obtain ⟨c, hc⟩ := hz'
        rw [coboundaries_succ, ← hc]
        exact ⟨formCoch q U a n c, (formCoch_d q U a n c).symm⟩

theorem formToCO_cls {n : ℕ} (c : (Glob.formCos q U a).X n) (hc : (Glob.formCos q U a).cx.d n c = 0) :
    formToCO q U a n ((Glob.formCos q U a).cx.cls c hc) =
      cls (formCoch q U a n c) (by rw [← formCoch_d]; exact (congrArg _ hc).trans (map_zero _)) := rfl

end CrystallineSemistableComparison.Om.Cech
