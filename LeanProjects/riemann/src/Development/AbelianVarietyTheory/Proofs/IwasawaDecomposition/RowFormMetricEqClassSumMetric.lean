import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerEqOfNormSq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IpMtTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Formalism.LocalToGlobal.Columns.CoefModAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PairingComplexFormsConstOnRowClassesStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section

namespace GlobalTheory.Mem.Df

set_option maxHeartbeats 1000000

theorem card_stabilizer_eq_of_smul {G α : Type*} [Group G] [MulAction G α] (g : G) (x : α) :
    Nat.card (MulAction.stabilizer G (g • x)) = Nat.card (MulAction.stabilizer G x) :=
  (Nat.card_congr (MulAction.stabilizerEquivStabilizer (rfl : g • x = g • x)).toEquiv).symm

private theorem finset_sum_univ_eq_of_equiv {α β M : Type*} [AddCommMonoid M] (i1 : Fintype α) (i2 : Fintype β) (e : α ≃ β)
    (f : α → M) (g : β → M) (h : ∀ x, f x = g (e x)) :
    @Finset.sum α M _ (@Finset.univ α i1) f = @Finset.sum β M _ (@Finset.univ β i2) g :=
  @Fintype.sum_equiv α β M i1 i2 _ e f g h

theorem ipMt_eq_cSum : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (F G : (I.per l u a).Mt) (F' G' : MtCx I a), SameForm I l u a F' F → SameForm I l u a G' G → I.ipMt l u a F G = cSum I hX a F' G' := by
  intro B X I hOk hP l hX Z u a F G F' G' hF hG
  rw [GlobalTheory.Mem.Col2.IpMt.ipMt_sum I hOk hP l Z u a F G]
  have hd : Disjoint (B.primes X).vGs (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K)) :=
    (GlobalTheory.TopStep.tilOk_of_avoid (mu := I.tup a) l.pr hOk.sel_ok u ⟨hOk.T_mem u, hOk.g_mem⟩).2.2
  have hs : (I.perIn u a).sgT = B.wts.sgTrue := by
    funext τ
    rfl
  rw [hs, GlobalTheory.Mem.Df.cSum_apply]
  refine finset_sum_univ_eq_of_equiv _ _ (GlobalTheory.PeriodOnStep.clEquiv (X := B.fields) (Pr := B.primes X) (R := B.R) B.wts I.Ch I.sel (I.tup a) I.Ps hd) _ _ (fun c => ?_)
  have hFc := hF ((stepX I.Ch I.sel (I.tup a) I.Ps).rep c)
  have hGc := hG ((stepX I.Ch I.sel (I.tup a) I.Ps).rep c)
  have hcls : (rowS I a).cls ((rowS I a).outSec.rep ((GlobalTheory.PeriodOnStep.clEquiv (X := B.fields) (Pr := B.primes X) (R := B.R) B.wts I.Ch I.sel (I.tup a) I.Ps hd) c)) =
      (rowS I a).cls (GlobalTheory.PeriodOnStep.rowPt (X := B.fields) (Pr := B.primes X) (R := B.R) I.Ch I.sel (I.tup a) I.Ps c) :=
    (rowS I a).outSec.spec _
  obtain ⟨g, hg⟩ := ((rowS I a).cls_eq_iff _ _).1 hcls
  have hcard := GlobalTheory.PeriodOnStep.card_stab (X := B.fields) (Pr := B.primes X) (R := B.R) B.wts I.Ch I.sel (I.tup a) I.Ps hd c
  have hpair := GlobalTheory.T.pairing_complexForms_const_on_row_classes I hX a F' G' _ _ hcls
  unfold cTerm
  rw [hpair, ← hg, @card_stabilizer_eq_of_smul (rowS I a).G (rowS I a).D _ (rowS I a).actD g _, ← hcard]
  exact congrArg₂ (fun x y => (((Nat.card ((stepX I.Ch I.sel (I.tup a) I.Ps).Stab c) : ℕ) : ℂ))⁻¹ *
    pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) x) y) hFc hGc

end GlobalTheory.Mem.Df

end
