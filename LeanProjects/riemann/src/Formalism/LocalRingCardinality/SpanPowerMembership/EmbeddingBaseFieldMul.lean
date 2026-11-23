import Formalism.LocalRingCardinality.SpanPowerMembership.TrivialSubgroupEigenspaceTop
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeI
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeL

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.Inhab
open scoped TensorProduct

section Emb

variable (D : D7) [hL : IsEmpty D.nd.Loc] (C : TwCore D.R D.host D.what₂ D.LL0 D.nd) (I : NzIn C)
  (he : ∀ g : G0g D.nd, D.what₂.embLL ((I.eL g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)
  (hLL0 : ∀ x : D.what₂.LL, x ∈ D.LL0)

set_option synthInstance.maxHeartbeats 400000 in
theorem embedding_baseField_mul (R : D7) (hR : ∀ x : R.what₂.LL, x ∈ R.LL0) (i : R.ntw.Tw) (x : R.LL0) (y z : R.ntw.O0 i)
    (h : R.ntw.emb0 i x * algebraMap (R.ntw.O0 i) (FractionRing (R.ntw.O0 i)) z =
      algebraMap (R.ntw.O0 i) (FractionRing (R.ntw.O0 i)) y) :
    embAt R hR i (x : R.what₂.LL) * algebraMap (R.ntw.Ok i 1) (FractionRing (R.ntw.Ok i 1))
        (algebraMap (R.ntw.O i) (R.ntw.Ok i 1) (algebraMap (R.ntw.O0 i) (R.ntw.O i) z)) =
      algebraMap (R.ntw.Ok i 1) (FractionRing (R.ntw.Ok i 1))
        (algebraMap (R.ntw.O i) (R.ntw.Ok i 1) (algebraMap (R.ntw.O0 i) (R.ntw.O i) y)) := by
  have h1 := congrArg (iotaOk R i 1) h
  rw [map_mul, iotaOk_alg, iotaOk_alg] at h1
  have h2 : toLL0 R hR (x : R.what₂.LL) = x := Subtype.ext rfl
  show iotaOk R i 1 (R.ntw.emb0 i (toLL0 R hR (x : R.what₂.LL))) * _ = _
  rw [h2]
  exact h1

set_option synthInstance.maxHeartbeats 400000 in

def embCOf : EmbC D C where
  twI := fun w => (cover_at (recN D C I he) hLL0 C.cover w).choose
  twI_l := fun w => (cover_at (recN D C I he) hLL0 C.cover w).choose_spec.1
  embW := fun w => embAt (recN D C I he) hLL0 (cover_at (recN D C I he) hLL0 C.cover w).choose
  embW_w := fun w x => embAt_w (recN D C I he) hLL0 w _ (cover_at (recN D C I he) hLL0 C.cover w).choose_spec.2 x
  embedding_baseField_condition := fun w x y z _ h => embedding_baseField_mul (recN D C I he) hLL0 _ x y z h

end Emb

section Good

variable {R : Ranks} (H : Host R) (Lb : Lbl H) (what₂ : Rows.Data R) (h : NHyp H what₂)
  [NumberField what₂.LL] [StarRing what₂.LL] {LL0 : IntermediateField ℚ what₂.LL}
  (C : TwCore R H what₂ LL0 (ndG H Lb what₂ h)) (ht : THyp H) (n : ℕ)

set_option synthInstance.maxHeartbeats 400000 in

def nzInL : NzIn C where
  eA i _ := eAlgL H Lb what₂ h C i
  eL g := ((qcL H Lb what₂ h g : ℚ) : ↥LL0)
  eA_def i b g := eAlgL_def H Lb what₂ h C i b g
  eA_idem i _ := eAlgL_idem H Lb what₂ h C i
  eA_central i _ x := eAlgL_central H Lb what₂ h C i x
  Psi i := haveI := C.charZeroK i; PsiU H (FractionRing (C.O i)) Lb what₂ h
  hPsi i _ V _ _ := by
    have := C.charZeroK i
    have e : scalAct (FractionRing (C.O i)) V (PsiU H (FractionRing (C.O i)) Lb what₂ h) =
        actGL H (FractionRing (C.O i)) Lb what₂ h V := by
      ext g x; rfl
    unfold eAlgL
    rw [e]
    exact lift_actGL H (FractionRing (C.O i)) Lb what₂ h V ht
  ix j := {_a : Fin n // 1 ≤ j ∧ j ≤ R.m}
  ix_out _ := fun ⟨a⟩ => a.2
  ixM _ := Fin n
  rM _ := Subtype.val

end Good

end Formalism.BasicNotions.Examples₂.NZ
