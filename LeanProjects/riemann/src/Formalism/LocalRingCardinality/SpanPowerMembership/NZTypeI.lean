import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeH
import Formalism.LocalRingCardinality.SpanPowerMembership.TwCore

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct

theorem TwCore.charZeroK {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
    {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂} (C : TwCore R H what₂ LL0 N) (i : C.Tw) :
    CharZero (FractionRing (C.O i)) := by
  have h1 : CharZero (FractionRing (C.O0 i)) := charZero_of_injective_ringHom (C.emb0 i).injective
  exact charZero_of_injective_ringHom
    (IsFractionRing.map (A := C.O0 i) (B := C.O i) (K := FractionRing (C.O0 i))
      (L := FractionRing (C.O i)) (C.O_inj i)).injective

namespace NZ

variable {R : Ranks} (H : Host R) (Lb : Lbl H) (what₂ : Rows.Data R) (h : NHyp H what₂)
  [NumberField what₂.LL] [StarRing what₂.LL] {LL0 : IntermediateField ℚ what₂.LL}
  (C : TwCore R H what₂ LL0 (ndG H Lb what₂ h))

instance : IsEmpty (ndG H Lb what₂ h).Loc := ⟨fun i => Empty.elim i⟩

def eAlgL (i : C.Tw) : MonoidAlgebra (FractionRing (C.O i)) (G0g (ndG H Lb what₂ h)) :=
  haveI := C.charZeroK i
  e0L H Lb what₂ h (FractionRing (C.O i))

theorem eAlgL_idem (i : C.Tw) : eAlgL H Lb what₂ h C i * eAlgL H Lb what₂ h C i = eAlgL H Lb what₂ h C i :=
  haveI := C.charZeroK i
  labelIdempotent_idem H Lb what₂ h _

theorem eAlgL_central (i : C.Tw) (x) : eAlgL H Lb what₂ h C i * x = x * eAlgL H Lb what₂ h C i :=
  haveI := C.charZeroK i
  labelIdempotent_central H Lb what₂ h _ x

theorem eAlgL_def (i : C.Tw) (b : Bool) (g) : (eAlgL H Lb what₂ h C i).coeff g =
    IsFractionRing.map (A := C.O0 i) (B := C.O i) (K := FractionRing (C.O0 i))
      (L := FractionRing (C.O i)) (C.O_inj i)
      ((if b then C.emb0 i else C.emb0b i) ((qcL H Lb what₂ h g : ℚ) : ↥LL0)) := by
  haveI := C.charZeroK i
  unfold eAlgL
  rw [labelIdempotent_coeff]
  cases b <;> simp only [Bool.false_eq_true, if_false, if_true, map_ratCast]

set_option synthInstance.maxHeartbeats 400000 in

def toExpL : NExp R H what₂ LL0 (ndG H Lb what₂ h) C.toTw where
  Fm _ _ _ := PUnit
  actG _ _ _ := 1
  U := ⊥
  psiU _ _ := 1
  eAlg i _ := eAlgL H Lb what₂ h C i
  eLL0 g := ((qcL H Lb what₂ h g : ℚ) : ↥LL0)
  eAlg_def i b g := eAlgL_def H Lb what₂ h C i b g
  eAlg_idem i _ := eAlgL_idem H Lb what₂ h C i
  eAlg_central i _ x := eAlgL_central H Lb what₂ h C i x
  Bsup _ _ _ := ⊥
  Dat _ _ _ := Empty
  th _ _ _ d := d.elim
  lev _ _ _ d := d.elim
  thPsi _ _ _ _ _ _ d := d.elim
  thPsi_one _ _ _ _ d := d.elim
  thU _ _ _ _ _ d := d.elim
  twPsi _ _ _ _ _ := 0
  twPsi_one _ _ _ _ _ := Subsingleton.elim _ _
  twDel _ _ _ _ _ := 0
  delU _ _ _ := 1
  delU_unr := by intros; rfl
  delU_l := by intros; rfl
  delU_anti _ _ _ _ _ _ := by simp
  delU_open _ _ _ := by simp [MonoidHom.ker_one]
  delU_res := by intros; rfl
  delU_conj _ _ _ _ _ _ _ _ := ⟨1, fun _ => by simp⟩
  MtV _ _ _ _ _ _ := PUnit
  MtLat _ _ _ _ _ _ := ⊥
  MtLat_fg _ _ _ _ _ _ := Submodule.fg_bot
  MtLat_span _ _ _ _ _ _ := Subsingleton.elim _ _
  thP _ _ _ _ _ _ := 0
  hkF _ _ _ _ _ := 1
  embB _ _ _ := 0
  embB_inj _ _ _ _ _ _ := rfl
  eH _ _ _ := 1
  eH_idem _ _ _ := mul_one _

open Classical in
set_option synthInstance.maxHeartbeats 400000 in

def toThL : NTh R H what₂ LL0 (ndG H Lb what₂ h) C.toTw (toExpL H Lb what₂ h C) where
  iC := C.iC
  iC_int := C.iC_int
  aL i := if ∃ k, C.l i = H.g k then 1 else 0
  aL_g i k h := if_pos ⟨k, h⟩
  aL_off i h := if_neg fun ⟨k, hk⟩ => h k hk
  Pt _ _ := Empty
  ev _ _ _ := 0
  ev_smul _ _ _ _ _ y := y.elim
  ev_inj _ _ _ _ _ _ := rfl
  Lt _ _ := PUnit
  Let _ _ := Empty
  Harm _ _ := Set.univ
  Ctr _ _ := Empty
  ctrC _ _ κ := κ.elim
  Harm_def _ _ _ := ⟨fun _ κ => κ.elim, fun _ => trivial⟩
  thV _ _ _ _ y := y.elim
  thV_add _ _ _ _ _ y := y.elim
  thV_smul _ _ _ _ _ y := y.elim
  thV_addP _ _ _ _ _ y := y.elim
  thV_smulP _ _ _ _ _ y := y.elim
  datPhi _ _ _ d := d.elim
  datP _ _ _ d := d.elim
  recDet _ _ y := y.elim
  Kq _ _ _ := PUnit
  actK _ _ _ _ y := y
  actK_one _ _ _ _ := rfl
  actK_mul _ _ _ _ _ _ := rfl
  recDetq _ _ _ y := y.elim
  recDetq_mem _ _ _ y := y.elim
  recDet_act _ _ _ _ y := y.elim
  recDetq_act _ _ _ _ _ y := y.elim
  hkIdx _ _ _ _ := Empty
  hkMove _ _ _ _ c := c.elim
  hkU _ _ _ _ _ c := c.elim
  hk_ev _ _ _ _ _ _ _ _ _ _ y := y.elim
  MaximalUnramifiedExtension _ := ⊤
  FmUr _ _ _ := ⊤
  FmUr_smul := by intros; trivial
  FmUr_span _ _ _ := eq_top_iff.mpr fun x _ => (show x = 0 from rfl) ▸ Submodule.zero_mem _
  Bsup_def _ _ _ := le_antisymm bot_le fun x _ => (show x = 0 from rfl) ▸ Submodule.zero_mem _

end NZ

end Formalism.BasicNotions.Examples₂
