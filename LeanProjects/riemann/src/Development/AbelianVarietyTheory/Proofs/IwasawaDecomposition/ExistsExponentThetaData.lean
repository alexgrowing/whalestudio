import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi

noncomputable section
namespace GlobalTheory.MemN
open Formalism.BasicNotions GlobalTheory.Mem NumberField IsDedekindDomain

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {nd : NData R H what₂} (tw : NTw R H what₂ LL0 nd)

def nexpOfEmpty [IsEmpty tw.Tw] (e : G0g nd → ↥LL0) : NExp R H what₂ LL0 nd tw where
  U := ⊥
  eLL0 := e
  Fm := fun i => isEmptyElim i
  acgFm := fun i => isEmptyElim i
  modFmK := fun i => isEmptyElim i
  modFmO := fun i => isEmptyElim i
  towFm := fun i => isEmptyElim i
  fdFm := fun i => isEmptyElim i
  actG := fun i => isEmptyElim i
  psiU := fun i => isEmptyElim i
  eAlg := fun i => isEmptyElim i
  eAlg_def := fun i => isEmptyElim i
  eAlg_idem := fun i => isEmptyElim i
  eAlg_central := fun i => isEmptyElim i
  Bsup := fun i => isEmptyElim i
  Dat := fun i => isEmptyElim i
  th := fun i => isEmptyElim i
  lev := fun i => isEmptyElim i
  thPsi := fun i => isEmptyElim i
  thPsi_one := fun i => isEmptyElim i
  thU := fun i => isEmptyElim i
  twPsi := fun i => isEmptyElim i
  twPsi_one := fun i => isEmptyElim i
  twDel := fun i => isEmptyElim i
  delU := fun i => isEmptyElim i
  delU_unr := fun i => isEmptyElim i
  delU_l := fun i => isEmptyElim i
  delU_anti := fun i => isEmptyElim i
  delU_open := fun i => isEmptyElim i
  delU_res := fun i => isEmptyElim i
  delU_conj := fun i => isEmptyElim i
  MtV := fun i => isEmptyElim i
  acgMt := fun i => isEmptyElim i
  modMtK := fun i => isEmptyElim i
  modMtO := fun i => isEmptyElim i
  towMt := fun i => isEmptyElim i
  fdMt := fun i => isEmptyElim i
  MtLat := fun i => isEmptyElim i
  MtLat_fg := fun i => isEmptyElim i
  MtLat_span := fun i => isEmptyElim i
  thP := fun i => isEmptyElim i
  hkF := fun i => isEmptyElim i
  embB := fun i => isEmptyElim i
  embB_inj := fun i => isEmptyElim i
  eH := fun i => isEmptyElim i
  eH_idem := fun i => isEmptyElim i

def nthOfEmpty [IsEmpty tw.Tw] (Y : NExp R H what₂ LL0 nd tw) : NTh R H what₂ LL0 nd tw Y where
  iC := fun i => isEmptyElim i
  iC_int := fun i => isEmptyElim i
  aL := fun i => isEmptyElim i
  aL_g := fun i => isEmptyElim i
  aL_off := fun i => isEmptyElim i
  Pt := fun i => isEmptyElim i
  ev := fun i => isEmptyElim i
  ev_smul := fun i => isEmptyElim i
  ev_inj := fun i => isEmptyElim i
  Lt := fun i => isEmptyElim i
  acgLt := fun i => isEmptyElim i
  modLt := fun i => isEmptyElim i
  freeLt := fun i => isEmptyElim i
  finLt := fun i => isEmptyElim i
  Let := fun i => isEmptyElim i
  finLet := fun i => isEmptyElim i
  Harm := fun i => isEmptyElim i
  Ctr := fun i => isEmptyElim i
  ctrC := fun i => isEmptyElim i
  Harm_def := fun i => isEmptyElim i
  thV := fun i => isEmptyElim i
  thV_add := fun i => isEmptyElim i
  thV_smul := fun i => isEmptyElim i
  thV_addP := fun i => isEmptyElim i
  thV_smulP := fun i => isEmptyElim i
  datPhi := fun i => isEmptyElim i
  datP := fun i => isEmptyElim i
  recDet := fun i => isEmptyElim i
  Kq := fun i => isEmptyElim i
  grpKq := fun i => isEmptyElim i
  actK := fun i => isEmptyElim i
  actK_one := fun i => isEmptyElim i
  actK_mul := fun i => isEmptyElim i
  recDetq := fun i => isEmptyElim i
  recDetq_mem := fun i => isEmptyElim i
  recDet_act := fun i => isEmptyElim i
  recDetq_act := fun i => isEmptyElim i
  hkIdx := fun i => isEmptyElim i
  finHk := fun i => isEmptyElim i
  hkMove := fun i => isEmptyElim i
  hkU := fun i => isEmptyElim i
  hk_ev := fun i => isEmptyElim i
  MaximalUnramifiedExtension := fun i => isEmptyElim i
  FmUr := fun i => isEmptyElim i
  FmUr_smul := fun i => isEmptyElim i
  FmUr_span := fun i => isEmptyElim i
  Bsup_def := fun i => isEmptyElim i

end

theorem exists_nexp_nth_of_isEmpty (B : Base) (C : Cols B) (W : RowsRest B C) (nd : NData B.R B.host W.what₂)
    (tw : NTw B.R B.host W.what₂ B.LL0 nd) (h : IsEmpty tw.Tw) (e : G0g nd → ↥B.LL0) :
    ∃ Y : NExp B.R B.host W.what₂ B.LL0 nd tw, Y.eLL0 = e ∧ Nonempty (NTh B.R B.host W.what₂ B.LL0 nd tw Y) :=
  ⟨nexpOfEmpty tw e, rfl, ⟨nthOfEmpty tw _⟩⟩

end GlobalTheory.MemN
