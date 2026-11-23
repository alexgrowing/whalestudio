import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NuInRange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SCuIsom
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ResCharThetaJetPlaceDegOne

noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

def assemble (B : Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) : D7 where
  R := B.R
  host := B.host
  sp := B.sp
  vol := G.vol
  vol_pos := G.vol_pos
  what₂ := W.what₂
  eTau := Equiv.refl _
  hc := B.hc
  wordFin := B.wordFin
  u₀ := B.u₀
  hcW := B.hcW
  hcW_base := B.hcW_base
  hcW_v := B.hcW_v
  hcW_b := B.hcW_b
  hcW_e := B.hcW_e
  hcW_first := B.hcW_first
  hcW_last := B.hcW_last
  mem := C.mem
  nfLL := B.nfLL
  starLL := B.starLL
  tcLL := B.tcLL
  galLL := B.galLL
  starLL_cx := B.starLL_cx
  div := V.div
  div_good := V.div_good
  embE := B.embE
  embE_φ₀ := B.embE_φ₀
  conjF := B.toPre.conjF
  conjF_eq := B.toPre.conjF_eq
  embE_conj := B.embE_conj
  LL0 := B.LL0
  hostField_le_fixedField := B.hostField_le_fixedField
  O_int := B.O_int
  O_contains := B.O_contains
  plEq := Equiv.refl _
  val_eq := Formalism.BasicNotions.Examples₂.placesOf_val_eq B.LL
  ram_eq := Formalism.BasicNotions.Examples₂.placesOf_ram_eq B.LL
  conj_val := Formalism.BasicNotions.Examples₂.placesOf_conj_val B.LL
  T_level := fun u => by rw [C.A_T]; exact B.T_level u
  T_norm := fun u => by rw [C.A_T]; exact B.T_norm u
  sp_T := by rw [C.A_T]; exact B.sp_T
  cOf := B.cOf
  cOf_ne := B.cOf_ne
  cOf_eq := fun u => by rw [C.A_T, C.A_T]; exact B.cOf_eq u
  T_win := fun u => by
    simp only [ColumnsAtT.Tstar, ColumnsAtT.Xu, C.A_T, C.A_duStar, C.A_Dstar, C.A_GamP]
    exact B.T_win u
  GamP_eq := fun u => (C.A_GamP u).trans (C.A_GamP B.u₀).symm
  T_ne_pde := fun u => by rw [C.A_T]; exact B.T_ne_pde u
  Dstar_eq := C.A_Dstar
  clsLat := C.clsLat
  clsLat_lat := C.clsLat_lat
  eMu := W.eMu
  eMt := W.eMt0
  perCol_base_eq_PtilCol := W.perCol_base_eq_PtilCol
  Bu_linL := W.Bu_linL
  Bu_linR := W.Bu_linR
  chTw := C.chTw
  memberColumns_twistedChain_base := C.memberColumns_twistedChain_base
  e0Tw := C.e0Tw
  PTw := C.PTw
  eMtTw := W.eMtTw
  perCol_tie := W.perCol_tie
  jEE := V.jEE
  jEE_basis := V.jEE_basis
  jN := V.jN
  jN_basis := V.jN_basis
  Dall_eq := V.Dall_eq
  delP_eq := V.delP_eq
  Dt := C.Dt
  instDt := C.instDt
  detCls := C.detCls
  muTil := C.muTil
  chiD := C.chiD
  UO := C.UO
  chiD_UO := C.chiD_UO
  e1Dt := C.e1Dt
  rest_detCharacter_on_unitary_eq := C.rest_detCharacter_on_unitary_eq
  relDet := C.relDet
  relDet_self := C.relDet_self
  relDet_mul := C.relDet_mul
  relDet_smul := C.relDet_smul
  rhoDet_eq_inv_muTilde_chiD_pow := C.rhoDet_eq_inv_muTilde_chiD_pow
  rhoDetPrime_eq_muTilde_mul_chi_pow := C.rhoDetPrime_eq_muTilde_mul_chi_pow
  dsig := S.dsig
  dsig_pos := S.dsig_pos
  s := S.s
  s_split := S.s_split
  s_HH := S.s_HH
  s_Cu := S.s_Cu
  s_PlF := S.s_PlF
  loc := N.loc
  locA := N.locA
  locT := N.locT
  nd := N.nd
  ntw := N.ntw
  naut := N.naut
  nbc := N.nbc
  nexp := N.nexp
  ntypes := N.ntypes
  nStage_trivialCharacter_compat := N.nStage_trivialCharacter_compat
  nStage_trivialCharacter_coeff_eq := N.nStage_trivialCharacter_coeff_eq
  nth := N.nth
  nbr := N.nbr
  nbr_ind := N.nbr_ind
  self_good := N.self_good
  ntwbr := N.ntwbr
  ntwbr_ind := N.ntwbr_ind
  loc_tie := N.loc_tie
  bc_tie := N.bc_tie
  rbar_tie := N.rbar_tie
  mtpar_tie := N.mtpar_tie
  Z_tie := N.Z_tie
  Zgood_tie := N.Zgood_tie
  etaJ_tie := N.etaJ_tie
  fm := C.fm
  eMu_isom := W.eMu_isom
  nuIn := V.nuIn
  nuIn_inj := V.nuIn_inj
  nuIn_range := V.nuIn_range
  nuIn_jN := V.nuIn_jN
  nuIn_norm := V.nuIn_norm
  jEE_norm := V.jEE_norm
  s_Cu_isom := S.s_Cu_isom
  sEE := S.sEE
  cd := G.cd
  jet := G.jet
  jetU := G.jetU
  jetL := G.jetL
  jetL' := G.jetL'
  jetW := G.jetW
  jetW_l := G.jetW_l
  jetTau := G.jetTau
  jetW1 := G.jetW1
  resChar_thetaJetPlaceDegOne := G.resChar_thetaJetPlaceDegOne
  jetTau1 := G.jetTau1
  jetU1 := G.jetU1
  jetL1 := G.jetL1
  jetL1' := G.jetL1'
  gx := G.gx
  gat := G.gat
  gat_d := G.gat_d
  Y_sigval := B.Y_sigval

section
variable (B : Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C)

theorem assemble_R : (assemble B C W V S N G).R = B.R := rfl
theorem assemble_host : (assemble B C W V S N G).host = B.host := rfl
theorem assemble_sp : (assemble B C W V S N G).sp = B.sp := rfl
theorem assemble_rows : (assemble B C W V S N G).what₂ = W.what₂ := rfl
theorem assemble_hc : (assemble B C W V S N G).hc = B.hc := rfl
theorem assemble_hcW : (assemble B C W V S N G).hcW = B.hcW := rfl
theorem assemble_u₀ : (assemble B C W V S N G).u₀ = B.u₀ := rfl
theorem assemble_mem : (assemble B C W V S N G).mem = C.mem := rfl
theorem assemble_div : (assemble B C W V S N G).div = V.div := rfl
theorem assemble_embE : (assemble B C W V S N G).embE = B.embE := rfl
theorem assemble_lattice : (assemble B C W V S N G).LL0 = B.LL0 := rfl
theorem assemble_s : (assemble B C W V S N G).s = S.s := rfl
theorem assemble_nd : (assemble B C W V S N G).nd = N.nd := rfl
theorem assemble_loc : (assemble B C W V S N G).loc = N.loc := rfl
theorem assemble_fm : (assemble B C W V S N G).fm = C.fm := rfl
theorem assemble_jet : (assemble B C W V S N G).jet = G.jet := rfl
theorem assemble_gx : (assemble B C W V S N G).gx = G.gx := rfl
theorem assemble_vol : (assemble B C W V S N G).vol = G.vol := rfl
theorem assemble_cd : (assemble B C W V S N G).cd = G.cd := rfl
theorem assemble_dsig : (assemble B C W V S N G).dsig = S.dsig := rfl
theorem assemble_chTw : (assemble B C W V S N G).chTw = C.chTw := rfl
theorem assemble_cOf : (assemble B C W V S N G).cOf = B.cOf := rfl

end

structure Stages where
  B : Base
  C : Cols B
  W : RowsRest B C
  V : DivStage B C W
  S : SStage B C W
  N : NStage B C W
  G : GJStage B C

def Stages.toD7 (X : Stages) : D7 := assemble X.B X.C X.W X.V X.S X.N X.G

end GlobalTheory.Mem

end
