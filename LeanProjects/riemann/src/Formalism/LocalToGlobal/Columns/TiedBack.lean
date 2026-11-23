import Formalism.LocalToGlobal.Columns.TiedCB

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Col

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

def CH.HermCols.toD {D : D7}
    (Z : CH.HermCols D.colRec) :
    Formalism.L2.Herm.HermCols D where
  lev0 := Z.lev0
  lev := Z.lev
  cls := Z.cls
  vT := Z.vT
  Fv := Z.Fv

set_option maxHeartbeats 16000000 in

def CH.AtT.toD {D : D7} {u : D.what₂.Word} {e : (D.mem u).A.vT ≃ {v : HeightOneSpectrum (𝓞 D.host.F) // (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}}
    {eF : ∀ v : (D.mem u).A.vT, (D.mem u).A.Fv v ≃+* (𝓞 D.host.F ⧸ (e v).1.asIdeal)}
    (Z : CH.AtT D.colRec u e eF) :
    Formalism.L2.Herm.AtT D u e eF where
  piU := Z.piU
  piU_K := Z.piU_K
  piU_norm := Z.piU_norm
  piU_cong := Z.piU_cong
  Pv := Z.Pv
  Pv_max := Z.Pv_max
  Pv_pi := Z.Pv_pi
  Pv_over := Z.Pv_over
  res := Z.res
  res_surj := Z.res_surj
  res_ker := Z.res_ker
  res_F := Z.res_F
  seen := Z.seen
  disc := Z.disc
  pr := Z.pr
  pr_surj := Z.pr_surj
  pr_smul := Z.pr_smul
  pr_ker := Z.pr_ker
  fv_ker := Z.fv_ker
  prk := Z.prk
  prk_surj := Z.prk_surj
  prk_smul := Z.prk_smul
  prk_ker := Z.prk_ker
  te_tie := Z.te_tie
  upG := Z.upG
  up_tie := Z.up_tie
  dnG := Z.dnG
  dn_tie := Z.dn_tie
  dilG := Z.dilG
  dil_tie := Z.dil_tie
  lattice₂ := Z.lattice₂
  levP := Z.levP
  clsP := Z.clsP
  z0 := Z.z0
  cocycle_zero_mem_invariants := Z.cocycle_zero_mem_invariants
  hermitianForm_lastCoordinateUniformizerVector_self := Z.hermitianForm_lastCoordinateUniformizerVector_self
  tilG := Z.tilG
  til_tie := Z.til_tie

set_option maxHeartbeats 4000000 in

theorem CH.AdTied.toD {D : D7} {H : CH.HermCols D.colRec} {aT : ∀ u, CH.AtT D.colRec u (H.vT u) (H.Fv u)}
    (Z : CH.AdTied D.colRec H aT) :
    Formalism.L2.Herm.AdTied D (CH.HermCols.toD H) (fun u => (CH.AtT.toD (aT u))) where
  up0 := Z.up0
  upI := Z.upI
  dn0 := Z.dn0
  dnI := Z.dnI
  dil0 := Z.dil0
  dilI := Z.dilI

set_option maxHeartbeats 4000000 in

def CH.ColsHerm.toD {D : D7}
    (Z : CH.ColsHerm D.colRec) :
    Formalism.L2.Herm.ColsHerm D where
  base := CH.HermCols.toD Z.base
  atT := fun u => CH.AtT.toD (Z.atT u)
  levelZeroCompatibility := Z.levelZeroCompatibility
  ad := CH.AdTied.toD Z.ad
  cof := Z.cof
  piG := Z.piG
  stabMap := Z.stabMap
  fvI := Z.fvI
  std := Z.std
  baseL := Z.baseL

set_option maxHeartbeats 4000000 in

def CF.ClsTied.toD {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m}
    (Z : CF.ClsTied (D := D.colRec) u i hi) :
    Formalism.L2.Forms.ClsTied (D := D) u i hi where
  lev := Z.lev
  y := Z.y
  y_bij := Z.y_bij
  y_lat := Z.y_lat
  stabI := Z.stabI
  stabI_inj := Z.stabI_inj
  stabI_range := Z.stabI_range

set_option maxHeartbeats 8000000 in

def CF.ValTied.toD {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} {eV : (D.mem u).A.vT ≃ Formalism.L2.Forms.PlT D u}
    {K : CF.ClsTied (D := D.colRec) u i hi}
    (Z : CF.ValTied (D := D.colRec) u eV i hi K) :
    Formalism.L2.Forms.ValTied (D := D) u eV i hi (CF.ClsTied.toD K) where
  eY := Z.eY
  de := Z.de
  Fi := Z.Fi
  ipV := Z.ipV
  rat := Z.rat
  lat := Z.lat
  dil := Z.dil
  dilT := Z.dilT

set_option maxHeartbeats 4000000 in

def CF.AtTTied.toD {D : D7} {u : D.what₂.Word}
    (Z : CF.AtTTied (D := D.colRec) u) :
    Formalism.L2.Forms.AtTTied (D := D) u where
  eV := Z.eV
  piU := Z.piU
  piU_K := Z.piU_K
  piU_norm := Z.piU_norm
  piU_cong := Z.piU_cong
  res := Z.res
  res_surj := Z.res_surj
  res_pi := Z.res_pi
  res_conj := Z.res_conj
  res_v := Z.res_v
  tauOf := Z.tauOf
  seenP := Z.seenP

set_option maxHeartbeats 8000000 in

def CF.LvTied.toD {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} {A : CF.AtTTied (D := D.colRec) u}
    (Z : CF.LvTied (D := D.colRec) u A i hi) :
    Formalism.L2.Forms.LvTied (D := D) u (CF.AtTTied.toD A) i hi where
  pr := Z.pr
  pr_surj := Z.pr_surj
  pr_smul := Z.pr_smul
  pr_ker := Z.pr_ker
  fv_ker := Z.fv_ker
  prk := Z.prk
  prk_surj := Z.prk_surj
  prk_smul := Z.prk_smul
  prk_ker := Z.prk_ker
  te := Z.te

set_option maxHeartbeats 4000000 in

def CF.ClsPTied.toD {D : D7} {u : D.what₂.Word}
    (Z : CF.ClsPTied (D := D.colRec) u) :
    Formalism.L2.Forms.ClsPTied (D := D) u where
  lev := Z.lev
  y := Z.y
  y_bij := Z.y_bij
  lat := Z.lat
  y_lat := Z.y_lat
  lat_fin := Z.lat_fin
  stabI := Z.stabI
  stabI_inj := Z.stabI_inj
  stabI_range := Z.stabI_range

set_option maxHeartbeats 8000000 in

def CF.ValPTied.toD {D : D7} {u : D.what₂.Word} {K : CF.ClsPTied (D := D.colRec) u}
    (Z : CF.ValPTied (D := D.colRec) u K) :
    Formalism.L2.Forms.ValPTied (D := D) u (CF.ClsPTied.toD K) where
  sg := Z.sg
  eW := Z.eW
  ptC := Z.ptC
  ipP := Z.ipP
  rat := Z.rat
  lat := Z.lat

set_option maxHeartbeats 8000000 in

def CF.TilTied.toD {D : D7} {u : D.what₂.Word} {A : CF.AtTTied (D := D.colRec) u} {K : CF.ClsPTied (D := D.colRec) u}
    {P : CF.LvTied (D := D.colRec) u A D.R.m le_rfl}
    (Z : CF.TilTied (D := D.colRec) u A K P) :
    Formalism.L2.Forms.TilTied (D := D) u (CF.AtTTied.toD A) (CF.ClsPTied.toD K) (CF.LvTied.toD P) where
  z0 := Z.z0
  lastCoordinateUniformizerVector_spans_orthogonal_line := Z.lastCoordinateUniformizerVector_spans_orthogonal_line
  hermitianForm_lastCoordinateUniformizerVector_self := Z.hermitianForm_lastCoordinateUniformizerVector_self
  ga := Z.ga
  til_lat := Z.til_lat
  til_fv := Z.til_fv

set_option maxHeartbeats 8000000 in

def CF.TilAd.toD {D : D7} {u : D.what₂.Word} {A : CF.AtTTied (D := D.colRec) u} {K : CF.ClsPTied (D := D.colRec) u}
    {P : CF.LvTied (D := D.colRec) u A D.R.m le_rfl} {Tl : CF.TilTied (D := D.colRec) u A K P}
    {Km : CF.ClsTied (D := D.colRec) u D.R.m le_rfl}
    (Z : CF.TilAd Tl Km) :
    Formalism.L2.Forms.TilAd (CF.TilTied.toD Tl) (CF.ClsTied.toD Km) where
  ka := Z.ka
  til_ad := Z.til_ad

set_option maxHeartbeats 16000000 in

def CF.FormsTied.toD {D : D7} {u : D.what₂.Word}
    (Z : CF.FormsTied D.colRec u) :
    Formalism.L2.Forms.FormsTied D u where
  atT := CF.AtTTied.toD Z.atT
  cls := fun i hi => CF.ClsTied.toD (Z.cls i hi)
  val := fun i hi => CF.ValTied.toD (Z.val i hi)
  gl := Z.gl
  gl_K := Z.gl_K
  glev := Z.glev
  lv := fun i hi => CF.LvTied.toD (Z.lv i hi)
  fMe := Z.fMe
  fv := Z.fv
  upN := Z.upN
  dnN := Z.dnN
  norm := Z.norm
  bw := Z.bw
  clsP := CF.ClsPTied.toD Z.clsP
  valP := CF.ValPTied.toD Z.valP
  normP := Z.normP
  glevP := Z.glevP
  til := CF.TilTied.toD Z.til
  tilLat := Z.tilLat
  tilFv := Z.tilFv
  tilAd := CF.TilAd.toD Z.tilAd
  frExt := Z.frExt
  eWz := Z.eWz
  evz := Z.evz
  jM := Z.jM
  per := Z.per
  DGam := Z.DGam

set_option maxHeartbeats 16000000 in

theorem CF.Joint.toD {D : D7} {X : CH.ColsHerm D.colRec} {u : D.what₂.Word} {T : CF.FormsTied D.colRec u}
    (Z : CF.Joint X u T) :
    Formalism.L2.Forms.Joint (CH.ColsHerm.toD X) u (CF.FormsTied.toD T) where
  eV := Z.eV
  piU := Z.piU
  res := Z.res
  car0 := Z.car0
  carI := Z.carI
  carP := Z.carP
  lattice₂ := Z.lattice₂
  pr := Z.pr
  prk := Z.prk
  z0 := Z.z0
  ga := Z.ga
  sp := Z.sp
  piG := Z.piG
  fr0 := Z.fr0

set_option maxHeartbeats 8000000 in

def CF.ColsTied.toD {D : D7}
    (Z : CF.ColsTied D.colRec) :
    Formalism.L2.Forms.ColsTied D where
  herm := CH.ColsHerm.toD Z.herm
  forms := fun u => CF.FormsTied.toD (Z.forms u)
  joint := fun u => CF.Joint.toD (Z.joint u)
  gl_const := Z.gl_const
  chi := Z.chi
  fr_const := Z.fr_const
  frP_const := Z.frP_const

def columnsAgreement_of_eq {D : D7} {c : ColRec} (h : D.colRec = c) (C : CF.ColsTied c) : Formalism.L2.Forms.ColsTied D :=
  CF.ColsTied.toD (h ▸ C)

def formsAgreement_of_eq {D : D7} {c : ColRec} (h : D.colRec = c) (T : ∀ u, CF.FormsTied c u) (u : D.what₂.Word) :
    Formalism.L2.Forms.FormsTied D u :=
  CF.FormsTied.toD ((h ▸ T : ∀ u, CF.FormsTied D.colRec u) u)

def colsHerm_of_eq {D : D7} {c : ColRec} (h : D.colRec = c) (X : CH.ColsHerm c) : Formalism.L2.Herm.ColsHerm D :=
  CH.ColsHerm.toD (h ▸ X)

end Formalism.L2.Col

end
