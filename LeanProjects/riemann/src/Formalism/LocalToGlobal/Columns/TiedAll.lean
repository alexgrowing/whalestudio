import Formalism.LocalToGlobal.Columns.TiedLv
import Formalism.LocalToGlobal.Columns.TiedValAll
import Formalism.LocalToGlobal.Columns.TiedBack

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d)

set_option maxHeartbeats 1000000 in

structure FormsOwed (u : d.what₂.Word) where
  gl : GLoc d.host.F d.host.E (CF.sigD (d.colRec a)) d.host.g
  gl_K : ∀ i, (gl.piG i : d.host.E) ∈ d.host.K
  glev : ∀ i hi, GLev (classAgreement a hS hH hP u i hi).lev gl (aOf d.R i) d.R.t i (skipOf d.R i) (fcOf d.R i) (decide (i = d.R.m))
  fMe : ∀ i hi v, (classAgreement a hS hH hP u i hi).lev.fM ((atTTied a hH u).eV v).1 ((atTTied a hH u).eV v).2 ≃+
    ((d.colRec a).mem u).A.Fv v
  fv : ∀ i hi, CF.FvTie (levelAgreement a hS hH u i hi) (classAgreement a hS hH hP u i hi) (fMe i hi)
  upN : ∀ i hi, CF.UpNatTie (levelAgreement a hS hH u i hi) (classAgreement a hS hH hP u i hi) (valuationAgreementConcrete a hS hH hP u i hi)
  dnN : ∀ i hi, CF.DnNatTie (levelAgreement a hS hH u i hi) (classAgreement a hS hH hP u i hi) (valuationAgreementConcrete a hS hH hP u i hi)
  clsP : CF.ClsPTied (D := d.colRec a) u
  valP : CF.ValPTied (D := d.colRec a) u clsP
  normP : CF.NormPTie valP
  glevP : GLev clsP.lev gl d.R.r d.R.t d.R.m (d.R.N d.R.m) (fcOf d.R d.R.m) false
  til : CF.TilTied (D := d.colRec a) u (atTTied a hH u) clsP (levelAgreement a hS hH u d.R.m le_rfl)
  tilLat : CF.TilBaseLat til (classAgreement a hS hH hP u d.R.m le_rfl)
  tilFv : CF.TilBaseFv til (classAgreement a hS hH hP u d.R.m le_rfl) (fMe d.R.m le_rfl)
  tilAd : CF.TilAd til (classAgreement a hS hH hP u d.R.m le_rfl)
  frExt : CF.FrExt til.z0 (glev d.R.m le_rfl) glevP
  eWz : ((d.colRec a).mem u).P.Wz ≃ₗ[ℂ] (((d.colRec a).fm u).clsP → ((d.colRec a).mem u).C.Y d.R.m → ℂ)
  evz : CF.EvzTie tilAd (valuationAgreementConcrete a hS hH hP u d.R.m le_rfl) eWz
  jM : ((d.colRec a).mem u).P.Mt →ₛₗ[starRingEnd ℂ] ((d.colRec a).mem u).P.Wrow
  per : CF.PerTie (D := d.colRec a) u jM

variable {a hS hH hP}

set_option maxHeartbeats 1000000 in

def formsTied {u : d.what₂.Word} (O : FormsOwed a hS hH hP u) : CF.FormsTied (d.colRec a) u where
  atT := atTTied a hH u
  cls := fun i hi => classAgreement a hS hH hP u i hi
  val := fun i hi => valuationAgreementConcrete a hS hH hP u i hi
  gl := O.gl
  gl_K := O.gl_K
  glev := O.glev
  lv := fun i hi => levelAgreement a hS hH u i hi
  fMe := O.fMe
  fv := O.fv
  upN := O.upN
  dnN := O.dnN
  norm := fun i hi => stepNormTie a hS hH hP u i hi
  bw := fun i hi => stepBwTie a hS hH hP u i hi
  clsP := O.clsP
  valP := O.valP
  normP := O.normP
  glevP := O.glevP
  til := O.til
  tilLat := O.tilLat
  tilFv := O.tilFv
  tilAd := O.tilAd
  frExt := O.frExt
  eWz := O.eWz
  evz := O.evz
  jM := O.jM
  per := O.per
  DGam := rfl

variable (a hS hH hP)

structure ColsOwed where
  forms : ∀ u : d.what₂.Word, FormsOwed a hS hH hP u
  herm : CH.ColsHerm (d.colRec a)
  joint : ∀ u, CF.Joint herm u (formsTied (forms u))
  gl_const : ∀ u u', (forms u).gl = (forms u').gl
  chi : CharacterCompatible (forms d.u₀).gl d.R.m
  fr_const : ∀ u u' (i : ℕ) (hi : i ≤ d.R.m), i < d.R.m → ((forms u).glev i hi).fr = ((forms u').glev i hi).fr
  frP_const : ∀ u u', (forms u).glevP.fr = (forms u').glevP.fr

variable {a hS hH hP}

def colsTied (O : ColsOwed a hS hH hP) : CF.ColsTied (d.colRec a) where
  herm := O.herm
  forms := fun u => formsTied (O.forms u)
  joint := O.joint
  gl_const := O.gl_const
  chi := O.chi
  fr_const := O.fr_const
  frP_const := O.frP_const

def colsTiedD {D : D7} (h : D.colRec = d.colRec a) (O : ColsOwed a hS hH hP) : Formalism.L2.Forms.ColsTied D :=
  columnsAgreement_of_eq h (colsTied O)

end Formalism.L2.Col
