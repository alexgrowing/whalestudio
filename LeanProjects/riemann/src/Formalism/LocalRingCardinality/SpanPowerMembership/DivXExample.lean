import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleClassGroupCardPos
import Formalism.LocalRingCardinality.SpanPowerMembership.PlOver

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

def geoExample (F : Type) [Field F] [NumberField F] [StarRing F] : DV.Geo F where
  Var := Empty
  dim := fun Y => Empty.elim Y
  Fn := fun Y => Empty.elim Y
  fnField := fun Y => Empty.elim Y
  fnAlg := fun Y => Empty.elim Y
  Dv := fun Y => Empty.elim Y
  dvGrp := fun Y => Empty.elim Y
  Eff := fun Y => Empty.elim Y
  eff_zero := fun Y => Empty.elim Y
  eff_add := fun Y => Empty.elim Y
  H0 := fun Y => Empty.elim Y
  degreeZeroCohomology_finiteDimensional := fun Y => Empty.elim Y
  mul_mem_riemannRochSpace_add := fun Y => Empty.elim Y
  riemannRoch_mono := fun Y => Empty.elim Y
  KY := fun Y => Empty.elim Y
  Cl := fun Y => Empty.elim Y
  properCl := fun Y => Empty.elim Y
  subCl := fun Y => Empty.elim Y
  supp := fun Y => Empty.elim Y
  inter := fun Y => Empty.elim Y
  nef := fun Y => Empty.elim Y
  big := fun Y => Empty.elim Y
  bpf := fun Y => Empty.elim Y
  phiBir := fun Y => Empty.elim Y
  phiNoContr := fun Y => Empty.elim Y
  vanishOn := fun Y => Empty.elim Y
  hdim := fun Y => Empty.elim Y
  pts := fun Y => Empty.elim Y
  ptsMeas := fun Y => Empty.elim Y
  vol := fun Y => Empty.elim Y
  FnC := fun Y => Empty.elim Y
  fnCRing := fun Y => Empty.elim Y
  fnCAlg := fun Y => Empty.elim Y
  cx := fun Y => Empty.elim Y
  cx_smul := fun Y => Empty.elim Y
  Met := fun Y => Empty.elim Y
  mAdd := fun Y => Empty.elim Y
  mPow := fun Y => Empty.elim Y
  fsMet := fun Y => Empty.elim Y
  pn := fun Y => Empty.elim Y
  pnK := fun Y => Empty.elim Y
  mSmooth := fun Y => Empty.elim Y
  mPsh := fun Y => Empty.elim Y
  redZero := fun Y => Empty.elim Y
  agreeOn := fun Y => Empty.elim Y
  resNorm := fun Y => Empty.elim Y
  Adl := fun Y => Empty.elim Y
  ofW := fun Y => Empty.elim Y
  twist := fun Y => Empty.elim Y
  arTop := fun Y => Empty.elim Y
  arVol := fun Y => Empty.elim Y
  nefA := fun Y => Empty.elim Y
  supInf := fun Y => Empty.elim Y
  supFin := fun Y => Empty.elim Y
  cutGood := fun Y => Empty.elim Y
  cutHt := fun Y => Empty.elim Y
  cutOrd := fun Y => Empty.elim Y
  resFull := fun Y => Empty.elim Y
  resDeg := fun Y => Empty.elim Y
  supInf_ofW := fun Y => Empty.elim Y
  supInf_twist := fun Y => Empty.elim Y
  supFin_twist := fun Y => Empty.elim Y
  regOn := fun Y => Empty.elim Y

variable (D : D7)

def divXExample (_h0 : D.what₂.Drows = 0) (hM : ∀ j, Subsingleton (D.what₂.Mj j)) : DivX D where
  geo := geoExample _
  Lev := Empty
  levPr := fun κ => κ.elim
  shv := fun _ κ => κ.elim
  shv_N := fun _ κ => κ.elim
  shv_lev := fun _ κ => κ.elim
  PlP := fun p _ => {w : D.what₂.places.Pl // D.what₂.places.resChar w = p}
  plpFin := fun p _ => PlOver.plFin D p
  plpNe := fun p _ => PlOver.plNe D p
  wtP := fun p _ la => PlOver.wt D p la.1
  divisorWeight_nonneg := fun p _ la => PlOver.wt_nonneg D p la.1
  divisorWeight_sum := fun p _ => PlOver.wt_sum D p
  plP := fun _ _ => Equiv.refl _
  divisorWeight_def := fun _ _ _ => rfl
  jC := fun p _ _ => (teich_Om_equiv p).some.toRingHom.comp (algebraMap (DV.KW p) (TeichOm p))
  Mp := fun _ κ => κ.elim
  md := fun _ κ => κ.elim
  vdd := fun _ _ => 0
  vdd_unram := fun _ _ _ => rfl
  vdd_nonneg := fun _ _ => le_rfl
  CurveM := fun _ κ => κ.elim
  degM := fun _ κ => κ.elim
  htMdl := fun _ κ => κ.elim
  htCurve := fun _ κ => κ.elim
  htCurve_deg := fun _ κ => κ.elim
  MjH := fun _ => zeroHLat _
  MjH_good := fun _ => zeroHLat_good _
  jM := fun _ => 0
  jM_basis := fun j => by
    have := hM j
    exact ⟨linearIndependent_empty_type (ι := Fin 0), Subsingleton.elim _ _⟩
  jM_lat := fun j _ _ _ => by
    have := hM j
    exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Submodule.mem_top⟩
  jM_metric := fun _ _ _ _ => (normAt_empty (ι := Fin 0) _ _ _ _).trans norm_zero.symm
  Qp := fun _ => ∅
  degreeZero_partial_set_empty := rfl
  Qp_muAt := fun _ => Finset.notMem_empty _
  Qp_g := fun _ _ _ => Finset.notMem_empty _
  QPl := fun _ => Empty
  qv := fun _ v => v.elim
  qv_gt := fun _ v => v.elim
  qv_char := fun _ _ v => v.elim
  nu := fun _ v => v.elim
  nu_ne := fun _ v => v.elim
  nu_abs := fun _ v => v.elim
  ZQ := fun _ v => v.elim
  quotientLocalValueFirst := fun _ v => v.elim
  typeDim := fun _ v => v.elim
  Comp := fun _ => Empty
  degHH := fun _ c => c.elim
  Yv := fun _ c => c.elim
  Ybd := fun _ c => c.elim
  Lw := fun _ c => c.elim
  iMj := fun _ c => c.elim
  iMj_mem := fun _ c => c.elim
  logLam := fun j σ _ => Real.log (D.what₂.lamP D.what₂.mu0 j σ)
  logLam_base := fun _ _ => rfl
  kapR := fun _ => 1
  kapR_pos := fun _ => one_pos
  kapR_conj := fun _ => rfl
  MjLat_sub := fun j _ _ _ _ => by
    have := hM j
    exact ⟨0, Subsingleton.elim _ _⟩
  phiFr_unram := fun _ κ => κ.elim
  Surf := Empty
  surfCh2 := fun _ => 0
  surfDegOm := fun _ => 0
  SurfFp := Empty
  surfFpCh2 := fun _ => 0

end Formalism.BasicNotions.Examples₂
