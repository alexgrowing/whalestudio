import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PairingMulFirstChern
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrableRegularVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularAlterationArithmeticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegrableOnDescendGenericallyFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModpFramesPullback
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArchIntAlter

open Set

variable {k : Type} [CommRing k] {Y Y' : Scheme.{0}} [IsIntegral Y] [IsIntegral Y'] {q : Y ⟶ Sp k}
  {σ : k →+* ℂ}

theorem continuousOn_logNorm {L : LB Y} (φ : Weight q σ L) {r : L.ι → Y.functionFieldˣ}
    (hr : IsRatSec L r) (hφ : φ.IsCInf) :
    ContinuousOn (logNorm φ r) (offSupp q σ (divOfRatSec φ.isLB hr)) := by
  intro y hy
  have ho := isOpen_offSupp (q := q) (σ := σ) (divOfRatSec φ.isLB hr)
  have hi : y ∈ ptsIn q σ (L.U (pick φ.isLB y)) := mem_pick _ y
  have hu := hr.unitAt φ.isLB hy hi
  have hn : ptsIn q σ (L.U (pick φ.isLB y)) ∩ offSupp q σ (divOfRatSec φ.isLB hr) ∈ 𝓝 y :=
    inter_mem ((isOpen_ptsIn _).mem_nhds hi) (ho.mem_nhds hy)
  refine ContinuousAt.continuousWithinAt ?_
  have hc : ContinuousAt (fun z => Real.log ‖ratVal (r (pick φ.isLB y) : Y.functionField) z‖ -
      φ.φ (pick φ.isLB y) z / 2) y :=
    ((LogNormInt.continuousAt_ratVal hu.regAt).norm.log (norm_ne_zero_iff.2 (ratVal_ne_zero hu))).sub
      ((hφ _ y hi).continuousAt.div_const 2)
  refine hc.congr ?_
  filter_upwards [hn] with z hz
  exact (logNorm_eq φ hr hz.2 hz.1).symm

variable (M : HermLB q) (ρ : Y' ⟶ Y) (hη : ρ (genericPoint Y') ⤳ genericPoint Y)
  {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r)

theorem mem_offSupp_pull {y : CxPts (ρ ≫ q) σ}
    (hy : y ∈ ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl)) :
    y ∈ offSupp (ρ ≫ q) σ ((M.restr ρ).div (MultPull.isRatSec_pull_map ρ hη hr)) := by
  have hx : PtsOver.map ρ rfl _ y ∈ offSupp q σ (M.div hr) := mem_ptsIn.2 (mem_ptsIn.1 hy)
  obtain ⟨c, hc⟩ := exists_chart (M.restr ρ).isLB (under y)
  have hc' : PtsOver.map ρ rfl _ y ∈ ptsIn q σ (M.B.U (c PUnit.unit)) :=
    mem_ptsIn.2 (Set.mem_iInter.1 hc PUnit.unit)
  have hu := hr.unitAt M.isLB hx hc'
  have hu' := FrameGlue.Pull.unitAt_fnMap ρ hη hu
  exact mem_offSupp.2 fun h => ((presents_divOfRatSec (M.restr ρ).isLB
    (MultPull.isRatSec_pull_map ρ hη hr)).isEqn c _ hc).mem_supp_iff.1 h hu'

theorem logNorm_pull {y : CxPts (ρ ≫ q) σ}
    (hy : y ∈ ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl)) :
    logNorm ((M.restr ρ).φ σ) (fun c => Units.map (TrueGeo.SmallSec.fnMap ρ hη).toMonoidHom
      (r (c PUnit.unit))) y = logNorm (M.φ σ) r (PtsOver.map ρ rfl _ y) := by
  have hx : PtsOver.map ρ rfl _ y ∈ offSupp q σ (M.div hr) := mem_ptsIn.2 (mem_ptsIn.1 hy)
  have hj : y ∈ ptsIn _ σ ((M.restr ρ).B.U (pick ((M.restr ρ).φ σ).isLB y)) := mem_pick _ y
  have hj' : PtsOver.map ρ rfl _ y ∈
      ptsIn q σ (M.B.U (pick ((M.restr ρ).φ σ).isLB y PUnit.unit)) :=
    mem_ptsIn.2 (Set.mem_iInter.1 (mem_ptsIn.1 hj) PUnit.unit)
  have hu := hr.unitAt M.isLB hx hj'
  have hu' := FrameGlue.Pull.unitAt_fnMap ρ hη hu
  have e₁ : ((M.restr ρ).φ σ).φ (pick ((M.restr ρ).φ σ).isLB y) y =
      (M.φ σ).φ (pick ((M.restr ρ).φ σ).isLB y PUnit.unit) (PtsOver.map ρ rfl _ y) :=
    (M.φ σ).pull_φ ρ rfl _ y
  have e₂ : ratVal ((Units.map (TrueGeo.SmallSec.fnMap ρ hη).toMonoidHom
      (r (pick ((M.restr ρ).φ σ).isLB y PUnit.unit)) : Y'.functionFieldˣ) : Y'.functionField) y =
      ratVal (r (pick ((M.restr ρ).φ σ).isLB y PUnit.unit) : Y.functionField)
      (PtsOver.map ρ rfl _ y) := by
    show ratVal (TrueGeo.SmallSec.fnMap ρ hη (r (pick ((M.restr ρ).φ σ).isLB y PUnit.unit) :
      Y.functionField)) y = _
    rw [TrueGeo.SmallSec.ratVal_eq_valAt y hu'.regAt, TrueGeo.SmallSec.valAt_fnMap ρ hη _ hu.regAt,
      TrueGeo.SmallSec.ratVal_eq_valAt _ hu.regAt]
    rfl
  rw [logNorm_eq (M.φ σ) hr hx hj', logNorm, e₁, e₂]

end GlobalTheory.ArchIntAlter

namespace GlobalTheory.ArchIntAlter

open Set

theorem archIntegrable : Published.RegularAlteration → ∀ (k : Type) [CommRing k] (Y : Scheme.{0})
    [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ), IsArithVar q e → ∀ (M N : HermLB q)
    (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), N.ArchIntegrable M e hr := by
  intro hRA k _ Y _ q e hY M N r hr σ
  obtain ⟨Y', _, ρ, hreg, hgen, hdeg⟩ := GlobalTheory.T.exists_regular_alteration_arithmetic hRA k Y q e hY
  have hη : ρ (genericPoint Y') ⤳ genericPoint Y := hgen ▸ specializes_rfl
  have hr' := MultPull.isRatSec_pull_map ρ hη hr
  have hup := LogNormInt.archIntegrable hreg (N.restr ρ) (M.restr ρ) hr' σ
  have hsub : ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl) ⊆
      offSupp (ρ ≫ q) σ ((M.restr ρ).div hr') := fun y hy => mem_offSupp_pull M ρ hη hr hy
  have hm : MeasurableSet (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl)) :=
    (isOpen_ptsIn _).measurableSet
  have heq : EqOn (logNorm ((M.restr ρ).φ σ) fun c => Units.map
      (TrueGeo.SmallSec.fnMap ρ hη).toMonoidHom (r (c PUnit.unit)))
      (fun y => logNorm (M.φ σ) r (PtsOver.map ρ rfl _ y))
      (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl)) := fun y hy => logNorm_pull M ρ hη hr hy
  exact GlobalTheory.T.chernIntegrableOn_descend_genericallyFinite k Y q e hY Y' ρ hreg.toIsArithVar hgen hdeg N σ _ _
    (continuousOn_logNorm (M.φ σ) hr (M.cInf σ))
    ⟨(hup.1.mono_set hsub).congr_fun heq hm, (hup.2.mono_set hsub).congr_fun heq hm⟩

end GlobalTheory.ArchIntAlter
