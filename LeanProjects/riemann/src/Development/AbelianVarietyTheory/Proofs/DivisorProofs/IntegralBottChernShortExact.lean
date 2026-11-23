import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondCountableTopologySphere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelDbarZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSubOfIsForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormPullbackHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIntegralFinSumCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormDbarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeformationToSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIntegralConstantFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottChernFormRealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcBottChernFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottChernFormPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottChernFormSplitZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBottChernMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedSequenceOfShortExactStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BcUnique

open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory OnePoint
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real ComplexOrder

theorem integral_eq_of_isExact {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : HolAtlas M n) {α β : A.Fld} (hα : A.IsForm α)
    (hβ : A.IsForm β) (h : A.IsExact (α - β)) : A.integral α = A.integral β := by
  obtain ⟨u, w, hu, hw, e⟩ := h
  have h0 := GlobalTheory.T.holAtlas_integral_fin_sum_compact A ![A.del u, A.dbar w] (by
    intro j; fin_cases j
    exacts [GlobalTheory.T.holAtlas_isForm_del A u hu, GlobalTheory.T.isForm_dbar' A w hw])
  have s : (∑ j, ![A.del u, A.dbar w] j) = α - β := by rw [e, Fin.sum_univ_two]; rfl
  rw [s, HolAtlas.integral_sub_of_isForm A α β hα hβ, Fin.sum_univ_two] at h0
  have s1 := (GlobalTheory.CxFormStokesBoth.stokes M n A u hu).1
  have s2 := (GlobalTheory.CxFormStokesBoth.stokes M n A w hw).2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h0
  linarith

theorem integral_zero {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : HolAtlas M n) : A.integral 0 = 0 := by
  have h0 : A.IsForm 0 := by
    have := A.isForm_fn (u := fun _ => 0) (fun i => (contDiffOn_const (c := (0 : ℂ))).congr fun v _ => by simp)
    convert this using 1
    funext x; simp [HolAtlas.fn]
  have := HolAtlas.integral_sub_of_isForm A 0 0 h0 h0
  rw [sub_zero] at this
  linarith

theorem integral_bc_eq_neg {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] [MeasurableSpace M] [BorelSpace M] (A : HolAtlas M 1) {r s : ℕ} (B : BottChern)
    (T : HermSeq A r s) (hT : IsInduced T) : A.integral (B.bc T) = -A.integral (bcFld T) := by
  obtain ⟨T', T₀, hsp, hInf, h0, hind⟩ := GlobalTheory.T.exists_deformation_to_split A T hT
  have hbc : A.IsForm (B.bc T) := (B.isRealForm T).1
  have hb' : (famAtlas A).IsRealForm 1 (B.bc T') := B.isRealForm T'
  have hf' : (famAtlas A).IsRealForm 1 (bcFld T') := GlobalTheory.T.bott_chern_form_real (famAtlas A) T'
  have pf (t : OnePoint ℂ) (α : (famAtlas A).Fld) (hα : (famAtlas A).IsForm α) : A.IsForm ((famAtlas A).pullback A (fib t) α) :=
    GlobalTheory.PullbackForm.isForm_pullback _ _ _ _ (famAtlas A) A (fib t) α (isHolo_fib A t) hα

  have e1 : A.integral (B.bc T) = A.integral ((famAtlas A).pullback A (fib _root_.OnePoint.infty) (B.bc T')) :=
    integral_eq_of_isExact A hbc (pf _ _ hb'.1) (B.pull T' T (fib _root_.OnePoint.infty) (isHolo_fib A _root_.OnePoint.infty) hInf)
  have e2 : bcFld T = (famAtlas A).pullback A (fib _root_.OnePoint.infty) (bcFld T') := GlobalTheory.T.bott_chern_form_pullback (famAtlas A) A T' T (fib _root_.OnePoint.infty) (isHolo_fib A _root_.OnePoint.infty) hInf

  have e3 : A.integral ((famAtlas A).pullback A (fib ((0 : ℂ) : OnePoint ℂ)) (B.bc T')) = 0 := by
    rw [← integral_eq_of_isExact A (B.isRealForm T₀).1 (pf _ _ hb'.1)
      (B.pull T' T₀ (fib _) (isHolo_fib A _) h0)]
    have z : A.fn (fun _ => (0 : ℝ)) = 0 := by funext x; simp [HolAtlas.fn]
    have h0f : A.IsForm 0 := z ▸ A.isForm_fn (u := fun _ => 0)
      (fun i => (contDiffOn_const (c := (0 : ℂ))).congr fun v _ => by simp)
    rw [integral_eq_of_isExact A (B.isRealForm T₀).1 h0f (by simpa using B.split T₀ hsp), integral_zero]
  have e4 : (famAtlas A).pullback A (fib ((0 : ℂ) : OnePoint ℂ)) (bcFld T') = 0 := by
    rw [← GlobalTheory.T.bott_chern_form_pullback (famAtlas A) A T' T₀ _ (isHolo_fib A _) h0, GlobalTheory.T.bott_chern_form_split_zero A T₀ hsp]
  have key := GlobalTheory.T.fibre_integral_constant_family M A (B.bc T') (bcFld T') hb' hf' (fun x => by
    obtain ⟨a, ha⟩ := T'.cover x.pt
    rw [B.ddc_bc T' a x ha, GlobalTheory.T.ddc_bott_chern_form (famAtlas A) T' hind a x ha]
    simp) _root_.OnePoint.infty ((0 : ℂ) : OnePoint ℂ)
  rw [e4, e3, integral_zero, ← e1, ← e2, add_zero] at key
  linarith

end GlobalTheory.BcUnique

section

open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas relCot dRel IsRelAcyclic)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

theorem GlobalTheory.BcUnique.integral_bc_seq : ∀ (B : CxForm.BottChern) (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (h : IsRegVar p 1) (S : ShortComplex X.Modules) (hS : S.ShortExact) (r s : ℕ) (g : VMetric p S.X₂ (r + s)) (G : g.IsCInf) (hi : VB.IsSubbundle S.f) (h₁ : VB.IsVB S.X₁ r) (h₃ : VB.IsVB S.X₃ s) (σ : k →+* ℂ), (g.met σ).bcMeas hS h₁ h₃ univ ≠ ⊤ → (h.atlas σ).integral (B.bc (h.seq hS (G.restrict hi h₁) G (G.quot hS h₁ h₃) σ)) = -((g.met σ).bcMeas hS h₁ h₃ univ).toReal := by
  intro B k _ X p _ h S hS r s g G hi h₁ h₃ σ hfin
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ h.isProjOver
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ h.isProjOver
  haveI : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ h.isProjOver
  rw [GlobalTheory.BcUnique.integral_bc_eq_neg (h.atlas σ) B _ (GlobalTheory.T.induced_sequence_of_short_exact k X p h S hS r s g G hi h₁ h₃ σ),
    GlobalTheory.T.integral_bott_chern_measure k X p h S hS r s g G hi h₁ h₃ σ hfin]

end
