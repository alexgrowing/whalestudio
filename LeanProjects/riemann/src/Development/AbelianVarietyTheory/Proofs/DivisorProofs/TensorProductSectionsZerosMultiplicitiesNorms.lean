import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectivePicClassAddIntegral
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix

theorem nonzeroLocus_prodSec {X : Scheme.{0}} {A B : LB X} (s : A.Sec) (t : B.Sec) :
    nonzeroLocus (EffBound.tensSec s t) = nonzeroLocus s ⊓ nonzeroLocus t := by
  have e (c : A.ι × B.ι) : X.basicOpen ((EffBound.tensSec s t).f c) =
      (A.U c.1 ⊓ B.U c.2) ⊓ X.basicOpen (s.f c.1) ⊓ ((A.U c.1 ⊓ B.U c.2) ⊓ X.basicOpen (t.f c.2)) :=
    (X.basicOpen_mul _ _).trans (congrArg₂ (· ⊓ ·) (X.basicOpen_res _ _) (X.basicOpen_res _ _))
  refine le_antisymm (iSup_le fun c => (e c).le.trans (inf_le_inf
    (inf_le_right.trans (le_iSup (fun i => X.basicOpen (s.f i)) c.1))
    (inf_le_right.trans (le_iSup (fun i => X.basicOpen (t.f i)) c.2)))) fun x hx => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx.1
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hx.2
  have h : x ∈ A.U i ⊓ B.U j := ⟨X.basicOpen_le _ hi, X.basicOpen_le _ hj⟩
  exact Opens.mem_iSup.2 ⟨(i, j), (e (i, j)).ge ⟨⟨h, hi⟩, h, hj⟩⟩

theorem secVal_prodSec {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (σ : k →+* ℂ) {A B : LB X}
    (s : A.Sec) (t : B.Sec) :
    secVal p σ (EffBound.tensSec s t) = secTens (secVal p σ s) (secVal p σ t) := by
  funext c y
  by_cases h : y ∈ ptsIn p σ (A.U c.1 ⊓ B.U c.2)
  · exact (ev_mul _ _ y).trans (congrArg₂ (· * ·) (ev_res inf_le_left h _) (ev_res inf_le_right h _))
  · exact (ev_of_notMem h _).trans ((secTens_mem (secVal_mem s) (secVal_mem t)).2 c y h).symm

theorem mult_prodSec {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {A B : LB X} (hA : A.IsLB)
    (hB : B.IsLB) (hAB : (tens A B).IsLB) (s : A.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : B.Sec)
    (ht : genericPoint X ∈ nonzeroLocus t) (h : genericPoint X ∈ nonzeroLocus (EffBound.tensSec s t)) (z : X) :
    (divOfSec hAB _ h).mult z = (divOfSec hA s hs).mult z + (divOfSec hB t ht).mult z := by
  obtain ⟨i, hi⟩ := Geo.Tor.exists_chart hA z
  obtain ⟨j, hj⟩ := Geo.Tor.exists_chart hB z
  have hij : z ∈ (tens A B).U (i, j) := ⟨hi, hj⟩
  rw [((presents_divOfRatSec hAB _).isEqn (i, j) z hij).mult_eq,
    ((presents_divOfRatSec hA _).isEqn i z hi).mult_eq, ((presents_divOfRatSec hB _).isEqn j z hj).mult_eq,
    val_ratOfSec (gen_mem hij), val_ratOfSec (gen_mem hi), val_ratOfSec (gen_mem hj),
    ← Scheme.ord_mul (fnOf_sec_ne_zero hs (gen_mem hi)) (fnOf_sec_ne_zero ht (gen_mem hj))]
  exact congrArg (Scheme.ord · z) ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (fnOf_resG inf_le_left _ _) (fnOf_resG inf_le_right _ _)))

theorem exists_sec_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (σ : k →+* ℂ) (M A : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (a : A.B.Sec) (ha : genericPoint X ∈ nonzeroLocus a), ∃ (s₁ : (M.tens A).B.Sec) (h₁ : genericPoint X ∈ nonzeroLocus s₁), nonzeroLocus s₁ = nonzeroLocus s ⊓ nonzeroLocus a ∧ (∀ z, (divOfSec (M.tens A).φ.isLB s₁ h₁).mult z = (divOfSec M.φ.isLB s hs).mult z + (divOfSec A.φ.isLB a ha).mult z) ∧ ∀ y ∈ ptsIn p σ (nonzeroLocus s₁), (M.tens A).logSec s₁ y = M.logSec s y + A.logSec a y := by
  intro k _ X _ _ p σ M A s hs a ha
  have e := nonzeroLocus_prodSec s a
  refine ⟨EffBound.tensSec s a, e.ge ⟨hs, ha⟩, e, mult_prodSec _ _ _ s hs a ha _, fun y hy => ?_⟩
  have hy' : y ∈ ptsIn p σ (nonzeroLocus s ⊓ nonzeroLocus a) := ptsIn_mono e.le hy
  have h0 (N : MLine p σ) (u : N.B.Sec) (hu : y ∈ ptsIn p σ (nonzeroLocus u)) : N.φ.nsq (secVal p σ u) y ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 ((secVal_ne_zero_iff u (mem_pick _ y)).2 hu)))
      (Real.exp_ne_zero _)
  have h : (M.φ.tens A.φ).nsq (secVal p σ (EffBound.tensSec s a)) y =
      M.φ.nsq (secVal p σ s) y * A.φ.nsq (secVal p σ a) y := by
    rw [secVal_prodSec]
    exact Weight.nsq_tens _ _ (secVal_mem s) (secVal_mem a) y
  refine (congrArg (Real.log · / 2) h).trans ?_
  rw [Real.log_mul (h0 M s (mem_ptsIn_inf.1 hy').1) (h0 A a (mem_ptsIn_inf.1 hy').2), add_div]
  rfl

end GlobalTheory.Mix
