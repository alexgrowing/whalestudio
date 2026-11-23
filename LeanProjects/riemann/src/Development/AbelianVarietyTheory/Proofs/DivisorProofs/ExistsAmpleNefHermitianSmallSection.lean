import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefShiftOfGeneratedAtCharZeroPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AmpleNefSmall

theorem mem_nonzeroLocus_secPow_one {X : Scheme.{0}} {L : LB X} (s : L.Sec) {x : X}
    (hx : x ∈ Out.nonzeroLocus s) : x ∈ Out.nonzeroLocus (Cartier.secPow s 1) := by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
  refine Opens.mem_iSup.2 ⟨fun _ => i, ?_⟩
  show x ∈ X.basicOpen (resG X (Cartier.lbPow_U L 1 (fun _ => i)).le (s.f i) ^ 1)
  rw [pow_one]
  unfold resG
  rw [Scheme.basicOpen_res]
  exact ⟨(Cartier.lbPow_U L 1 (fun _ => i)).ge (X.basicOpen_le _ hi), hi⟩

end GlobalTheory.AmpleNefSmall

namespace GlobalTheory.AmpleNefSmall

open ProjSpace in

theorem exists_ample_nef_smallSec : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∃ A : HermLB p, IsAmpleLB A.B ∧ A.IsNef D ∧ ∃ s ∈ A.smallSec, s ≠ 0 := by
  intro hAr k _ X _ p D hX
  obtain ⟨N, j, hj, hjp⟩ := hX.isProjOver
  have := hj
  have := hX.finite
  have := isProper_str k N
  have : IsProper p := hjp ▸ inferInstance
  let B : LB X := (O1 k N).pull j
  have hB : B.IsLB := LB.isLB_pull (O1_isLB k N) j
  let c : Fin (N + 1) → B.Sec := fun a => Cartier.secPull (coord k N a) j
  have hc : ⨆ a, Out.nonzeroLocus (c a) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨a, ha⟩ := Opens.mem_iSup.1 ((iSup_nonzeroLocus_coord k N).ge (Opens.mem_top (j x)))
    refine Opens.mem_iSup.2 ⟨a, ?_⟩
    show x ∈ Out.nonzeroLocus (Cartier.secPull (coord k N a) j)
    rw [Cartier.nonzeroLocus_secPull]
    exact ha
  let A₀ : HermLB p := HermLB.fs p hB c hc (fun _ => 1) (fun _ => by simp)
    fun _ => ⟨1, one_mem _, by rw [mul_one, Matrix.map_one _ (map_zero _) (map_one _)]⟩
  have hA : IsAmpleLB A₀.B := (isAmple_projective_O_one k N).pull_of_isClosedImmersion j
  have hsmall : ∀ a, c a ∈ A₀.smallSec := by
    intro a σ y
    have e (a) : Weight.combVal p σ c 1 a = secVal _ σ (c a) := by
      simp [Weight.combVal, Matrix.one_apply]
    refine le_of_le_of_eq ?_ (Weight.sum_nsq_fs (hB := hB) (he := fun a => e a ▸ secVal_mem _)
      (h := Weight.noCommonZero_combVal hc (M := 1) (by simp)) y)
    exact le_of_eq_of_le (congrArg (Weight.nsq _ · y) (e a).symm)
      (Finset.single_le_sum (fun b _ => Weight.nsq_nonneg _ _ y) (Finset.mem_univ a))
  have hgen : ∀ x : X, CharZero (X.residueField x) →
      ∃ i, x ∈ Out.nonzeroLocus (Cartier.secPow (c i) 1 : (A₀.pow 1).B.Sec) := fun x _ =>
    have ⟨a, ha⟩ := Opens.mem_iSup.1 (hc.ge (Opens.mem_top x))
    ⟨a, mem_nonzeroLocus_secPow_one _ ha⟩
  obtain ⟨t, ht, hnef⟩ := GlobalTheory.NefOfGen.nef_of_gen hAr k X p D hX A₀ 1 (N + 1)
    (fun i => Cartier.secPow (c i) 1) le_rfl hgen (HermLB.semiPos_fs hB c hc _ _ _)
    (ProjModel.nefFib_of_isAmpleLB A₀ hA)
  refine ⟨A₀.shift (fun _ => t) fun _ => rfl, hA, hnef, ?_⟩
  obtain ⟨a, ha⟩ := Opens.mem_iSup.1 (hc.ge (Opens.mem_top (genericPoint X)))
  refine ⟨c a, fun σ y => ?_, fun h0 => ?_⟩
  · refine le_of_eq_of_le (HermLB.nsq_shift A₀ (fun _ => t) (fun _ => rfl) (secVal p σ (c a)) y) ?_
    have h1 := hsmall a σ y
    have h2 : Real.exp (-(2 * t)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h3 := Weight.nsq_nonneg (A₀.φ σ) (secVal p σ (c a)) y
    nlinarith
  · have e : c a = (0 : B.Sec) := h0
    rw [e] at ha
    simp [Out.nonzeroLocus] at ha

end GlobalTheory.AmpleNefSmall
