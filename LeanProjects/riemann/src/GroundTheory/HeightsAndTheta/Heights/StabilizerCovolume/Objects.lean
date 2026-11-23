import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.GaussCM
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.TwistVecLinearIndependent
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree
  GroundTheory.Heights₂.Heights.LowerBoundFree.Line GroundTheory.Heights₂.Heights.NineStatements.Twist
open scoped Matrix

namespace LineFuller

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

def twistData : ComponentData II Unit Unit (PBlk 2) Ω (fun _ => Fin 2 → Ω) :=
  { lineData II hII with
    W := fun _ => twistBundle (segreCoord yLine)
    h := fun _ => twistMetric }

theorem twistVec_image (c : Unit → Fin 2) :
    twistVec (segreCoord yLine) c '' {i : Fin 2 | (i : ℕ) < 1} = {Pi.single 0 1} := by
  ext v
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [show i = 0 from Fin.ext (Nat.lt_one_iff.mp hi)]
    simp [twistVec, twW]
  · rintro rfl
    exact ⟨0, by simp, by simp [twistVec, twW]⟩

theorem isFrameOver_twist {c : Unit → Fin 2} (hc : segreCoord yLine c ≠ 0) :
    IsFrameOver yLine (twistBundle (segreCoord yLine)) c 1 (twistVec (segreCoord yLine) c) :=
  ⟨hc, one_mem _, one_ne_zero, twistVec_linearIndependent hc, twist_frame_iff hc⟩

theorem isSubbundle_twist : IsSubbundle yLine (twistBundle (segreCoord yLine)) lineF 1 := by
  intro c hc
  refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp, fun _ _ => ?_⟩
  refine ⟨twistVec (segreCoord yLine) c, isFrameOver_twist hc, ?_⟩
  rw [twistVec_image]
  rfl

def twistDataHodge : ComponentDataHodge II Unit Unit (PBlk 2) Ω (fun _ => Fin 2 → Ω) where
  toComponentData := twistData II hII
  F _ := lineF
  hodge _ := isSubbundle_twist

theorem ιMulti_const_smul {K M : Type*} [Field K] [AddCommGroup M] [Module K M] (n : ℕ) (r : K) (v : M) :
    exteriorPower.ιMulti K n (fun _ => r • v) = r ^ n • exteriorPower.ιMulti K n (fun _ => v) := by
  have h := AlternatingMap.map_smul_univ (exteriorPower.ιMulti K n) (fun _ => r) (fun _ => v)
  simpa [Finset.prod_const] using h

theorem tprod_unit_scale {K M : Type*} [Field K] [AddCommGroup M] [Module K M] (x : K) (hx : x ≠ 0) (v : M) :
    PiTensorProduct.tprod K (fun _ : Unit => v) =
      (1 * x) • PiTensorProduct.tprod K (fun _ : Unit => (x⁻¹) ^ (2 - 1) • v) := by
  have h := MultilinearMap.map_smul_univ (PiTensorProduct.tprod K (s := fun _ : Unit => M))
    (fun _ => (x⁻¹) ^ (2 - 1)) (fun _ => v)
  simp only [Finset.univ_unique, Finset.prod_singleton] at h
  rw [h, smul_smul]
  norm_num [hx]

set_option synthInstance.maxHeartbeats 400000 in

theorem tprod_unit_scale' {K M : Type*} [Field K] [AddCommGroup M] [Module K M] (x y : K) (hxy : y = x)
    (hx : x ≠ 0) (v w : M) (hw : w = (x⁻¹) ^ (2 - 1) • v) :
    PiTensorProduct.tprod K (fun _ : Unit => v) = (1 * y) • PiTensorProduct.tprod K (fun _ : Unit => w) := by
  subst hxy
  subst hw
  exact tprod_unit_scale y hx v

def eBar : ⋀[Ω]^(2 - 1) ((Fin 2 → Ω) ⧸ lineF) := exteriorPower.ιMulti Ω (2 - 1) fun _ => lineF.mkQ (Pi.single 1 1)

set_option synthInstance.maxHeartbeats 400000 in
theorem quotWedge_twist (c : Unit → Fin 2) (hj : 1 ≤ 2) :
    quotWedge lineF hj (twistVec (segreCoord yLine) c) = (segreCoord yLine c)⁻¹ ^ (2 - 1) • eBar := by
  have hv : ∀ a : Fin (2 - 1), lineF.mkQ (twistVec (segreCoord yLine) c (tailIdx hj a)) =
      (segreCoord yLine c)⁻¹ • lineF.mkQ (Pi.single 1 1) := by
    intro a
    have ha : tailIdx hj a = 1 := Fin.ext (by have := a.isLt; simp only [tailIdx]; omega)
    rw [ha, twistVec, twW, if_neg (by decide), map_smul]
  unfold quotWedge eBar
  rw [← ιMulti_const_smul]
  congr 1
  funext a
  exact hv a

theorem headIdx_range (c : Unit → Fin 2) (hj : 1 ≤ 2) :
    Set.range (twistVec (segreCoord yLine) c ∘ headIdx hj) = {Pi.single 0 1} := by
  ext v
  simp only [Set.mem_range, Function.comp_apply, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, rfl⟩
    rw [Fin.fin_one_eq_zero a]
    simp [headIdx, twistVec, twW]
  · rintro rfl
    exact ⟨0, by simp [headIdx, twistVec, twW]⟩

set_option synthInstance.maxHeartbeats 400000 in
theorem twistMu_eq (c : Unit → Fin 2) (hc : segreCoord yLine c ≠ 0) :
    (PiTensorProduct.tprod Ω fun _ : Unit => eBar) = (1 * chartMono yLine c 1) •
      PiTensorProduct.tprod Ω fun _ : Unit => quotWedge lineF (show 1 ≤ 2 by decide) (twistVec (segreCoord yLine) c) := by
  have hx : chartMono yLine c 1 = segreCoord yLine c := by
    simp [chartMono, segreCoord]
  exact tprod_unit_scale' _ _ hx hc eBar _ (quotWedge_twist c _)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

def twistMu : HodgeData (twistData II hII) where
  F _ := lineF
  aMu := 1
  Λ := PiTensorProduct.tprod Ω fun _ => eBar
  locally c hc := by
    refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp, fun _ => ?_⟩
    refine ⟨fun _ => twistVec (segreCoord yLine) c, fun _ => ⟨isFrameOver_twist hc, twistVec_span hc, ?_⟩,
      1, isUnitOn_one _ _ _, ?_⟩
    · show Submodule.span Ω (Set.range (twistVec (segreCoord yLine) c ∘ headIdx (show 1 ≤ 2 by decide))) = lineF
      rw [headIdx_range]
      rfl
    · exact twistMu_eq c hc

def lineFuller : FullerData II Unit Unit (PBlk 2) Ω (fun _ => Fin 2 → Ω) Gauss.Em where
  toComponentDataHodge := twistDataHodge II hII
  herm := Gauss.gaussDatum
  per _ _ := 1
  per_witt _ _ _ := Gauss.gauss_signature
  per_torus _ _ _ := rfl
  nStrata := 0
  stratum := Fin.elim0
  stratum_sub s := s.elim0
  stratum_cover _ h := absurd h (Set.notMem_empty _)
  stratum_torus s := s.elim0
  torLat := Fin.elim0
  torLat_le s := s.elim0
  torLat_ne s := s.elim0
  torLat_iso s := s.elim0
  torLat_sat s := s.elim0
  nz_near s := s.elim0
  mu := twistMu II hII
  mu_F _ := rfl
  htLat _ _ := twistBundle (segreCoord yLine)
  ht_away _ h := absurd h (Finset.notMem_empty _)

def lineFullerZero : FullerData zeroSystem Unit Unit (PBlk 2) Ω (fun _ => Fin 2 → Ω) Gauss.Em :=
  lineFuller zeroSystem fun _ _ => le_rfl

theorem lineFuller_n : (lineFuller II hII).n = 1 := rfl

theorem lineFuller_aMu : (lineFuller II hII).mu.aMu = 1 := rfl

theorem lineFuller_cuspU (z : (Σ _ : Unit, Fin 2) → ℂ) : (lineFuller II hII).cuspU z = 0 := by
  simp [FullerData.cuspU, lineFuller, Real.iSup_of_isEmpty]

end LineFuller

end GroundTheory.Heights₂.Heights.NineStatements
