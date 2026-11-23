import Formalism.SharpRestriction.CuspSpanNormBounds.RadialGaugeOfGaugeIdentitySlices
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointnessPolynomiallyBounded
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CmHalfIntegralGeneratorMemAlgebraicClosure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.FormalDegreeBessel.FinalBF
import Formalism.FormalDegreeBessel.FinalG

section PartHU

open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.B2x1

variable {k r : ℕ}

theorem hu_pull_sigmaFinite {U : Set (Mat k r)} (hU : IsClosedSubgroup U) (μ : Measure (Mt k r)) [SigmaFinite μ] :
    SigmaFinite (pull hU μ) := by
  refine (Measure.FiniteSpanningSetsIn.sigmaFinite (C := Set.univ)
    ⟨fun n => (inc : Gp U hU → Mt k r) ⁻¹' spanningSets μ n, fun _ => trivial, fun n => ?_, ?_⟩)
  · rw [pull, inc_memb.comap_apply]
    exact lt_of_le_of_lt (measure_mono (Set.image_preimage_subset _ _)) (measure_spanningSets_lt_top μ n)
  · rw [← Set.preimage_iUnion, iUnion_spanningSets, Set.preimage_univ]

theorem hu_smul {U : Set (Mat k r)} {ν : Measure (Mt k r)} (h : Formalism.FourierDecayAlt.B.IsHaarOn U ν) {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc1 : c ≠ ∞) : Formalism.FourierDecayAlt.B.IsHaarOn U (c • ν) where
  conc := by simp [h.conc]
  left := fun a ha => by rw [Measure.map_smul, h.left a ha]
  right := fun a ha => by rw [Measure.map_smul, h.right a ha]
  finite_compact := fun K hK => by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc1) (h.finite_compact K hK)
  ne_zero := by
    intro h0
    apply h.ne_zero
    ext s _
    have := congrArg (fun m : Measure (Mt k r) => m s) h0
    simp only [Measure.smul_apply, Measure.coe_zero, Pi.zero_apply, smul_eq_mul, mul_eq_zero] at this
    rcases this with h1 | h1
    · exact absurd h1 hc0
    · simpa using h1

theorem hu_eq_smul {U : Set (Mat k r)} (hU : IsClosedSubgroup U) {ν μ : Measure (Mt k r)}
    (hν : Formalism.FourierDecayAlt.B.IsHaarOn U ν) (hμ : Formalism.MainNotions.S.IsHaarOn U μ) : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ = c • ν := by
  obtain ⟨hσ, h0, hc, hl⟩ := hμ
  have hc' : μ Uᶜ = 0 := hc
  have : SigmaFinite ν := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hν
  have i1 : SigmaFinite (pull hU μ) := hu_pull_sigmaFinite hU μ
  have i2 : SigmaFinite (pull hU ν) := hu_pull_sigmaFinite hU ν
  have i3 : (pull hU μ).IsMulLeftInvariant := pull_left μ hl
  have i4 : (pull hU ν).IsMulLeftInvariant := pull_left ν hν.left
  have i5 : IsFiniteMeasureOnCompacts (pull hU ν) := pull_fin ν hν.finite_compact
  have hν0 : pull hU ν ≠ 0 := by
    intro h
    apply hν.ne_zero
    rw [← map_pull (hU := hU) ν hν.conc, h, Measure.map_zero]
  have hμ0 : pull hU μ ≠ 0 := by
    intro h
    apply h0
    rw [← map_pull (hU := hU) μ hc', h, Measure.map_zero]
  obtain ⟨K, hK, hK0⟩ := exists_pos (pull hU ν) hν0
  have hKt : pull hU ν K ≠ ∞ := hK.measure_lt_top.ne
  have key := measure_eq_div_smul (pull hU μ) (pull hU ν) hK0 hKt
  set c : ℝ≥0∞ := pull hU μ K / pull hU ν K with hcdef
  have hc0 : c ≠ 0 := by
    intro h
    apply hμ0
    rw [key, h, zero_smul]
  have hc1 : c ≠ ∞ := by
    intro h
    obtain ⟨n, hn⟩ := exists_pos_measure_of_cover (iUnion_spanningSets (pull hU μ)) hμ0
    have hfin := measure_spanningSets_lt_top (pull hU μ) n
    have e0 : ∀ s : Set (Gp U hU), pull hU μ s = ∞ * pull hU ν s := by
      intro s
      have := congrArg (fun m : Measure (Gp U hU) => m s) key
      simpa only [Measure.smul_apply, smul_eq_mul, h] using this
    have e := e0 (spanningSets (pull hU μ) n)
    by_cases hz : pull hU ν (spanningSets (pull hU μ) n) = 0
    · rw [e, hz, mul_zero] at hn
      exact lt_irrefl _ hn
    · rw [e, ENNReal.top_mul hz] at hfin
      exact lt_irrefl _ hfin
  refine ⟨c, hc0, hc1, ?_⟩
  calc μ = (pull hU μ).map inc := (map_pull μ hc').symm
    _ = (c • pull hU ν).map inc := by rw [← key]
    _ = c • ν := by rw [Measure.map_smul, map_pull ν hν.conc]

theorem hu_general {U : Set (Mat k r)} (hU : IsClosedSubgroup U) {ν μ : Measure (Mt k r)}
    (hν : Formalism.FourierDecayAlt.B.IsHaarOn U ν) (hμ : Formalism.MainNotions.S.IsHaarOn U μ) : Formalism.FourierDecayAlt.B.IsHaarOn U μ := by
  obtain ⟨c, hc0, hc1, rfl⟩ := hu_eq_smul hU hν hμ
  exact hu_smul hν hc0 hc1

theorem hu_haarUp :
    (∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ : Measure (Mt k r)), inWb k r z → 0 < Tz k r z →
      Formalism.MainNotions.S.IsHaarOn (UWset k r z) μ → Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) μ) ∧
    ∀ (k r : ℕ) (μ : Measure (Mt k r)), Formalism.MainNotions.S.IsHaarOn (Nset k r) μ → Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μ := by
  refine ⟨fun k r z μ hz hT hμ => ?_, fun k r μ hμ => ?_⟩
  · obtain ⟨ν, hν⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z hz hT
    exact hu_general (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) hν hμ
  · obtain ⟨ν, hν⟩ := Formalism.FourierDecayAlt.P.unipotent_haar_exists k r
    exact hu_general (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) hν hμ

theorem hu_haarG (k r : ℕ) (μ : Measure (Mt k r)) (hμ : Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μ) :
    Formalism.FourierDecayAlt.B.IsHaarOn (GV k r) μ := by
  obtain ⟨ν, hν⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  exact hu_general (Formalism.FourierDecayAlt.P.unitary_group_closed k r) hν hμ

end Formalism.MainNotions.BridgeLemma₃

end

end PartHU

section PartRP

open Matrix

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.QuantumDeterminants Formalism.MainNotions.S

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section aux

variable {k r : ℕ}

def rp_Mid (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val < r + k

def rp_ι (k r : ℕ) (i : Fin k) : Fin (2 * r + k + 1) := ⟨r + i.val, by have := i.2; omega⟩

def rp_blk (k r : ℕ) (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => m (rp_ι k r i) (rp_ι k r j)

def rp_Std (k r : ℕ) (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ i, ¬ rp_Mid k r i → (∀ j, m i j = if i = j then 1 else 0) ∧ (∀ j, m j i = if j = i then 1 else 0)

theorem rp_mid_ι (i : Fin k) : rp_Mid k r (rp_ι k r i) := by
  have := i.2
  constructor <;> simp only [rp_ι] <;> omega

theorem rp_ι_inj : Function.Injective (rp_ι k r) := fun a b hab =>
  Fin.ext (by have := congrArg Fin.val hab; simpa [rp_ι] using this)

theorem rp_eq_blockW (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (h : rp_Std k r m) :
    m = blockW k r (rp_blk k r m) := by
  ext i j
  unfold blockW
  by_cases hi : r ≤ i.val ∧ i.val < r + k
  · rw [dif_pos hi]
    by_cases hj : r ≤ j.val ∧ j.val < r + k
    · rw [dif_pos hj]
      have e1 : rp_ι k r ⟨i.val - r, by omega⟩ = i := Fin.ext (by simp only [rp_ι]; omega)
      have e2 : rp_ι k r ⟨j.val - r, by omega⟩ = j := Fin.ext (by simp only [rp_ι]; omega)
      simp only [rp_blk, e1, e2]
    · rw [dif_neg hj, (h j hj).2 i, if_neg]
      rintro rfl
      exact hj hi
  · rw [dif_neg hi, (h i hi).1 j]

theorem rp_sum (f : Fin (2 * r + k + 1) → ℂ) (h : ∀ l, ¬ rp_Mid k r l → f l = 0) :
    ∑ l, f l = ∑ i, f (rp_ι k r i) := by
  symm
  refine Fintype.sum_of_injective (rp_ι k r) rp_ι_inj _ _ ?_ (fun _ => rfl)
  intro l hl
  apply h
  intro hm
  exact hl ⟨⟨l.val - r, by have := hm.2; have := hm.1; omega⟩, Fin.ext (by simp only [rp_ι]; have := hm.1; omega)⟩

theorem rp_blk_mul (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ha : rp_Std k r a) :
    rp_blk k r (a * b) = rp_blk k r a * rp_blk k r b := by
  ext i j
  simp only [rp_blk, Matrix.mul_apply]
  refine rp_sum _ fun l hl => ?_
  rw [(ha l hl).2 (rp_ι k r i), if_neg, zero_mul]
  rintro rfl
  exact hl (rp_mid_ι i)

theorem rp_blk_one : rp_blk k r 1 = 1 := by
  ext i j
  simp only [rp_blk, Matrix.one_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun e => h (rp_ι_inj e))]

theorem rp_mulVec_bvec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) : M *ᵥ bvec c = fun i => M i c := by
  ext i
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem rp_col {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) (h : g *ᵥ bvec c = bvec c) (l : Fin n) :
    g l c = if l = c then 1 else 0 := by
  have e := congrFun h l
  rw [rp_mulVec_bvec] at e
  simpa [bvec, Pi.single_apply] using e

theorem rp_rowOf {n : ℕ} (m H : Matrix (Fin n) (Fin n) ℂ) (hm : mᴴ * H * m = H) (c i : Fin n) (s : ℂ) (hs : s ≠ 0)
    (hc : m *ᵥ bvec c = bvec c) (hH : H *ᵥ bvec c = s • bvec i) (j : Fin n) : m i j = if i = j then 1 else 0 := by
  have h1 : mᴴ *ᵥ (H *ᵥ (m *ᵥ bvec c)) = H *ᵥ bvec c := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm]
  rw [hc, hH, Matrix.mulVec_smul] at h1
  have h2 : mᴴ *ᵥ bvec i = bvec i := smul_right_injective _ hs h1
  have h3 := rp_col mᴴ i h2 j
  rw [Matrix.conjTranspose_apply] at h3
  have h4 := congrArg star h3
  rw [star_star] at h4
  rw [h4]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos hij.symm, star_one]
  · rw [if_neg hij, if_neg (fun e => hij e.symm), star_zero]

theorem rp_H_e (a : Fin r) : Hpk k r *ᵥ bvec (eI k r a) = (1 : ℂ) • bvec (esI k r a) := by
  rw [rp_mulVec_bvec]
  ext i
  have := a.2
  have := i.2
  simp only [Hpk, esI, eI, bvec, Pi.smul_apply, Pi.single_apply, Fin.ext_iff, smul_eq_mul, one_mul]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem rp_H_es (a : Fin r) : Hpk k r *ᵥ bvec (esI k r a) = (1 : ℂ) • bvec (eI k r a) := by
  rw [rp_mulVec_bvec]
  ext i
  have := a.2
  have := i.2
  simp only [Hpk, esI, eI, bvec, Pi.smul_apply, Pi.single_apply, Fin.ext_iff, smul_eq_mul, one_mul]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem rp_H_w : Hpk k r *ᵥ bvec (wI k r (Fin.last k)) = (-1 : ℂ) • bvec (wI k r (Fin.last k)) := by
  rw [rp_mulVec_bvec]
  ext i
  have := i.2
  simp only [Hpk, wI, bvec, Pi.smul_apply, Pi.single_apply, Fin.ext_iff, smul_eq_mul, Fin.val_last]
  split_ifs <;> first | rfl | (exfalso; omega) | simp

theorem rp_H_mid (i : Fin (2 * r + k + 1)) (hi : rp_Mid k r i) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if i = j then 1 else 0 := by
  have := i.2
  have := j.2
  obtain ⟨h1, h2⟩ := hi
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem rp_std_of_fix (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hU : m ∈ UH (Hpk k r))
    (hfix : ∀ a : Fin r, m *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ m *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (hw : m *ᵥ bvec (wI k r (Fin.last k)) = bvec (wI k r (Fin.last k))) : rp_Std k r m := by
  intro i hi
  have hi2 := i.2
  have hcase : i.val < r ∨ i.val = r + k ∨ r + k < i.val := by
    unfold rp_Mid at hi
    omega
  rcases hcase with h | h | h
  · obtain ⟨a, rfl⟩ : ∃ a, i = eI k r a := ⟨⟨i.val, h⟩, rfl⟩
    exact ⟨fun j => rp_rowOf m _ hU (esI k r a) _ 1 one_ne_zero (hfix a).2 (rp_H_es a) j,
      fun j => rp_col m _ (hfix a).1 j⟩
  · obtain rfl : i = wI k r (Fin.last k) := Fin.ext (by simp only [wI, Fin.val_last]; omega)
    exact ⟨fun j => rp_rowOf m _ hU _ _ (-1) (by norm_num) hw rp_H_w j, fun j => rp_col m _ hw j⟩
  · obtain ⟨a, rfl⟩ : ∃ a, i = esI k r a :=
      ⟨⟨2 * r + k - i.val, by omega⟩, Fin.ext (by simp only [esI]; omega)⟩
    exact ⟨fun j => rp_rowOf m _ hU (eI k r a) _ 1 one_ne_zero (hfix a).1 (rp_H_e a) j,
      fun j => rp_col m _ (hfix a).2 j⟩

theorem rp_blk_unitary (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hU : m ∈ UH (Hpk k r))
    (hs : rp_Std k r m) : (rp_blk k r m)ᴴ * rp_blk k r m = 1 := by
  ext i j
  have e := congrFun (congrFun (show mᴴ * Hpk k r * m = Hpk k r from hU) (rp_ι k r i)) (rp_ι k r j)
  rw [Matrix.mul_assoc, Matrix.mul_apply, rp_H_mid _ (rp_mid_ι i)] at e
  have e2 : ∑ l, mᴴ (rp_ι k r i) l * (Hpk k r * m) l (rp_ι k r j) =
      ∑ a, mᴴ (rp_ι k r i) (rp_ι k r a) * (Hpk k r * m) (rp_ι k r a) (rp_ι k r j) :=
    rp_sum _ fun l hl => by
      rw [Matrix.conjTranspose_apply, (hs l hl).1 (rp_ι k r i), if_neg, star_zero, zero_mul]
      rintro rfl
      exact hl (rp_mid_ι i)
  have e3 : ∀ a, (Hpk k r * m) (rp_ι k r a) (rp_ι k r j) = m (rp_ι k r a) (rp_ι k r j) := by
    intro a
    rw [Matrix.mul_apply]
    simp only [rp_H_mid _ (rp_mid_ι a), ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [e2] at e
  simp only [e3] at e
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, rp_blk, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply] at e
  rw [e]
  by_cases h : i = j
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun e => h (rp_ι_inj e))]

theorem rp_blk_mem (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hU : m ∈ UH (Hpk k r))
    (hs : rp_Std k r m) : rp_blk k r m ∈ UJset (allPos k) := by
  have hJ : Formalism.REAL.Jm (allPos k) = 1 := by
    simp [Formalism.REAL.Jm, allPos]
  show (rp_blk k r m)ᴴ * Formalism.REAL.Jm (allPos k) * rp_blk k r m = Formalism.REAL.Jm (allPos k)
  rw [hJ, Matrix.mul_one, rp_blk_unitary m hU hs]

end aux

theorem rp_repOfHC :
    ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)), inWb k r z → 0 < Tz k r z →
      Formalism.MainNotions.S.IsHCTypeW k r z u π →
        IsCRepOn (UWset k r z) π ∧ (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) ∧ ContinuousOn π (UWset k r z) := by
  intro k r z u H _ _ π _ hT hπ0
  obtain ⟨g, ⟨hgU, hgfix, hgz⟩, -, hfd, ⟨⟨hσ1, hσm⟩, hσi, hσc⟩, -⟩ := hπ0
  have hsq : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  have hdet : IsUnit (Hpk k r).det := (Matrix.isUnit_iff_isUnit_det _).mp ⟨⟨Hpk k r, Hpk k r, hsq, hsq⟩, rfl⟩
  obtain ⟨hone, hmul, hinv⟩ := uHGroup _ (Hpk k r) hdet
  obtain ⟨hgdet, hgi⟩ := hinv g hgU
  have hgg : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hgdet
  have hgg' : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hgdet
  have hfixv : ∀ (h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ),
      h *ᵥ (g *ᵥ v) = g *ᵥ v → (g⁻¹ * h * g) *ᵥ v = v := by
    intro h v hv
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
  have hs0 : ((Real.sqrt (Tz k r z) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hT).ne'
  have key : ∀ h ∈ UWset k r z, (g⁻¹ * h * g) ∈ UH (Hpk k r) ∧ rp_Std k r (g⁻¹ * h * g) := by
    intro h hh
    obtain ⟨hhU, hhfix, hhz⟩ := hh
    have hU : (g⁻¹ * h * g) ∈ UH (Hpk k r) := hmul _ (hmul _ hgi _ hhU) _ hgU
    refine ⟨hU, rp_std_of_fix _ hU (fun a => ⟨?_, ?_⟩) ?_⟩
    · exact hfixv h _ (by rw [(hgfix a).1]; exact (hhfix a).1)
    · exact hfixv h _ (by rw [(hgfix a).2]; exact (hhfix a).2)
    · have h1 := hfixv h _ (by rw [hgz]; exact hhz)
      rw [Matrix.mulVec_smul] at h1
      exact smul_right_injective _ hs0 h1
  have hback : ∀ h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, g * (g⁻¹ * h * g) * g⁻¹ = h := by
    intro h
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hgg', Matrix.one_mul, Matrix.mul_assoc, hgg', Matrix.mul_one]
  have hπ : ∀ h ∈ UWset k r z, π h = π (g * blockW k r (rp_blk k r (g⁻¹ * h * g)) * g⁻¹) := by
    intro h hh
    rw [← rp_eq_blockW _ (key h hh).2, hback]
  have hmem : ∀ h ∈ UWset k r z, rp_blk k r (g⁻¹ * h * g) ∈ UJset (allPos k) := fun h hh =>
    rp_blk_mem _ (key h hh).1 (key h hh).2
  have h1mem : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z :=
    ⟨hone, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hπ 1 h1mem, Matrix.mul_one, hgg, rp_blk_one]
    exact hσ1
  · intro a ha b hb
    have hab : a * b ∈ UWset k r z := by
      refine ⟨hmul _ ha.1 _ hb.1, fun c => ⟨?_, ?_⟩, ?_⟩
      · rw [← Matrix.mulVec_mulVec, (hb.2.1 c).1, (ha.2.1 c).1]
      · rw [← Matrix.mulVec_mulVec, (hb.2.1 c).2, (ha.2.1 c).2]
      · rw [← Matrix.mulVec_mulVec, hb.2.2, ha.2.2]
    have hsplit : g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by
      have : (g⁻¹ * a * g) * (g⁻¹ * b * g) = g⁻¹ * a * (g * g⁻¹) * b * g := by
        simp only [Matrix.mul_assoc]
      rw [this, hgg', Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    rw [hπ _ hab, hπ a ha, hπ b hb, hsplit, rp_blk_mul _ _ (key a ha).2]
    exact hσm _ (hmem a ha) _ (hmem b hb)
  · intro h hh v
    rw [hπ h hh]
    exact hσi _ (hmem h hh) v
  · have := hfd
    have hσC : ContinuousOn (fun x => π (g * blockW k r x * g⁻¹)) (UJset (allPos k)) :=
      continuousOn_clm_apply.2 hσc
    have hb : Continuous fun h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => rp_blk k r (g⁻¹ * h * g) := by
      refine continuous_matrix fun i j => ?_
      exact ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_elem _ _
    exact (hσC.comp hb.continuousOn hmem).congr hπ

end Formalism.MainNotions.BridgeLemma₃

end PartRP

section PartCal

open Matrix Filter Topology

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

abbrev cal_Ix (k r : ℕ) := Fin (2 * r + k + 1) × Fin (2 * r + k + 1)

def cal_Ew (w : List (cal_Ix k r)) (f : Mat k r → E) : Mat k r → E :=
  w.foldr (fun ab h => EabH (Hpk k r) ab.1 ab.2 h) f

def hermitianRealPartUnit (ab : cal_Ix k r) : Mat k r := hpart1 (Hpk k r) (Matrix.single ab.1 ab.2 1)
def hermitianImagPartUnit (ab : cal_Ix k r) : Mat k r := hpart2 (Hpk k r) (Matrix.single ab.1 ab.2 1)

def cal_mn (X : Mat k r) : ℝ := ∑ ab : cal_Ix k r, ‖X ab.1 ab.2‖

def cal_exp : List (Mat k r) → List (ℂ × List (cal_Ix k r))
  | [] => [(1, [])]
  | X :: v => (Finset.univ : Finset (cal_Ix k r)).toList.flatMap fun ab =>
      (cal_exp v).map fun cw => (X ab.1 ab.2 * cw.1, ab :: cw.2)

def cal_expE : List (cal_Ix k r) → List (ℂ × List (Mat k r))
  | [] => [(1, [])]
  | ab :: w => ((cal_expE w).map fun cv => (cv.1, hermitianRealPartUnit ab :: cv.2)) ++
      ((cal_expE w).map fun cv => (Complex.I * cv.1, hermitianImagPartUnit ab :: cv.2))

theorem cal_Hh : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
theorem cal_HH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
theorem cal_Hinv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_right_inv cal_HH

theorem cal_twoI : (1 / (2 * Complex.I) : ℂ) = -(Complex.I / 2) := by
  rw [eq_comm, eq_div_iff (mul_ne_zero two_ne_zero Complex.I_ne_zero)]
  linear_combination (-1 : ℂ) * Complex.I_sq

theorem cal_hpart1_lie (Z : Mat k r) : inLie k r (hpart1 (Hpk k r) Z) := by
  unfold inLie hpart1
  rw [cal_Hinv, conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    cal_Hh, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub]
  have e1 : Hpk k r * (Z * Hpk k r) * Hpk k r = Hpk k r * Z := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, cal_HH, Matrix.mul_one]
  have e2 : Hpk k r * (Hpk k r * Zᴴ * Hpk k r) = Zᴴ * Hpk k r := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc, cal_HH, Matrix.one_mul]
  rw [e1, e2]
  have : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [this, ← smul_add]
  simp

theorem cal_hpart2_lie (Z : Mat k r) : inLie k r (hpart2 (Hpk k r) Z) := by
  unfold inLie hpart2
  rw [cal_twoI, cal_Hinv, conjTranspose_smul, conjTranspose_add, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_conjTranspose, cal_Hh, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add]
  have e1 : Hpk k r * (Z * Hpk k r) * Hpk k r = Hpk k r * Z := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, cal_HH, Matrix.mul_one]
  have e2 : Hpk k r * (Hpk k r * Zᴴ * Hpk k r) = Zᴴ * Hpk k r := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc, cal_HH, Matrix.one_mul]
  rw [e1, e2]
  have : star (-(Complex.I / 2) : ℂ) = Complex.I / 2 := by
    simp [Complex.conj_I]
    ring
  rw [this, neg_smul, add_comm (Hpk k r * Z)]
  simp

theorem hermitian_real_part_index_lie (ab : cal_Ix k r) : inLie k r (hermitianRealPartUnit ab) := cal_hpart1_lie _
theorem hermitian_imag_part_index_lie (ab : cal_Ix k r) : inLie k r (hermitianImagPartUnit ab) := cal_hpart2_lie _

theorem cal_expE_lie (w : List (cal_Ix k r)) : ∀ cv ∈ cal_expE w, ∀ X ∈ cv.2, inLie k r X := by
  induction w with
  | nil => intro cv h; simp [cal_expE] at h; simp [h]
  | cons ab w ih =>
    intro cv h X hX
    simp only [cal_expE, List.mem_append, List.mem_map] at h
    rcases h with ⟨cv', h', rfl⟩ | ⟨cv', h', rfl⟩
    · rcases List.mem_cons.1 hX with rfl | hX
      · exact hermitian_real_part_index_lie ab
      · exact ih cv' h' X hX
    · rcases List.mem_cons.1 hX with rfl | hX
      · exact hermitian_imag_part_index_lie ab
      · exact ih cv' h' X hX

end Formalism.MainNotions.BridgeLemma₃

end

end PartCal

section PartCal2

open Matrix Filter Topology

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P

section Frob

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace Matrix.frobeniusNormedRing

end Frob

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

end Formalism.MainNotions.BridgeLemma₃

end

end PartCal2

section PartCCI

open Matrix Filter Topology

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P Formalism.MainNotions.S.TopsChoicePartA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.MainNotions.BridgeLemma₃

end

end PartCCI

section PartAdj0

open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cls

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def CCl (l : ℕ) (A : ℝ) (m : ℕ) (F : Mat k r → E) (c : ℝ) : Prop :=
  CkOn (m : ℕ∞) (GV k r) F ∧
  ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → u.length ≤ l → u.length + v.length ≤ m →
    ∀ g ∈ GV k r, gN g ^ A * ‖dLR u v F g‖ ≤ c

def InCCl (l : ℕ) (A : ℝ) (m : ℕ) (F : Mat k r → E) : Prop := ∃ c, CCl l A m F c

end cls

section poly

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def PolyCoefl (D : RealPlaceData k r Wp Wq) (l : ℕ) (ε d : ℝ) (m : ℕ) (Θ : DiffOp k r Wp Wq) : Prop :=
  ∀ T ∈ Θ, ∃ C : ℝ, ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → u.length ≤ l →
    u.length + v.length ≤ m → ∀ g ∈ GV k r, ε ≤ Gf k r D.z D.z' g →
      ‖dLR u v T.coef g‖ ≤ C * gN g ^ d ∧ ‖dLR u v T.coefAdj g‖ ≤ C * gN g ^ d

end poly

open Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

def AAdegS (L : Lev) (ε Dg : ℝ) (d : ℕ) (Θ : L.GF → L.GF) : Prop :=
  ∃ (N : ℕ) (ws : Fin N → List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1)))
    (a : Fin N → TopsChoicePartA.Mat L.k0 L.r → (L.Hom →L[ℂ] L.Hom)),
    (∀ j, (ws j).length ≤ d) ∧
    (∀ j, ∃ U : Set (TopsChoicePartA.Mat L.k0 L.r), IsOpen U ∧
      UH (Hpk (L.k0 + 1) L.r) ∩ {g | 0 < Gf (L.k0 + 1) L.r L.z L.z' g} ⊆ U ∧ ContDiffOn ℝ ∞ (a j) U) ∧
    (∀ j, ∀ w : List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1)), w.length ≤ d + 5 →
      ∃ C : ℝ, ∀ g ∈ UH (Hpk (L.k0 + 1) L.r), ε ≤ Gf (L.k0 + 1) L.r L.z L.z' g →
        ‖L.EwordV w (a j) g‖ ≤ C * (1 + Lev.matNorm g) ^ Dg) ∧
    ∀ F : L.GF, SmoothOnH (Hpk (L.k0 + 1) L.r) F → ∀ g ∈ UH (Hpk (L.k0 + 1) L.r),
      0 < Gf (L.k0 + 1) L.r L.z L.z' g → Θ F g = ∑ j, a j g (L.Eword (ws j) F g)

def LemmaBAdjS (CB : ℝ) : Prop :=
  ∀ L : Lev, L.Std → ∀ u u', L.HC u u' → ∀ μG : Measure (Mt (L.k0 + 1) L.r), Formalism.MainNotions.S.IsHaarOn (UH (Hpk (L.k0 + 1) L.r)) μG →
    ∀ Θ Θs : L.GF → L.GF, Θ ∈ L.AA → Θs ∈ L.AA →
      (∀ F F' : L.GF, SmoothOnH (Hpk (L.k0 + 1) L.r) F → SmoothOnH (Hpk (L.k0 + 1) L.r) F' →
        HasCompactSupport F → HasCompactSupport F' → (∃ ε : ℝ, 0 < ε ∧ SuppGe L ε F ∧ SuppGe L ε F') →
        ∫ x, Formalism.MainNotions.S.hsInner (Θ F (Matrix.of x)) (F' (Matrix.of x)) ∂μG =
          ∫ x, Formalism.MainNotions.S.hsInner (F (Matrix.of x)) (Θs F' (Matrix.of x)) ∂μG) →
    ∀ (ε Dg : ℝ) (d : ℕ), 0 < ε → 0 ≤ Dg → AAdegS L ε Dg d Θ → AAdegS L ε Dg d Θs →
    ∀ (A : ℝ) (mm : ℕ), Big CB L 0 A mm → ∀ h : L.Haar, h.Ok →
      ∀ F F' : L.GF, SmoothOnH (Hpk (L.k0 + 1) L.r) F → SmoothOnH (Hpk (L.k0 + 1) L.r) F' →
        L.CC (A + Dg) (mm + d) F → L.CC (A + Dg) (mm + d) F' → SuppGe L ε F → SuppGe L ε F' →
        lbeta L h (Θ F) F' = lbeta L h F (Θs F')

end Formalism.MainNotions.BridgeLemma₃

end

end PartAdj0

section PartAdj1

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

section partA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end partA

section partB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end partB

section partC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end partC

end Formalism.MainNotions.BridgeLemma₃

end

end PartAdj1

section PartAdj2a

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']

def dimensionReal (k r : ℕ) : ℝ := ((2 * r + k + 1 : ℕ) : ℝ)

end Formalism.MainNotions.BridgeLemma₃

end

end PartAdj2a

section PartAdj2b

open Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def hsColumnsInverse : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  ∑ i, (ContinuousLinearMap.smulRightL ℂ Wq Wp (innerSL ℂ (stdOrthonormalBasis ℂ Wq i))).comp
    (PiLp.proj 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) i)

theorem hs_columns_inverse_apply (y : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) (x : Wq) :
    hsColumnsInverse y x = ∑ i, ⟪stdOrthonormalBasis ℂ Wq i, x⟫_ℂ • y i := by
  simp [hsColumnsInverse]

theorem hs_columns_inverse_left_inv (A : Wq →L[ℂ] Wp) : hsColumnsInverse (hsVec A) = A := by
  ext x
  rw [hs_columns_inverse_apply]
  conv_rhs => rw [← (stdOrthonormalBasis ℂ Wq).sum_repr' x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  rfl

theorem hs_columns_right_inv (y : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) : hsVec (hsColumnsInverse y) = y := by
  ext i
  show hsColumnsInverse y (stdOrthonormalBasis ℂ Wq i) = y i
  rw [hs_columns_inverse_apply]
  have h := (stdOrthonormalBasis ℂ Wq).orthonormal
  simp [orthonormal_iff_ite.1 h]

def hsAdjoint (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  hsColumnsInverse.comp ((ContinuousLinearMap.adjoint ((B5.hsL (Wp := Wp) (Wq := Wq)).comp (T.comp hsColumnsInverse))).comp
    (B5.hsL (Wp := Wp) (Wq := Wq)))

theorem hs_inner_adjoint_identity (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (A B : Wq →L[ℂ] Wp) :
    hsInner (T A) B = hsInner A (hsAdjoint T B) := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  unfold hsInner hsAdjoint
  simp only [ContinuousLinearMap.comp_apply, B5.hsL_apply, hs_columns_right_inv]
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [ContinuousLinearMap.comp_apply, B5.hsL_apply, hs_columns_inverse_left_inv]

theorem hs_adjoint_add (S T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : hsAdjoint (S + T) = hsAdjoint S + hsAdjoint T := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  unfold hsAdjoint
  simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, map_add]

theorem hs_adjoint_real_smul (c : ℝ) (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : hsAdjoint (c • T) = c • hsAdjoint T := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have e : ∀ (X : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)), c • X = (c : ℂ) • X := fun X => by
    ext; simp
  rw [e, e]
  unfold hsAdjoint
  simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, map_smulₛₗ, Complex.conj_ofReal]

def hsAdjointRealLinear : ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) →L[ℝ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :=
  LinearMap.toContinuousLinearMap
    { toFun := hsAdjoint
      map_add' := hs_adjoint_add
      map_smul' := fun c T => by simpa using hs_adjoint_real_smul c T }

end Formalism.MainNotions.BridgeLemma₃

end

end PartAdj2b

section PartAdj2

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section core

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

open Classical in

def wordOperatorTerm (c : ℂ) (a : Mat k r → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))) (v : List (Mat k r)) : DTerm k r Wp Wq where
  coef := fun g => c • a g
  coefAdj := fun g => hsAdjointRealLinear (c • a g)
  word := if (∀ X ∈ v, inLie k r X) then v else []
  word_lie := by
    split_ifs with h
    · exact h
    · simp
  adj_id := fun x A B => hs_inner_adjoint_identity _ A B

def wordOperator {N : ℕ} (ws : Fin N → List (cal_Ix k r)) (a : Fin N → Mat k r → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))) :
    DiffOp k r Wp Wq :=
  (List.finRange N).flatMap fun j => (cal_expE (ws j)).map fun cv => wordOperatorTerm cv.1 (a j) cv.2

end core

section packet

open Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

end packet

end Formalism.MainNotions.BridgeLemma₃

end

end PartAdj2

section PartAdj3

open Matrix MeasureTheory Filter Topology
open scoped ContDiff ENNReal ComplexConjugate

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section gen

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def invariantWordDerivative (w : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (f : Mat k r → E) : Mat k r → E :=
  w.foldr (fun ab f => EabH (Hpk k r) ab.1 ab.2 f) f

end gen

section adj

open Formalism.FourierDecayAlt.P

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end adj

section helpers

open Formalism.FourierDecayAlt.P

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end helpers

section core

open Formalism.FourierDecayAlt.P

variable {k r : ℕ}

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def invariantWordOperator {N : ℕ} (ws : Fin N → List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)))
    (b : Fin N → Mat k r → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    Wq →L[ℂ] Wp :=
  ∑ j, b j g (invariantWordDerivative (ws j) F g)

end core

section core2

open Formalism.FourierDecayAlt.P

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end core2

section core3

open Formalism.FourierDecayAlt.P

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end core3

section packet

open Formalism.FourierDecayAlt.P Formalism.MainNotions.S.TopsChoicePartA

end packet

end Formalism.MainNotions.BridgeLemma₃

end

end PartAdj3

section PartAdj6a

open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end Formalism.MainNotions.BridgeLemma₃

end

end PartAdj6a

section PartCont

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.MainNotions Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.BridgeLemma₅

theorem lbHaarUp_proved : lbHaarUp := hu_haarUp

theorem lbRepOfHC_proved : lbRepOfHC := rp_repOfHC

end Formalism.MainNotions.BridgeLemma₃

end PartCont

section PartAdj6bP

open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.MainNotions.BridgeLemma₃

end

end PartAdj6bP

section PartRad0

open Matrix MeasureTheory Filter Topology
open scoped ContDiff ENNReal ComplexConjugate

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section gen

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def invariantWordDerivativeLocal (w : List (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (f : Mat k r → E) : Mat k r → E :=
  w.foldr (fun ab f => EabH (Hpk k r) ab.1 ab.2 f) f

end gen

section adj

open Formalism.FourierDecayAlt.P

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end adj

section helpers

open Formalism.FourierDecayAlt.P

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end helpers

end Formalism.MainNotions.BridgeLemma₃

end

end PartRad0

section PartRad1

open Matrix MeasureTheory Filter Topology
open scoped ContDiff ENNReal ComplexConjugate

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def rd_Dom (D : RealPlaceData k r Wp Wq) (A : ℝ) (V : Set (Mat k r)) (Φ : SS k r → ℝ) : Prop :=
  Integrable Φ D.μSS ∧ ∀ g ∈ V, g ∈ GV k r → ∀ p, D.inSS p → gN (sgs p g) ^ (-A) ≤ Φ p

def rd_Dec (A c : ℝ) (f : Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  ContinuousOn f (GV k r) ∧ ∀ g ∈ GV k r, gN g ^ A * ‖f g‖ ≤ c

def rd_hsF (B : Wq →L[ℂ] Wp) : (Wq →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ (hsVec B)).comp B5.hsL

end Formalism.MainNotions.BridgeLemma₃

end

end PartRad1

section PartRad2

open Matrix MeasureTheory Filter Topology
open scoped ContDiff ENNReal ComplexConjugate

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end Formalism.MainNotions.BridgeLemma₃

end

end PartRad2

section PartRad3

open Matrix MeasureTheory Filter Topology
open scoped ContDiff ENNReal ComplexConjugate

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def rd_OrbDom (C : ℝ) : Prop :=
  ∀ L : Lev, L.Std → ∀ h : L.Haar, h.Ok → ∀ A : ℝ,
    C * ((L.r : ℝ) + 1) ^ 4 * ((2 * L.r + L.k0 + 2 : ℕ) : ℝ) ^ 3 ≤ A →
    ∀ g₀ ∈ UH (Hpk (L.k0 + 1) L.r), 0 < Gf (L.k0 + 1) L.r L.z L.z' g₀ →
      (∀ l, Dmin (L.k0 + 1) L.r L.z L.z' g₀ l ≠ 0) →
      ∃ (V : Set (TopsChoicePartA.Mat L.k0 L.r)) (Φ : SS (L.k0 + 1) L.r → ℝ), IsOpen V ∧ g₀ ∈ V ∧
        Integrable Φ ((h.μW.prod h.μN).prod (h.μW'.prod h.μN)) ∧
        ∀ g ∈ V, g ∈ UH (Hpk (L.k0 + 1) L.r) → ∀ p : SS (L.k0 + 1) L.r,
          (Matrix.of p.1.1 : TopsChoicePartA.Mat L.k0 L.r) ∈ UWset (L.k0 + 1) L.r L.z →
          (Matrix.of p.1.2 : TopsChoicePartA.Mat L.k0 L.r) ∈ Nset (L.k0 + 1) L.r →
          (Matrix.of p.2.1 : TopsChoicePartA.Mat L.k0 L.r) ∈ UWset (L.k0 + 1) L.r L.z' →
          (Matrix.of p.2.2 : TopsChoicePartA.Mat L.k0 L.r) ∈ Nset (L.k0 + 1) L.r →
          gN ((Matrix.of p.1.1 : TopsChoicePartA.Mat L.k0 L.r)⁻¹ * (Matrix.of p.1.2 : TopsChoicePartA.Mat L.k0 L.r)⁻¹ * g *
            Matrix.of p.2.2 * Matrix.of p.2.1) ^ (-A) ≤ Φ p

end Formalism.MainNotions.BridgeLemma₃

end

end PartRad3

section PartOrb0

open Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def od_GaussEx : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), ∀ g ∈ GV k r,
    (∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' g l ≠ 0) →
    ∃ ν ∈ Nset k r, ∃ ν' ∈ Nset k r, ∃ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
      (∀ a, c a ≠ 0) ∧ μᴴ * Hb k * μ = Hb k ∧ g = ν⁻¹ * bigCell k r c μ * ν'

def od_ColBound : Prop :=
  ∀ (k r : ℕ), ∀ m ∈ Nset k r, ∀ n' ∈ Nset k r, ∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (u : Fin (2 * r + k + 1)) (a : Fin r),
    ‖m u (esI k r a)‖ * ∏ b : Fin r with b.val ≤ a.val, ‖c b‖ ≤
      ((a.val + 1).factorial : ℝ) * gN (m * bigCell k r c μ * n') ^ (a.val + 1)

def od_NBound : Prop :=
  ∀ (k r : ℕ), ∃ K : ℝ, ∀ m ∈ Nset k r, ∀ R : ℝ, 1 ≤ R → (∀ (u : Fin (2 * r + k + 1)) (a : Fin r), ‖m u (esI k r a)‖ ≤ R) →
    gN m ≤ K * R ^ (r + 1)

def od_NInt : Prop :=
  ∀ (k r : ℕ) (μN : Measure (Mt k r)) (B : ℝ), IsHaarOn (Nset k r) μN → AB k r ≤ B →
    (∫⁻ n : Mt k r, ENNReal.ofReal (gN (Matrix.of n) ^ (-B)) ∂μN) < ∞

end Formalism.MainNotions.BridgeLemma₃

end

end PartOrb0

section PartOrbGD

open Matrix MeasureTheory

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def gd_min (k r : ℕ) (g : Mat k r) (l : ℕ) (hl : l ≤ r) : ℂ :=
  (Matrix.of fun a b : Fin l => g (esI k r ⟨a.val, by omega⟩) (eI k r ⟨b.val, by omega⟩)).det

section step

variable (k r' : ℕ) (c : ℂ) (g₁ : Mat k r')

end step

def gd_P (k r : ℕ) : Prop :=
  ∀ g ∈ GV k r, (∀ (l : ℕ) (hl : l ≤ r), gd_min k r g l hl ≠ 0) →
    ∃ ν ∈ Nset k r, ∃ ν' ∈ Nset k r, ∃ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
      (∀ a, c a ≠ 0) ∧ μᴴ * Hb k * μ = Hb k ∧ g = ν⁻¹ * bigCell k r c μ * ν'

end Formalism.MainNotions.BridgeLemma₃

end

end PartOrbGD

section PartOrbCB

open Matrix MeasureTheory

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

variable {k r : ℕ}

def cb_up (a : Fin r) (t : Fin (a.val + 1)) : Fin r := ⟨t.val, Nat.lt_of_lt_of_le t.isLt a.isLt⟩

def cb_J (k : ℕ) (a : Fin r) (t : Fin (a.val + 1)) : Fin (2 * r + k + 1) := eI k r (cb_up a t)

def cb_Js (k : ℕ) (a : Fin r) (t : Fin (a.val + 1)) : Fin (2 * r + k + 1) := esI k r (cb_up a t)

def cb_I (k : ℕ) (a : Fin r) (u : Fin (2 * r + k + 1)) (t : Fin (a.val + 1)) : Fin (2 * r + k + 1) :=
  if t.val < a.val then esI k r (cb_up a t) else u

end Formalism.MainNotions.BridgeLemma₃

end

end PartOrbCB

section PartOrbNB

open Matrix

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

variable {k r : ℕ}

def nb_U (w : Mat k r) : Matrix (Fin r) (Fin r) ℂ := fun i p => w (eI k r i) (eI k r p)

end Formalism.MainNotions.BridgeLemma₃

end

end PartOrbNB

section PartOrbNI

open Matrix MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def ni_f (k r : ℕ) (B : ℝ) (g : Mt k r) : ℝ≥0∞ := ENNReal.ofReal (gN (Matrix.of g : Mat k r) ^ (-B))

end Formalism.MainNotions.BridgeLemma₃

end

end PartOrbNI

section PartOrbOD1

open Matrix MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def od_BigCellInv : Prop :=
  ∀ (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) → μᴴ * Hb k * μ = Hb k →
    (bigCell k r c μ)⁻¹ = bigCell k r (fun a => star (c a)) μ⁻¹

variable {k r : ℕ}

def od_nn (k r : ℕ) : ℝ := ((2 * r + k + 1 : ℕ) : ℝ)

end Formalism.MainNotions.BridgeLemma₃

end

end PartOrbOD1

section PartOrbOD2

open Matrix MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

end Formalism.MainNotions.BridgeLemma₃

end

end PartOrbOD2

section PartOrbOD

open Matrix MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

end Formalism.MainNotions.BridgeLemma₃

end

end PartOrbOD

section PartPX

namespace Formalism.MainNotions.BridgeLemma₃

open Formalism.MainNotions Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₃

end PartPX
