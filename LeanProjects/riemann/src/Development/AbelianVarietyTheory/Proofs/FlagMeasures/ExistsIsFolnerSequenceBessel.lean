import Mathlib
import Formalism.FormalDegreeBessel.FinalG
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselRootDilationNormalizesContractsUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedSubgroupBesselHaarFiniteCompactPosOpenStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedSubgroupBesselUnitaryHaarUniqueStatement

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.FolnerSets

variable {k r : ℕ}

def sn (a : Mat k r) : ℝ := @norm (Mt k r) _ a

theorem sn_nonneg (a : Mat k r) : 0 ≤ sn a := @norm_nonneg (Mt k r) _ a

theorem entry_le (a : Mat k r) (i j : Fin (2 * r + k + 1)) : ‖a i j‖ ≤ sn a :=
  (norm_le_pi_norm (a i) j).trans (norm_le_pi_norm (show Mt k r from a) i)

theorem sn_le {a : Mat k r} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i j, ‖a i j‖ ≤ c) : sn a ≤ c :=
  (pi_norm_le_iff_of_nonneg (x := (show Mt k r from a)) hc).2 fun i =>
    (pi_norm_le_iff_of_nonneg hc).2 fun j => h i j

theorem sn_add_le (a b : Mat k r) : sn (a + b) ≤ sn a + sn b := @norm_add_le (Mt k r) _ a b

theorem sn_sub_le (a b : Mat k r) : sn (a - b) ≤ sn a + sn b := @norm_sub_le (Mt k r) _ a b

theorem sn_one_le : sn (1 : Mat k r) ≤ 1 := sn_le zero_le_one fun i j => by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem continuous_sn : Continuous (sn : Mat k r → ℝ) := @continuous_norm (Mt k r) _

def dd (k r : ℕ) : ℝ := ((2 * r + k + 1 : ℕ) : ℝ)

theorem dd_nonneg : 0 ≤ dd k r := Nat.cast_nonneg _

theorem sn_mul_le {a b : Mat k r} {A B : ℝ} (ha : sn a ≤ A) (hb : sn b ≤ B) :
    sn (a * b) ≤ dd k r * A * B := by
  have hA : 0 ≤ A := (sn_nonneg a).trans ha
  have hB : 0 ≤ B := (sn_nonneg b).trans hb
  refine sn_le (mul_nonneg (mul_nonneg dd_nonneg hA) hB) fun i j => ?_
  rw [Matrix.mul_apply]
  calc ‖∑ l, a i l * b l j‖ ≤ ∑ l, ‖a i l * b l j‖ := norm_sum_le _ _
    _ ≤ ∑ _l : Fin (2 * r + k + 1), A * B := Finset.sum_le_sum fun l _ => by
        rw [norm_mul]
        exact mul_le_mul ((entry_le a i l).trans ha) ((entry_le b l j).trans hb) (norm_nonneg _) hA
    _ = dd k r * A * B := by simp [dd, mul_assoc]

theorem exists_bound {C : Set (Mat k r)} (hC : IsCompact C) : ∃ M, 0 ≤ M ∧ ∀ a ∈ C, sn a ≤ M := by
  obtain ⟨M, hM⟩ := (hC.image continuous_sn).bddAbove
  exact ⟨max M 0, le_max_right _ _, fun a ha => (hM ⟨a, ha, rfl⟩).trans (le_max_left _ _)⟩

theorem isUnit_det_of_mem {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det := by
  have hH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  have : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [mul_assoc, mul_assoc, ← mul_assoc gᴴ, h, hH]
  exact Matrix.isUnit_det_of_left_inverse this

def cj (a b : Mat k r) (hab : a * b = 1) (hba : b * a = 1) : Mt k r ≃ₜ Mt k r where
  toFun x := b * Matrix.of x * a
  invFun x := a * Matrix.of x * b
  left_inv x := by
    show a * (b * Matrix.of x * a) * b = Matrix.of x
    rw [← mul_assoc, ← mul_assoc, hab, one_mul, mul_assoc, hab, mul_one]
  right_inv x := by
    show b * (a * Matrix.of x * b) * a = Matrix.of x
    rw [← mul_assoc, ← mul_assoc, hba, one_mul, mul_assoc, hba, mul_one]
  continuous_toFun := (continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

theorem of_cj (a b : Mat k r) (hab : a * b = 1) (hba : b * a = 1) (x : Mt k r) :
    (Matrix.of (cj a b hab hba x) : Mat k r) = b * Matrix.of x * a := rfl

theorem continuous_lmulM (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) :=
  continuous_const.matrix_mul (continuous_id (X := Mat k r))

theorem of_lmulM (a : Mat k r) (x : Mt k r) : (Matrix.of (lmulM a x) : Mat k r) = a * Matrix.of x := rfl

theorem mem_iff_cj {S : Set (Mat k r)} {a b : Mat k r} (hab : a * b = 1) (hba : b * a = 1)
    (h1 : ∀ s ∈ S, a * s * b ∈ S) (h2 : ∀ s ∈ S, b * s * a ∈ S) (x : Mt k r) :
    Matrix.of (cj a b hab hba x) ∈ S ↔ Matrix.of x ∈ S := by
  refine ⟨fun h => ?_, fun h => h2 _ h⟩
  have := h1 _ h
  rwa [of_cj, ← mul_assoc, ← mul_assoc, hab, one_mul, mul_assoc, hab, mul_one] at this

theorem isHaarOn_map_cj {S : Set (Mat k r)} (hS : IsClosed S) {μ : Measure (Mt k r)} (hμ : IsHaarOn S μ)
    {a b : Mat k r} (hab : a * b = 1) (hba : b * a = 1)
    (h1 : ∀ s ∈ S, a * s * b ∈ S) (h2 : ∀ s ∈ S, b * s * a ∈ S) :
    IsHaarOn S (μ.map (cj a b hab hba)) := by
  obtain ⟨hσ, hne, hc, hinv⟩ := hμ
  have hm : Measurable (cj a b hab hba) := (cj a b hab hba).continuous.measurable
  refine ⟨(cj a b hab hba).toMeasurableEquiv.sigmaFinite_map, ?_, ?_, fun s hs => ?_⟩
  · exact (Measure.map_ne_zero_iff hm.aemeasurable).2 hne
  · have hop : IsOpen {x : Mt k r | Matrix.of x ∉ S} := hS.isOpen_compl
    rw [Measure.map_apply hm hop.measurableSet, ← hc]
    congr 1
    ext x
    exact not_congr (mem_iff_cj hab hba h1 h2 x)
  · rw [Measure.map_map (continuous_lmulM s).measurable hm]
    have : lmulM s ∘ cj a b hab hba = cj a b hab hba ∘ lmulM (a * s * b) := by
      funext x
      show s * (b * Matrix.of x * a) = b * (a * s * b * Matrix.of x) * a
      simp only [← mul_assoc, hba, one_mul]
    rw [this, ← Measure.map_map hm (continuous_lmulM _).measurable, hinv _ (h1 s hs)]

def AA (S H : Set (Mat k r)) (t : ℝ) : Set (Mt k r) :=
  {x | Matrix.of x ∈ S} ∩ {x | ∃ h ∈ H, sn (h * Matrix.of x) < t}

theorem isOpen_U (H : Set (Mat k r)) (t : ℝ) :
    IsOpen {x : Mt k r | ∃ h ∈ H, sn (h * Matrix.of x) < t} := by
  have : {x : Mt k r | ∃ h ∈ H, sn (h * Matrix.of x) < t} =
      ⋃ h ∈ H, {x : Mt k r | sn (lmulM h x) < t} := by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]; rfl
  rw [this]
  exact isOpen_biUnion fun h _ => isOpen_lt (continuous_sn.comp (continuous_lmulM h)) continuous_const

theorem measurableSet_AA {S : Set (Mat k r)} (hS : IsClosed S) (H : Set (Mat k r)) (t : ℝ) :
    MeasurableSet (AA S H t) := by
  have hc : IsClosed {x : Mt k r | Matrix.of x ∈ S} := hS
  exact hc.measurableSet.inter (isOpen_U H t).measurableSet

theorem AA_mono (S H : Set (Mat k r)) {t t' : ℝ} (h : t ≤ t') : AA S H t ⊆ AA S H t' :=
  fun _ ⟨h1, g, hg, h2⟩ => ⟨h1, g, hg, h2.trans_le h⟩

theorem AA_bound {S H : Set (Mat k r)} (hH : IsClosedSub k r H) {M : ℝ} (hM : ∀ h ∈ H, sn h ≤ M) {t : ℝ}
    {x : Mt k r} (hx : x ∈ AA S H t) : sn (Matrix.of x) ≤ dd k r * M * t := by
  obtain ⟨-, h, hh, hlt⟩ := hx
  have : (Matrix.of x : Mat k r) = h⁻¹ * (h * Matrix.of x) := by
    rw [← mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_det_of_mem (hH.1 hh)), one_mul]
  rw [this]
  exact sn_mul_le (hM _ (hH.2.2.2.2 _ hh)) hlt.le

theorem lmulM_mem_AA {S H : Set (Mat k r)} (hS : IsClosedSub k r S) (hH : IsClosedSub k r H) {M : ℝ}
    (hM : ∀ h ∈ H, sn h ≤ M) {t ε : ℝ} {x : Mt k r} (hx : x ∈ AA S H t) {h₀ m : Mat k r} (h0 : h₀ ∈ H)
    (hm : sn (m - 1) ≤ ε) (hc : h₀ * m ∈ S) :
    lmulM (h₀ * m) x ∈ AA S H (t * (1 + dd k r * (dd k r * (dd k r * M * ε) * M))) := by
  obtain ⟨hxS, h, hh, hlt⟩ := hx
  refine ⟨hS.2.2.2.1 _ hc _ hxS, h * h₀⁻¹, hH.2.2.2.1 _ hh _ (hH.2.2.2.2 _ h0), ?_⟩
  have e0 := Matrix.nonsing_inv_mul _ (isUnit_det_of_mem (hH.1 h0))
  have e1 := Matrix.nonsing_inv_mul _ (isUnit_det_of_mem (hH.1 hh))
  have : h * h₀⁻¹ * Matrix.of (lmulM (h₀ * m) x) =
      h * Matrix.of x + (h * (m - 1) * h⁻¹) * (h * Matrix.of x) := by
    rw [of_lmulM]
    calc h * h₀⁻¹ * (h₀ * m * Matrix.of x) = h * (h₀⁻¹ * h₀) * m * Matrix.of x := by
          simp only [mul_assoc]
      _ = h * Matrix.of x + h * (m - 1) * (h⁻¹ * h) * Matrix.of x := by
          rw [e0, e1]; noncomm_ring
      _ = _ := by simp only [mul_assoc]
  rw [this]
  have b1 := sn_mul_le (sn_mul_le (hM _ hh) hm) (hM _ (hH.2.2.2.2 _ hh))
  have b2 := sn_mul_le b1 (le_refl (sn (h * Matrix.of x)))
  have b3 : 0 ≤ dd k r * (dd k r * (dd k r * M * ε) * M) :=
    mul_nonneg dd_nonneg ((sn_nonneg _).trans b1)
  calc _ ≤ _ := sn_add_le _ _
    _ ≤ sn (h * Matrix.of x) * (1 + dd k r * (dd k r * (dd k r * M * ε) * M)) := by linarith
    _ < _ := mul_lt_mul_of_pos_right hlt (by linarith)

theorem tendsto_AA (S H : Set (Mat k r)) (μ : Measure (Mt k r)) {L : ℝ} (hL : 0 ≤ L) :
    Filter.Tendsto (fun j : ℕ => μ (AA S H (2 / (1 + L * ((j : ℝ) + 1)⁻¹)))) Filter.atTop
      (nhds (μ (AA S H 2))) := by
  have hlim : Filter.Tendsto (fun j : ℕ => 2 / (1 + L * ((j : ℝ) + 1)⁻¹)) Filter.atTop (nhds 2) := by
    have h0 : Filter.Tendsto (fun j : ℕ => ((j : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have := (tendsto_const_nhds (x := (2 : ℝ))).div ((h0.const_mul L).const_add 1) (by simp)
    rw [mul_zero, add_zero, div_one] at this
    exact this
  have hU : AA S H 2 = ⋃ j : ℕ, AA S H (2 / (1 + L * ((j : ℝ) + 1)⁻¹)) := by
    apply Set.Subset.antisymm
    · rintro x ⟨h1, h, hh, hlt⟩
      obtain ⟨j, hj⟩ := (hlim.eventually (lt_mem_nhds hlt)).exists
      exact Set.mem_iUnion.2 ⟨j, h1, h, hh, hj⟩
    · refine Set.iUnion_subset fun j => AA_mono S H ?_
      have : 0 ≤ L * ((j : ℝ) + 1)⁻¹ := by positivity
      exact div_le_self (by norm_num) (by linarith)
  rw [hU]
  refine tendsto_measure_iUnion_atTop fun i j hij => AA_mono S H ?_
  have : (i : ℝ) ≤ j := Nat.cast_le.2 hij
  gcongr

theorem exists_isFolner : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μS : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → IsHaarOn (Sset k r z) μS → ∃ Om : ℕ → Set (Mt k r), IsFolner (Sset k r z) μS Om := by
  intro k r z μ hz hT hμ
  obtain ⟨-, hN, hH, hS, hHc⟩ := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT
  obtain ⟨hd1, hd2⟩ := GlobalTheory.T.besselRootDilation_normalizes_contracts_unipotent k r z hz
  obtain ⟨hfin, hpos⟩ := GlobalTheory.T.closedSubgroupBessel_haar_finite_compact_pos_open k r _ μ hS hμ
  obtain ⟨M, hM0, hM⟩ := exists_bound hHc
  set a : ℕ → Mat k r := fun j => dil k r ((j : ℝ) + 1) with ha
  have hτ : ∀ j : ℕ, (0 : ℝ) < (j : ℝ) + 1 := fun j => by positivity
  have hu : ∀ j, IsUnit (a j).det := fun j => isUnit_det_of_mem (hd1 _ (hτ j)).1
  have hab : ∀ j, a j * (a j)⁻¹ = 1 := fun j => Matrix.mul_nonsing_inv _ (hu j)
  have hba : ∀ j, (a j)⁻¹ * a j = 1 := fun j => Matrix.nonsing_inv_mul _ (hu j)
  have hc1 : ∀ j, ∀ h ∈ UWset k r z, a j * h = h * a j := fun j => (hd1 _ (hτ j)).2.1
  have hc2 : ∀ j, ∀ h ∈ UWset k r z, (a j)⁻¹ * h = h * (a j)⁻¹ := fun j h hh => by
    calc (a j)⁻¹ * h = (a j)⁻¹ * (h * a j) * (a j)⁻¹ := by simp only [mul_assoc, hab, mul_one]
      _ = _ := by rw [← hc1 j h hh, ← mul_assoc, hba, one_mul]
  have e1 : ∀ j, ∀ h ∈ UWset k r z, ∀ m, a j * (h * m) * (a j)⁻¹ = h * (a j * m * (a j)⁻¹) :=
    fun j h hh m => by rw [← mul_assoc, hc1 j h hh]; simp only [mul_assoc]
  have e2 : ∀ j, ∀ h ∈ UWset k r z, ∀ m, (a j)⁻¹ * (h * m) * a j = h * ((a j)⁻¹ * m * a j) :=
    fun j h hh m => by rw [← mul_assoc, hc2 j h hh]; simp only [mul_assoc]
  have h1 : ∀ j, ∀ s ∈ Sset k r z, a j * s * (a j)⁻¹ ∈ Sset k r z := by
    rintro j s ⟨h, hh, m, hm, rfl⟩
    exact ⟨h, hh, _, ((hd1 _ (hτ j)).2.2 m hm).1, e1 j h hh m⟩
  have h2 : ∀ j, ∀ s ∈ Sset k r z, (a j)⁻¹ * s * a j ∈ Sset k r z := by
    rintro j s ⟨h, hh, m, hm, rfl⟩
    exact ⟨h, hh, _, ((hd1 _ (hτ j)).2.2 m hm).2, e2 j h hh m⟩
  set ψ : ℕ → Mt k r ≃ₜ Mt k r := fun j => cj (a j) (a j)⁻¹ (hab j) (hba j) with hψ
  have hψm : ∀ j, Measurable (ψ j) := fun j => (ψ j).continuous.measurable
  choose c hc0 hct hc using fun j => GlobalTheory.T.closedSubgroupBesselUnitary_haar_unique k r _ μ _ hS hμ
    (isHaarOn_map_cj hS.2.1 hμ (hab j) (hba j) (h1 j) (h2 j))
  have hmeas : ∀ j t, μ (ψ j ⁻¹' AA (Sset k r z) (UWset k r z) t) =
      c j * μ (AA (Sset k r z) (UWset k r z) t) := fun j t => by
    rw [← Measure.map_apply (hψm j) (measurableSet_AA hS.2.1 _ t), hc j]; rfl
  have hA0 : 0 < μ (AA (Sset k r z) (UWset k r z) 2) := by
    have hU := hpos _ (isOpen_U (UWset k r z) 2) ⟨(1 : Mat k r), ⟨1, hH.2.2.1, by
      show sn ((1 : Mat k r) * 1) < 2
      rw [one_mul]; linarith [sn_one_le (k := k) (r := r)]⟩, hS.2.2.1⟩
    rw [AA, Set.inter_comm, measure_inter_conull' ]
    · exact hU
    · exact measure_mono_null (fun x hx => hx.2) hμ.2.2.1
  have hAt : μ (AA (Sset k r z) (UWset k r z) 2) < ⊤ := by
    refine lt_of_le_of_lt (measure_mono fun x hx => ?_)
      (hfin _ (isCompact_closedBall (0 : Mt k r) (dd k r * M * 2)))
    exact mem_closedBall_zero_iff.2 (AA_bound hH hM hx)
  refine ⟨fun j => ψ j ⁻¹' AA (Sset k r z) (UWset k r z) 2, fun j => ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hψm j (measurableSet_AA hS.2.1 _ _)
  · exact fun x hx => (mem_iff_cj (hab j) (hba j) (h1 j) (h2 j) x).1 hx.1
  · refine isBounded_iff_forall_norm_le.2
      ⟨dd k r * (dd k r * sn (a j) * (dd k r * M * 2)) * sn (a j)⁻¹, fun x hx => ?_⟩
    have hb := sn_mul_le (sn_mul_le (le_refl (sn (a j))) (AA_bound hH hM hx)) (le_refl (sn (a j)⁻¹))
    have : a j * Matrix.of (ψ j x) * (a j)⁻¹ = Matrix.of x := (ψ j).left_inv x
    rw [this] at hb
    exact hb
  · rw [hmeas]; exact ENNReal.mul_pos (hc0 j).ne' hA0.ne'
  · rw [hmeas]; exact ENNReal.mul_lt_top (hct j) hAt
  intro C hC hCS
  obtain ⟨K, hK0, hK⟩ := exists_bound hC
  have hd := dd_nonneg (k := k) (r := r)
  set L : ℝ := dd k r * (dd k r * (dd k r * M * (dd k r * M * K + 1)) * M) with hL
  have hL0 : 0 ≤ L := by positivity
  refine ⟨fun j => ψ j ⁻¹' AA (Sset k r z) (UWset k r z) (2 / (1 + L * ((j : ℝ) + 1)⁻¹)),
    fun j => ⟨hψm j (measurableSet_AA hS.2.1 _ _), ?_, ?_⟩, ?_⟩
  · refine Set.preimage_mono (AA_mono _ _ ?_)
    have : 0 ≤ L * ((j : ℝ) + 1)⁻¹ := by positivity
    exact div_le_self (by norm_num) (by linarith)
  · intro s hs x hx
    obtain ⟨h, hh, m, hm, rfl⟩ := hCS hs
    have hmb : sn (m - 1) ≤ dd k r * M * K + 1 := by
      have : m = h⁻¹ * (h * m) := by
        rw [← mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_det_of_mem (hH.1 hh)), one_mul]
      have hb := sn_mul_le (hM _ (hH.2.2.2.2 _ hh)) (hK _ hs)
      rw [← this] at hb
      linarith [sn_sub_le m 1, sn_one_le (k := k) (r := r)]
    have hm' : sn ((a j)⁻¹ * m * a j - 1) ≤ ((j : ℝ) + 1)⁻¹ * (dd k r * M * K + 1) := by
      refine sn_le (by positivity) fun p q => (hd2 _ (by simp) m hm p q).trans ?_
      exact mul_le_mul_of_nonneg_left ((entry_le _ p q).trans hmb) (by positivity)
    have hmem := lmulM_mem_AA hS hH hM hx hh hm' (e2 j h hh m ▸ h2 j _ (hCS hs))
    have e : ψ j (lmulM (h * m) x) = lmulM (h * ((a j)⁻¹ * m * a j)) (ψ j x) := by
      rw [← e2 j h hh m]
      show (a j)⁻¹ * (h * m * Matrix.of x) * a j =
        (a j)⁻¹ * (h * m) * a j * ((a j)⁻¹ * Matrix.of x * a j)
      simp only [mul_assoc]
      rw [← mul_assoc (a j) (a j)⁻¹, hab, one_mul]
    have et : 2 / (1 + L * ((j : ℝ) + 1)⁻¹) * (1 + dd k r * (dd k r * (dd k r * M *
        (((j : ℝ) + 1)⁻¹ * (dd k r * M * K + 1))) * M)) = 2 := by
      have : dd k r * (dd k r * (dd k r * M * (((j : ℝ) + 1)⁻¹ * (dd k r * M * K + 1))) * M) =
          L * ((j : ℝ) + 1)⁻¹ := by rw [hL]; ring
      rw [this]
      exact div_mul_cancel₀ _ (by positivity)
    rw [et, ← e] at hmem
    exact hmem
  · have := ENNReal.Tendsto.div_const (tendsto_AA (Sset k r z) (UWset k r z) μ hL0)
      (b := μ (AA (Sset k r z) (UWset k r z) 2)) (Or.inr hA0.ne')
    rw [ENNReal.div_self hA0.ne' hAt.ne] at this
    refine this.congr fun j => ?_
    rw [hmeas, hmeas, ENNReal.mul_div_mul_left _ _ (hc0 j).ne' (hct j).ne]

end GlobalTheory.SgInf.FolnerSets
