import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaFixedTerm
import GroundTheory.PAdicHodge.ExtRobbaFixedSum
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

def fixRad : Set.Ioo (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩

def tildeOf (b : T.B) (hb : T.ConvAll b) : T.RobbaTilde := T.ofRad fixRad (T.ofAll b hb fixRad)

variable {T}

theorem ofRad_ofAll_eq (b : T.B) (hb : T.ConvAll b) (σ σ' : Set.Ioo (0 : ℝ) 1) :
    T.ofRad σ (T.ofAll b hb σ) = T.ofRad σ' (T.ofAll b hb σ') := by
  let m : Set.Ioo (0 : ℝ) 1 := ⟨min σ σ', lt_min σ.2.1 σ'.2.1, (min_le_left _ _).trans_lt σ.2.2⟩
  have h1 : (m : ℝ) ≤ σ := min_le_left _ _
  have h2 : (m : ℝ) ≤ σ' := min_le_right _ _
  rw [← T.ofRad_res h1, res_ofAll, ← T.ofRad_res h2, res_ofAll]

theorem tildeOf_eq (b : T.B) (hb : T.ConvAll b) (σ : Set.Ioo (0 : ℝ) 1) :
    T.tildeOf b hb = T.ofRad σ (T.ofAll b hb σ) := ofRad_ofAll_eq b hb fixRad σ

theorem tildeOf_congr {b b' : T.B} (hb : T.ConvAll b) (hb' : T.ConvAll b') (h : b = b') :
    T.tildeOf b hb = T.tildeOf b' hb' := by subst h; rfl

theorem tildeOf_mul {a b : T.B} (ha : T.ConvAll a) (hb : T.ConvAll b) :
    T.tildeOf (a * b) (ha.mul hb) = T.tildeOf a ha * T.tildeOf b hb := by
  rw [tildeOf, tildeOf, tildeOf, ofAll_mul, map_mul]

theorem convAll_πB : T.ConvAll T.πB := by
  have := convAll_πB_zpow (T := T) 1
  rwa [zpow_one] at this

theorem tildeOf_πB : T.tildeOf T.πB convAll_πB = T.πTilde := by
  rw [tildeOf, ← T.ofRad_πExt fixRad]
  rfl

def shiftCorr (τ : AddAut T.B) (s : ℤ) (b : T.B) : T.B :=
  if 0 ≤ s then ∑ l ∈ Finset.range s.toNat, ((l : ℤ) • τ) b
  else -∑ l ∈ Finset.range (-s).toNat, ((-((l : ℤ) + 1)) • τ) b

namespace TeichFrob

variable (F : T.TeichFrob)

theorem tildeFrob_tildeOf {b : T.B} (hb : T.ConvAll b) :
    F.tildeFrob (T.tildeOf b hb) = T.tildeOf (F.toB b) (F.convAll_toB hb) := by
  rw [tildeOf, tildeOf, F.tildeFrob_ofRad, F.extFrob_ofAll]
  exact ofRad_ofAll_eq _ _ _ _

def tildeW (y : T.RobbaTilde) : T.RobbaTilde := T.πTilde * F.tildeFrob y

end TeichFrob

namespace TeichFrob

variable (F : T.TeichFrob)

end TeichFrob

theorem DigLe.π_pow_mul {x : Γ} {Θ : ℝ} (hx : T.DigLe x Θ) (hΘ : 0 ≤ Θ) (N : ℕ) :
    T.DigLe (T.π ^ N * x) Θ := by
  induction N with
  | zero => simpa using hx
  | succ N ih => rw [pow_succ', mul_assoc]; exact (digLe_π_mul_iff hΘ).2 ih

theorem exists_eq_π_pow_mul_digLe {x : Γ} {M : ℕ} (hx : x ∈ Ideal.span {T.π ^ M}) {Θ : ℝ}
    (hd : T.DigLe x Θ) : ∃ x', x = T.π ^ M * x' ∧ T.DigLe x' Θ := by
  obtain ⟨x', rfl⟩ := T.mem_span_pow.1 hx
  refine ⟨x', rfl, fun n => ?_⟩
  have := hd (n + M)
  rwa [T.coeff_π_pow_mul_add] at this

theorem gaussNorm_π_pow_mul_le {x : Γ} {Θ : ℝ} (hx : T.DigLe x Θ) (hΘ : 0 ≤ Θ) (M : ℕ) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) : gaussNorm (T.zcoeff (T.π ^ M * x)) r ≤ r ^ M * Θ := by
  have hπ : ConvergesAt (T.zcoeff (T.π ^ M)) r := by
    rw [T.zcoeff_π_pow]; exact convergesAt_pi_single _ _ _
  rw [T.gaussNorm_zcoeff_mul hr0 hr1 hπ (hx.convergesAt hr0 hr1), T.zcoeff_π_pow,
    gaussNorm_pi_single _ _ hr0, norm_one, one_mul, zpow_natCast]
  exact mul_le_mul_of_nonneg_left (hx.gaussNorm_le hΘ hr0 hr1) (pow_nonneg hr0.le M)

end TeichLift

end GroundTheory.PAdicHodge
