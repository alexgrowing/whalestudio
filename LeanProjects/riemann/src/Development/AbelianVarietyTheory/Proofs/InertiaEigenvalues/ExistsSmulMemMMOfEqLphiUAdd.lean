import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology Matrix

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

open PowerSeries Filter Topology Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
omit [IsUltrametricDist K] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
private lemma coeff_eq_add_of_X_pow_succ_dvd_sub {f s g : K⟦X⟧} {c : K} {n : ℕ}
    (h : (X : K⟦X⟧) ^ (n + 1) ∣ f - (s + c • g)) :
    coeff n f = coeff n s + c * coeff n g := by
  have h0 := (PowerSeries.X_pow_dvd_iff.mp h) n (Nat.lt_succ_self n)
  rw [map_sub, map_add, PowerSeries.coeff_smul, smul_eq_mul, sub_eq_zero] at h0
  exact h0

open PowerSeries Filter Topology Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
private lemma norm_add_mul_mul_le_max {x y c : K} {w : ℝ} (hw : 0 ≤ w) :
    ‖x + c * y‖ * w ≤ max (‖x‖ * w) (‖c‖ * (‖y‖ * w)) := by
  calc ‖x + c * y‖ * w ≤ max ‖x‖ ‖c * y‖ * w :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) hw
    _ = max (‖x‖ * w) (‖c‖ * (‖y‖ * w)) := by
        rw [max_mul_of_nonneg _ _ hw, norm_mul, mul_assoc]

open PowerSeries Filter Topology Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
omit [IsUltrametricDist K] in
private lemma norm_natCast_prime_lt_one_inertia_eigenvalues : ‖(l : K)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] K), norm_algebraMap']
  exact Padic.norm_p_lt_one

open PowerSeries Filter Topology Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in

theorem _root_.GlobalTheory.BK.mem_S_of_approx {f : K⟦X⟧}
    (h : ∀ k : ℕ, ∃ s ∈ _root_.GlobalTheory.BK.S O K e, ∀ m : ℕ,
      ∃ g ∈ _root_.GlobalTheory.BK.S O K e,
        (X : K⟦X⟧) ^ m ∣ f - (s + (l : K) ^ k • g)) : f ∈ _root_.GlobalTheory.BK.S O K e := by
  rw [_root_.GlobalTheory.BK.mem_S]
  have hw := _root_.GlobalTheory.BK.wS_nonneg (K := K) e
  refine ⟨fun n => ?_, ?_⟩
  · obtain ⟨s, hs, hm⟩ := h 0
    obtain ⟨g, hg, hdvd⟩ := hm (n + 1)
    rw [coeff_eq_add_of_X_pow_succ_dvd_sub hdvd]
    refine (norm_add_mul_mul_le_max (hw n)).trans (max_le ((_root_.GlobalTheory.BK.mem_S.mp hs).1 n) ?_)
    rw [pow_zero, norm_one, one_mul]
    exact (_root_.GlobalTheory.BK.mem_S.mp hg).1 n
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (norm_natCast_prime_lt_one_inertia_eigenvalues (K := K) (l := l))
    obtain ⟨s, hs, hm⟩ := h k
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (_root_.GlobalTheory.BK.mem_S.mp hs).2 ε hε
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨g, hg, hdvd⟩ := hm (n + 1)
    have hsn := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hw n))] at hsn ⊢
    rw [coeff_eq_add_of_X_pow_succ_dvd_sub hdvd]
    refine (norm_add_mul_mul_le_max (hw n)).trans_lt (max_lt hsn ?_)
    calc ‖(l : K) ^ k‖ * (‖coeff n g‖ * _root_.GlobalTheory.BK.wS K e n)
        ≤ ‖(l : K) ^ k‖ * 1 :=
          mul_le_mul_of_nonneg_left ((_root_.GlobalTheory.BK.mem_S.mp hg).1 n)
            (norm_nonneg _)
      _ < ε := by rw [mul_one, norm_pow]; exact hk

namespace PhiMod

variable (P : PhiMod O K l e a ι)

open PowerSeries Filter Topology Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
theorem _root_.GlobalTheory.BK.PhiMod.l_pow_smul_mem_MM (n : ℕ) {v : _root_.GlobalTheory.BK.Vec K a ι} (hv : v ∈ P.MM) :
    (l : K) ^ n • v ∈ P.MM := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hv _

open PowerSeries Filter Topology Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
theorem _root_.GlobalTheory.BK.PhiMod.smul_mem_MM {f : K⟦X⟧}
    (hf : f ∈ _root_.GlobalTheory.BK.S O K e) {v : _root_.GlobalTheory.BK.Vec K a ι}
    (hv : v ∈ P.MM) : f • v ∈ P.MM :=
  Submodule.smul_mem _ (⟨f, hf⟩ : _root_.GlobalTheory.BK.S O K e) hv

variable [NeZero e]

open PowerSeries Filter Topology Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
variable [NeZero e] in

theorem _root_.GlobalTheory.BK.PhiMod.l_pow_smul_phi_mem_MM {k : ℕ} {v : _root_.GlobalTheory.BK.Vec K a ι}
    (hv : _root_.GlobalTheory.BK.E K l e ^ k • v ∈
      P.Mext (_root_.GlobalTheory.BK.S O K e)) :
    (l : K) ^ k • P.phi v ∈ P.MM := by
  obtain ⟨c, hc, hcE⟩ :=
    _root_.GlobalTheory.BK.exists_mul_frob_E (O := O) (K := K) l e
  set F := _root_.GlobalTheory.BK.frob K l with hF
  set E := _root_.GlobalTheory.BK.E K l e with hE
  have hw : ∀ τ i, (E ^ k • v) τ i ∈ _root_.GlobalTheory.BK.S O K e := by
    intro τ i
    unfold _root_.GlobalTheory.BK.PhiMod.Mext at hv
    rw [_root_.GlobalTheory.BK.mem_tot] at hv
    exact _root_.GlobalTheory.BK.mem_vecs.mp (hv τ) i
  have hmem : P.phi (E ^ k • v) ∈ P.MM := by
    unfold _root_.GlobalTheory.BK.PhiMod.MM
    rw [_root_.GlobalTheory.BK.PhiMod.ext, _root_.GlobalTheory.BK.mem_tot]
    intro τ
    rw [_root_.GlobalTheory.BK.PhiMod.mem_extc]
    refine ⟨_root_.GlobalTheory.BK.frobV l ((E ^ k • v) (τ - 1)), ?_, _root_.GlobalTheory.BK.PhiMod.phi_apply _ _ _⟩
    rw [_root_.GlobalTheory.BK.mem_vecs]
    intro i
    rw [_root_.GlobalTheory.BK.frobV_apply]
    exact _root_.GlobalTheory.BK.frob_mem_S l (hw _ i)
  have heq : (l : K) ^ k • P.phi v =
      ((⟨c, hc⟩ : _root_.GlobalTheory.BK.S O K e) ^ k) •
        P.phi (E ^ k • v) := by
    funext τ i
    have hvec : _root_.GlobalTheory.BK.frobV l ((E ^ k • v) (τ - 1)) =
        F E ^ k • _root_.GlobalTheory.BK.frobV l (v (τ - 1)) := by
      funext j
      simp only [Pi.smul_apply, _root_.GlobalTheory.BK.frobV_apply, smul_eq_mul, map_mul, map_pow, hF]
    change (l : K) ^ k • P.phi v τ i =
      (c ^ k) • P.phi (E ^ k • v) τ i
    rw [_root_.GlobalTheory.BK.PhiMod.phi_apply, _root_.GlobalTheory.BK.PhiMod.phi_apply, hvec, Matrix.mulVec_smul, Pi.smul_apply, smul_smul, ← mul_pow, hcE,
      ← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [heq]
  exact Submodule.smul_mem _ _ hmem

def lphiU : Module.End K (Vec K a ι) := mulV K a ι (X ^ (l - 1)) * P.lphi

variable {η : ℕ} (hη : ∀ v ∈ P.MM, (l : K) ^ η • P.phi v ∈ P.MM)

include hη

end PhiMod

namespace BKDat

variable [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ} (D : BKDat O K l e a ι η H)

end BKDat

end GlobalTheory.BK
