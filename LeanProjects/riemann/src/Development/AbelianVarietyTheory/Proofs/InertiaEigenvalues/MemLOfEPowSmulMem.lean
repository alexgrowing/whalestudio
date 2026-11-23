import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

open GlobalTheory.BK PowerSeries

namespace GlobalTheory.BK.PhiMod

section

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι)

variable [CompleteSpace K]

end

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
omit [IsUltrametricDist K] [_root_.GlobalTheory.BK.IsUnitBall O K] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] in
private lemma pow_mul_mem_of_pow_mul_mem_of_le {S : Subalgebra O (PowerSeries K)} {s f : PowerSeries K}
    (hs : s ∈ S) {n N : ℕ} (h : n ≤ N) (hf : s ^ n * f ∈ S) : s ^ N * f ∈ S := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, mul_comm (s ^ n), mul_assoc]
  exact mul_mem (pow_mem hs k) hf

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
omit [IsUltrametricDist K] [_root_.GlobalTheory.BK.IsUnitBall O K] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] in
private lemma exists_uniform_pow_mul_mem {T : Type} [Finite T] {S : Subalgebra O (PowerSeries K)}
    {s : PowerSeries K} (hs : s ∈ S) (f : T → PowerSeries K) (h : ∀ t, ∃ n, s ^ n * f t ∈ S) :
    ∃ N, ∀ t, s ^ N * f t ∈ S := by
  cases nonempty_fintype T
  choose n hn using h
  exact ⟨Finset.univ.sup n, fun t => pow_mul_mem_of_pow_mul_mem_of_le hs (Finset.le_sup (Finset.mem_univ t)) (hn t)⟩

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
private lemma eisenstein_mem_integral :
    _root_.GlobalTheory.BK.E K l e ∈ _root_.GlobalTheory.BK.A O K := by
  rw [← _root_.GlobalTheory.BK.coe_EIn l e (_root_.GlobalTheory.BK.A O K)]
  exact Subtype.property _

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
private lemma exists_eisenstein_pow_mul_mem_integral {f : PowerSeries K}
    (hf : f ∈ _root_.GlobalTheory.BK.invE l e (_root_.GlobalTheory.BK.A O K)) :
    ∃ n, _root_.GlobalTheory.BK.E K l e ^ n * f ∈ _root_.GlobalTheory.BK.A O K := by
  unfold _root_.GlobalTheory.BK.invE at hf
  obtain ⟨n, hn⟩ := _root_.GlobalTheory.BK.mem_away.1 hf
  exact ⟨n, by rwa [_root_.GlobalTheory.BK.coe_EIn] at hn⟩

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
private lemma exists_eisenstein_pow_mul_matrix_mem_integral [NeZero a] : ∃ N : ℕ, ∀ τ i j,
    _root_.GlobalTheory.BK.E K l e ^ N * P.mx τ i j ∈
        _root_.GlobalTheory.BK.A O K ∧
      _root_.GlobalTheory.BK.E K l e ^ N * P.mxInv τ i j ∈
        _root_.GlobalTheory.BK.A O K := by
  obtain ⟨N₁, h₁⟩ := exists_uniform_pow_mul_mem eisenstein_mem_integral
    (fun t : ZMod a × ι × ι => P.mx t.1 t.2.1 t.2.2)
    (fun t => exists_eisenstein_pow_mul_mem_integral (P.mx_mem _ _ _))
  obtain ⟨N₂, h₂⟩ := exists_uniform_pow_mul_mem eisenstein_mem_integral
    (fun t : ZMod a × ι × ι => P.mxInv t.1 t.2.1 t.2.2)
    (fun t => exists_eisenstein_pow_mul_mem_integral (P.mxInv_mem _ _ _))
  exact ⟨max N₁ N₂, fun τ i j =>
    ⟨pow_mul_mem_of_pow_mul_mem_of_le eisenstein_mem_integral (le_max_left _ _) (h₁ (τ, i, j)),
      pow_mul_mem_of_pow_mul_mem_of_le eisenstein_mem_integral (le_max_right _ _) (h₂ (τ, i, j))⟩⟩

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] in
private lemma mem_baseChangeSpan_iff {S : Subalgebra O (PowerSeries K)} {v : _root_.GlobalTheory.BK.Vec K a ι} :
    v ∈ P.ext S ↔ ∀ τ i, (P.mxInv τ).mulVec (v τ) i ∈ S := by
  simp only [_root_.GlobalTheory.BK.PhiMod.ext, _root_.GlobalTheory.BK.mem_tot,
    _root_.GlobalTheory.BK.PhiMod.mem_extc_iff, _root_.GlobalTheory.BK.mem_vecs]

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] in
private lemma mem_baseChangeAll_iff {S : Subalgebra O (PowerSeries K)} {v : _root_.GlobalTheory.BK.Vec K a ι} :
    v ∈ P.Mext S ↔ ∀ τ i, v τ i ∈ S := by
  simp only [_root_.GlobalTheory.BK.PhiMod.Mext, _root_.GlobalTheory.BK.mem_tot,
    _root_.GlobalTheory.BK.mem_vecs]

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] in
private lemma mx_mulVec_mxInv_mulVec_eq_self (τ : ZMod a) (w : ι → PowerSeries K) :
    (P.mx τ).mulVec ((P.mxInv τ).mulVec w) = w := by
  rw [Matrix.mulVec_mulVec, P.mx_mul_mxInv, Matrix.one_mulVec]

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
omit [IsUltrametricDist K] [_root_.GlobalTheory.BK.IsUnitBall O K] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] in
private lemma mulVec_mem_of_forall_mem {S : Subalgebra O (PowerSeries K)} {A : Matrix ι ι (PowerSeries K)}
    {w : ι → PowerSeries K} (hA : ∀ i j, A i j ∈ S) (hw : ∀ i, w i ∈ S) (i : ι) :
    A.mulVec w i ∈ S := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => mul_mem (hA i j) (hw j)

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
private lemma eisenstein_pow_smul_mem_baseChangeAll {S : Subalgebra O (PowerSeries K)}
    (hS : _root_.GlobalTheory.BK.A O K ≤ S) {N : ℕ}
    (hN : ∀ τ i j, _root_.GlobalTheory.BK.E K l e ^ N * P.mx τ i j ∈
        _root_.GlobalTheory.BK.A O K)
    {x : _root_.GlobalTheory.BK.Vec K a ι} (hx : x ∈ P.ext S) :
    _root_.GlobalTheory.BK.E K l e ^ N • x ∈ P.Mext S := by
  rw [mem_baseChangeSpan_iff] at hx
  rw [mem_baseChangeAll_iff]
  intro τ i
  show _root_.GlobalTheory.BK.E K l e ^ N * x τ i ∈ S
  rw [← mx_mulVec_mxInv_mulVec_eq_self P τ (x τ)]
  have h : _root_.GlobalTheory.BK.E K l e ^ N *
      (P.mx τ).mulVec ((P.mxInv τ).mulVec (x τ)) i =
      (_root_.GlobalTheory.BK.E K l e ^ N • P.mx τ).mulVec
        ((P.mxInv τ).mulVec (x τ)) i := by
    rw [Matrix.smul_mulVec]; rfl
  rw [h]
  exact mulVec_mem_of_forall_mem (fun i j => hS (hN τ i j)) (hx τ) i

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] in
private lemma integral_le_invertPrime :
    _root_.GlobalTheory.BK.A O K ≤
      _root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K) :=
  _root_.GlobalTheory.BK.le_away _ _

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
omit [IsUltrametricDist K] [_root_.GlobalTheory.BK.IsUnitBall O K] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [DecidableEq ι] in
private lemma mulVec_smul_apply_eq_mul_mulVec_apply (A : Matrix ι ι (PowerSeries K)) (f : PowerSeries K)
    (v : _root_.GlobalTheory.BK.Vec K a ι) (τ : ZMod a) (i : ι) :
    A.mulVec ((f • v) τ) i = f * A.mulVec (v τ) i := by
  rw [Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
private lemma eisenstein_pow_smul_mem_baseChangeSpan {S : Subalgebra O (PowerSeries K)}
    (hS : _root_.GlobalTheory.BK.A O K ≤ S) {N : ℕ}
    (hN : ∀ τ i j, _root_.GlobalTheory.BK.E K l e ^ N * P.mxInv τ i j ∈
        _root_.GlobalTheory.BK.A O K)
    {m : _root_.GlobalTheory.BK.Vec K a ι} (hm : m ∈ P.Mext S) :
    _root_.GlobalTheory.BK.E K l e ^ N • m ∈ P.ext S := by
  rw [mem_baseChangeAll_iff] at hm
  rw [mem_baseChangeSpan_iff]
  intro τ i
  rw [mulVec_smul_apply_eq_mul_mulVec_apply]
  have h : _root_.GlobalTheory.BK.E K l e ^ N * (P.mxInv τ).mulVec (m τ) i =
      (_root_.GlobalTheory.BK.E K l e ^ N • P.mxInv τ).mulVec (m τ) i := by
    rw [Matrix.smul_mulVec]; rfl
  rw [h]
  exact mulVec_mem_of_forall_mem (fun i j => hS (hN τ i j)) (hm τ) i

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
private lemma ezpow_smul_mem_submodule_of_nonneg
    (W : Submodule (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K))
      (_root_.GlobalTheory.BK.Vec K a ι))
    {n : ℤ} (hn : 0 ≤ n) {w : _root_.GlobalTheory.BK.Vec K a ι} (hw : w ∈ W) :
    _root_.GlobalTheory.BK.Ezpow K l e n • w ∈ W :=
  W.smul_mem ⟨_, _root_.GlobalTheory.BK.Ezpow_mem_invL_A_iff.2 hn⟩ hw

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
omit [IsUltrametricDist K] [Fintype ι] [DecidableEq ι] in
private lemma ezpow_smul_ezpow_smul_eq_ezpow_add_smul (m n : ℤ) (w : _root_.GlobalTheory.BK.Vec K a ι) :
    _root_.GlobalTheory.BK.Ezpow K l e m • _root_.GlobalTheory.BK.Ezpow K l e n • w =
      _root_.GlobalTheory.BK.Ezpow K l e (m + n) • w := by
  rw [smul_smul, _root_.GlobalTheory.BK.Ezpow_add]

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
omit [IsUltrametricDist K] [Fintype ι] [DecidableEq ι] in
private lemma ezpow_zero_smul_eq_self (w : _root_.GlobalTheory.BK.Vec K a ι) : _root_.GlobalTheory.BK.Ezpow K l e 0 • w = w := by
  have h := _root_.GlobalTheory.BK.Ezpow_natCast (K := K) l e 0
  simp only [Nat.cast_zero, pow_zero] at h
  rw [h, one_smul]

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
private lemma filL_eq_ext_of_le (c : ℕ)
    (hc : ∀ x ∈ P.ext
        (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)),
      _root_.GlobalTheory.BK.Ezpow K l e c • x ∈ P.Mext
        (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)))
    {j : ℤ} (hj : j ≤ -(c : ℤ)) :
    P.filL j = P.ext
      (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)) := by
  unfold _root_.GlobalTheory.BK.PhiMod.filL
  apply le_antisymm
  · refine sup_le inf_le_left fun z hz => ?_
    rw [_root_.GlobalTheory.BK.mem_shiftE] at hz
    have h := ezpow_smul_mem_submodule_of_nonneg (O := O) (e := e) _ zero_le_one hz
    rwa [ezpow_smul_ezpow_smul_eq_ezpow_add_smul, show (1 : ℤ) + -1 = 0 by norm_num, ezpow_zero_smul_eq_self] at h
  · intro x hx
    refine Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hx, ?_⟩)
    rw [_root_.GlobalTheory.BK.mem_shiftE, show -j = (-j - c) + c by ring, ← ezpow_smul_ezpow_smul_eq_ezpow_add_smul]
    exact ezpow_smul_mem_submodule_of_nonneg (O := O) _ (by omega) (hc x hx)

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
private lemma filL_eq_shiftE_of_ge (c : ℕ)
    (hc : ∀ m ∈ P.Mext
        (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)),
      _root_.GlobalTheory.BK.Ezpow K l e c • m ∈ P.ext
        (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)))
    {j : ℤ} (hj : (c : ℤ) + 1 ≤ j) :
    P.filL j = _root_.GlobalTheory.BK.shiftE l e 1 (P.ext
      (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K))) := by
  unfold _root_.GlobalTheory.BK.PhiMod.filL
  refine le_antisymm (sup_le (fun x hx => ?_) le_rfl) le_sup_right
  obtain ⟨_, hxm⟩ := Submodule.mem_inf.1 hx
  rw [_root_.GlobalTheory.BK.mem_shiftE] at hxm ⊢
  have h := ezpow_smul_mem_submodule_of_nonneg (O := O) (e := e) _ (show (0 : ℤ) ≤ j - 1 - c by omega) (hc _ hxm)
  rwa [ezpow_smul_ezpow_smul_eq_ezpow_add_smul, ezpow_smul_ezpow_smul_eq_ezpow_add_smul, show j - 1 - c + c + -j = -1 by ring] at h

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] in
private lemma mem_allComponents_iff {v : _root_.GlobalTheory.BK.Vec K a ι} :
    v ∈ P.M ↔ ∀ τ i, v τ i ∈ _root_.GlobalTheory.BK.A O K := by
  simp only [_root_.GlobalTheory.BK.PhiMod.M, _root_.GlobalTheory.BK.mem_tot,
    _root_.GlobalTheory.BK.mem_vecs]

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] in
private lemma mem_frobeniusImageSpan_iff {v : _root_.GlobalTheory.BK.Vec K a ι} :
    v ∈ P.L ↔
      ∀ τ i, (P.mxInv τ).mulVec (v τ) i ∈ _root_.GlobalTheory.BK.A O K :=
  mem_baseChangeSpan_iff P

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
private lemma exists_eq_prime_mul_of_eisenstein_mul {g h : PowerSeries K}
    (hg : g ∈ _root_.GlobalTheory.BK.A O K) (hh : h ∈ _root_.GlobalTheory.BK.A O K)
    (hgh : _root_.GlobalTheory.BK.E K l e * g = (l : PowerSeries K) * h) :
    ∃ h' ∈ _root_.GlobalTheory.BK.A O K, g = (l : PowerSeries K) * h' := by
  refine ⟨PowerSeries.mk fun m => coeff (m + e) h - coeff (m + e) g, ?_, ?_⟩
  · intro n
    rw [coeff_mk, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hh _) ?_)
    rw [norm_neg]
    exact hg _
  · ext m
    have key := congrArg (coeff (m + e)) hgh
    simp only [_root_.GlobalTheory.BK.E, add_mul, map_add,
      coeff_X_pow_mul', le_add_iff_nonneg_left, zero_le, if_true, Nat.add_sub_cancel] at key
    rw [← map_natCast (PowerSeries.C (R := K)), coeff_C_mul, coeff_C_mul] at key
    rw [← map_natCast (PowerSeries.C (R := K)), coeff_C_mul, coeff_mk]
    linear_combination key

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
private lemma exists_eq_prime_mul_of_eisenstein_pow_mul (N : ℕ) {g : PowerSeries K}
    (hg : g ∈ _root_.GlobalTheory.BK.A O K) {h : PowerSeries K}
    (hh : h ∈ _root_.GlobalTheory.BK.A O K)
    (hgh : _root_.GlobalTheory.BK.E K l e ^ N * g = (l : PowerSeries K) * h) :
    ∃ h' ∈ _root_.GlobalTheory.BK.A O K, g = (l : PowerSeries K) * h' := by
  induction N generalizing h with
  | zero => exact ⟨h, hh, by simpa using hgh⟩
  | succ N ih =>
    have hg' : _root_.GlobalTheory.BK.E K l e ^ N * g ∈ _root_.GlobalTheory.BK.A O K :=
      mul_mem (pow_mem eisenstein_mem_integral N) hg
    obtain ⟨h'', hh'', he⟩ := exists_eq_prime_mul_of_eisenstein_mul hg' hh
      (by rw [← mul_assoc, ← pow_succ']; exact hgh)
    exact ih hh'' he

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
omit [IsUltrametricDist K] [NeZero e] in
private lemma natCast_prime_ne_zero_powerSeries : ((l : ℕ) : PowerSeries K) ≠ 0 := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  rw [← map_natCast (PowerSeries.C (R := K))]
  exact (map_ne_zero_iff _ PowerSeries.C_injective).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
private lemma mem_integral_of_mem_invertPrime_of_eisenstein_pow_mul {f : PowerSeries K}
    (hf : f ∈ _root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)) (N : ℕ)
    (hN : _root_.GlobalTheory.BK.E K l e ^ N * f ∈ _root_.GlobalTheory.BK.A O K) :
    f ∈ _root_.GlobalTheory.BK.A O K := by
  unfold _root_.GlobalTheory.BK.invL at hf
  obtain ⟨n, hn⟩ := _root_.GlobalTheory.BK.mem_away.1 hf
  push_cast at hn
  clear hf
  induction n generalizing f with
  | zero => simpa using hn
  | succ n ih =>
    have hlf : (l : PowerSeries K) * f ∈ _root_.GlobalTheory.BK.A O K :=
      ih (by rw [mul_left_comm]; exact mul_mem (natCast_mem _ l) hN)
        (by rw [← mul_assoc, ← pow_succ]; exact hn)
    obtain ⟨h', hh', he⟩ := exists_eq_prime_mul_of_eisenstein_pow_mul N hlf hN (by rw [mul_left_comm])
    rw [mul_left_cancel₀ natCast_prime_ne_zero_powerSeries he]
    exact hh'

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
private lemma eisenstein_pow_smul_mem_frobeniusImageSpan (H N : ℕ)
    (hN : ∀ τ i j, _root_.GlobalTheory.BK.E K l e ^ N * P.mxInv τ i j ∈
        _root_.GlobalTheory.BK.A O K)
    (hB : ∀ m ∈ P.Mext
        (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)),
      _root_.GlobalTheory.BK.Ezpow K l e H • m ∈ P.ext
        (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)))
    {m : _root_.GlobalTheory.BK.Vec K a ι} (hm : m ∈ P.M) :
    _root_.GlobalTheory.BK.E K l e ^ H • m ∈ P.L := by
  have hm' : m ∈ P.Mext (_root_.GlobalTheory.BK.A O K) :=
    (mem_baseChangeAll_iff P).2 ((mem_allComponents_iff P).1 hm)
  have hmB : m ∈ P.Mext
      (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)) :=
    P.Mext_mono integral_le_invertPrime hm'
  have h₁ := (mem_baseChangeSpan_iff P).1 (hB m hmB)
  rw [_root_.GlobalTheory.BK.Ezpow_natCast] at h₁
  have h₂ := (mem_baseChangeSpan_iff P).1 (eisenstein_pow_smul_mem_baseChangeSpan P le_rfl hN hm')
  rw [mem_frobeniusImageSpan_iff]
  intro τ i
  refine mem_integral_of_mem_invertPrime_of_eisenstein_pow_mul (e := e) (h₁ τ i) N ?_
  have h₃ := h₂ τ i
  rw [mulVec_smul_apply_eq_mul_mulVec_apply] at h₃ ⊢
  rw [mul_left_comm]
  exact mul_mem (pow_mem eisenstein_mem_integral H) h₃

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
private lemma eisenstein_zpow_smul_mem_baseChangeSpan_invertPrime (H N : ℕ)
    (hN : ∀ m ∈ P.Mext
        (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)),
      _root_.GlobalTheory.BK.Ezpow K l e N • m ∈ P.ext
        (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)))
    (hF : P.filL ((H : ℤ) + 1) = _root_.GlobalTheory.BK.shiftE l e 1
      (P.ext
        (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K))))
    {m : _root_.GlobalTheory.BK.Vec K a ι}
    (hm : m ∈ P.Mext
      (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K))) :
    _root_.GlobalTheory.BK.Ezpow K l e H • m ∈ P.ext
      (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)) := by
  have top : ∀ x ∈ P.ext
      (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)),
      _root_.GlobalTheory.BK.Ezpow K l e (-((H : ℤ) + 1)) • x ∈ P.Mext
        (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)) →
      _root_.GlobalTheory.BK.Ezpow K l e (-1) • x ∈ P.ext
        (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)) := by
    intro x hx hxm
    have hmem : x ∈ P.filL ((H : ℤ) + 1) := by
      unfold _root_.GlobalTheory.BK.PhiMod.filL
      exact Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hx, (_root_.GlobalTheory.BK.mem_shiftE).2 hxm⟩)
    rw [hF] at hmem
    exact (_root_.GlobalTheory.BK.mem_shiftE).1 hmem
  have key : ∀ k : ℕ, _root_.GlobalTheory.BK.Ezpow K l e ((H : ℤ) + k) • m ∈ P.ext
      (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)) →
      _root_.GlobalTheory.BK.Ezpow K l e H • m ∈ P.ext
        (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)) := by
    intro k
    induction k with
    | zero => intro h; simpa using h
    | succ k ih =>
      intro h
      apply ih
      have h₁ := top _ h (by
        rw [ezpow_smul_ezpow_smul_eq_ezpow_add_smul, show -((H : ℤ) + 1) + ((H : ℤ) + ((k + 1 : ℕ) : ℤ)) = (k : ℤ) by
          push_cast; ring]
        exact ezpow_smul_mem_submodule_of_nonneg (O := O) _ (Nat.cast_nonneg k) hm)
      rwa [ezpow_smul_ezpow_smul_eq_ezpow_add_smul, show -1 + ((H : ℤ) + ((k + 1 : ℕ) : ℤ)) = (H : ℤ) + k by
        push_cast; ring] at h₁
  apply key N
  rw [← ezpow_smul_ezpow_smul_eq_ezpow_add_smul]
  exact ezpow_smul_mem_submodule_of_nonneg (O := O) _ (Nat.cast_nonneg H) (hN m hm)

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
private lemma eisenstein_pow_smul_mem_allComponents (η N : ℕ)
    (hN : ∀ τ i j, _root_.GlobalTheory.BK.E K l e ^ N * P.mx τ i j ∈
        _root_.GlobalTheory.BK.A O K)
    (hB : ∀ x ∈ P.ext
        (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)),
      _root_.GlobalTheory.BK.Ezpow K l e η • x ∈ P.Mext
        (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)))
    {v : _root_.GlobalTheory.BK.Vec K a ι} (hv : v ∈ P.L) :
    _root_.GlobalTheory.BK.E K l e ^ η • v ∈ P.M := by
  have hvB : v ∈ P.ext
      (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)) :=
    P.ext_mono integral_le_invertPrime hv
  have h₁ := (mem_baseChangeAll_iff P).1 (hB v hvB)
  rw [_root_.GlobalTheory.BK.Ezpow_natCast] at h₁
  have h₂ := (mem_baseChangeAll_iff P).1 (eisenstein_pow_smul_mem_baseChangeAll P le_rfl hN hv)
  rw [mem_allComponents_iff]
  intro τ i
  refine mem_integral_of_mem_invertPrime_of_eisenstein_pow_mul (e := e) (h₁ τ i) N ?_
  show _root_.GlobalTheory.BK.E K l e ^ N * (_root_.GlobalTheory.BK.E K l e ^ η * v τ i) ∈ _
  rw [mul_left_comm]
  exact mul_mem (pow_mem eisenstein_mem_integral η) (h₂ τ i)

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
private lemma eisenstein_zpow_smul_mem_baseChangeAll_invertPrime (η N : ℕ)
    (hN : ∀ x ∈ P.ext
        (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)),
      _root_.GlobalTheory.BK.Ezpow K l e N • x ∈ P.Mext
        (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)))
    (hF : P.filL (-(η : ℤ)) = P.ext
      (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)))
    {x : _root_.GlobalTheory.BK.Vec K a ι}
    (hx : x ∈ P.ext
      (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K))) :
    _root_.GlobalTheory.BK.Ezpow K l e η • x ∈ P.Mext
      (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)) := by
  have step : ∀ y ∈ P.ext
      (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)),
      ∃ f ∈ P.ext
        (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)) ⊓
        _root_.GlobalTheory.BK.shiftE l e (-(η : ℤ)) (P.Mext
          (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K))),
      ∃ z ∈ P.ext
        (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)),
      y = f + _root_.GlobalTheory.BK.Ezpow K l e 1 • z := by
    intro y hy
    rw [← hF] at hy
    unfold _root_.GlobalTheory.BK.PhiMod.filL at hy
    obtain ⟨f, hf, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
    refine ⟨f, hf, _root_.GlobalTheory.BK.Ezpow K l e (-1) • z, (_root_.GlobalTheory.BK.mem_shiftE).1 hz, ?_⟩
    rw [ezpow_smul_ezpow_smul_eq_ezpow_add_smul, show (1 : ℤ) + -1 = 0 by norm_num, ezpow_zero_smul_eq_self]
  have iter : ∀ k : ℕ, ∀ y ∈ P.ext
      (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)),
      ∃ f ∈ P.ext
        (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)) ⊓
        _root_.GlobalTheory.BK.shiftE l e (-(η : ℤ)) (P.Mext
          (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K))),
      ∃ z ∈ P.ext
        (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)),
      y = f + _root_.GlobalTheory.BK.Ezpow K l e k • z := by
    intro k
    induction k with
    | zero =>
      intro y hy
      exact ⟨0, zero_mem _, y, hy, by rw [Nat.cast_zero, ezpow_zero_smul_eq_self, zero_add]⟩
    | succ k ih =>
      intro y hy
      obtain ⟨f, hf, z, hz, rfl⟩ := ih y hy
      obtain ⟨f', hf', z', hz', rfl⟩ := step z hz
      refine ⟨f + _root_.GlobalTheory.BK.Ezpow K l e k • f',
        add_mem hf (ezpow_smul_mem_submodule_of_nonneg (O := O) _ (Nat.cast_nonneg k) hf'), z', hz', ?_⟩
      rw [smul_add, ezpow_smul_ezpow_smul_eq_ezpow_add_smul, add_assoc, Nat.cast_succ]
  obtain ⟨f, hf, z, hz, rfl⟩ := iter N x hx
  obtain ⟨_, hf₂⟩ := Submodule.mem_inf.1 hf
  rw [_root_.GlobalTheory.BK.mem_shiftE, neg_neg] at hf₂
  rw [smul_add]
  exact add_mem hf₂ (ezpow_smul_mem_submodule_of_nonneg (O := O) _ (Nat.cast_nonneg η) (hN z hz))

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
private lemma eisenstein_zpow_smul_mem_baseChangeAll_of_pow_smul [NeZero a] (η : ℕ)
    (hL : ∀ v ∈ P.L,
      _root_.GlobalTheory.BK.E K l e ^ η • v ∈ P.M)
    {x : _root_.GlobalTheory.BK.Vec K a ι} (hx : x ∈ P.ext
      (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K))) :
    _root_.GlobalTheory.BK.Ezpow K l e η • x ∈ P.Mext
      (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)) := by
  rw [mem_baseChangeSpan_iff] at hx
  obtain ⟨n, hn⟩ := exists_uniform_pow_mul_mem (natCast_mem (_root_.GlobalTheory.BK.A O K) l)
    (fun t : ZMod a × ι => (P.mxInv t.1).mulVec (x t.1) t.2) (fun t => by
      have h := hx t.1 t.2
      unfold _root_.GlobalTheory.BK.invL at h
      obtain ⟨n, hn⟩ := _root_.GlobalTheory.BK.mem_away.1 h
      push_cast at hn
      exact ⟨n, hn⟩)
  have hv : (l : PowerSeries K) ^ n • x ∈ P.L := by
    rw [mem_frobeniusImageSpan_iff]
    intro τ i
    rw [mulVec_smul_apply_eq_mul_mulVec_apply]
    exact hn (τ, i)
  have h := (mem_allComponents_iff P).1 (hL _ hv)
  rw [mem_baseChangeAll_iff, _root_.GlobalTheory.BK.Ezpow_natCast]
  intro τ i
  unfold _root_.GlobalTheory.BK.invL
  rw [_root_.GlobalTheory.BK.mem_away]
  refine ⟨n, ?_⟩
  push_cast
  have h' := h τ i
  show (l : PowerSeries K) ^ n * (_root_.GlobalTheory.BK.E K l e ^ η * x τ i) ∈ _
  convert h' using 1
  show _ = _root_.GlobalTheory.BK.E K l e ^ η * ((l : PowerSeries K) ^ n * x τ i)
  ring

open PowerSeries in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
private lemma eisenstein_zpow_smul_mem_baseChangeSpan_of_pow_smul [NeZero a] (H : ℕ)
    (hM : ∀ m ∈ P.M,
      _root_.GlobalTheory.BK.E K l e ^ H • m ∈ P.L)
    {m : _root_.GlobalTheory.BK.Vec K a ι} (hm : m ∈ P.Mext
      (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K))) :
    _root_.GlobalTheory.BK.Ezpow K l e H • m ∈ P.ext
      (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)) := by
  rw [mem_baseChangeAll_iff] at hm
  obtain ⟨n, hn⟩ := exists_uniform_pow_mul_mem (natCast_mem (_root_.GlobalTheory.BK.A O K) l)
    (fun t : ZMod a × ι => m t.1 t.2) (fun t => by
      have h := hm t.1 t.2
      unfold _root_.GlobalTheory.BK.invL at h
      obtain ⟨n, hn⟩ := _root_.GlobalTheory.BK.mem_away.1 h
      push_cast at hn
      exact ⟨n, hn⟩)
  have hv : (l : PowerSeries K) ^ n • m ∈ P.M := by
    rw [mem_allComponents_iff]
    intro τ i
    exact hn (τ, i)
  have h := (mem_frobeniusImageSpan_iff P).1 (hM _ hv)
  rw [mem_baseChangeSpan_iff, _root_.GlobalTheory.BK.Ezpow_natCast]
  intro τ i
  unfold _root_.GlobalTheory.BK.invL
  rw [_root_.GlobalTheory.BK.mem_away]
  refine ⟨n, ?_⟩
  push_cast
  have h' := h τ i
  rw [mulVec_smul_apply_eq_mul_mulVec_apply, mulVec_smul_apply_eq_mul_mulVec_apply] at h'
  rw [mulVec_smul_apply_eq_mul_mulVec_apply]
  convert h' using 1
  ring

open PowerSeries in

theorem _root_.GlobalTheory.BK.PhiMod.jumps_subset_Icc_iff : ∀ (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [_root_.GlobalTheory.BK.IsUnitBall O K] (l e a : ℕ) (ι : Type)
    [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
    [CompleteSpace K] (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) (η H : ℕ),
    P.jumps ⊆ Set.Icc (-(η : ℤ)) H ↔
      (∀ m ∈ P.M,
        _root_.GlobalTheory.BK.E K l e ^ H • m ∈ P.L) ∧
      ∀ m ∈ P.L,
        _root_.GlobalTheory.BK.E K l e ^ η • m ∈ P.M := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ P η H
  obtain ⟨N, hN⟩ := exists_eisenstein_pow_mul_matrix_mem_integral P
  have hLN : ∀ x ∈ P.ext
      (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)),
      _root_.GlobalTheory.BK.Ezpow K l e N • x ∈ P.Mext
        (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)) := by
    intro x hx
    rw [_root_.GlobalTheory.BK.Ezpow_natCast]
    exact eisenstein_pow_smul_mem_baseChangeAll P integral_le_invertPrime
      (fun τ i j => (hN τ i j).1) hx
  have hMN : ∀ m ∈ P.Mext
      (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)),
      _root_.GlobalTheory.BK.Ezpow K l e N • m ∈ P.ext
        (_root_.GlobalTheory.BK.invL l (_root_.GlobalTheory.BK.A O K)) := by
    intro m hm
    rw [_root_.GlobalTheory.BK.Ezpow_natCast]
    exact eisenstein_pow_smul_mem_baseChangeSpan P integral_le_invertPrime
      (fun τ i j => (hN τ i j).2) hm
  constructor
  · intro hJ
    have hconst : ∀ i : ℤ, (i < -(η : ℤ) ∨ (H : ℤ) < i) →
        P.filL (i + 1) = P.filL i := by
      intro i hi
      by_contra hne
      have hmem := Set.mem_Icc.1 (hJ (show i ∈ P.jumps from hne))
      omega
    have hlow : ∀ k : ℕ, P.filL (-(η : ℤ) - k) =
        P.filL (-(η : ℤ)) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [← ih, ← hconst (-(η : ℤ) - ((k + 1 : ℕ) : ℤ)) (Or.inl (by omega))]
        congr 1
        omega
    have hhigh : ∀ k : ℕ, P.filL ((H : ℤ) + 1 + k) =
        P.filL ((H : ℤ) + 1) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [← ih, ← hconst ((H : ℤ) + 1 + k) (Or.inr (by omega))]
        rfl
    have hLow := (hlow N).symm.trans
      (filL_eq_ext_of_le P N hLN (j := -(η : ℤ) - N) (by omega))
    have hHigh := (hhigh N).symm.trans
      (filL_eq_shiftE_of_ge P N hMN (j := (H : ℤ) + 1 + N) (by omega))
    exact ⟨fun m hm => eisenstein_pow_smul_mem_frobeniusImageSpan P H N (fun τ i j => (hN τ i j).2)
        (fun m hm => eisenstein_zpow_smul_mem_baseChangeSpan_invertPrime P H N hMN hHigh hm) hm,
      fun v hv => eisenstein_pow_smul_mem_allComponents P η N (fun τ i j => (hN τ i j).1)
        (fun x hx => eisenstein_zpow_smul_mem_baseChangeAll_invertPrime P η N hLN hLow hx) hv⟩
  · rintro ⟨hM, hL⟩ i hi
    have hi' : P.filL (i + 1) ≠ P.filL i := hi
    rw [Set.mem_Icc]
    by_contra hout
    apply hi'
    rcases not_and_or.1 hout with h | h
    · rw [filL_eq_ext_of_le P η
          (fun x hx => eisenstein_zpow_smul_mem_baseChangeAll_of_pow_smul P η hL hx) (j := i + 1) (by omega),
        filL_eq_ext_of_le P η
          (fun x hx => eisenstein_zpow_smul_mem_baseChangeAll_of_pow_smul P η hL hx) (j := i) (by omega)]
    · rw [filL_eq_shiftE_of_ge P H
          (fun m hm => eisenstein_zpow_smul_mem_baseChangeSpan_of_pow_smul P H hM hm) (j := i + 1) (by omega),
        filL_eq_shiftE_of_ge P H
          (fun m hm => eisenstein_zpow_smul_mem_baseChangeSpan_of_pow_smul P H hM hm) (j := i) (by omega)]

end GlobalTheory.BK.PhiMod
