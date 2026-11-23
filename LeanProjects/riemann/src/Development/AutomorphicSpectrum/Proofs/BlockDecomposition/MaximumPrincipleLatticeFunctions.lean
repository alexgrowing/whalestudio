import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClopenCoset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZpowMulVec
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZCore.MaxPrin

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ}

theorem exists_pow_val_lt {ϖ : k} (hϖ : ValuativeRel.valuation k ϖ < 1) (γ : ValuativeRel.ValueGroupWithZero k)
    (hγ : γ ≠ 0) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ValuativeRel.valuation k ϖ ^ n < γ := by
  have : MulArchimedean (ValuativeRel.ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ (Units.mk0 γ hγ)
  exact ⟨n, fun m hm => lt_of_le_of_lt (pow_le_pow_right_of_le_one' hϖ.le hm) hn⟩

theorem latZ_add (z : GL (Fin d) k) (a b : ℤ) : latZ z (a + b) = (latZ z b).act (z ^ a) := by
  rw [latZ, latZ, COSub.act_act, _root_.zpow_add]

theorem smul_mem_latZ (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k)) (hϖ0 : ϖ ≠ 0) (a b : ℤ)
    (w : Fin d → k) : ϖ ^ a • w ∈ (latZ z (a + b)).sub ↔ w ∈ (latZ z b).sub := by
  rw [latZ_add, ← zpow_mulVec z ϖ hz hϖ0 a w]
  exact COSub.mulVec_mem_act _

theorem scale_step (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (F : COSub k d → (Fin d → k) → ℂ)
    (hS : ∀ (L : COSub k d) (x : Fin d → k), F (L.act z) ((z : Matrix (Fin d) (Fin d) k).mulVec x) = F L x)
    (r : ℤ) (x : Fin d → k) : F (latZ z (r + 1)) (ϖ • x) = F (latZ z r) x := by
  have h := hS (latZ z r) x
  have e : (latZ z r).act z = latZ z (r + 1) := by
    rw [add_comm, latZ_add, zpow_one]
  rw [e, hz, Matrix.smul_mulVec, one_mulVec] at h
  exact h

theorem scale (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k)) (hϖ0 : ϖ ≠ 0)
    (F : COSub k d → (Fin d → k) → ℂ)
    (hS : ∀ (L : COSub k d) (x : Fin d → k), F (L.act z) ((z : Matrix (Fin d) (Fin d) k).mulVec x) = F L x)
    (r : ℤ) : ∀ x : Fin d → k, F (latZ z r) (ϖ ^ r • x) = F (latZ z 0) x := by
  induction r using Int.induction_on with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    rw [zpow_add₀ hϖ0, zpow_one, mul_comm, mul_smul, scale_step z ϖ hz F hS, ih]
  | pred n ih =>
    intro x
    have h := scale_step z ϖ hz F hS (-(n : ℤ) - 1) (ϖ ^ (-(n : ℤ) - 1) • x)
    rw [sub_add_cancel, smul_smul, ← zpow_one_add₀ hϖ0, add_sub_cancel, ih] at h
    exact h.symm

theorem scale_inv (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k)) (hϖ0 : ϖ ≠ 0)
    (F : COSub k d → (Fin d → k) → ℂ)
    (hS : ∀ (L : COSub k d) (x : Fin d → k), F (L.act z) ((z : Matrix (Fin d) (Fin d) k).mulVec x) = F L x)
    (r : ℤ) (y : Fin d → k) : F (latZ z r) y = F (latZ z 0) (ϖ ^ (-r) • y) := by
  rw [← scale z ϖ hz hϖ0 F hS r, smul_smul, ← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero, one_smul]

theorem shell_unif (z : GL (Fin d) k) (F : COSub k d → (Fin d → k) → ℂ) (c : ℂ)
    (hN : ∀ x : Fin d → k, x ≠ 0 → ∃ s : ℕ, ∀ y : Fin d → k, y - x ∈ (latZ z (s : ℤ)).sub → ∀ r : ℕ, s ≤ r →
      F (latZ z (r : ℤ)) y = c) :
    ∃ r₁ : ℕ, ∀ y : Fin d → k, y ∈ (latZ z 0).sub → y ∉ (latZ z 1).sub → ∀ r : ℕ, r₁ ≤ r →
      F (latZ z (r : ℤ)) y = c := by
  have hK : IsCompact (((latZ z 0).sub : Set (Fin d → k)) \ ((latZ z 1).sub : Set (Fin d → k))) :=
    (latZ z 0).isCompact.diff (latZ z 1).isOpen
  have h := hK.induction_on
    (p := fun A => ∃ s : ℕ, ∀ y ∈ A, ∀ r : ℕ, s ≤ r → F (latZ z (r : ℤ)) y = c)
    ⟨0, by simp⟩
    (fun A B hAB ⟨s, hs⟩ => ⟨s, fun y hy => hs y (hAB hy)⟩)
    (fun A B ⟨s, hs⟩ ⟨t, ht⟩ => ⟨max s t, fun y hy r hr => hy.elim
      (fun h => hs y h r (le_trans (le_max_left _ _) hr))
      (fun h => ht y h r (le_trans (le_max_right _ _) hr))⟩)
    (by
      intro x hx
      have hx0 : x ≠ 0 := fun h => hx.2 (h ▸ (latZ z 1).sub.zero_mem)
      obtain ⟨s, hs⟩ := hN x hx0
      exact ⟨{y | y - x ∈ (latZ z (s : ℤ)).sub},
        mem_nhdsWithin_of_mem_nhds ((isClopen_coset _ x).isOpen.mem_nhds
          (by simp [(latZ z (s : ℤ)).sub.zero_mem])), s, fun y hy r hr => hs y hy r hr⟩)
  obtain ⟨s, hs⟩ := h
  exact ⟨s, fun y h0 h1 r hr => hs y ⟨h0, h1⟩ r hr⟩

theorem exists_shell (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (w : Fin d → k) (hw : w ≠ 0) :
    ∃ m : ℤ, w ∈ (latZ z m).sub ∧ w ∉ (latZ z (m + 1)).sub := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
  have hvi : ValuativeRel.valuation k (w i) ≠ 0 := by simpa using hi
  have hv : 0 < ValuativeRel.valuation k ϖ := zero_lt_iff.2 (by simpa using hϖ0)
  have hbdd : ∃ b : ℤ, ∀ m : ℤ, w ∈ (latZ z m).sub → m ≤ b := by
    obtain ⟨N, hN⟩ := exists_pow_val_lt hϖ _ hvi
    refine ⟨N, fun m hm => ?_⟩
    by_contra hlt
    have hm0 : 0 ≤ m := by omega
    lift m to ℕ using hm0
    have h1 := (mem_latZ z ϖ hz hϖ0 _ w).1 hm i
    rw [zpow_natCast] at h1
    exact absurd h1 (not_le.2 (hN m (by omega)))
  have hinh : ∃ m : ℤ, w ∈ (latZ z m).sub := by
    have hall : ∀ᶠ n : ℕ in Filter.atTop, ∀ j, ValuativeRel.valuation k (w j) ≤
        (ValuativeRel.valuation k ϖ ^ n)⁻¹ := by
      refine Filter.eventually_all.2 fun j => ?_
      by_cases hj : ValuativeRel.valuation k (w j) = 0
      · exact Filter.Eventually.of_forall fun n => by rw [hj]; exact zero_le'
      · obtain ⟨N, hN⟩ := exists_pow_val_lt hϖ _ (inv_ne_zero hj)
        filter_upwards [Filter.eventually_ge_atTop N] with n hn
        exact (le_inv_comm₀ (zero_lt_iff.2 hj) (pow_pos hv n)).2 (hN n hn).le
    obtain ⟨n, hn⟩ := hall.exists
    refine ⟨-(n : ℤ), (mem_latZ z ϖ hz hϖ0 _ w).2 fun j => ?_⟩
    rw [_root_.zpow_neg, zpow_natCast]
    exact hn j
  obtain ⟨m, hm, hmax⟩ := Int.exists_greatest_of_bdd hbdd hinh
  exact ⟨m, hm, fun h => absurd (hmax _ h) (by omega)⟩

theorem far (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (F : COSub k d → (Fin d → k) → ℂ) (c : ℂ)
    (hS : ∀ (L : COSub k d) (x : Fin d → k), F (L.act z) ((z : Matrix (Fin d) (Fin d) k).mulVec x) = F L x)
    (r₁ : ℕ)
    (hr₁ : ∀ y : Fin d → k, y ∈ (latZ z 0).sub → y ∉ (latZ z 1).sub → ∀ r : ℕ, r₁ ≤ r →
      F (latZ z (r : ℤ)) y = c)
    (w : Fin d → k) (hw : w ∉ (latZ z (-(r₁ : ℤ))).sub) : F (latZ z 0) w = c := by
  have hw0 : w ≠ 0 := fun h => hw (h ▸ (latZ z (-(r₁ : ℤ))).sub.zero_mem)
  obtain ⟨m, hm, hm1⟩ := exists_shell z ϖ hz hϖ hϖ0 w hw0
  have hlt : m < -(r₁ : ℤ) := by
    by_contra hge
    exact hw (latZ_anti z ϖ hz hϖ hϖ0 _ _ (not_lt.1 hge) hm)
  have h0 : ϖ ^ (-m) • w ∈ (latZ z 0).sub := by
    have := (smul_mem_latZ z ϖ hz hϖ0 (-m) m w).2 hm
    rwa [neg_add_cancel] at this
  have h1 : ϖ ^ (-m) • w ∉ (latZ z 1).sub := by
    intro h
    have e : (1 : ℤ) = -m + (m + 1) := by ring
    rw [e] at h
    exact hm1 ((smul_mem_latZ z ϖ hz hϖ0 (-m) (m + 1) w).1 h)
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = -m := ⟨(-m).toNat, by omega⟩
  have h2 := hr₁ _ h0 h1 t (by omega)
  rw [ht, scale z ϖ hz hϖ0 F hS] at h2
  exact h2

theorem exists_vector_standard_lattice_not_sub {hd : 0 < d} (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) :
    ∃ e : Fin d → k, e ∈ (latZ z 0).sub ∧ e ∉ (latZ z 1).sub := by
  classical
  refine ⟨Pi.single ⟨0, hd⟩ 1, (mem_latZ z ϖ hz hϖ0 _ _).2 fun j => ?_, fun h => ?_⟩
  · rw [zpow_zero, Pi.single_apply]
    split_ifs <;> simp
  · have h1 := (mem_latZ z ϖ hz hϖ0 _ _).1 h ⟨0, hd⟩
    rw [zpow_one, Pi.single_eq_same, map_one] at h1
    exact absurd h1 (not_le.2 hϖ)

theorem eq_const_standard_lattice_refining (hd : 0 < d) (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (F : COSub k d → (Fin d → k) → ℂ) (c : ℂ)
    (hR : Refines F) (hP : ∀ (L : COSub k d) (x l : Fin d → k), l ∈ L.sub → F L (x + l) = F L x)
    (hS : ∀ (L : COSub k d) (x : Fin d → k), F (L.act z) ((z : Matrix (Fin d) (Fin d) k).mulVec x) = F L x)
    (r₁ : ℕ)
    (hfar : ∀ w : Fin d → k, w ∉ (latZ z (-(r₁ : ℤ))).sub → F (latZ z 0) w = c) (x : Fin d → k) :
    F (latZ z 0) x = c := by
  classical
  have hcont : Continuous (F (latZ z 0)) := by
    refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_)
    filter_upwards [(isClopen_coset (latZ z 0) x).isOpen.mem_nhds
      (by simp [(latZ z 0).sub.zero_mem])] with y hy
    have h := hP (latZ z 0) x (y - x) hy
    rwa [add_sub_cancel] at h
  obtain ⟨xs, -, hmax⟩ := (latZ z (-(r₁ : ℤ))).isCompact.exists_isMaxOn
    ⟨0, (latZ z (-(r₁ : ℤ))).sub.zero_mem⟩
    (f := fun x => ‖F (latZ z 0) x - c‖) (hcont.sub continuous_const).norm.continuousOn
  set M : ℝ := ‖F (latZ z 0) xs - c‖ with hM
  have hall : ∀ x, ‖F (latZ z 0) x - c‖ ≤ M := by
    intro x
    by_cases hx : x ∈ (latZ z (-(r₁ : ℤ))).sub
    · exact hmax hx
    · rw [hfar x hx, sub_self, norm_zero]
      exact norm_nonneg _
  have hle : (latZ z ((r₁ + 1 : ℕ) : ℤ)).sub ≤ (latZ z 0).sub :=
    latZ_anti z ϖ hz hϖ hϖ0 _ _ (by positivity)
  have hle1 : (latZ z ((r₁ + 1 : ℕ) : ℤ)).sub ≤ (latZ z 1).sub :=
    latZ_anti z ϖ hz hϖ hϖ0 _ _ (by push_cast; omega)
  obtain ⟨S, hSr⟩ := exists_reps _ _ hle
  have hsum := hR _ _ S hle hSr xs
  obtain ⟨e, he0, he1⟩ := exists_vector_standard_lattice_not_sub (hd := hd) z ϖ hz hϖ hϖ0
  have hex : ∃ s ∈ S, xs + s ∉ (latZ z 1).sub := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨s0, ⟨hs0, h0⟩, -⟩ := hSr.2 0 (latZ z 0).sub.zero_mem
    obtain ⟨s1, ⟨hs1, h1⟩, -⟩ := hSr.2 e he0
    apply he1
    have e' : e = (e - s1) + (xs + s1) - (xs + s0) - (0 - s0) := by abel
    rw [e']
    exact (latZ z 1).sub.sub_mem ((latZ z 1).sub.sub_mem ((latZ z 1).sub.add_mem (hle1 h1) (hcon s1 hs1))
      (hcon s0 hs0)) (hle1 h0)
  obtain ⟨ss, hss, hss1⟩ := hex
  let t : (Fin d → k) → ℂ := fun s => F (latZ z 0) (ϖ ^ (-((r₁ + 1 : ℕ) : ℤ)) • (xs + s)) - c
  have hts : t ss = 0 := by
    have hn : ϖ ^ (-((r₁ + 1 : ℕ) : ℤ)) • (xs + ss) ∉ (latZ z (-(r₁ : ℤ))).sub := by
      intro h
      have e' : -(r₁ : ℤ) = -((r₁ + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
      rw [e'] at h
      exact hss1 ((smul_mem_latZ z ϖ hz hϖ0 _ 1 _).1 h)
    simp only [t]
    rw [hfar _ hn, sub_self]
  have hid : (S.card : ℂ) * (F (latZ z 0) xs - c) = ∑ s ∈ S, t s := by
    simp only [t, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [mul_sub, hsum]
    congr 1
    exact Finset.sum_congr rfl fun s _ => scale_inv z ϖ hz hϖ0 F hS _ _
  have h1 : (S.card : ℝ) * M ≤ ∑ s ∈ S, ‖t s‖ := by
    have := norm_sum_le S t
    rw [← hid, norm_mul, Complex.norm_natCast] at this
    exact this
  have h2 : M ≤ ∑ s ∈ S, (M - ‖t s‖) := by
    have := Finset.single_le_sum (f := fun s => M - ‖t s‖) (fun s _ => sub_nonneg.2 (hall _)) hss
    simpa [hts] using this
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h2
  have hM0 : M ≤ 0 := by linarith
  have := (hall x).trans hM0
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

theorem eq_const (hd : 0 < d) (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (F : COSub k d → (Fin d → k) → ℂ) (c : ℂ)
    (hR : Refines F) (hP : ∀ (L : COSub k d) (x l : Fin d → k), l ∈ L.sub → F L (x + l) = F L x)
    (hS : ∀ (L : COSub k d) (x : Fin d → k), F (L.act z) ((z : Matrix (Fin d) (Fin d) k).mulVec x) = F L x)
    (hN : ∀ x : Fin d → k, x ≠ 0 → ∃ s : ℕ, ∀ y : Fin d → k, y - x ∈ (latZ z (s : ℤ)).sub → ∀ r : ℕ, s ≤ r →
      F (latZ z (r : ℤ)) y = c) (r : ℕ) (x : Fin d → k) : F (latZ z (r : ℤ)) x = c := by
  obtain ⟨r₁, hr₁⟩ := shell_unif z F c hN
  rw [scale_inv z ϖ hz hϖ0 F hS]
  exact eq_const_standard_lattice_refining hd z ϖ hz hϖ hϖ0 F c hR hP hS r₁ (far z ϖ hz hϖ hϖ0 F c hS r₁ hr₁) _

end GlobalTheory.CompanionTheory.BZCore.MaxPrin

end
