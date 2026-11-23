import Formalism.LocalToGlobal.GlobalTheory.GL4.PMsFrame

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions NumberField Formalism.MainNotions.flipTwoThree

section Count

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def msLat (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * (2 * D.R.f * Real.log (C₀ * (C₀ * D.R.f * (n : ℝ) ^ 2 * D.host.v ^ 2 * (Tu D u : ℝ) ^ 2))) +
    4 * D.R.f * n * ((n : ℝ) + 1) * (Real.log (C₀ * D.R.f * (n : ℝ) ^ 2 * D.host.v ^ 2 * (Tu D u : ℝ) ^ 2) / 2)

theorem msBound_eq (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (n : ℕ) :
    msBound D u C₀ n = msLat D u C₀ n +
      2 * D.R.f * (n : ℝ) ^ 2 * (Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1)) := rfl

def IsoCount (D : D7) (C₀ : ℝ) : Prop :=
  ∀ u : D.what₂.Word,
    (∀ i ≤ D.R.m, ∀ (ι : Type) [Fintype ι] (L : ι → Submodule (𝓞 D.host.E) (D.sp.X i).V),
      (∀ c, Submodule.IsLattice D.host.E (L c) ∧ LatT (D.sp.X i) (Tu D u ^ (2 * D.R.f)) (L c)) →
      ∃ R : Finset ι, (∀ c, ∃ r ∈ R, IsoLat (D.sp.X i) (L c) (L r)) ∧
        Real.log R.card ≤ msLat D u C₀ (D.R.N i)) ∧
    ∀ (ι : Type) [Fintype ι] (L : ι → Submodule (𝓞 D.host.E) D.sp.X'.V),
      (∀ c, Submodule.IsLattice D.host.E (L c) ∧ LatT D.sp.X' 1 (L c)) →
      ∃ R : Finset ι, (∀ c, ∃ r ∈ R, IsoLat D.sp.X' (L c) (L r)) ∧
        Real.log R.card ≤ msLat D u C₀ (D.R.N D.R.m - 1)

def DualIdx (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (M : ℕ), 0 < M →
    (∀ i ≤ D.R.m, ∀ L : Submodule (𝓞 D.host.E) (D.sp.X i).V, Submodule.IsLattice D.host.E L →
      LatT (D.sp.X i) (Tu D u ^ (2 * D.R.f)) L →
      (mulDual (D.sp.X i) M L).relIndex (dualSub (D.sp.X i) L) = M ^ (2 * D.R.f * D.R.N i)) ∧
    ∀ L : Submodule (𝓞 D.host.E) D.sp.X'.V, Submodule.IsLattice D.host.E L → LatT D.sp.X' 1 L →
      (mulDual D.sp.X' M L).relIndex (dualSub D.sp.X' L) = M ^ (2 * D.R.f * (D.R.N D.R.m - 1))

theorem two_le_rdE' (D : D7) : 2 ≤ D.host.rdE := by
  have h := (Formalism.BasicNotions.factRd D.R D.host).2.2
  have hf : (2 : ℝ) ≤ D.R.f := by
    have : 2 ≤ D.R.f := Nat.le_mul_of_pos_right 2 D.R.ord_pos
    exact_mod_cast this
  have h0 : 0 ≤ D.host.rdE := by
    refine le_trans ?_ (Formalism.BasicNotions.factRd D.R D.host).1
    positivity
  nlinarith

theorem one_le_hostv (D : D7) : 1 ≤ D.host.v := by
  have := two_le_rdE' D
  show 1 ≤ D.host.rdE / 2
  linarith

theorem one_le_f (D : D7) : 1 ≤ D.R.f := by
  exact Nat.mul_pos two_pos D.R.ord_pos

theorem msLat_nonneg (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (hC : 1 ≤ C₀) (n : ℕ) : 0 ≤ msLat D u C₀ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [msLat]
  have hv : 1 ≤ D.host.v := one_le_hostv D
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast one_le_f D
  have hT : (1 : ℝ) ≤ (Tu D u : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.one_lt.le
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 ≤ C₀ * D.R.f * (n : ℝ) ^ 2 * D.host.v ^ 2 * (Tu D u : ℝ) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hC hf) (one_le_pow₀ hn1)) (one_le_pow₀ hv)) (one_le_pow₀ hT)
  have h2 : 1 ≤ C₀ * (C₀ * D.R.f * (n : ℝ) ^ 2 * D.host.v ^ 2 * (Tu D u : ℝ) ^ 2) :=
    one_le_mul_of_one_le_of_one_le hC h1
  have l1 := Real.log_nonneg h1
  have l2 := Real.log_nonneg h2
  unfold msLat
  exact add_nonneg (mul_nonneg (by positivity) (mul_nonneg (by positivity) l2))
    (mul_nonneg (by positivity) (div_nonneg l1 (by norm_num)))

theorem log_card_le {K Rc Q n : ℕ} (hK : K ≤ Rc * Q ^ n) (hQ : 1 ≤ Q) (B : ℝ) (hR : Real.log Rc ≤ B)
    (hB : 0 ≤ B + n * Real.log Q) : Real.log K ≤ B + n * Real.log Q := by
  rcases Nat.eq_zero_or_pos K with h | h
  · rw [h, Nat.cast_zero, Real.log_zero]; exact hB
  have hRc : 0 < Rc := by
    rcases Nat.eq_zero_or_pos Rc with h' | h'
    · rw [h', zero_mul] at hK; omega
    · exact h'
  have hK' : (K : ℝ) ≤ (Rc : ℝ) * (Q : ℝ) ^ n := by exact_mod_cast hK
  have hpos : (0 : ℝ) < K := by exact_mod_cast h
  have hRc' : (0 : ℝ) < Rc := by exact_mod_cast hRc
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  calc Real.log K ≤ Real.log ((Rc : ℝ) * (Q : ℝ) ^ n) := Real.log_le_log hpos hK'
    _ = Real.log Rc + n * Real.log Q := by
        rw [Real.log_mul hRc'.ne' (pow_pos hQ' n).ne', Real.log_pow]
    _ ≤ B + n * Real.log Q := by linarith

theorem msCount_of (D : D7) (C₀ : ℝ) (hC : 1 ≤ C₀) (hI : IsoCount D C₀) (hQ : DualIdx D) : MsCount D C₀ := by
  intro u hT
  have hM0 : 0 < Tu D u * D.host.g 0 * D.host.g 1 := by
    have := (D.mem u).A.T_prime.pos; have := (D.host.g_prime 0).pos; have := (D.host.g_prime 1).pos
    positivity
  have hlogM : Real.log ((Tu D u * D.host.g 0 * D.host.g 1 : ℕ) : ℝ) =
      Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1) := by
    have := (D.mem u).A.T_prime.pos; have := (D.host.g_prime 0).pos; have := (D.host.g_prime 1).pos
    push_cast
    rw [mul_assoc, Real.log_mul (by positivity) (by positivity)]
  have hlg : 0 ≤ Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1) := by
    rw [← hlogM]; exact Real.log_nonneg (by exact_mod_cast hM0)
  have key : ∀ (n K Rc : ℕ), K ≤ Rc * ((Tu D u * D.host.g 0 * D.host.g 1) ^ (2 * D.R.f * n)) ^ n →
      Real.log Rc ≤ msLat D u C₀ n → Real.log K ≤ msBound D u C₀ n := by
    intro n K Rc hK hR
    have hQ1 : 1 ≤ (Tu D u * D.host.g 0 * D.host.g 1) ^ (2 * D.R.f * n) := Nat.one_le_pow _ _ hM0
    have hlogQ : (n : ℝ) * Real.log (((Tu D u * D.host.g 0 * D.host.g 1) ^ (2 * D.R.f * n) : ℕ) : ℝ) =
        2 * D.R.f * (n : ℝ) ^ 2 * (Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1)) := by
      rw [Nat.cast_pow, Real.log_pow, hlogM]; push_cast; ring
    have hB := log_card_le hK hQ1 _ hR (by
      rw [hlogQ]; exact add_nonneg (msLat_nonneg D u C₀ hC n) (mul_nonneg (by positivity) hlg))
    rw [hlogQ] at hB
    rw [msBound_eq]; exact hB
  refine ⟨fun i hi => ?_, ?_⟩
  · obtain ⟨hLat, e, he, hsep⟩ := hT.1 i hi
    obtain ⟨R, hR, hlog⟩ := (hI u).1 i hi _ (D.clsLat u i) (fun c => ⟨D.clsLat_lat u i c, hLat c⟩)
    refine key _ _ R.card ?_ hlog
    refine card_le_of_frames (D.sp.X i) _ (D.R.N i) (D.clsLat u i) e he hsep R hR _ (fun r _ => ?_)
    rw [(hQ u _ hM0).1 i hi _ (D.clsLat_lat u i r) (hLat r)]
    exact ⟨pow_ne_zero _ hM0.ne', le_rfl⟩
  · obtain ⟨LP, hLP, e, he, hsep⟩ := hT.2
    obtain ⟨R, hR, hlog⟩ := (hI u).2 _ LP hLP
    refine key _ _ R.card ?_ hlog
    refine card_le_of_frames D.sp.X' _ _ LP e he hsep R hR _ (fun r _ => ?_)
    rw [(hQ u _ hM0).2 _ (hLP r).1 (hLP r).2]
    exact ⟨pow_ne_zero _ hM0.ne', le_rfl⟩

end Count

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
