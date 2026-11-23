import Mathlib
import Formalism.PeriodIntegrals.UpqRep
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.HarishChandraParameters

open Matrix Finset

noncomputable section

namespace GlobalTheory.KTypeCompare

open GlobalTheory.IndefiniteRowSideFullHecke

variable {n : ℕ}

theorem root_eq (a b : Fin n) : PI.UpqRep.root a b = HarishChandraRootData.root a b := rfl

theorem Kset_eq (ε : Fin n → Bool) : PI.UpqRep.Kset ε = HarishChandraRootData.grpK ε := by
  ext g
  simp only [PI.UpqRep.Kset, HarishChandraRootData.grpK, Set.mem_ofPred_eq, PI.UpqRep.Jm]
  refine and_congr_right fun _ => ?_
  rw [← Matrix.ext_iff]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  constructor
  · intro h a b hab
    have h' := h a b
    cases ha : ε a <;> cases hb : ε b
    · exact absurd (ha.trans hb.symm) hab
    · simp [ha, hb] at h'
      first | exact h' | linear_combination (1 / 2 : ℂ) * h' | linear_combination (-1 / 2 : ℂ) * h'
    · simp [ha, hb] at h'
      first | exact h' | linear_combination (1 / 2 : ℂ) * h' | linear_combination (-1 / 2 : ℂ) * h'
    · exact absurd (ha.trans hb.symm) hab
  · intro h a b
    by_cases hab : ε a = ε b
    · rw [hab, mul_comm]
    · rw [h a b hab, zero_mul, mul_zero]

theorem isHCParam_iff (μ : Fin n → ℝ) : PI.UpqRep.IsHCParam μ ↔ HarishChandraRootData.IsHCParam μ := by
  unfold PI.UpqRep.IsHCParam HarishChandraRootData.IsHCParam
  exact and_congr_right fun _ => forall_congr' fun a => exists_congr fun m => sub_eq_iff_eq_add

theorem cDom_iff (ε : Fin n → Bool) (ω Λ : Fin n → ℝ) :
    PI.UpqRep.CDom ε ω Λ ↔ HarishChandraRootData.CptLE ε ω Λ := by
  unfold PI.UpqRep.CDom HarishChandraRootData.CptLE
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨fun x => c x.1 x.2, ?_⟩
    rw [h, ← Fintype.sum_prod_type', HarishChandraRootData.cptPairs, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with hx
    · rfl
    · have h0 : c x.1 x.2 = 0 := by
        by_contra h0
        exact hx (hc _ _ h0)
      simp [h0]
  · rintro ⟨c, h⟩
    refine ⟨fun a b => if a < b ∧ ε a = ε b then c (a, b) else 0, ?_, ?_⟩
    · intro a b hab
      by_contra hn
      exact hab (if_neg hn)
    · rw [h, ← Fintype.sum_prod_type', HarishChandraRootData.cptPairs, Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : x.1 < x.2 ∧ ε x.1 = ε x.2
      · simp [if_pos hx, root_eq]
      · simp [if_neg hx]

theorem torus_eq (θ : Fin n → ℝ) :
    (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) = HarishChandraRootData.torus θ := by
  unfold HarishChandraRootData.torus
  congr 1
  funext a
  rw [mul_comm]

theorem torus_mem (ε : Fin n → Bool) (θ : Fin n → ℝ) : HarishChandraRootData.torus θ ∈ HarishChandraRootData.grpK ε := by
  refine ⟨?_, fun a b hab => ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, HarishChandraRootData.torus, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp [Complex.conj_ofReal, Complex.conj_I]
  · have hne : a ≠ b := fun h => hab (h ▸ rfl)
    simp [HarishChandraRootData.torus, Matrix.diagonal_apply_ne _ hne]

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem isURepOn_iff (G : Set (Matrix (Fin n) (Fin n) ℂ))
    (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) :
    PI.UpqRep.IsURepOn G σ ↔ HarishChandraRootData.IsUnitaryRepOn G σ := by
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2⟩, h3, h4⟩

theorem isWtOn_iff_of_torus (G : Set (Matrix (Fin n) (Fin n) ℂ))
    (hG : ∀ θ, HarishChandraRootData.torus θ ∈ G)
    (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (ω : Fin n → ℝ) (v : H) :
    PI.UpqRep.IsWtOn G σ ω v ↔ v ∈ HarishChandraRootData.weightSpace σ ω := by
  change _ ↔ ∀ θ : Fin n → ℝ, σ (HarishChandraRootData.torus θ) v = HarishChandraRootData.wtChar ω θ • v
  unfold PI.UpqRep.IsWtOn HarishChandraRootData.wtChar
  simp only [torus_eq]
  constructor
  · intro h θ
    rw [h θ (hG θ), mul_comm Complex.I]
  · intro h θ _
    rw [h θ, mul_comm Complex.I]

theorem isWtOn_iff (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (ω : Fin n → ℝ) (v : H) :
    PI.UpqRep.IsWtOn (PI.UpqRep.Kset ε) σ ω v ↔ v ∈ HarishChandraRootData.weightSpace σ ω := by
  refine isWtOn_iff_of_torus _ (fun θ => ?_) σ ω v
  rw [Kset_eq]
  exact torus_mem ε θ

theorem isKStableOn_iff (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (S : Submodule ℂ H) :
    PI.UpqRep.IsKStableOn ε σ S ↔ HarishChandraRootData.KStable ε σ S := by
  unfold PI.UpqRep.IsKStableOn HarishChandraRootData.KStable
  rw [Kset_eq]

theorem isKTypeOf_iff (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (Λ : Fin n → ℝ) (S : Submodule ℂ H) :
    PI.UpqRep.IsKTypeOf ε σ Λ S ↔ HarishChandraRootData.IsKType ε σ S Λ := by
  simp only [PI.UpqRep.IsKTypeOf, isKStableOn_iff, isWtOn_iff, cDom_iff]
  constructor
  · rintro ⟨h1, h2, h3, ⟨v, hv, hv0, hw⟩, h5⟩
    exact ⟨h1, h2, h3, ⟨v, hv, hv0, hw⟩, fun ω v hv hw => h5 ω v hv hw.1 hw.2⟩
  · rintro ⟨h1, h2, h3, ⟨v, hv, hv0, hw⟩, h5⟩
    exact ⟨h1, h2, h3, ⟨v, hv, hv0, hw⟩, fun ω v hv hv0 hw => h5 ω v hv ⟨hv0, hw⟩⟩

theorem weight_integral {σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H} {ω : Fin n → ℝ} {v : H}
    (h : HarishChandraRootData.IsWeightVector σ ω v) (a : Fin n) : ∃ m : ℤ, ω a = m := by
  obtain ⟨hv0, hv⟩ := h
  have hw : ∀ θ, σ (HarishChandraRootData.torus θ) v = HarishChandraRootData.wtChar ω θ • v := hv
  obtain ⟨θ₁, hθ₁⟩ : ∃ θ₁ : Fin n → ℝ, θ₁ = Pi.single a (2 * Real.pi) := ⟨_, rfl⟩
  have htor : HarishChandraRootData.torus θ₁ = HarishChandraRootData.torus 0 := by
    unfold HarishChandraRootData.torus
    congr 1
    funext b
    by_cases hb : b = a
    · rw [hb, hθ₁, Pi.single_eq_same, Pi.zero_apply, Complex.ofReal_zero, mul_zero,
        Complex.exp_zero, ← Complex.exp_two_pi_mul_I]
      congr 1
      push_cast
      ring
    · simp [hθ₁, Pi.single_eq_of_ne hb]
  have h1 := hw θ₁
  rw [htor, hw 0] at h1
  have h0 : HarishChandraRootData.wtChar ω 0 = 1 := by simp [HarishChandraRootData.wtChar]
  rw [h0, one_smul] at h1
  have hc : HarishChandraRootData.wtChar ω θ₁ = 1 := by
    have hz : (HarishChandraRootData.wtChar ω θ₁ - 1) • v = 0 := by
      rw [sub_smul, ← h1, one_smul, sub_self]
    rcases smul_eq_zero.mp hz with hz | hz
    · exact sub_eq_zero.mp hz
    · exact absurd hz hv0
  unfold HarishChandraRootData.wtChar at hc
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hc
  refine ⟨m, ?_⟩
  have hsum : (∑ b, ω b * θ₁ b) = ω a * (2 * Real.pi) := by
    simp [hθ₁, Pi.single_apply]
  rw [hsum] at hm
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hc' : ((ω a : ℝ) : ℂ) = ((m : ℝ) : ℂ) := by
    apply mul_right_cancel₀ hpi
    push_cast at hm ⊢
    linear_combination hm
  exact_mod_cast hc'

theorem cptLE_pair {ε : Fin n → Bool} {ω Λ : Fin n → ℝ} (h : HarishChandraRootData.CptLE ε ω Λ) :
    ∑ i : Fin n, ((i : ℕ) : ℝ) * (Λ - ω) i ≤ 0 := by
  obtain ⟨c, hc⟩ := h
  rw [hc]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_nonpos
  intro x hx
  have hlt : x.1 < x.2 := (Finset.mem_filter.mp hx).2.1
  have hne : x.2 ≠ x.1 := (ne_of_lt hlt).symm
  have key : ∑ i : Fin n, ((i : ℕ) : ℝ) * ((c x : ℝ) * HarishChandraRootData.root x.1 x.2 i) =
      (c x : ℝ) * (((x.1 : ℕ) : ℝ) - ((x.2 : ℕ) : ℝ)) := by
    simp only [HarishChandraRootData.root, Pi.sub_apply, Pi.single_apply, mul_sub, Finset.sum_sub_distrib,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  rw [key]
  apply mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
  have : ((x.1 : ℕ) : ℝ) < ((x.2 : ℕ) : ℝ) := by exact_mod_cast hlt
  linarith

theorem highest_dominant {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H}
    (hσ : HarishChandraRootData.IsUnitaryRepOn (HarishChandraRootData.grpK ε) σ) {S : Submodule ℂ H} {Λ : Fin n → ℝ}
    (h : HarishChandraRootData.IsKType ε σ S Λ) {a b : Fin n} (hab : a < b) (hε : ε a = ε b) : Λ b ≤ Λ a := by
  set s : Equiv.Perm (Fin n) := Equiv.swap a b with hs_def
  have hεs : ∀ i, ε (s i) = ε i := by
    intro i
    rw [hs_def, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, hε]
    · rw [h2, hε]
    · rfl
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin n) (Fin n) ℂ,
      P = Matrix.of fun i j => if s i = j then (1 : ℂ) else 0 := ⟨_, rfl⟩
  have hPl : ∀ M : Matrix (Fin n) (Fin n) ℂ, P * M = M.submatrix s id := by
    intro M
    ext i k
    simp [hP, Matrix.mul_apply, ite_mul]
  have hPr : ∀ M : Matrix (Fin n) (Fin n) ℂ, M * P = M.submatrix id s := by
    intro M
    ext i k
    simp [hP, Matrix.mul_apply, mul_ite, hs_def, Equiv.swap_apply_eq_iff]
  have hPstar : star P = P := by
    ext i j
    simp only [hP, Matrix.star_apply, Matrix.of_apply]
    by_cases hij : s i = j
    · have hji : s j = i := by rw [← hij, hs_def, Equiv.swap_apply_self]
      simp [hij, hji]
    · have hji : s j ≠ i := fun h' => hij (by rw [← h', hs_def, Equiv.swap_apply_self])
      simp [hij, hji]
  have hPP : P * P = 1 := by
    rw [hPl]
    ext i k
    simp [hP, Matrix.one_apply, hs_def]
  have hPK : P ∈ HarishChandraRootData.grpK ε := by
    refine ⟨?_, fun i j hij => ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff, hPstar, hPP]
    · rw [hP, Matrix.of_apply, if_neg]
      rintro rfl
      exact hij (hεs i).symm
  have hcomm : ∀ θ : Fin n → ℝ, HarishChandraRootData.torus θ * P = P * HarishChandraRootData.torus (fun i => θ (s i)) := by
    intro θ
    rw [hPl, hPr]
    ext i k
    simp only [HarishChandraRootData.torus, Matrix.submatrix_apply, id, Matrix.diagonal_apply]
    by_cases hik : i = s k
    · have hk : s i = k := by rw [hik, hs_def, Equiv.swap_apply_self]
      rw [if_pos hik, if_pos hk, hk, ← hik]
    · have hk : s i ≠ k := fun h' => hik (by rw [← h', hs_def, Equiv.swap_apply_self])
      rw [if_neg hik, if_neg hk]
  have hTK : ∀ θ, HarishChandraRootData.torus θ ∈ HarishChandraRootData.grpK ε := torus_mem ε
  obtain ⟨v, hvS, hv0, hvw⟩ := h.exists_highest
  have hvw' : ∀ θ, σ (HarishChandraRootData.torus θ) v = HarishChandraRootData.wtChar Λ θ • v := hvw
  have hwS : σ P v ∈ S := h.stable P hPK v hvS
  have hw0 : σ P v ≠ 0 := by
    intro h0
    apply hv0
    have hn := hσ.norm_map P hPK v
    rw [h0, norm_zero] at hn
    exact norm_eq_zero.mp hn.symm
  have hww : HarishChandraRootData.IsWeightVector σ (fun i => Λ (s i)) (σ P v) := by
    refine ⟨hw0, ?_⟩
    show ∀ θ : Fin n → ℝ,
      σ (HarishChandraRootData.torus θ) (σ P v) = HarishChandraRootData.wtChar (fun i => Λ (s i)) θ • σ P v
    intro θ
    have hre : ∑ i, Λ i * θ (s i) = ∑ i, Λ (s i) * θ i := by
      rw [← Equiv.sum_comp s (fun i => Λ i * θ (s i))]
      simp [hs_def, Equiv.swap_apply_self]
    calc σ (HarishChandraRootData.torus θ) (σ P v) = σ (HarishChandraRootData.torus θ * P) v := by
          rw [hσ.map_mul _ (hTK θ) _ hPK]
          rfl
      _ = σ (P * HarishChandraRootData.torus (fun i => θ (s i))) v := by rw [hcomm]
      _ = σ P (σ (HarishChandraRootData.torus (fun i => θ (s i))) v) := by
          rw [hσ.map_mul _ hPK _ (hTK _)]
          rfl
      _ = HarishChandraRootData.wtChar Λ (fun i => θ (s i)) • σ P v := by
          rw [hvw', ContinuousLinearMap.map_smul]
      _ = HarishChandraRootData.wtChar (fun i => Λ (s i)) θ • σ P v := by
          unfold HarishChandraRootData.wtChar
          rw [hre]
  have hle := cptLE_pair (h.le_highest _ (σ P v) hwS hww)
  have hsum : ∑ i : Fin n, ((i : ℕ) : ℝ) * (Λ - fun i => Λ (s i)) i =
      (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) * (Λ a - Λ b) := by
    rw [Fintype.sum_eq_add a b (ne_of_lt hab)]
    · simp only [Pi.sub_apply, hs_def, Equiv.swap_apply_left, Equiv.swap_apply_right]
      ring
    · rintro x ⟨hxa, hxb⟩
      simp [hs_def, Equiv.swap_apply_of_ne_of_ne hxa hxb]
  rw [hsum] at hle
  have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  nlinarith

end Rep

theorem UJset_allPos (k : ℕ) : PI.UpqRep.UJset (PI.UpqRep.allPos k) =
    (Matrix.unitaryGroup (Fin k) ℂ : Set (Matrix (Fin k) (Fin k) ℂ)) := by
  have hJ : PI.UpqRep.Jm (PI.UpqRep.allPos k) = 1 := by
    simp [PI.UpqRep.Jm, PI.UpqRep.allPos, Matrix.diagonal_one]
  ext g
  simp only [PI.UpqRep.UJset, PI.UpqRep.inUJ, Set.mem_ofPred_eq, hJ, Matrix.mul_one,
    SetLike.mem_coe, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]

theorem lowK_allPos (k : ℕ) (u : Fin k → ℝ) :
    PI.UpqRep.lowK (PI.UpqRep.allPos k) u = u - HarishChandraRootData.rhoU k := by
  funext a
  have ha : (a : ℕ) + 1 ≤ k := a.isLt
  have h1 : ((Finset.univ.filter fun b : Fin k => a < b).card : ℝ) = (k : ℝ) - 1 - (a : ℕ) := by
    rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi, Nat.cast_sub (show (a : ℕ) ≤ k - 1 by omega),
      Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one]
  have h2 : ((Finset.univ.filter fun b : Fin k => b < a).card : ℝ) = (a : ℕ) := by
    rw [Finset.filter_gt_eq_Iio, Fin.card_Iio]
  simp only [PI.UpqRep.lowK, PI.UpqRep.rhoN, PI.UpqRep.rhoC, PI.UpqRep.allPos, HarishChandraRootData.rhoU,
    Pi.add_apply, Pi.sub_apply, ne_eq, not_true_eq_false, and_false, Finset.filter_false,
    Finset.card_empty, and_true, h1, h2, Nat.cast_zero, sub_zero, zero_div, add_zero]
  ring

theorem isHCTypeU_iff {k : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u : Fin k → ℝ) (π : Matrix (Fin k) (Fin k) ℂ → H →L[ℂ] H) :
    PI.UpqRep.IsHCTypeU k u π ↔ HarishChandraRootData.IsCompactIrrep π u := by
  have hc : PI.UpqRep.allPos k = fun _ => true := rfl
  unfold PI.UpqRep.IsHCTypeU
  rw [isURepOn_iff, UJset_allPos, isKTypeOf_iff, lowK_allPos, hc]
  constructor
  · rintro ⟨-, -, hrep, htype⟩
    have hrep' : HarishChandraRootData.IsUnitaryRepOn (HarishChandraRootData.grpK (fun _ : Fin k => true)) π := by
      rw [HarishChandraRootData.grpK_const]
      exact hrep
    obtain ⟨v, -, hv⟩ := htype.exists_highest
    refine ⟨⟨fun a b hab => ?_, fun i => ?_⟩, hrep, htype⟩
    · have hd := highest_dominant hrep' htype hab rfl
      simp only [Pi.sub_apply, HarishChandraRootData.rhoU] at hd
      have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
      linarith
    · obtain ⟨m, hm⟩ := weight_integral hv i
      refine ⟨m - ((i : ℕ) : ℤ), ?_⟩
      simp only [Pi.sub_apply, HarishChandraRootData.rhoU] at hm
      push_cast
      linarith
  · rintro ⟨-, hrep, htype⟩
    obtain ⟨v, -, hv0, -⟩ := htype.exists_highest
    have := htype.finDim
    exact ⟨nontrivial_of_ne v 0 hv0, LinearEquiv.finiteDimensional Submodule.topEquiv, hrep, htype⟩

end GlobalTheory.KTypeCompare
