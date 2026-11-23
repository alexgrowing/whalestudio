import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreLie

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

namespace Harm

section MP

variable {σ : Type}

theorem hc_hc (d e : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent d (homogeneousComponent e P) = if d = e then homogeneousComponent e P else 0 :=
  homogeneousComponent_of_mem (homogeneousComponent_mem e P)

theorem hc_ext {P Q : MvPolynomial σ ℂ} (h : ∀ d, homogeneousComponent d P = homogeneousComponent d Q) : P = Q := by
  ext m
  have := congrArg (coeff m) (h m.degree)
  simpa [coeff_homogeneousComponent] using this

theorem mp_hc (A : Module.End ℂ (MvPolynomial σ ℂ)) (P : MvPolynomial σ ℂ) (d : ℕ) :
    homogeneousComponent d (minusPart A P) = homogeneousComponent d (A (homogeneousComponent (d + 2) P)) := by
  have hfin : Function.HasFiniteSupport
      (fun e => homogeneousComponent e (A (homogeneousComponent (e + 2) P))) := by
    apply (Set.finite_Iic P.totalDegree).subset
    intro e he
    by_contra hlt
    apply he
    simp only [Set.mem_Iic, not_le] at hlt
    simp only
    rw [homogeneousComponent_eq_zero (e + 2) P (by omega)]
    simp
  unfold minusPart
  rw [map_finsum _ hfin, finsum_eq_single _ d]
  · rw [hc_hc, if_pos rfl]
  · intro e he
    rw [hc_hc, if_neg (Ne.symm he)]

theorem mp_comm (T A B : Module.End ℂ (MvPolynomial σ ℂ))
    (hT : ∀ e P, homogeneousComponent e (T P) = T (homogeneousComponent e P))
    (h : T * A - A * T = B) (g : MvPolynomial σ ℂ) :
    T (minusPart A g) - minusPart A (T g) = minusPart B g := by
  apply hc_ext
  intro d
  have e1 : homogeneousComponent d (T (minusPart A g)) =
      homogeneousComponent d (T (A (homogeneousComponent (d + 2) g))) := by
    rw [hT, mp_hc, ← hT]
  have e2 : homogeneousComponent d (minusPart A (T g)) =
      homogeneousComponent d (A (T (homogeneousComponent (d + 2) g))) := by
    rw [mp_hc, hT]
  rw [map_sub, e1, e2, mp_hc, ← h, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, map_sub]

theorem mp_sub (A B : Module.End ℂ (MvPolynomial σ ℂ)) (g : MvPolynomial σ ℂ) :
    minusPart (A - B) g = minusPart A g - minusPart B g := by
  apply hc_ext
  intro d
  simp only [map_sub, mp_hc, LinearMap.sub_apply]

theorem mp_zero (g : MvPolynomial σ ℂ) : minusPart (0 : Module.End ℂ (MvPolynomial σ ℂ)) g = 0 := by
  apply hc_ext
  intro d
  simp [mp_hc]

theorem mp_add_right (A : Module.End ℂ (MvPolynomial σ ℂ)) (g g' : MvPolynomial σ ℂ) :
    minusPart A (g + g') = minusPart A g + minusPart A g' := by
  refine hc_ext fun d => ?_
  simp only [map_add, mp_hc]

theorem mp_smul_right (A : Module.End ℂ (MvPolynomial σ ℂ)) (c : ℂ) (g : MvPolynomial σ ℂ) :
    minusPart A (c • g) = c • minusPart A g := by
  refine hc_ext fun d => ?_
  simp only [map_smul, mp_hc]

end MP

theorem isPC_Eab {m n : ℕ} {a b : Ix m n} (h : ¬ sameBlock a b) : IsPC (Eab a b) := by
  intro x y hxy
  simp only [Eab, Matrix.single_apply]
  split_ifs with hh
  · obtain ⟨rfl, rfl⟩ := hh
    exact absurd hxy h
  · rfl

theorem sb_iff {m n : ℕ} (a b : Ix m n) : sameBlock a b ↔ a.isLeft = b.isLeft :=
  PI.FockOneDegW.Core.side_sb a b

theorem isPC_brk {m n : ℕ} {a b : Ix m n} (h : sameBlock a b) {Z : Mat m n} (hZ : IsPC Z) :
    IsPC (Eab a b * Z - Z * Eab a b) := by
  intro x y hxy
  rw [sb_iff] at h hxy
  have hZ' : ∀ u v : Ix m n, u.isLeft = v.isLeft → Z u v = 0 :=
    fun u v huv => hZ u v ((sb_iff u v).2 huv)
  have h1 : ∀ k, Eab a b x k * Z k y = 0 := by
    intro k
    simp only [Eab, Matrix.single_apply]
    split_ifs with hh
    · obtain ⟨rfl, rfl⟩ := hh
      rw [one_mul]
      exact hZ' _ _ (h.symm.trans hxy)
    · rw [zero_mul]
  have h2 : ∀ k, Z x k * Eab a b k y = 0 := by
    intro k
    simp only [Eab, Matrix.single_apply]
    split_ifs with hh
    · obtain ⟨rfl, rfl⟩ := hh
      rw [mul_one]
      exact hZ' _ _ (hxy.trans h.symm)
    · rw [mul_zero]
  simp only [Matrix.sub_apply, Matrix.mul_apply, h1, h2, Finset.sum_const_zero, sub_zero]

variable {p q r s : ℕ}

theorem homogComponent_comm_first_action {a b : Ix p q} (h : sameBlock a b) (e : ℕ) (P : Pol p q r s) :
    homogeneousComponent e (fockAct1 p q r s (Eab a b) P) =
      fockAct1 p q r s (Eab a b) (homogeneousComponent e P) := by
  exact PI.FockOneDegW.kernel_highest_weight p q r s a b h e P

theorem homogComponent_comm_second_action {a b : Ix r s} (h : sameBlock a b) (e : ℕ) (P : Pol p q r s) :
    homogeneousComponent e (fockAct2 p q r s (Eab a b) P) =
      fockAct2 p q r s (Eab a b) (homogeneousComponent e P) := by
  apply PI.FockOneDegW.Swap.rename_sw_injective p q r s
  rw [← PI.FockOneDegW.Swap.hc_rename, PI.FockOneDegW.Swap.rename_fockAct2,
    PI.FockOneDegW.kernel_highest_weight r s p q a b h, PI.FockOneDegW.Swap.hc_rename,
    PI.FockOneDegW.Swap.rename_fockAct2]

theorem minusPart_second_action_Eab {c d : Ix r s} (h : ¬ sameBlock c d) (g : Pol p q r s) :
    minusPart (fockAct2 p q r s (Eab c d)) g = - PI.FockOneDegW.lowOp (p := p) (q := q) c d g := by
  rw [PI.FockOneDegW.minus2_eq _ (isPC_Eab h)]
  congr 1
  rw [Finset.sum_eq_single c, Finset.sum_eq_single d]
  · simp [Eab]
  · intro y _ hy
    simp [Eab, Matrix.single_apply, Ne.symm hy]
  · simp
  · intro x _ hx
    refine Finset.sum_eq_zero (fun y _ => ?_)
    simp [Eab, Matrix.single_apply, Ne.symm hx]
  · simp

def low1 (a b : Ix p q) : Module.End ℂ (Pol p q r s) :=
  ∑ c : Ix r s, if linePos ((b, c) : Ln p q r s) = true then
    (pderiv ((a, c) : Ln p q r s)).toLinearMap * (pderiv ((b, c) : Ln p q r s)).toLinearMap
  else 0

open PI.FockOneDegW.Swap in
theorem rename_first_lowering (a b : Ix p q) (P : Pol p q r s) :
    rename (sw p q r s) (low1 a b P) =
      PI.FockOneDegW.lowOp (p := r) (q := s) a b (rename (sw p q r s) P) := by
  rw [PI.FockOneDegW.RedOps.lowOp_apply]
  unfold low1
  rw [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hl : linePos ((c, b) : Ln r s p q) = linePos ((b, c) : Ln p q r s) := linePos_sw (b, c)
  rw [hl]
  split_ifs
  · change rename (sw p q r s) (pderiv (a, c) (pderiv (b, c) P)) = _
    rw [rename_pderiv, rename_pderiv]
    rfl
  · simp

open PI.FockOneDegW.Swap in
theorem minus1_eq (Z : Mat p q) (hZ : IsPC Z) (P : Pol p q r s) :
    minusPart (fockAct1 p q r s Z) P = -∑ a, ∑ b, Z a b • low1 a b P := by
  apply rename_sw_injective p q r s
  rw [minusPart_rename (sw p q r s) _ _ (fun Q => (rename_fockAct1 Z Q).symm) P,
    PI.FockOneDegW.minus2_eq _ hZ]
  simp only [map_neg, map_sum, map_smul, rename_first_lowering]

theorem first_lowering_commute_lowering (a b : Ix p q) (c d : Ix r s) :
    Commute (low1 (r := r) (s := s) a b) (PI.FockOneDegW.lowOp (p := p) (q := q) c d) := by
  unfold low1 PI.FockOneDegW.lowOp
  refine Commute.sum_left _ _ _ fun x _ => Commute.sum_right _ _ _ fun y _ => ?_
  split_ifs
  · have hp : ∀ u v : Ln p q r s, Commute ((pderiv u).toLinearMap : Module.End ℂ (Pol p q r s))
        (pderiv v).toLinearMap := fun u v => pd_pd u v
    exact ((hp _ _).mul_right (hp _ _)).mul_left ((hp _ _).mul_right (hp _ _))
  · exact Commute.zero_right _
  · exact Commute.zero_left _
  · exact Commute.zero_left _

end Harm

open Harm

variable {p q r s : ℕ}

private theorem minusPart_zero {σ : Type} (A : Module.End ℂ (MvPolynomial σ ℂ)) :
    minusPart A (0 : MvPolynomial σ ℂ) = 0 := by
  simpa using mp_smul_right A 0 0

theorem mem_harm1_iff (g : Pol p q r s) : g ∈ harm1 p q r s ↔
    ∀ Z : Mat p q, IsPC Z → minusPart (fockAct1 p q r s Z) g = 0 := by
  unfold harm1
  constructor
  · intro hg Z hZ
    induction hg using Submodule.span_induction with
    | mem x hx => exact hx.1 rfl Z hZ
    | zero => exact minusPart_zero _
    | add x y _ _ hx hy => rw [mp_add_right, hx, hy, add_zero]
    | smul c x _ hx => rw [mp_smul_right, hx, smul_zero]
  · intro h
    exact Submodule.subset_span ⟨fun _ => h, fun h' => absurd h' Bool.false_ne_true⟩

private theorem minusPart_fockAct2_eq_zero_iff_lowOp (g : Pol p q r s) :
    (∀ Y : Mat r s, IsPC Y → minusPart (fockAct2 p q r s Y) g = 0) ↔
      ∀ c d : Ix r s, ¬ sameBlock c d → PI.FockOneDegW.lowOp (p := p) (q := q) c d g = 0 := by
  constructor
  · intro h c d hcd
    have h1 := h (Eab c d) (isPC_Eab hcd)
    rw [minusPart_second_action_Eab hcd, neg_eq_zero] at h1
    exact h1
  · intro h Y hY
    rw [PI.FockOneDegW.minus2_eq Y hY, neg_eq_zero]
    refine Finset.sum_eq_zero (fun c _ => Finset.sum_eq_zero (fun d _ => ?_))
    by_cases hcd : sameBlock c d
    · rw [hY c d hcd, zero_smul]
    · rw [h c d hcd, smul_zero]

private theorem mem_jHarm_iff' (g : Pol p q r s) : g ∈ jHarm p q r s ↔
    (∀ Z : Mat p q, IsPC Z → minusPart (fockAct1 p q r s Z) g = 0) ∧
      ∀ Y : Mat r s, IsPC Y → minusPart (fockAct2 p q r s Y) g = 0 := by
  unfold jHarm
  constructor
  · intro hg
    induction hg using Submodule.span_induction with
    | mem x hx => exact ⟨hx.1, hx.2⟩
    | zero => exact ⟨fun Z _ => minusPart_zero _, fun Y _ => minusPart_zero _⟩
    | add x y _ _ hx hy =>
      exact ⟨fun Z hZ => by rw [mp_add_right, hx.1 Z hZ, hy.1 Z hZ, add_zero],
        fun Y hY => by rw [mp_add_right, hx.2 Y hY, hy.2 Y hY, add_zero]⟩
    | smul c x _ hx =>
      exact ⟨fun Z hZ => by rw [mp_smul_right, hx.1 Z hZ, smul_zero],
        fun Y hY => by rw [mp_smul_right, hx.2 Y hY, smul_zero]⟩
  · intro h
    exact Submodule.subset_span ⟨h.1, h.2⟩

theorem mem_jHarm_iff (g : Pol p q r s) : g ∈ jHarm p q r s ↔ g ∈ harm1 p q r s ∧
    ∀ c d : Ix r s, ¬ sameBlock c d → PI.FockOneDegW.lowOp (p := p) (q := q) c d g = 0 := by
  rw [mem_jHarm_iff', mem_harm1_iff, minusPart_fockAct2_eq_zero_iff_lowOp]

private theorem minusPart_apply_eq_zero_of_commutator {σ : Type} (T A B : Module.End ℂ (MvPolynomial σ ℂ))
    (hT : ∀ e P, homogeneousComponent e (T P) = T (homogeneousComponent e P))
    (h : T * A - A * T = B) {x : MvPolynomial σ ℂ} (hA : minusPart A x = 0) (hB : minusPart B x = 0) :
    minusPart A (T x) = 0 := by
  have h1 := mp_comm T A B hT h x
  rw [hA, hB, map_zero, zero_sub, neg_eq_zero] at h1
  exact h1

theorem harmonic_stable_first_action : KSt (units (fockAct1 p q r s)) (harm1 p q r s) := by
  unfold KSt units
  intro a b hab x hx
  rw [mem_harm1_iff] at hx ⊢
  intro Z hZ
  exact minusPart_apply_eq_zero_of_commutator _ _ _ (homogComponent_comm_first_action hab) (lie1 p q r s _ _) (hx Z hZ) (hx _ (isPC_brk hab hZ))

theorem harmonic_stable_second_action : KSt (units (fockAct2 p q r s)) (harm1 p q r s) := by
  unfold KSt units
  intro a b hab x hx
  rw [mem_harm1_iff] at hx ⊢
  intro Z hZ
  exact minusPart_apply_eq_zero_of_commutator _ _ 0 (homogComponent_comm_second_action hab) (by rw [fockAct1_fockAct2_commute, sub_self]) (hx Z hZ) (mp_zero x)

theorem jHarmonic_stable_first_action : KSt (units (fockAct1 p q r s)) (jHarm p q r s) := by
  unfold KSt units
  intro a b hab x hx
  rw [mem_jHarm_iff'] at hx ⊢
  exact ⟨fun Z hZ => minusPart_apply_eq_zero_of_commutator _ _ _ (homogComponent_comm_first_action hab) (lie1 p q r s _ _) (hx.1 Z hZ) (hx.1 _ (isPC_brk hab hZ)),
    fun Y hY => minusPart_apply_eq_zero_of_commutator _ _ 0 (homogComponent_comm_first_action hab) (by rw [fockAct1_fockAct2_commute, sub_self]) (hx.2 Y hY) (mp_zero x)⟩

theorem jHarmonic_stable_second_action : KSt (units (fockAct2 p q r s)) (jHarm p q r s) := by
  unfold KSt units
  intro a b hab x hx
  rw [mem_jHarm_iff'] at hx ⊢
  exact ⟨fun Z hZ => minusPart_apply_eq_zero_of_commutator _ _ 0 (homogComponent_comm_second_action hab) (by rw [fockAct1_fockAct2_commute, sub_self]) (hx.1 Z hZ) (mp_zero x),
    fun Y hY => minusPart_apply_eq_zero_of_commutator _ _ _ (homogComponent_comm_second_action hab) (lie2 p q r s _ _) (hx.2 Y hY) (hx.2 _ (isPC_brk hab hY))⟩

theorem homogeneous_stable_first_action (d : ℕ) : KSt (units (fockAct1 p q r s)) (homog (Ix p q × Ix r s) d) := by
  unfold KSt units
  intro a b hab P hP
  have hP' : P = homogeneousComponent d P := by rw [homogeneousComponent_of_mem hP, if_pos rfl]
  rw [hP', ← homogComponent_comm_first_action hab]
  exact homogeneousComponent_mem _ _

theorem homogeneous_stable_second_action (d : ℕ) : KSt (units (fockAct2 p q r s)) (homog (Ix p q × Ix r s) d) := by
  unfold KSt units
  intro a b hab P hP
  have hP' : P = homogeneousComponent d P := by rw [homogeneousComponent_of_mem hP, if_pos rfl]
  rw [hP', ← homogComponent_comm_second_action hab]
  exact homogeneousComponent_mem _ _

theorem polChi_stable_second_action (c : ℂ) (W : Mat r s) {g : Pol p q r s} (hg : g ∈ polChi p q r s c) :
    fockAct2 p q r s W g ∈ polChi p q r s c := by
  unfold polChi jointEig at *
  rw [Submodule.mem_iInf] at hg ⊢
  intro Z
  have h1 := hg Z
  rw [LinearMap.mem_ker] at h1 ⊢
  have hc := fockAct1_fockAct2_commute (p := p) (q := q) (r := r) (s := s) Z.1 W
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at h1 ⊢
  rw [← Module.End.mul_apply, hc, Module.End.mul_apply, ← map_smul, ← map_sub, h1, map_zero]

theorem harmonic_stable_lowering {c d : Ix r s} (hcd : ¬ sameBlock c d) {g : Pol p q r s} (hg : g ∈ harm1 p q r s) :
    PI.FockOneDegW.lowOp (p := p) (q := q) c d g ∈ harm1 p q r s := by
  rw [mem_harm1_iff] at hg ⊢
  intro Z hZ
  have h := hg Z hZ
  rw [minus1_eq Z hZ] at h ⊢
  have e : ∀ a b, low1 a b (PI.FockOneDegW.lowOp (p := p) (q := q) c d g) =
      PI.FockOneDegW.lowOp (p := p) (q := q) c d (low1 a b g) :=
    fun a b => LinearMap.congr_fun (first_lowering_commute_lowering a b c d).eq g
  have h2 := congrArg (PI.FockOneDegW.lowOp (p := p) (q := q) c d) h
  simpa only [map_neg, map_sum, map_smul, map_zero, e] using h2

private theorem homogeneousComponent_fockAct1_of_isKC (Z : Mat p q) (hZ : IsKC Z) (e : ℕ) (P : Pol p q r s) :
    homogeneousComponent e (fockAct1 p q r s Z P) = fockAct1 p q r s Z (homogeneousComponent e P) := by
  have hZs : Z = ∑ a, ∑ b, Z a b • Eab a b := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
    simp only [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hZs]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  by_cases hab : sameBlock a b
  · rw [homogComponent_comm_first_action hab]
  · rw [hZ a b hab, zero_smul, zero_smul]

theorem polChi_low (c0 : ℂ) {c d : Ix r s} (hcd : ¬ sameBlock c d) {g : Pol p q r s}
    (hg : g ∈ polChi p q r s c0) : PI.FockOneDegW.lowOp (p := p) (q := q) c d g ∈ polChi p q r s c0 := by
  unfold polChi jointEig at *
  rw [Submodule.mem_iInf] at hg ⊢
  intro Z
  have h1 := hg Z
  rw [LinearMap.mem_ker] at h1 ⊢
  have hcomm : fockAct1 p q r s Z.1 (PI.FockOneDegW.lowOp (p := p) (q := q) c d g) =
      PI.FockOneDegW.lowOp (p := p) (q := q) c d (fockAct1 p q r s Z.1 g) := by
    have h2 := mp_comm (fockAct1 p q r s Z.1) (fockAct2 p q r s (Eab c d)) 0 (homogeneousComponent_fockAct1_of_isKC Z.1 Z.2)
      (by rw [fockAct1_fockAct2_commute, sub_self]) g
    rw [mp_zero, minusPart_second_action_Eab hcd, minusPart_second_action_Eab hcd, map_neg, sub_eq_zero] at h2
    exact neg_inj.mp h2
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at h1 ⊢
  rw [hcomm, ← map_smul, ← map_sub, h1, map_zero]

theorem low_homog (c d : Ix r s) {e : ℕ} {g : Pol p q r s} (hg : g ∈ homog (Ix p q × Ix r s) (e + 2)) :
    PI.FockOneDegW.lowOp (p := p) (q := q) c d g ∈ homog (Ix p q × Ix r s) e := by
  have h1 : PI.FockOneDegW.lowOp (p := p) (q := q) c d g =
      homogeneousComponent e (PI.FockOneDegW.lowOp (p := p) (q := q) c d g) := by
    rw [PI.FockOneDegW.RedOps.hc_lowOp, homogeneousComponent_of_mem hg, if_pos rfl]
  rw [h1]
  exact homogeneousComponent_mem _ _

theorem low_homog_small (c d : Ix r s) {e : ℕ} (he : e < 2) {g : Pol p q r s}
    (hg : g ∈ homog (Ix p q × Ix r s) e) : PI.FockOneDegW.lowOp (p := p) (q := q) c d g = 0 := by
  refine hc_ext fun n => ?_
  rw [PI.FockOneDegW.RedOps.hc_lowOp, homogeneousComponent_of_mem hg, if_neg (by omega), map_zero, map_zero]

private theorem fockAct2_Eab_eq_sum_omE (c d : Ix r s) (P : Pol p q r s) :
    fockAct2 p q r s (Eab c d) P = ∑ a : Ix p q, omE (a, c) (a, d) P := by
  apply PI.FockOneDegW.Swap.rename_sw_injective p q r s
  rw [PI.FockOneDegW.Swap.rename_fockAct2, PI.FockOneDegW.fockAct1_Eab_apply, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [PI.FockOneDegW.Swap.rename_omE]
  rfl

private theorem omE_add_pderiv_pderiv_eq_X_mul_X_of_not_sameBlock {c d : Ix r s} (hcd : ¬ sameBlock c d) (a : Ix p q) (P : Pol p q r s) :
    omE (a, c) (a, d) P +
        (if linePos ((a, d) : Ln p q r s) = true then pderiv (a, c) (pderiv (a, d) P) else 0) =
      if linePos ((a, c) : Ln p q r s) = true then X (a, c) * (X (a, d) * P) else 0 := by
  rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;>
    simp_all [omE, raiB, lowB, linePos, sameBlock, Module.End.mul_apply]

theorem second_action_add_lowering {c d : Ix r s} (hcd : ¬ sameBlock c d) {e : ℕ} {g : Pol p q r s}
    (hg : g ∈ homog (Ix p q × Ix r s) e) :
    fockAct2 p q r s (Eab c d) g + PI.FockOneDegW.lowOp (p := p) (q := q) c d g ∈
      homog (Ix p q × Ix r s) (e + 2) := by
  rw [fockAct2_Eab_eq_sum_omE, PI.FockOneDegW.RedOps.lowOp_apply, ← Finset.sum_add_distrib]
  simp_rw [omE_add_pderiv_pderiv_eq_X_mul_X_of_not_sameBlock hcd]
  refine Submodule.sum_mem _ (fun a _ => ?_)
  split_ifs
  · rw [mem_homogeneousSubmodule] at hg ⊢
    have h1 := (isHomogeneous_X ℂ ((a, c) : Ln p q r s)).mul
      ((isHomogeneous_X ℂ ((a, d) : Ln p q r s)).mul hg)
    convert h1 using 1
    omega
  · exact Submodule.zero_mem _

private theorem Eab_commutator (a b c d : Ix r s) :
    Eab a b * Eab c d - Eab c d * Eab a b =
      (if b = c then Eab a d else 0) - (if d = a then Eab c b else 0) := by
  have e1 : Eab a b * Eab c d = if b = c then Eab a d else 0 := by
    split_ifs with h
    · subst h
      simp only [Eab, Matrix.single_mul_single_same, mul_one]
    · simp only [Eab]
      exact Matrix.single_mul_single_of_ne _ _ _ _ h _
  have e2 : Eab c d * Eab a b = if d = a then Eab c b else 0 := by
    split_ifs with h
    · subst h
      simp only [Eab, Matrix.single_mul_single_same, mul_one]
    · simp only [Eab]
      exact Matrix.single_mul_single_of_ne _ _ _ _ h _
  rw [e1, e2]

theorem low_comm {a b c d : Ix r s} (hab : sameBlock a b) (hcd : ¬ sameBlock c d) (g : Pol p q r s) :
    fockAct2 p q r s (Eab a b) (PI.FockOneDegW.lowOp (p := p) (q := q) c d g) -
      PI.FockOneDegW.lowOp (p := p) (q := q) c d (fockAct2 p q r s (Eab a b) g) =
    (if b = c then PI.FockOneDegW.lowOp (p := p) (q := q) a d g else 0) -
      (if d = a then PI.FockOneDegW.lowOp (p := p) (q := q) c b g else 0) := by
  have key := mp_comm (fockAct2 p q r s (Eab a b)) (fockAct2 p q r s (Eab c d)) _ (homogComponent_comm_second_action (p := p) (q := q) hab)
    (lie2 p q r s _ _) g
  rw [minusPart_second_action_Eab hcd, minusPart_second_action_Eab hcd, map_neg, neg_sub_neg, Eab_commutator, map_sub, mp_sub] at key
  rw [← neg_sub, key]
  have hab' := (sb_iff a b).1 hab
  have hcd' : ¬ (c.isLeft = d.isLeft) := fun h => hcd ((sb_iff c d).2 h)
  split_ifs with h1 h2 h2
  · subst h1
    subst h2
    exact absurd (hab'.trans (rfl)) (by simpa [eq_comm] using hcd')
  · subst h1
    have had : ¬ sameBlock a d := fun h => hcd' (by rw [sb_iff] at h; rw [← hab']; exact h)
    rw [minusPart_second_action_Eab had, map_zero, mp_zero, sub_zero, neg_neg, sub_zero]
  · subst h2
    have hcb : ¬ sameBlock c b := fun h => hcd' (by rw [sb_iff] at h; rw [h, ← hab'])
    rw [minusPart_second_action_Eab hcb, map_zero, mp_zero, zero_sub, neg_neg, zero_sub]
  · rw [map_zero, mp_zero, sub_zero, neg_zero]

end PositivityTheory.KReal

end
