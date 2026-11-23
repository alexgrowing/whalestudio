import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.StepSt

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3

namespace PositivityTheory.Rg.Ming.StepX

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n r : ℕ}

theorem isUnit_det_val {m : ℕ} (h : GL (Fin m) k) : IsUnit h.val.det := by
  exact (Matrix.isUnit_iff_isUnit_det h.val).mp h.isUnit

theorem rank_conj (h : GL (Fin n) k) (g : GL (Fin r) k) (x : Matrix (Fin n) (Fin r) k) :
    (h.val * x * g.val).rank = x.rank := by
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (isUnit_det_val g),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_val h)]

theorem conj_cancel (h : GL (Fin n) k) (g : GL (Fin r) k) (x : Matrix (Fin n) (Fin r) k) :
    (h⁻¹ : GL (Fin n) k).val * (h.val * x * g.val) * (g⁻¹ : GL (Fin r) k).val = x := by
  simp [← Matrix.mul_assoc]

theorem conj_cancel' (h : GL (Fin n) k) (g : GL (Fin r) k) (x : Matrix (Fin n) (Fin r) k) :
    h.val * ((h⁻¹ : GL (Fin n) k).val * x * (g⁻¹ : GL (Fin r) k).val) * g.val = x := by
  simp [← Matrix.mul_assoc]

theorem mem_ballM_self (c : kˣ) (x : Matrix (Fin n) (Fin r) k) : x ∈ ballM c x := by
  intro i l
  simp

theorem tr_mem (h : GL (Fin n) k) (g : GL (Fin r) k) (Ψ : SB (Matrix (Fin n) (Fin r) k)) :
    (fun y => Ψ.1 (h.val * y * g.val)) ∈ SB (Matrix (Fin n) (Fin r) k) := by
  let e : Matrix (Fin n) (Fin r) k ≃ₜ Matrix (Fin n) (Fin r) k :=
    { toFun := fun y => h.val * y * g.val
      invFun := fun y => (h⁻¹ : GL (Fin n) k).val * y * (g⁻¹ : GL (Fin r) k).val
      left_inv := fun y => conj_cancel h g y
      right_inv := fun y => conj_cancel' h g y
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  obtain ⟨h1, h2⟩ := Ψ.2
  exact ⟨h1.comp_continuous e.continuous, h2.comp_homeomorph e⟩

variable {μ : kˣ →* ℂˣ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (GL (Fin r) k) V} {π : Representation ℂ (GL (Fin n) k) W}
  {B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V}

theorem kill (hE : Equi μ σ π B) (h : GL (Fin n) k) (g : GL (Fin r) k)
    (Φ Ψ : SB (Matrix (Fin n) (Fin r) k)) (hΨ : ∀ y, Ψ.1 y = Φ.1 (h.val * y * g.val))
    (hΦ : B Φ = 0) : B Ψ = 0 := by
  apply LinearMap.ext
  intro F
  rw [LinearMap.zero_apply]
  let Φ' : SB (Matrix (Fin n) (Fin r) k) := ⟨om μ g⁻¹ h Ψ.1, om_mem_SB μ g⁻¹ h Ψ.2⟩
  have hΦ' : Φ' = om μ g⁻¹ h (fun _ => (1 : ℂ)) 0 • Φ := by
    apply Subtype.ext
    funext y
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    show om μ g⁻¹ h Ψ.1 y = om μ g⁻¹ h (fun _ => (1 : ℂ)) 0 * Φ.1 y
    simp only [om]
    rw [hΨ, conj_cancel', mul_one]
  have h1 := hE g⁻¹ h Ψ Φ' rfl F
  rw [hΦ', map_smul, hΦ, smul_zero, LinearMap.zero_apply] at h1
  have h3 := congrArg (σ g) h1
  rw [map_zero, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h3
  exact h3.symm

theorem key (hball : BallSt) (hnf : NfSt) (hcore : CoreSt) {j : ℕ} (hj : j < r) (hjn : 2 * j < n)
    (hμ : IsUnitaryChar μ) (hσ : IsUnitarisable σ) (hE : Equi μ σ π B) (hV : VanRk B (j + 1))
    (c : kˣ) (hc : valuation k (c : k) < 1) (Ψ : SB (Matrix (Fin n) (Fin r) k))
    (hsupp : ∀ y, Ψ.1 y ≠ 0 → y ∈ ballM c (idem k r n j))
    (hvan : ∀ y : Matrix (Fin n) (Fin r) k, y.rank < j → Ψ.1 y = 0) : B Ψ = 0 := by
  obtain ⟨hB1, -, hB3⟩ := hball k n r
  obtain ⟨c₀, hc₀⟩ := hB3 Ψ
  obtain ⟨c', hc'1, hc'0⟩ : ∃ c' : kˣ, valuation k (c' : k) < 1 ∧ valuation k (c' : k) ≤ valuation k (c₀ : k) := by
    by_cases h0 : valuation k (c₀ : k) < 1
    · exact ⟨c₀, h0, le_rfl⟩
    · exact ⟨c, hc, le_of_lt (lt_of_lt_of_le hc (not_lt.mp h0))⟩
  obtain ⟨S, hS, hsum⟩ := hc₀ c' hc'0
  have hind : ∀ x₀ : Matrix (Fin n) (Fin r) k,
      ((ballM c' x₀).indicator fun _ => (1 : ℂ)) ∈ SB (Matrix (Fin n) (Fin r) k) :=
    fun x₀ => (hB1 c' x₀).2.2.1
  have hpiece : ∀ x ∈ S, B ⟨_, hind x⟩ = 0 := by
    intro x hx
    by_cases hr : ∃ y ∈ ballM c' x, y.rank = j
    · obtain ⟨y, hy, hyr⟩ := hr
      have hball_eq : ballM c' y = ballM c' x := (hB1 c' x).2.2.2.1 y hy
      have hyS : y ∈ ballM c (idem k r n j) := by
        apply hsupp
        rw [(hS x hx y hy).1]
        exact (hS x hx y hy).2
      obtain ⟨h, hh, g, hg, hye⟩ := (hnf k n r j y hyr).2 c hc hyS
      have hcore' : B ⟨_, hind (idem k r n j)⟩ = 0 :=
        hcore k n r μ V W σ π B j hj hjn hμ hσ hE hV c' hc'1 _ rfl
      refine kill hE h⁻¹ g⁻¹ ⟨_, hind (idem k r n j)⟩ ⟨_, hind x⟩ (fun z => ?_) hcore'
      show (ballM c' x).indicator (fun _ => (1 : ℂ)) z = (ballM c' (idem k r n j)).indicator (fun _ => (1 : ℂ))
        ((h⁻¹ : GL (Fin n) k).val * z * (g⁻¹ : GL (Fin r) k).val)
      have hiff : (h⁻¹ : GL (Fin n) k).val * z * (g⁻¹ : GL (Fin r) k).val ∈ ballM c' (idem k r n j) ↔
          z ∈ ballM c' x := by
        have h4 := (hB1 c' y).2.2.2.2 h⁻¹ (inv_mem hh) g⁻¹ (inv_mem hg) z
        rw [hball_eq, hye, conj_cancel] at h4
        exact h4
      by_cases hz : z ∈ ballM c' x
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (hiff.mpr hz)]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h' => hz (hiff.mp h'))]
    · push_neg at hr
      apply hV
      intro z hz
      show (ballM c' x).indicator (fun _ => (1 : ℂ)) z = 0
      apply Set.indicator_of_notMem
      intro hzx
      have hne : Ψ.1 z ≠ 0 := by
        rw [(hS x hx z hzx).1]
        exact (hS x hx z hzx).2
      have h1 : j ≤ z.rank := by
        by_contra hl
        exact hne (hvan z (lt_of_not_ge hl))
      have h2 := hr z hzx
      omega
  have hΨeq : Ψ = ∑ x ∈ S, Ψ.1 x • (⟨_, hind x⟩ : SB (Matrix (Fin n) (Fin r) k)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    exact hsum
  rw [hΨeq, map_sum]
  apply Finset.sum_eq_zero
  intro x hx
  rw [map_smul, hpiece x hx, smul_zero]

end PositivityTheory.Rg.Ming.StepX

namespace PositivityTheory.Rg.Ming

open PositivityTheory.Rg.Ming.StepX

theorem step : BallSt → LocSt → NfSt → RkSt → CoreSt → StepSt := by
  intro hBall hLoc hNf hRk hCore
  intro k _ _ _ _ n r μ V _ _ W _ _ σ π B j hj hjn hμ hσ hE hV
  intro Φ hΦ
  have hPker : Φ ∈ LinearMap.ker B := by
    apply hLoc k n r (LinearMap.ker B) Φ
    intro x hx
    obtain ⟨m, hm⟩ : ∃ m, x.rank = m := ⟨_, rfl⟩
    have hjm : j ≤ m := by
      rw [← hm]
      by_contra hlt
      exact hx (hΦ x (lt_of_not_ge hlt))
    have hmn : m ≤ n := by
      rw [← hm]
      simpa using Matrix.rank_le_height x
    have hmr : m ≤ r := by
      rw [← hm]
      simpa using Matrix.rank_le_width x
    obtain ⟨⟨h, g, hxe⟩, -⟩ := hNf k n r m x hm
    obtain ⟨c, hc, -⟩ := (hBall k n r).2.1 (0 : Matrix (Fin n) (Fin r) k) Set.univ Filter.univ_mem
    refine ⟨{y | (h⁻¹ : GL (Fin n) k).val * y * (g⁻¹ : GL (Fin r) k).val ∈ ballM c (idem k r n m)}, ?_, ?_, ?_⟩
    · exact ((hBall k n r).1 c _).1.preimage
        ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
    · have e1 : (h⁻¹ : GL (Fin n) k).val * x * (g⁻¹ : GL (Fin r) k).val = idem k r n m := by
        rw [hxe]
        exact conj_cancel h g _
      simp only [Set.mem_setOf_eq]
      rw [e1]
      exact mem_ballM_self c _
    · intro Ψ hΨ
      rw [LinearMap.mem_ker]
      rcases eq_or_lt_of_le hjm with hjm' | hjm'
      · subst hjm'
        let Ψ' : SB (Matrix (Fin n) (Fin r) k) := ⟨fun y => Ψ.1 (h.val * y * g.val), tr_mem h g Ψ⟩
        have hsupp : ∀ y, Ψ'.1 y ≠ 0 → y ∈ ballM c (idem k r n j) := by
          intro y hy
          have hmem := (hΨ _ hy).1
          simp only [Set.mem_setOf_eq] at hmem
          rw [conj_cancel] at hmem
          exact hmem
        have hvan : ∀ y : Matrix (Fin n) (Fin r) k, y.rank < j → Ψ'.1 y = 0 := by
          intro y hy
          by_contra hne
          have h2 := (hΨ _ hne).2
          apply h2
          apply hΦ
          rw [rank_conj]
          exact hy
        have hB' : B Ψ' = 0 := key hBall hNf hCore hj hjn hμ hσ hE hV c hc Ψ' hsupp hvan
        refine kill hE h⁻¹ g⁻¹ Ψ' Ψ (fun y => ?_) hB'
        show Ψ.1 y = Ψ.1 (h.val * ((h⁻¹ : GL (Fin n) k).val * y * (g⁻¹ : GL (Fin r) k).val) * g.val)
        rw [conj_cancel']
      · apply hV Ψ
        intro y hy
        by_contra hne
        have hmem := (hΨ y hne).1
        simp only [Set.mem_setOf_eq] at hmem
        have h5 := hRk k n r m hmn hmr c hc _ hmem
        rw [rank_conj] at h5
        omega
  exact LinearMap.mem_ker.mp hPker

end PositivityTheory.Rg.Ming
