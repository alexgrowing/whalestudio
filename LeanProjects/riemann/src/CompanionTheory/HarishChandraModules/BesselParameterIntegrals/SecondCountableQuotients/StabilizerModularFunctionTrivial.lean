import Mathlib
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SecondCountableQuotients.NContract

open Matrix

namespace CompanionTheory.D.Upq.QuotSetU

open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

local notation "𝕄" => Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

theorem pow_mem_Sset {x : 𝕄} (hx : x ∈ Sset k r z) (p : ℕ) : x ^ p ∈ Sset k r z := by
  induction p with
  | zero => rw [pow_zero]; exact one_mem_Sset
  | succ p ih => rw [pow_succ]; exact mul_mem_Sset ih hx

theorem pow_mem_UW {x : 𝕄} (hx : x ∈ UWset k r z) (p : ℕ) : x ^ p ∈ UWset k r z := by
  induction p with
  | zero => rw [pow_zero]; exact one_mem_UW
  | succ p ih => rw [pow_succ]; exact mul_mem_UW ih hx

theorem pow_mem_N {x : 𝕄} (hx : x ∈ Nset k r) (p : ℕ) : x ^ p ∈ Nset k r := by
  induction p with
  | zero => rw [pow_zero]; exact (nilpotent_subgroup k r).1
  | succ p ih => rw [pow_succ]; exact (nilpotent_subgroup k r).2.1 _ ih _ hx

theorem entry_le_two {g : 𝕄} (hg : ∀ i j, ‖(g - 1) i j‖ ≤ 1) (i j : Fin (2 * r + k + 1)) :
    ‖g i j‖ ≤ 2 := by
  have e : g i j = (g - 1) i j + (1 : 𝕄) i j := by
    rw [Matrix.sub_apply, sub_add_cancel]
  have h1 : ‖(1 : 𝕄) i j‖ ≤ 1 := by rw [Matrix.one_apply]; split_ifs <;> simp
  calc ‖g i j‖ = ‖(g - 1) i j + (1 : 𝕄) i j‖ := by rw [← e]
    _ ≤ ‖(g - 1) i j‖ + ‖(1 : 𝕄) i j‖ := norm_add_le _ _
    _ ≤ 2 := by linarith [hg i j]

theorem isCompact_nearOne (hz : inWb k r z) (hT : 0 < Tz k r z) :
    IsCompact {g : 𝕄 | g ∈ Sset k r z ∧ ∀ i j, ‖(g - 1) i j‖ ≤ 1} := by
  have hcl : IsClosed {g : 𝕄 | g ∈ Sset k r z ∧ ∀ i j, ‖(g - 1) i j‖ ≤ 1} := by
    have e : {g : 𝕄 | g ∈ Sset k r z ∧ ∀ i j, ‖(g - 1) i j‖ ≤ 1} =
        Sset k r z ∩ ⋂ i, ⋂ j, {g : 𝕄 | ‖(g - 1) i j‖ ≤ 1} := by
      ext g; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [e]
    refine (isClosed_Sset hz hT).inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
    exact isClosed_le (((continuous_apply j).comp
      ((continuous_apply i).comp (continuous_id.sub continuous_const))).norm) continuous_const
  have hB : IsCompact ((Set.pi Set.univ fun _ : Fin (2 * r + k + 1) =>
      Set.pi Set.univ fun _ : Fin (2 * r + k + 1) => Metric.closedBall (0 : ℂ) 2) : Set 𝕄) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hB.of_isClosed_subset hcl ?_
  intro g hg' i _ j _
  rw [Metric.mem_closedBall, dist_zero_right]
  exact entry_le_two hg'.2 i j

section ModFun

variable {D : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℝ}
  (hD : UnitaryGroupMassFormula.ModProps (Sset k r z) D)
include hD

theorem modFun_one : D 1 = 1 := by
  have h := hD.2.1 1 one_mem_Sset 1 one_mem_Sset
  rw [Matrix.one_mul] at h
  have h0 := hD.1 1 one_mem_Sset
  have h' : D 1 * D 1 = D 1 * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel₀ h0.ne' h'

theorem modFun_pow {x : 𝕄} (hx : x ∈ Sset k r z) (p : ℕ) : D (x ^ p) = D x ^ p := by
  induction p with
  | zero => rw [pow_zero, pow_zero]; exact modFun_one hD
  | succ p ih => rw [pow_succ, pow_succ, hD.2.1 _ (pow_mem_Sset hx p) _ hx, ih]

theorem modFun_eq_one_of_bdd {x : 𝕄} (hx : x ∈ Sset k r z) (hxi : x⁻¹ ∈ Sset k r z)
    (hb : ∃ M : ℝ, ∀ p : ℕ, D (x ^ p) ≤ M) (hbi : ∃ M : ℝ, ∀ p : ℕ, D (x⁻¹ ^ p) ≤ M) :
    D x = 1 := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨M', hM'⟩ := hbi
  have h1 : D x ≤ 1 := pow_bdd_le_one (hD.1 x hx) fun p => by rw [← modFun_pow hD hx]; exact hM p
  have h2 : D x⁻¹ ≤ 1 :=
    pow_bdd_le_one (hD.1 _ hxi) fun p => by rw [← modFun_pow hD hxi]; exact hM' p
  have h3 : D x * D x⁻¹ = 1 := by
    rw [← hD.2.1 x hx _ hxi, mul_inv_UH (siegel_set_subset k r z hx), modFun_one hD]
  have h4 := hD.1 x hx
  have h5 := hD.1 _ hxi
  nlinarith

theorem modFun_UW (hz : inWb k r z) (hT : 0 < Tz k r z) {h : 𝕄} (hh : h ∈ UWset k r z) :
    D h = 1 := by
  obtain ⟨M, hM⟩ := hD.2.2.2 (UWset k r z) (fun x hx => SW.uw_sub_S hx) (unitary_weyl_compact k r z hz hT)
  exact modFun_eq_one_of_bdd hD (SW.uw_sub_S hh) (SW.uw_sub_S (inv_mem_UW hh))
    ⟨M, fun p => hM _ (pow_mem_UW hh p)⟩ ⟨M, fun p => hM _ (pow_mem_UW (inv_mem_UW hh) p)⟩

theorem modFun_N (hz : inWb k r z) (hT : 0 < Tz k r z) {m : 𝕄} (hm : m ∈ Nset k r) : D m = 1 := by
  have hVsub : {g : 𝕄 | g ∈ Sset k r z ∧ ∀ i j, ‖(g - 1) i j‖ ≤ 1} ⊆ Sset k r z :=
    fun x hx => hx.1
  obtain ⟨M, hM⟩ := hD.2.2.2 _ hVsub (isCompact_nearOne hz hT)
  have key : ∀ x : 𝕄, x ∈ Nset k r → D x ≤ M := by
    intro x hx
    obtain ⟨c, hcu, hcn, hcb⟩ := unipotent_radical_contracting k r z hz x hx 1 one_pos
    have hxS : x ∈ Sset k r z := SW.n_sub_S hx
    rw [← hD.2.2.1 c hcu hcn x hxS]
    exact hM _ ⟨(hcn x).2 hxS, hcb⟩
  have hmi : m⁻¹ ∈ Nset k r := (nilpotent_subgroup k r).2.2 m hm
  exact modFun_eq_one_of_bdd hD (SW.n_sub_S hm) (SW.n_sub_S hmi)
    ⟨M, fun p => key _ (pow_mem_N hm p)⟩ ⟨M, fun p => key _ (pow_mem_N hmi p)⟩

end ModFun

theorem stabilizer_modular_function_trivial : TrivS := by
  intro k r z hz hT D hD g hg
  obtain ⟨h, hh, m, hm, rfl⟩ := hg
  rw [hD.2.1 h (SW.uw_sub_S hh) m (SW.n_sub_S hm), modFun_UW hD hz hT hh, modFun_N hD hz hT hm,
    mul_one]

end CompanionTheory.D.Upq.QuotSetU
