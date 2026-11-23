import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.FormulaStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.TrivKtype
import Lemmata.GeneralBFactLeftVariant.Imports

noncomputable section

namespace PI.WeylForKWork

open PI PI.UpqRep Matrix
open scoped InnerProductSpace

def wtTorus {N : ℕ} (θ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)

theorem wt_char_real (f : ℝ → ℂ) (hc : Continuous f) (hm : ∀ s t, f (s + t) = f s * f t)
    (h0 : f 0 = 1) (hn : ∀ t, ‖f t‖ = 1) :
    ∃ m : ℝ, ∀ t, f t = Complex.exp (((m * t : ℝ) : ℂ) * Complex.I) := by
  first | exact Bl.general_b_fact_left_variant.goal1 .. | (apply Bl.general_b_fact_left_variant.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_variant.goal1 <;> assumption)

theorem wt_common_eigvec {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ι : Type}
    (A : ι → (H →L[ℂ] H)) (W : Submodule ℂ H) [FiniteDimensional ℂ W] (hW : W ≠ ⊥)
    (hst : ∀ i, ∀ v ∈ W, A i v ∈ W) (hcomm : ∀ i j, ∀ v, A i (A j v) = A j (A i v)) :
    ∃ w ∈ W, w ≠ 0 ∧ ∀ i, ∃ c : ℂ, A i w = c • w := by
  classical
  have hex : ∃ n, ∃ W₀ : Submodule ℂ H, W₀ ≤ W ∧ W₀ ≠ ⊥ ∧ (∀ i, ∀ v ∈ W₀, A i v ∈ W₀) ∧
      Module.finrank ℂ W₀ = n := ⟨_, W, le_rfl, hW, hst, rfl⟩
  obtain ⟨W₀, hW₀W, hW₀, hW₀st, hW₀n⟩ := Nat.find_spec hex
  have hmin : ∀ W₁ : Submodule ℂ H, W₁ ≤ W → W₁ ≠ ⊥ → (∀ i, ∀ v ∈ W₁, A i v ∈ W₁) →
      Module.finrank ℂ W₀ ≤ Module.finrank ℂ W₁ := fun W₁ h1 h2 h3 => by
    rw [hW₀n]; exact Nat.find_min' hex ⟨W₁, h1, h2, h3, rfl⟩
  have : FiniteDimensional ℂ W₀ := Submodule.finiteDimensional_of_le hW₀W
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W₀).mp hW₀
  refine ⟨w, hW₀W hw, hw0, fun i => ?_⟩
  let f : Module.End ℂ W₀ := (A i : H →ₗ[ℂ] H).restrict (fun x hx => hW₀st i x hx)
  have : Nontrivial W₀ := Submodule.nontrivial_iff_ne_bot.mpr hW₀
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  let E : Submodule ℂ H := W₀ ⊓ LinearMap.ker ((A i : H →ₗ[ℂ] H) - c • LinearMap.id)
  have hmemE : ∀ x, x ∈ E ↔ x ∈ W₀ ∧ A i x = c • x := by
    intro x; simp [E, sub_eq_zero]
  have hEst : ∀ j, ∀ x ∈ E, A j x ∈ E := by
    intro j x hx
    rw [hmemE] at hx ⊢
    exact ⟨hW₀st j x hx.1, by rw [hcomm i j, hx.2, map_smul]⟩
  have hvE : (v : H) ∈ E := by
    rw [hmemE]
    refine ⟨v.2, ?_⟩
    have h1 := Module.End.mem_eigenspace_iff.mp hv.1
    have h2 := congrArg Subtype.val h1
    simpa [f] using h2
  have hE0 : E ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    refine ⟨v, hvE, fun h => hv.2 ?_⟩
    exact Subtype.ext h
  have hEW : E ≤ W₀ := inf_le_left
  have hEeq : E = W₀ := Submodule.eq_of_le_of_finrank_le hEW (hmin E (hEW.trans hW₀W) hE0 hEst)
  have hwE : w ∈ E := hEeq ▸ hw
  exact ⟨c, ((hmemE w).mp hwE).2⟩

theorem wt_inner_iso {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : H →L[ℂ] H)
    (hT : ∀ v, ‖T v‖ = ‖v‖) (x y : H) : ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (⟨(T : H →ₗ[ℂ] H), hT⟩ : H →ₗᵢ[ℂ] H).inner_map_map x y

theorem wt_perp_stable {N : ℕ} (ε : Fin N → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (hσ : IsURepOn (Kset ε) σ) (X' X : Submodule ℂ H)
    (hX' : IsKStableOn ε σ X') (hX : IsKStableOn ε σ X) : IsKStableOn ε σ (X'ᗮ ⊓ X) := by
  intro g hg v hv
  refine ⟨?_, hX g hg v hv.2⟩
  show σ g v ∈ X'ᗮ
  rw [Submodule.mem_orthogonal]
  intro u hu
  have hg' : star g ∈ Kset ε := Kset_star ε hg
  have h1 : ⟪σ (star g) u, v⟫_ℂ = 0 := (Submodule.mem_orthogonal X' v).mp hv.1 _ (hX' _ hg' u hu)
  have h2 : σ g (σ (star g) u) = u := by
    have h3 := hσ.1.2 g hg (star g) hg'
    rw [Unitary.mul_star_self_of_mem hg.1, hσ.1.1] at h3
    have h4 := DFunLike.congr_fun h3 u
    simpa using h4.symm
  calc ⟪u, σ g v⟫_ℂ = ⟪σ g (σ (star g) u), σ g v⟫_ℂ := by rw [h2]
    _ = ⟪σ (star g) u, v⟫_ℂ := wt_inner_iso (σ g) (hσ.2.1 g hg) _ _
    _ = 0 := h1

theorem false_of_neg_smul_eq_smul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (z : ℂ) (hz : z ≠ 0)
    (w : H) (hw : w ≠ 0) (h : (z * -1) • w = z • w) : False := by
  have e3 := sub_eq_zero.mpr h
  rw [← sub_smul, smul_eq_zero] at e3
  rcases e3 with h' | h'
  · apply hz; linear_combination (-1/2 : ℂ) * h'
  · exact hw h'

theorem weight_unique_holds : WtUniq := by
  intro n H _ _ σ μ μ' w hw h1 h2
  funext a
  by_contra hne
  have hd : μ a - μ' a ≠ 0 := sub_ne_zero.mpr hne
  have hT := PI.WeylForKInhab.diag_mem (allPos n) (Pi.single a (Real.pi / (μ a - μ' a)))
  have e1 := h1 _ hT
  have e2 := h2 _ hT
  rw [e1] at e2
  have s : ∀ ν : Fin n → ℝ, ∑ b, ν b * (Pi.single a (Real.pi / (μ a - μ' a)) : Fin n → ℝ) b =
      ν a * (Real.pi / (μ a - μ' a)) := by
    intro ν
    rw [Finset.sum_eq_single a]
    · rw [Pi.single_eq_same]
    · intro b _ hb; rw [Pi.single_eq_of_ne hb]; ring
    · intro hh; exact absurd (Finset.mem_univ a) hh
  rw [s, s] at e2
  have hc : (μ a - μ' a) * (Real.pi / (μ a - μ' a)) = Real.pi := mul_div_cancel₀ _ hd
  have hxy : μ a * (Real.pi / (μ a - μ' a)) = μ' a * (Real.pi / (μ a - μ' a)) + Real.pi := by
    linear_combination hc
  rw [hxy, Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I] at e2
  exact false_of_neg_smul_eq_smul _ (Complex.exp_ne_zero _) w hw e2

theorem torus_weight_exists : TorusWt := by
  intro N ε H _ _ σ W hσ hWf hW0 hWst
  have := hWf
  have hTK : ∀ θ : Fin N → ℝ, wtTorus θ ∈ Kset ε := fun θ => PI.WeylForKInhab.diag_mem ε θ
  have hTadd : ∀ θ θ' : Fin N → ℝ, wtTorus (θ + θ') = wtTorus θ * wtTorus θ' := by
    intro θ θ'
    simp only [wtTorus, diagonal_mul_diagonal]
    congr 1; funext a
    simp [add_mul, Complex.exp_add]
  have hσadd : ∀ θ θ' : Fin N → ℝ, ∀ v, σ (wtTorus (θ + θ')) v = σ (wtTorus θ) (σ (wtTorus θ') v) := by
    intro θ θ' v; rw [hTadd, hσ.1.2 _ (hTK θ) _ (hTK θ')]; rfl
  have hcomm : ∀ θ θ' : Fin N → ℝ, ∀ v, σ (wtTorus θ) (σ (wtTorus θ') v) = σ (wtTorus θ') (σ (wtTorus θ) v) := by
    intro θ θ' v; rw [← hσadd, ← hσadd, add_comm]
  obtain ⟨w, hwW, hw0, hwe⟩ := wt_common_eigvec (fun θ => σ (wtTorus θ)) W hW0 (fun θ v hv => hWst θ v hv) hcomm
  choose χ hχ using hwe
  have hχ' : ∀ θ, σ (wtTorus θ) w = χ θ • w := hχ
  have hinner : ⟪w, w⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hw0
  have hχeq : ∀ θ, χ θ = ⟪w, σ (wtTorus θ) w⟫_ℂ / ⟪w, w⟫_ℂ := by
    intro θ
    rw [hχ' θ, inner_smul_right, mul_div_assoc, div_self hinner, mul_one]
  have hTc : Continuous (fun θ : Fin N → ℝ => wtTorus θ) := by
    unfold wtTorus
    apply Continuous.matrix_diagonal
    exact continuous_pi fun a => by fun_prop
  have hχc : Continuous χ := by
    have h1 : Continuous (fun θ => σ (wtTorus θ) w) := (hσ.2.2 w).comp_continuous hTc hTK
    have : χ = fun θ => ⟪w, σ (wtTorus θ) w⟫_ℂ / ⟪w, w⟫_ℂ := funext hχeq
    rw [this]; exact (continuous_const.inner h1).div_const _
  have hsm : ∀ c d : ℂ, c • w = d • w → c = d := fun c d h => smul_left_injective ℂ hw0 h
  have hχadd : ∀ θ θ', χ (θ + θ') = χ θ * χ θ' := by
    intro θ θ'; apply hsm
    rw [← hχ', hσadd, hχ' θ', map_smul, hχ' θ, smul_smul, mul_comm]
  have hχ0 : χ 0 = 1 := by
    apply hsm
    rw [← hχ', one_smul]
    have : wtTorus (0 : Fin N → ℝ) = 1 := by simp [wtTorus]
    rw [this, hσ.1.1]; rfl
  have hχn : ∀ θ, ‖χ θ‖ = 1 := by
    intro θ
    have h := hσ.2.1 _ (hTK θ) w
    rw [hχ' θ, norm_smul] at h
    have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have h2 : (‖χ θ‖ - 1) * ‖w‖ = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · linarith
  have hcoord : ∀ a : Fin N, ∃ m : ℝ, ∀ t,
      χ (Pi.single a t) = Complex.exp (((m * t : ℝ) : ℂ) * Complex.I) := by
    intro a
    apply wt_char_real (fun t => χ (Pi.single a t))
    · exact hχc.comp ((LinearMap.single ℝ (fun _ : Fin N => ℝ) a).continuous_of_finiteDimensional)
    · intro s t; simp only [Pi.single_add]; exact hχadd _ _
    · simpa using hχ0
    · intro t; exact hχn _
  choose m hm using hcoord
  refine ⟨m, w, hwW, hw0, fun θ _ => ?_⟩
  show σ (wtTorus θ) w = _
  rw [hχ' θ]
  congr 1
  have hprod : ∀ s : Finset (Fin N),
      χ (∑ a ∈ s, Pi.single a (θ a)) = ∏ a ∈ s, χ (Pi.single a (θ a)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [hχ0]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hχadd, ih]
  calc χ θ = χ (∑ a, Pi.single a (θ a)) := by rw [Finset.univ_sum_single]
    _ = ∏ a, χ (Pi.single a (θ a)) := hprod _
    _ = ∏ a, Complex.exp (((m a * θ a : ℝ) : ℂ) * Complex.I) :=
        Finset.prod_congr rfl fun a _ => hm a (θ a)
    _ = Complex.exp (((∑ a, m a * θ a : ℝ) : ℂ) * Complex.I) := by
        rw [← Complex.exp_sum]; congr 1; push_cast; rw [Finset.sum_mul]

theorem minimal_irreducible_exists : MinIrr := by
  classical
  intro p H _ _ σ₁ S μ v hσ hS hSst hvS hv0 hvw
  have hex : ∃ n, ∃ X : Submodule ℂ H, X ≤ S ∧ IsKStableOn (allPos p) σ₁ X ∧
      (∃ x ∈ X, x ≠ 0 ∧ IsWtOn (Kset (allPos p)) σ₁ μ x) ∧ Module.finrank ℂ X = n :=
    ⟨_, S, le_rfl, hSst, ⟨v, hvS, hv0, hvw⟩, rfl⟩
  obtain ⟨X, hXS, hXst, ⟨x, hxX, hx0, hxw⟩, hXn⟩ := Nat.find_spec hex
  have hmin : ∀ X₁ : Submodule ℂ H, X₁ ≤ S → IsKStableOn (allPos p) σ₁ X₁ →
      (∃ x ∈ X₁, x ≠ 0 ∧ IsWtOn (Kset (allPos p)) σ₁ μ x) →
      Module.finrank ℂ X ≤ Module.finrank ℂ X₁ := fun X₁ h1 h2 h3 => by
    rw [hXn]; exact Nat.find_min' hex ⟨X₁, h1, h2, h3, rfl⟩
  have : FiniteDimensional ℂ X := Submodule.finiteDimensional_of_le hXS
  refine ⟨X, hXS, hXst, ?_, x, hxX, hx0, hxw⟩
  intro X' hX'X hX'st
  have : FiniteDimensional ℂ X' := Submodule.finiteDimensional_of_le hX'X
  have : CompleteSpace X' := FiniteDimensional.complete ℂ X'
  have hX''st := wt_perp_stable (allPos p) σ₁ hσ X' X hX'st hXst
  have hxsup : x ∈ X' ⊔ X'ᗮ := by rw [Submodule.sup_orthogonal_of_hasOrthogonalProjection]; trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hxsup
  have hzX : z ∈ X := by
    have : z = x - y := by rw [← hyz]; abel
    rw [this]; exact X.sub_mem hxX (hX'X hy)
  have hz'' : z ∈ X'ᗮ ⊓ X := ⟨hz, hzX⟩
  have hperp0 : ∀ u, u ∈ X' → u ∈ X'ᗮ → u = 0 := fun u h1 h2 =>
    inner_self_eq_zero.mp ((Submodule.mem_orthogonal X' u).mp h2 u h1)
  have hsplit : ∀ θ : Fin p → ℝ, diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset (allPos p) →
      σ₁ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) y =
        Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • y ∧
      σ₁ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) z =
        Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • z := by
    intro θ hT
    have hx := hxw θ hT
    have hAy := hX'st _ hT y hy
    have hAz := (hX''st _ hT z hz'').1
    set A := σ₁ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) with hA
    set e := Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) with he
    have hu1 : A y - e • y ∈ X' := X'.sub_mem hAy (X'.smul_mem e hy)
    have hu2 : A z - e • z ∈ X'ᗮ := X'ᗮ.sub_mem hAz (X'ᗮ.smul_mem e hz)
    have hsum : A y - e • y + (A z - e • z) = 0 := by
      rw [← hyz, map_add, smul_add] at hx
      rw [show A y - e • y + (A z - e • z) = (A y + A z) - (e • y + e • z) by abel, hx, sub_self]
    have hneg : A y - e • y = -(A z - e • z) := eq_neg_of_add_eq_zero_left hsum
    have h0y : A y - e • y = 0 := hperp0 _ hu1 (by rw [hneg]; exact X'ᗮ.neg_mem hu2)
    have h0z : A z - e • z = 0 := by rw [h0y] at hneg; exact neg_eq_zero.mp hneg.symm
    exact ⟨sub_eq_zero.mp h0y, sub_eq_zero.mp h0z⟩
  have hwy : IsWtOn (Kset (allPos p)) σ₁ μ y := fun θ hT => (hsplit θ hT).1
  have hwz : IsWtOn (Kset (allPos p)) σ₁ μ z := fun θ hT => (hsplit θ hT).2
  by_cases hy0 : y = 0
  · left
    have hzx : z = x := by rw [← hyz, hy0, zero_add]
    have hz0 : z ≠ 0 := by rw [hzx]; exact hx0
    have hle : X'ᗮ ⊓ X ≤ X := inf_le_right
    have heq : X'ᗮ ⊓ X = X := Submodule.eq_of_le_of_finrank_le hle
      (hmin _ (hle.trans hXS) hX''st ⟨z, hz'', hz0, hwz⟩)
    rw [Submodule.eq_bot_iff]
    intro u hu
    have hu' : u ∈ X'ᗮ ⊓ X := by rw [heq]; exact hX'X hu
    exact hperp0 u hu hu'.1
  · right
    exact Submodule.eq_of_le_of_finrank_le hX'X (hmin X' (hX'X.trans hXS) hX'st ⟨y, hy, hy0, hwy⟩)

end PI.WeylForKWork
