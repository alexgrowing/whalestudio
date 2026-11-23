import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KTypeIntDomStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.LowComp
import Formalism.RealPlaceAnalysis.QuotientSettingHolds

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem tensHW_mem_khwSub {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ W) (ν : Fin n → ℝ) (v : W) :
    v ∈ khwSub ε E ν ↔ Formalism.REAL.KHighest ε E ν v := by
  simp only [khwSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero, Formalism.REAL.KHighest,
    Formalism.REAL.IsWeight]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun a => by simpa using h1 a, fun a b hab he => h2 a b ⟨hab, he⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun a => by simpa using h1 a, fun a b h => h2 a b h.1 h.2⟩

theorem tensHW_hw_eq {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {ε : Fin n → Bool} {A : Fin n → Fin n → Module.End ℂ V} {Λ : Fin n → ℝ} {w : V}
    (hA : Formalism.REAL.KRel ε A) (hU : Formalism.REAL.KUnit ε A) (hw : Formalism.REAL.KHighest ε A Λ w)
    (hspan : Formalism.REAL.kSpan ε A w = ⊤) {μ : Fin n → ℝ} {y : V}
    (hy : Formalism.REAL.KHighest ε A μ y) (hy0 : y ≠ 0) :
    μ = Λ ∧ ∃ c : ℂ, y = c • w := by
  rcases Formalism.REAL.kHiUniq V n ε A Λ μ w y hA hU hw (by rw [hspan]; exact Submodule.mem_top) hy with h | h
  · exact absurd h hy0
  · exact h

theorem tensHW_of (h : LowCompStatement) : TensHWStatement := by
  intro V _ _ n ε A Λ w ι _ _ M γ hA hU hw hspan hM hdiag
  have key : ∀ (ν : Fin n → ℝ) (x : PiLp 2 (fun _ : ι => V)), x ≠ 0 →
      Formalism.REAL.KHighest ε (tensAct A M) ν x →
      ∃ i, ν = Λ + γ i ∧ x i ≠ 0 ∧ ∃ c : ℂ, x i = c • w := by
    intro ν x hx hK
    obtain ⟨β, ⟨i, hi, hxi⟩, hall⟩ := h V n ε A ι M γ hM hdiag ν x hx hK
    obtain ⟨hμ, c, hc⟩ := tensHW_hw_eq hA hU hw hspan (hall i hi) hxi
    refine ⟨i, ?_, hxi, c, hc⟩
    rw [hi, ← hμ, sub_add_cancel]
  refine ⟨fun ν x hx hK => ?_, fun ν => ?_⟩
  · obtain ⟨i, hi, -⟩ := key ν x hx hK
    exact ⟨i, hi⟩
  · classical
    let L : khwSub ε (tensAct A M) ν →ₗ[ℂ] ({i : ι // ν = Λ + γ i} → ℂ) :=
      { toFun := fun x i => ⟪w, (x : PiLp 2 (fun _ : ι => V)) i.1⟫_ℂ
        map_add' := fun x y => by ext i; simp
        map_smul' := fun c x => by ext i; simp }
    have hL : Function.Injective L := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx0
      by_contra hne
      have hx' : (x : PiLp 2 (fun _ : ι => V)) ≠ 0 := fun h0 => hne (Subtype.ext h0)
      have hK := (tensHW_mem_khwSub ε _ ν _).1 x.2
      obtain ⟨i, hi, hxi, c, hc⟩ := key ν x hx' hK
      have h1 : ⟪w, (x : PiLp 2 (fun _ : ι => V)) i⟫_ℂ = 0 := congrFun hx0 ⟨i, hi⟩
      rw [hc, inner_smul_right] at h1
      rcases mul_eq_zero.1 h1 with h2 | h2
      · exact hxi (by rw [hc, h2, zero_smul])
      · exact hxi (by rw [hc, inner_self_eq_zero.1 h2, smul_zero])
    have : FiniteDimensional ℂ (khwSub ε (tensAct A M) ν) := Module.Finite.of_injective L hL
    refine ⟨this, ?_⟩
    calc Module.finrank ℂ (khwSub ε (tensAct A M) ν)
        ≤ Module.finrank ℂ ({i : ι // ν = Λ + γ i} → ℂ) :=
          LinearMap.finrank_le_finrank_of_injective hL
      _ = Nat.card {i : ι // ν = Λ + γ i} := by
          rw [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

theorem tensHW : TensHWStatement := tensHW_of lowComp

end ReciprocityTheory.ChartRestriction.DS.HW
