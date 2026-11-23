import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

open Filter Topology

namespace GlobalTheory

theorem limsup_max_add_tendsto_eq_toReal (α : Type) (l : Filter α) [l.NeBot] (c f : α → ℝ)
    (c₀ κ M : ℝ) (hc : Filter.Tendsto c l (nhds c₀)) (hf : ∀ᶠ t in l, f t ≤ M) :
    Filter.limsup (fun t => max (c t + f t) (-κ)) l =
      (max ((c₀ : EReal) + Filter.limsup (fun t => (f t : EReal)) l) ((-κ : ℝ) : EReal)).toReal := by
  set g : α → ℝ := fun t => max (c t + f t) (-κ) with hg

  have hC : Tendsto (fun t => (c t : EReal)) l (𝓝 (c₀ : EReal)) :=
    (continuous_coe_real_ereal.tendsto c₀).comp hc
  have hCs : limsup (fun t => (c t : EReal)) l = (c₀ : EReal) := hC.limsup_eq
  have hCi : liminf (fun t => (c t : EReal)) l = (c₀ : EReal) := hC.liminf_eq

  have hsum : limsup (fun t => (c t : EReal) + (f t : EReal)) l =
      (c₀ : EReal) + limsup (fun t => (f t : EReal)) l := by
    apply le_antisymm
    · have := EReal.limsup_add_le (f := l) (u := fun t => (c t : EReal))
        (v := fun t => (f t : EReal)) (by rw [hCs]; exact .inl (EReal.coe_ne_bot c₀))
        (by rw [hCs]; exact .inl (EReal.coe_ne_top c₀))
      rw [hCs] at this
      exact this
    · have := EReal.le_limsup_add (f := l) (u := fun t => (f t : EReal))
        (v := fun t => (c t : EReal))
      rw [hCi] at this
      rw [add_comm]
      convert this using 2
      funext t
      simp [add_comm]

  have hmax : limsup (fun t => max ((c t : EReal) + (f t : EReal)) ((-κ : ℝ) : EReal)) l =
      max (limsup (fun t => (c t : EReal) + (f t : EReal)) l) ((-κ : ℝ) : EReal) := by
    have hmono : Monotone (fun x : EReal => max x ((-κ : ℝ) : EReal)) :=
      fun a b hab => max_le_max hab le_rfl
    have hcont : Continuous (fun x : EReal => max x ((-κ : ℝ) : EReal)) :=
      continuous_id.max continuous_const
    exact (hmono.map_limsup_of_continuousAt (F := l) (fun t => (c t : EReal) + (f t : EReal))
      hcont.continuousAt).symm

  have hbdd : IsBoundedUnder (· ≤ ·) l g := by
    have hcb : ∀ᶠ t in l, c t ≤ c₀ + 1 :=
      hc.eventually (gt_mem_nhds (by linarith)) |>.mono fun t ht => ht.le
    refine ⟨max (c₀ + 1 + M) (-κ), eventually_map.2 ?_⟩
    filter_upwards [hcb, hf] with t h1 h2
    show max (c t + f t) (-κ) ≤ _
    exact max_le_max (by linarith) le_rfl
  have hcobdd : IsCoboundedUnder (· ≤ ·) l g :=
    isCoboundedUnder_le_of_le l (x := -κ) (fun t => le_max_right _ _)
  have hreal : ((limsup g l : ℝ) : EReal) = limsup (fun t => ((g t : ℝ) : EReal)) l :=
    Monotone.map_limsup_of_continuousAt (F := l) (f := fun x : ℝ => (x : EReal))
      (fun a b h => EReal.coe_le_coe_iff.2 h) g continuous_coe_real_ereal.continuousAt hbdd hcobdd
  have hcoe : (fun t => ((g t : ℝ) : EReal)) =
      fun t => max ((c t : EReal) + (f t : EReal)) ((-κ : ℝ) : EReal) := by
    funext t
    show ((max (c t + f t) (-κ) : ℝ) : EReal) = _
    rw [EReal.coe_strictMono.monotone.map_max, EReal.coe_add]
  rw [hcoe, hmax, hsum] at hreal
  rw [← hreal, EReal.toReal_coe]

end GlobalTheory
