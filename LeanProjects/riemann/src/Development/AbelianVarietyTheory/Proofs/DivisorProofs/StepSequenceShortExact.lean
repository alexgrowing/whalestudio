import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepInclStepProj
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.FlagChi Matrix

set_option autoImplicit false

namespace GlobalTheory.FlagChi

theorem stepSeq_shortExact : ∀ (Z : Scheme.{0}) [IsIntegral Z] (N : ℕ)
    (M : Matrix (Fin N) (Fin N) Z.functionField) (l : Fin N) (L : LB Z)
    (r : L.ι → Z.functionFieldˣ) (hr : IsRatSec L r), L.IsLB → Epi (stepProj M l hr) →
    (stepSeq M l hr).ShortExact := by
  intro Z _ N M l L r hr hL hepi
  refine ShortComplex.ShortExact.mk' ?_ ?_ hepi
  · refine DualExact.exact_of_locally _ fun V x hx => ⟨V, le_rfl, hx, fun t ht => ?_⟩
    have hmem : vec t ∈ vsec (stepC M l) V := by
      intro h y hy
      have hq : genVec h (vec t) ∈ quotC M l L r y := vec_mem t h y hy
      obtain ⟨c, hc⟩ := Semi.LB.mem_of_cover hL (genericPoint Z)
      have e := fnOf_coord_vproj L r (coordFn M l) hr
        (fun x w (hw : w ∈ quotC M l L r x) c hc => (show RegAt x (coordFn M l w * r c) from hw.2 c hc)) t c ⟨h, hc⟩
      have ht' : (stepProj M l hr).app V t = 0 := ht
      rw [stepProj] at ht'
      rw [ht', LB.coord_zero, map_zero, coordFn_apply] at e
      have hl : (M *ᵥ genVec h (vec t)) l = 0 := by
        rcases mul_eq_zero.1 e.symm with h0 | h0
        · exact h0
        · exact absurd h0 (Units.ne_zero _)
      intro k hk
      rcases eq_or_lt_of_le hk with hk' | hk'
      · have : k = l := Fin.ext hk'.symm
        rw [this]; exact hl
      · exact hq.1 k hk'
    exact ⟨mk (vec t) hmem, sec_ext rfl⟩
  · refine QCoh.mono_of_locally_app_injective _ fun W x hx => ⟨W, hx, le_rfl, fun s u e => ?_⟩
    apply sec_ext
    have := congrArg vec e
    exact this

end GlobalTheory.FlagChi
