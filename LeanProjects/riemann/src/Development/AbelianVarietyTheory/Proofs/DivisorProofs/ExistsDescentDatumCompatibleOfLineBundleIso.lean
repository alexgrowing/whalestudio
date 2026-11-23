import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBDescent

theorem descCompat_of_lbIso : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X), L.IsLB →
    LBIso (L.pull (pullback.fst f f)) (L.pull (pullback.snd f f)) →
    ∃ φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ, DescCompat f L φ := by
  intro X Y f L hL hI
  obtain ⟨w, hw⟩ := hI
  have hP := (isGen_iff w).1 hw
  have hle : ∀ i j, chart f L i j ≤ (L.pull (pullback.snd f f)).U (fun _ => j) ⊓ (L.pull (pullback.fst f f)).U (fun _ => i) :=
    fun i j z hz => ⟨mem_pull.2 hz.2, mem_pull.2 hz.1⟩
  refine ⟨fun i j => res (hle i j) (w.s (fun _ => j, fun _ => i)), ?_⟩
  intro z i i' j j' hi hi' hj hj'
  have hc : ∀ a b, pullback.fst f f z ∈ L.U a → pullback.snd f f z ∈ L.U b →
      gm (𝟙 _) z (chart f L a b) (res (hle a b) (w.s (fun _ => b, fun _ => a))) =
        gw w (𝟙 _) z b (fun _ => a) := fun a b ha hb =>
    gm_res (𝟙 _) z (hle a b) ⟨ha, hb⟩ _
  have key := hP _ (𝟙 _) z j' j (fun _ => i') (fun _ => i) hj' hj (mem_pull.2 hi') (mem_pull.2 hi)
  have e1 : gm (𝟙 _) z _ ((L.pull (pullback.fst f f)).g (fun _ => i') (fun _ => i)) =
      gm (pullback.fst f f) z _ (L.g i' i) := by
    have := gm_pull_g L (pullback.fst f f) (𝟙 _) z (fun _ => i') (fun _ => i) (mem_pull.2 hi') (mem_pull.2 hi)
    rw [Category.id_comp] at this
    exact this
  have e2 : (gm (pullback.fst f f) z _ (L.g i' i))⁻¹ = gm (pullback.fst f f) z _ (L.g i i') := by
    rw [inv_eq_iff_mul_eq_one, gm_cocycle hL _ z hi' hi hi', gm_self hL _ z hi']
  rw [Category.id_comp, e1, e2] at key
  rw [hc i' j' hi' hj', hc i j hi hj, key]
  ac_rfl

end GlobalTheory.LBDescent
