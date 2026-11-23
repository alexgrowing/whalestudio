import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FormMem

theorem prod_fil_mem {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) (T : C) : ∀ (n : ℕ) (f : Fin n → Φ.A.obj T), (∀ k, f k ∈ (Fil 1).S T) →
      ∏ k, f k ∈ (Fil (n : ℤ)).S T
  | 0, f, _ => by
    have h : (Fil ((0 : ℕ) : ℤ)).S T = ⊤ := hF.top _ (by simp) T
    rw [h]
    exact Submodule.mem_top
  | n + 1, f, h => by
    rw [Fin.prod_univ_succ]
    have h0 : f 0 ∈ (Fil ((1 : ℕ) : ℤ)).S T := by simpa using h 0
    have := hF.mul 1 n T h0 (prod_fil_mem hF T n (fun k => f k.succ) fun k => h k.succ)
    rwa [Nat.add_comm] at this

theorem form_mem : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil)
    {d : ℕ} (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (j q : ℕ) (I : Fin j → Fin d) (x : Φ.A.obj E.D), x ∈ (Fil q).S E.D →
    ∀ s : ComposableArrows C j, E.form σ I x s ∈ (Fil ((j + q : ℕ) : ℤ)).S (s.obj (Fin.last j)) := by
  intro R _ C _ Φ Fil hF d E σ j q I x hx s
  refine hF.mul j q _ (prod_fil_mem hF _ j _ fun k => (Fil 1).map_mem _ ?_) ((Fil q).map_mem (σ _) hx)
  rw [hF.one]
  exact E.mem _ _ _

end GlobalTheory.CompanionTheory.FormMem
