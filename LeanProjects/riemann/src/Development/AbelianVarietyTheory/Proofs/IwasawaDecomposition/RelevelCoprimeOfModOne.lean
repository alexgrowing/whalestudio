import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory

theorem host_relevel : ∀ (R : Ranks) (H : Host R), H.ccK = ⊤ → ∀ (g : Fin 2 → ℕ) (p p' : ℕ) (S : Finset ℕ), (∀ i, (g i).Prime) → g 0 ≠ g 1 → p.Prime → p'.Prime → p ≠ p' → p % 15 = 1 → p' % 15 = 1 → (∀ i, p ≠ g i ∧ p' ≠ g i) → (∀ x ∈ insert (g 0) (insert (g 1) (insert p (insert p' S))), Nat.Coprime x H.QS) → ∃ (hg : ∀ i, (g i).Prime) (hne : g 0 ≠ g 1) (lv : Finset ℕ) (hl : ∀ i, g i ∈ lv) (hp : p.Prime) (hp' : p'.Prime) (hpp : p ≠ p') (hpl : p ∈ lv ∧ p' ∈ lv) (hm : p % 15 = 1 ∧ p' % 15 = 1) (hpg : ∀ i, p ≠ g i ∧ p' ≠ g i) (hc : ∀ x ∈ insert 2 (insert 3 (insert 5 (insert H.q (insert H.d lv)))), Nat.Coprime (Ideal.absNorm H.ccK) x) (hcs : ∀ x ∈ lv, Nat.Coprime x H.QS), lv = insert (g 0) (insert (g 1) (insert p (insert p' S))) ∧ ∃ H' : Host R, H' = { H with levelPrimes := lv, g := g, g_prime := hg, g_ne := hne, g_level := hl, pde := p, pde' := p', pde_prime := hp, pde'_prime := hp', pde_ne := hpp, pde_level := hpl, pde_mod := hm, pde_ne_g := hpg, ccK_coprime := hc, level_coprimeS := hcs } := by
  intro R H hK g p p' S hg hne hp hp' hpp h1 h2 hpg hcs
  refine ⟨hg, hne, insert (g 0) (insert (g 1) (insert p (insert p' S))), ?_, hp, hp', hpp, ?_,
    ⟨h1, h2⟩, hpg, ?_, hcs, rfl, _, rfl⟩
  · intro i
    fin_cases i <;> simp
  · constructor <;> simp
  · intro x _
    rw [hK]
    simp

end GlobalTheory
