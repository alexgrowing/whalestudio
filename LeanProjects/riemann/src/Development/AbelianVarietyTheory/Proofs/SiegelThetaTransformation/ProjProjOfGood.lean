import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndexStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ProjProj

open GlobalTheory.SW.TensVac

theorem proj_proj_of_good {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}
    {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)
    (hs : IsSympl X bas) (hn : Even n) {w : E}
    {A₁ A₂ A₃ : AddSubgroup (Matrix (Fin n) (Fin r) E)} (h₂ : Good X w A₂) (h₃ : Good X w A₃)
    (hle : A₂ ≤ (A₂ ⊓ A₁) ⊔ (A₂ ⊓ A₃)) {v : TF n g} (hv : IsVac X bas w A₁ v) :
    projA X bas w A₃ (projA X bas w A₂ v) = projA X bas w A₃ v := by
  obtain ⟨v₂, hv₂, -⟩ := h₂.vac hs
  obtain ⟨v₃, hv₃, -⟩ := h₃.vac hs
  have hsb₂ := (h₂.proj idx hs hn hv.1 hv₂).1
  rw [(h₃.proj idx hs hn hsb₂ hv₃).2, (h₃.proj idx hs hn hv.1 hv₃).2]
  congr 1
  have hfin := h₂.finite idx hs hn hv.1
  have hsb : ∀ ψ ∈ hfin.toFinset, IsSB ψ := by
    intro ψ hψ
    obtain ⟨y, -, rfl⟩ := hfin.mem_toFinset.1 hψ
    exact rho_sb idx hs hn y hv.1
  have hpos : (((fun y => epsW X w y • heisG X bas y v) '' A₂).ncard : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 ((Set.ncard_pos hfin).2 ⟨_, 0, A₂.zero_mem, rfl⟩).ne'
  obtain ⟨h1, h2⟩ := sum_sb_ip _ hsb hv₃.1
  rw [projA, finsum_mem_eq_finite_toFinset_sum _ hfin, ip_smul_left _ h1 hv₃.1, h2,
    Finset.sum_congr rfl (g := fun _ => SW.ip v v₃), Finset.sum_const,
    ← Set.ncard_eq_toFinset_card _ hfin, nsmul_eq_mul, inv_mul_cancel_left₀ hpos]
  intro ψ hψ
  obtain ⟨y, hy, rfl⟩ := hfin.mem_toFinset.1 hψ
  obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 (hle hy)
  show SW.ip (epsW X w (a + b) • heisG X bas (a + b) v) v₃ = SW.ip v v₃
  rw [add_comm a b, ← h₂.rho_rho idx hs hn hb.1 ha.1 hv.1, hv.2.2 a ha.2,
    ← rho_ip (w := w) idx hs hn b hv.1 hv₃.1, hv₃.2.2 b hb.2]

theorem proj_proj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L₁ L₂ L₃ : Lt E r, SelfD X L₁ → SelfD X L₂ → SelfD X L₃ → ∀ Λ₁ ∈ Vset E n 1, ∀ Λ₂ ∈ Vset E n 1, ∀ Λ₃ ∈ Vset E n 1, tens Λ₂ L₂ ≤ (tens Λ₂ L₂ ⊓ tens Λ₁ L₁) ⊔ (tens Λ₂ L₂ ⊓ tens Λ₃ L₃) → ∀ v : TF n g, IsVac X bas w (tens Λ₁ L₁) v → projA X bas w (tens Λ₃ L₃) (projA X bas w (tens Λ₂ L₂) v) = projA X bas w (tens Λ₃ L₃) v := by
  intro E _ _ _ r X g bas idx n hs hn w hw hw' L₁ L₂ L₃ _ hL₂ hL₃ Λ₁ _ Λ₂ hΛ₂ Λ₃ hΛ₃ hle v hv
  have good (L) (hL : SelfD X L) (Λ) (hΛ : Λ ∈ Vset E n 1) : Good X w (tens Λ L) := by
    obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.tensorLattice_selfDual_semicharacter_index E r X g bas idx n hs hn w hw hw' L hL 1 Λ hΛ
    exact ⟨h1, h2, h3⟩
  exact proj_proj_of_good idx hs hn (good L₂ hL₂ Λ₂ hΛ₂) (good L₃ hL₃ Λ₃ hΛ₃) hle hv

end GlobalTheory.Dict.ProjProj
