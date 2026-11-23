import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubMemOfMkEq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField GlobalTheory.FinDecomp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinDecomp

theorem heisAvg_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (m : ℕ)
    (lam : WO S T → ℂ), (∀ x ∈ Λ, ∀ y ∈ Λ, lam (x + y) = lam x * lam y * ψ (symplOH S T x y)) →
    ∀ [Fintype (Qm m Λ)] (g : WO S T → ℂ), (∀ l ∈ Λ, lam (m • l) • heisO ψ S T (m • l) g = g) →
    ∀ b ∈ Λ, lam b • heisO ψ S T b (∑ q : Qm m Λ, lam (repm q) • heisO ψ S T (repm q) g) =
      ∑ q : Qm m Λ, lam (repm q) • heisO ψ S T (repm q) g := by
  intro D ψ S T Λ m lam hlam _ g hg b hb
  have hsm : ∀ (x : WO S T) (c : ℂ) (f : WO S T → ℂ), heisO ψ S T x (c • f) = c • heisO ψ S T x f := by
    intro x c f; funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
  have hsumlin : ∀ (x : WO S T) (F : Qm m Λ → WO S T → ℂ),
      heisO ψ S T x (∑ q, F q) = ∑ q, heisO ψ S T x (F q) := by
    intro x F; funext w; simp only [heisO, Finset.sum_apply, Finset.mul_sum]
  have hmul : ∀ x ∈ Λ, ∀ y ∈ Λ, lam x • heisO ψ S T x (lam y • heisO ψ S T y g) =
      lam (x + y) • heisO ψ S T (x + y) g := by
    intro x hx y hy
    rw [hsm, GlobalTheory.FinTranslate.heisO_heisO, smul_smul, smul_smul, hlam x hx y hy]
  have key : ∀ q : Qm m Λ, lam b • heisO ψ S T b (lam (repm q) • heisO ψ S T (repm q) g) =
      lam (repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q)) •
        heisO ψ S T (repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q)) g := by
    intro q
    have hbq : b + repm q ∈ Λ := Λ.add_mem hb (repm_mem q)
    rw [hmul b hb _ (repm_mem q)]
    have hmk : (QuotientAddGroup.mk (⟨b + repm q, hbq⟩ : Λ) : Qm m Λ) =
        (QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q := by
      conv_rhs => rw [← mk_repm q]
      rfl
    have h1 := repm_mk_sub (m := m) hbq
    rw [hmk] at h1
    obtain ⟨l, hl, hl'⟩ := mem_mLat.1 h1
    have he : repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q) = (b + repm q) + m • l := by
      rw [hl']; abel
    rw [he, ← hmul _ hbq _ (Λ.nsmul_mem hl m), hg l hl]
  calc lam b • heisO ψ S T b (∑ q : Qm m Λ, lam (repm q) • heisO ψ S T (repm q) g)
      = ∑ q : Qm m Λ, lam (repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q)) •
          heisO ψ S T (repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q)) g := by
        rw [hsumlin, Finset.smul_sum]
        exact Finset.sum_congr rfl fun q _ => key q
    _ = _ := Equiv.sum_comp (Equiv.addLeft (QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ))
          (fun q => lam (repm q) • heisO ψ S T (repm q) g)

end GlobalTheory.FinDecomp

end
