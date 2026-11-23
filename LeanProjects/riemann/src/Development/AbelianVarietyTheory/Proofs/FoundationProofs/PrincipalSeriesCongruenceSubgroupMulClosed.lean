import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTrivialOnUnitsModConductorUnitCharacterValuePr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem triv_mul_int_left (χ : kˣ →* ℂˣ) {x y : k} (hx : valuation k x ≤ 1) (hy : Triv χ y) :
    Triv χ (x * y) :=
  triv_mono χ y (x * y) (by rw [map_mul]; exact mul_le_of_le_one_left' hx) hy

theorem triv_mul_int_right (χ : kˣ →* ℂˣ) {x y : k} (hy : valuation k y ≤ 1) (hx : Triv χ x) :
    Triv χ (x * y) := by
  rw [mul_comm]; exact triv_mul_int_left χ hy hx

theorem grp_mul {n : ℕ} (ψ : Fin n → kˣ →* ℂˣ) (hψ : Ordered ψ) {a b : GL (Fin n) k}
    (ha : a ∈ grp ψ) (hb : b ∈ grp ψ) : a * b ∈ grp ψ := by
  refine ⟨(KO k (Fin n)).mul_mem ha.1 hb.1, fun i j hij => ?_⟩
  rw [Units.val_mul, Matrix.mul_apply]
  refine Finset.sum_induction _ (fun x => Triv (ψ i / ψ j) x) (fun x y hx hy => triv_add _ x y hx hy)
    (triv_zero _) (fun l _ => ?_)
  rcases le_or_gt l i with hli | hil
  ·
    have h1 : Triv (ψ l / ψ j) (b.val l j) := hb.2 l j (lt_of_le_of_lt hli hij)
    have h2 : Triv (ψ i / ψ j) (b.val l j) := hψ l i j j hli hij.le le_rfl _ h1
    exact triv_mul_int_left _ (GlobalTheory.BlockType.val_le_one_of_mem_KO ha.1 i l) h2
  · rcases lt_or_ge l j with hlj | hjl
    · have h1 : Triv (ψ i / ψ l) (a.val i l * b.val l j) :=
        triv_mul_int_right _ (GlobalTheory.BlockType.val_le_one_of_mem_KO hb.1 l j) (ha.2 i l hil)
      have h2 : Triv (ψ l / ψ j) (a.val i l * b.val l j) :=
        triv_mul_int_left _ (GlobalTheory.BlockType.val_le_one_of_mem_KO ha.1 i l) (hb.2 l j hlj)
      have h3 := triv_mul _ _ _ h1 h2
      rwa [div_mul_div_cancel] at h3
    · have h1 : Triv (ψ i / ψ l) (a.val i l) := ha.2 i l hil
      have h2 : Triv (ψ i / ψ j) (a.val i l) := hψ i i j l le_rfl hij.le hjl _ h1
      exact triv_mul_int_right _ (GlobalTheory.BlockType.val_le_one_of_mem_KO hb.1 l j) h2

theorem grp_mul_closed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp ψ, ∀ b ∈ grp ψ, a * b ∈ grp ψ :=
  fun _ _ _ _ _ _ ψ hψ _ ha _ hb => grp_mul ψ hψ ha hb

end GlobalTheory.PsType
