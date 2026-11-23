import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi

open Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.RootEx
open scoped Topology

noncomputable section
namespace GlobalTheory.CompanionTheory.CharPerp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def perp {n : ℕ} (ψ : AddChar k Circle) (A : AddSubgroup (Fin n → k)) :
    AddSubgroup (Fin n → k) where
  carrier := {ξ | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1}
  zero_mem' := fun a _ => by simp
  add_mem' := fun {x y} hx hy a ha => by
    rw [add_dotProduct, AddChar.map_add_eq_mul, hx a ha, hy a ha, one_mul]
  neg_mem' := fun {x} hx a ha => by
    rw [neg_dotProduct, AddChar.map_neg_eq_inv, hx a ha, inv_one]

theorem isOpen_perp {n : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (A : AddSubgroup (Fin n → k)) (hAc : IsCompact (A : Set (Fin n → k))) :
    IsOpen (perp ψ A : Set (Fin n → k)) := by
  obtain ⟨s, hs⟩ := exists_cball_addChar_eq_one ψ hψ
  have hN : IsOpen ((fun q : (Fin n → k) × (Fin n → k) => q.1 ⬝ᵥ q.2) ⁻¹' cball s) :=
    (isOpen_cball s).preimage continuous_dot
  have hsub : ({0} : Set (Fin n → k)) ×ˢ (A : Set (Fin n → k)) ⊆
      (fun q : (Fin n → k) × (Fin n → k) => q.1 ⬝ᵥ q.2) ⁻¹' cball s := by
    rintro ⟨x, a⟩ ⟨hx, -⟩
    obtain rfl : x = 0 := hx
    simp [cball]
  obtain ⟨u, v, hu, -, h0u, hAv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hAc hN hsub
  refine AddSubgroup.isOpen_of_mem_nhds (perp ψ A) (g := 0) ?_
  refine Filter.mem_of_superset (hu.mem_nhds (h0u rfl)) fun ξ hξ a ha => ?_
  exact hs _ (huv (Set.mk_mem_prod hξ (hAv ha)))

theorem isClosed_perp {n : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (A : AddSubgroup (Fin n → k)) : IsClosed (perp ψ A : Set (Fin n → k)) := by
  have : (perp ψ A : Set (Fin n → k)) =
      ⋂ a ∈ A, (fun ξ : Fin n → k => ψ (ξ ⬝ᵥ a)) ⁻¹' {1} := by
    ext ξ
    simp [perp]
  rw [this]
  refine isClosed_biInter fun a _ => isClosed_singleton.preimage ?_
  exact hψ.comp (continuous_id.dotProduct continuous_const)

theorem isCompact_perp {n : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (A : AddSubgroup (Fin n → k)) (hAo : IsOpen (A : Set (Fin n → k))) :
    IsCompact (perp ψ A : Set (Fin n → k)) := by
  classical
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
  obtain ⟨s, hs⟩ := exists_box_subset (n := Fin n) (hAo.mem_nhds A.zero_mem)
  refine (isCompact_box (n := Fin n) (c * s⁻¹)).of_isClosed_subset (isClosed_perp ψ hψ A) ?_
  intro ξ hξ i _
  by_contra hi
  obtain ⟨t, ht, hne⟩ := hc.exists_ne_one s hi
  have hmem : Pi.single i t ∈ box (Fin n) s := by
    intro j _
    by_cases hj : j = i
    · subst hj; simpa using ht
    · simp [Pi.single_eq_of_ne hj, cball]
  apply hne
  have := hξ _ (hs hmem)
  rwa [dotProduct_single, mul_comm] at this

theorem perp_isOpen_isCompact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) →
    IsOpen (A : Set (Fin n → k)) →
    IsOpen {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} ∧
      IsCompact {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} := by
  intro k _ _ _ _ ψ hψ h1 n A hAc hAo
  exact ⟨isOpen_perp ψ hψ A hAc, isCompact_perp ψ hψ h1 A hAo⟩

end GlobalTheory.CompanionTheory.CharPerp
