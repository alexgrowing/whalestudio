import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem invariant_sup_alt {Γ k : Type} [Group Γ] [Field k] {d : ℕ} {ρ : Γ →* GL (Fin d) k}
    {U V : Submodule k (Fin d → k)} (hU : IsInv ρ U) (hV : IsInv ρ V) : IsInv ρ (U ⊔ V) := by
  intro g v hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  rw [Matrix.mulVec_add]
  exact Submodule.add_mem_sup (hU g a ha) (hV g b hb)

private theorem invariant_inf {Γ k : Type} [Group Γ] [Field k] {d : ℕ} {ρ : Γ →* GL (Fin d) k}
    {U V : Submodule k (Fin d → k)} (hU : IsInv ρ U) (hV : IsInv ρ V) : IsInv ρ (U ⊓ V) := by
  intro g v hv
  exact ⟨hU g v hv.1, hV g v hv.2⟩

private theorem invariant_bot_alt {Γ k : Type} [Group Γ] [Field k] {d : ℕ} (ρ : Γ →* GL (Fin d) k) :
    IsInv ρ (⊥ : Submodule k (Fin d → k)) := by
  intro g v hv
  rw [(Submodule.mem_bot k).1 hv, Matrix.mulVec_zero]
  exact Submodule.zero_mem _

theorem UpperTheory.Gal.Int.Geo.sSOfSum_of :
    SSOfSum := by
  intro Γ k _ _ d ρ B hB hS hT W hW
  obtain ⟨W', ⟨hinv, hdis⟩, hmax⟩ :=
    (wellFounded_gt (α := Submodule k (Fin d → k))).has_min
      {X | IsInv ρ X ∧ Disjoint W X} ⟨⊥, invariant_bot_alt ρ, disjoint_bot_right⟩
  have key : ∀ i, B i ≤ W ⊔ W' := by
    intro i
    rcases hS i (B i ⊓ (W ⊔ W')) (invariant_inf (hB i) (invariant_sup_alt hW hinv)) inf_le_left with h | h
    · have hd : Disjoint W (W' ⊔ B i) := by
        rw [Submodule.disjoint_def]
        intro w hw hw2
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw2
        have h2 : (a + b) + -a ∈ W ⊔ W' := Submodule.add_mem_sup hw (neg_mem ha)
        have h3 : (a + b) + -a = b := by abel
        rw [h3] at h2
        have hbU : b ∈ B i ⊓ (W ⊔ W') := ⟨hb, h2⟩
        rw [h] at hbU
        have hb0 : b = 0 := (Submodule.mem_bot k).1 hbU
        subst hb0
        rw [add_zero] at hw ⊢
        exact Submodule.disjoint_def.1 hdis a hw ha
      have hle : W' ⊔ B i ≤ W' := by
        by_contra hn
        exact hmax _ ⟨invariant_sup_alt hinv (hB i), hd⟩
          (lt_of_le_not_ge le_sup_left hn)
      exact (le_sup_right.trans hle).trans le_sup_right
    · exact inf_eq_left.1 h
  refine ⟨W', hinv, hdis, codisjoint_iff.2 ?_⟩
  exact top_le_iff.1 (hT ▸ iSup_le key)
