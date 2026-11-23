import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPerfectIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupIdempotentSplitFieldStatement

set_option autoImplicit false

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDivGroup

theorem exists_isConn_isEt_splitting :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k),
      ∃ (G₀ G₁ : PDivGroup p k) (i₀ : G₀ ⟶ G) (q₀ : G ⟶ G₀) (i₁ : G₁ ⟶ G) (q₁ : G ⟶ G₁),
        G₀.IsConn ∧ G₁.IsEt ∧ i₀ ≫ q₀ = 𝟙 G₀ ∧ i₁ ≫ q₁ = 𝟙 G₁ ∧ q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G := by
  intro p _ k _ _ _ G
  obtain ⟨e, he, hnil, hred⟩ := GlobalTheory.T.exists_idempotent_nilpotent_complement_of_perfect p k G
  have h1 : e + (𝟙 G - e) = 𝟙 G := add_sub_cancel _ _
  have h1' : (𝟙 G - e) + e = 𝟙 G := sub_add_cancel _ _
  have h2 : e ≫ (𝟙 G - e) = 0 := by rw [Preadditive.comp_sub, Category.comp_id, he, sub_self]
  have h3 : (𝟙 G - e) ≫ e = 0 := by rw [Preadditive.sub_comp, Category.id_comp, he, sub_self]
  obtain ⟨G₀, i₀, q₀, a₀, b₀, c₀⟩ := GlobalTheory.T.pDivGroup_idempotent_split_field p k G e (𝟙 G - e) h1 h2 h3
  obtain ⟨G₁, i₁, q₁, a₁, b₁, c₁⟩ := GlobalTheory.T.pDivGroup_idempotent_split_field p k G (𝟙 G - e) e h1' h3 h2
  refine ⟨G₀, G₁, i₀, q₀, i₁, q₁, fun n x hx => ?_, fun n => ⟨fun x hx => ?_⟩, a₀, a₁,
    by rw [b₀, b₁, h1']⟩
  · obtain ⟨a, rfl⟩ := (c₀ n).1 x
    have ha : a ∈ augIdeal k (G.A n) := by
      have hx' : counit (R := k) (i₀.app n a) = 0 := hx
      rw [CoalgHomClass.counit_comp_apply] at hx'
      exact hx'
    have hk : e.app n a ∈ RingHom.ker (i₀.app n) := by
      rw [(c₀ n).2]
      exact Ideal.mem_map_of_mem (e.app n : G.A n →ₐ[k] G.A n) ha
    have := (hnil n a).map (i₀.app n)
    rwa [map_sub, RingHom.mem_ker.1 hk, sub_zero] at this
  · obtain ⟨a, rfl⟩ := (c₁ n).1 x
    have hq : q₁.app n (i₁.app n a) = e.app n a := congrArg (fun g : G ⟶ G => g.app n a) b₁
    have hi : i₁.app n (q₁.app n (i₁.app n a)) = i₁.app n a :=
      congrArg (fun g : G₁ ⟶ G₁ => g.app n (i₁.app n a)) a₁
    have h0 : e.app n a = 0 := hred n a (hq ▸ hx.map (q₁.app n))
    rw [← hi, hq, h0, map_zero]

end PDivGroup

end GlobalTheory
