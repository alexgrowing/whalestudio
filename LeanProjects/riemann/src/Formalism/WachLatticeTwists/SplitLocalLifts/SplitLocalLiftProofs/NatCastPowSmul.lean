import Formalism.WachLatticeTwists.SplitLocalLifts.Statement
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.DualWByLettersExtended

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JL

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N2

theorem natCast_pow_smul (ℓ : ℕ) [Fact ℓ.Prime] {O : Type*} [CommRing O] [Algebra ℤ_[ℓ] O]
    {H : Type*} [AddCommGroup H] [Module O H] [Module ℤ_[ℓ] H] [IsScalarTower ℤ_[ℓ] O H]
    (e : ℕ) (x : H) : ((ℓ : ℤ_[ℓ]) ^ e) • x = ((ℓ : O) ^ e) • x := by
  rw [← algebraMap_smul O ((ℓ : ℤ_[ℓ]) ^ e) x, map_pow, map_natCast]

theorem scal : StatScal := by
  intro ℓ _ O _ _ H₁ H₂ _ _ _ _ _ _ _ _ Hf₁ Hf₂ g e
  constructor
  · intro h κ hκ
    obtain ⟨κ₁, h₁, h₂⟩ := h κ hκ
    exact ⟨κ₁, h₁, by rw [← natCast_pow_smul ℓ]; exact h₂⟩
  · intro h κ hκ
    obtain ⟨κ₁, h₁, h₂⟩ := h κ hκ
    exact ⟨κ₁, h₁, by rw [natCast_pow_smul ℓ (O := O)]; exact h₂⟩

theorem mono : StatMono := by
  intro O _ ℓ H₁ H₂ _ _ _ _ Hf₁ Hf₂ g e e' hee h κ hκ
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hee
  rw [pow_add, mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ (h κ hκ)

theorem prodB_lift (ℓ : ℕ) [Fact ℓ.Prime] {H₁ H₂ : Type} [AddCommGroup H₁] [Module ℤ_[ℓ] H₁]
    [AddCommGroup H₂] [Module ℤ_[ℓ] H₂] (Hf₁ : Submodule ℤ_[ℓ] H₁) (Hf₂ : Submodule ℤ_[ℓ] H₂)
    (g : H₁ →ₗ[ℤ_[ℓ]] H₂) (e : ℕ) (h : ProdB ℓ Hf₁ Hf₂ g e) : LiftZ ℓ Hf₁ Hf₂ g e := by
  obtain ⟨A, _, _, B, M, u, s, H, jumps, D₀, D₁, D₂, _, _, _, _, _, _, _, _, _, _, _, _, W₀, W₁, W₂,
    S, cl₁, cl₂, I, _, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
    a18, a19, a20, a21, rfl⟩ := h
  exact lifting_theorem.1 ℓ A B M u s H jumps a1 a2 a3 a4 a5 a6 a7 D₀ D₁ D₂ W₀ W₁ W₂ S H₁ H₂ cl₁ cl₂ Hf₁ Hf₂
    g I a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21

theorem prodA_lift (ℓ : ℕ) [Fact ℓ.Prime] {H₁ H₂ : Type} [AddCommGroup H₁] [Module ℤ_[ℓ] H₁]
    [AddCommGroup H₂] [Module ℤ_[ℓ] H₂] (Hf₁ : Submodule ℤ_[ℓ] H₁) (Hf₂ : Submodule ℤ_[ℓ] H₂)
    (g : H₁ →ₗ[ℤ_[ℓ]] H₂) (e : ℕ) (h : ProdA ℓ Hf₁ Hf₂ g e) : LiftZ ℓ Hf₁ Hf₂ g e := by
  obtain ⟨h2, A, _, _, B, M, u, H, jumps, c, D₀, D₁, D₂, _, _, _, _, _, _, _, _, _, _, _, _, W₀, W₁,
    W₂, S, δ, cl₁, cl₂, I, _, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16,
    a17, a18, a19, rfl⟩ := h
  exact lifting_theorem.2.1 ℓ h2 A B M u H jumps c a1 a2 a3 a4 a5 D₀ D₁ D₂ W₀ W₁ W₂ S δ H₁ H₂ cl₁ cl₂ Hf₁
    Hf₂ g I a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19

theorem src : StatSrc := by
  intro ℓ _ H₁ H₂ _ _ _ _ Hf₁ Hf₂ g e h
  rcases h with h | h | h
  · exact prodB_lift ℓ Hf₁ Hf₂ g e h
  · exact prodA_lift ℓ Hf₁ Hf₂ g e h
  · obtain ⟨K₁, K₂, _, _, _, _, Kf₁, Kf₂, hh, res₂, cor₁, cor₂, n, E, b1, b2, b3, b4, b5, b6, rfl⟩ := h
    refine lifting_theorem.2.2 ℓ K₁ K₂ H₁ H₂ Kf₁ Kf₂ Hf₁ Hf₂ hh g res₂ cor₁ cor₂ n E b1 b2 b3 b4 b5 ?_
    rcases b6 with b6 | b6
    · exact prodB_lift ℓ Kf₁ Kf₂ hh E b6
    · exact prodA_lift ℓ Kf₁ Kf₂ hh E b6

theorem srcO : StatSrcO := by
  intro ℓ _ O _ _ H₁ H₂ _ _ _ _ _ _ _ _ Hf₁ Hf₂ g e' h
  obtain ⟨e, he, h⟩ := h
  exact mono O ℓ H₁ H₂ Hf₁ Hf₂ g e e' he
    ((scal ℓ O H₁ H₂ Hf₁ Hf₂ g e).1 (src ℓ H₁ H₂ _ _ _ e h))

end Formalism.RepresentationBoundsCohomology.JL
