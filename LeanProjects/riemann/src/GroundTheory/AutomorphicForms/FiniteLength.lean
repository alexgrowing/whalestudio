import Mathlib
import GroundTheory.AutomorphicForms.FiniteLengthCuspidal
import GroundTheory.AutomorphicForms.FiniteLengthLeviJacquet
import GroundTheory.AutomorphicForms.FiniteLengthSeries
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function Iwasawa

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section Levi

variable {β δ : Fin n → ℕ} {U U' : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup U']
  [Module ℂ U'] {Y : Representation ℂ (levi F n β) U} {π : Representation ℂ (levi F n β) U'}

theorem leviJacquetMap_injective (h : Refines β δ) (hY : IsSmooth Y) (hπ : IsSmooth π)
    (i : Representation.IntertwiningMap Y π) (hi : Injective i) :
    Injective (leviJacquetMap h i) := by
  have hex := exact_leviJacquetMap h hY hπ (0 : Representation.IntertwiningMap Y Y) i
    (fun y => ⟨fun hy => ⟨0, by
      show (0 : U) = y
      exact (hi (hy.trans (map_zero i).symm)).symm⟩, by rintro ⟨z, rfl⟩; exact map_zero i⟩)
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  obtain ⟨z, hz⟩ := (hex y).1 hy
  obtain ⟨z, rfl⟩ := Representation.Coinvariants.mk_surjective _ z
  rw [leviJacquetMap_mk] at hz
  rw [← hz]
  exact map_zero (Representation.Coinvariants.mk _)

theorem _root_.GroundTheory.Automorphic.IsSubquotient.leviJacquetRep (h : Refines β δ) (hY : IsSmooth Y)
    (hsub : IsSubquotient π Y) : IsSubquotient (leviJacquetRep h π) (leviJacquetRep h Y) := by
  obtain ⟨C, p, hp⟩ := hsub
  refine .of_injective_of_surjective (leviJacquetMap h (subrepInclusion C))
    (leviJacquetMap_injective h (isSmooth_subrep hY C) hY _ (fun a b h => Subtype.ext h))
    (leviJacquetMap h p) fun y => ?_
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ y
  obtain ⟨u, rfl⟩ := hp v
  exact ⟨Representation.Coinvariants.mk _ u, leviJacquetMap_mk _ _ _⟩

theorem surjective_leviFrobenius [Nontrivial U'] (h : Refines β δ) {X : Type*} [AddCommGroup X]
    [Module ℂ X] {τ : Representation ℂ (levi F n δ) X} [τ.IsIrreducible] (hπ : IsSmooth π)
    (Φ : Representation.IntertwiningMap π (leviParabolicInd F n β δ τ)) (hΦ : Injective Φ) :
    Surjective (leviFrobenius π τ h hπ Φ) := by
  rcases Representation.IsIrreducible.surjective_or_eq_zero (leviFrobenius π τ h hπ Φ) with h' | h'
  · exact h'
  · exfalso
    have h0 : Φ = 0 := (leviFrobenius π τ h hπ).injective (h'.trans (map_zero _).symm)
    obtain ⟨v, hv⟩ := exists_ne (0 : U')
    exact hv (hΦ (by rw [map_zero, h0]; rfl))

end Levi

section Cuspidal

variable {γ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {τ : Representation ℂ (levi F n γ) W}

theorem hasFiniteLength_jacquetRep_parabolicInd_of_isCuspidal [τ.IsIrreducible] (hτ : IsSmooth τ)
    (hτc : IsCuspidal τ) (β : Fin n → ℕ) :
    HasFiniteLength (jacquetRep F n β (parabolicInd F n γ τ)) := by
  classical
  set X := parabolicInd F n γ τ
  have hX : IsSmooth X := isSmooth_parabolicInd τ
  have hY : IsSmooth (jacquetRep F n β X) := isSmooth_jacquetRep X hX

  let ι := {δ : Fin n → Fin n // Refines β (fun i => (δ i : ℕ)) ∧
    ∃ w : Equiv.Perm (Fin n), ∀ a b, δ a = δ b ↔ γ (w a) = γ (w b)}
  let dN : ι → Fin n → ℕ := fun δ i => (δ.1 i : ℕ)
  have hdN : ∀ (δ : ι) a b, dN δ a = dN δ b ↔ δ.1 a = δ.1 b := fun δ a b => Fin.val_inj
  refine hasFiniteLength_of_coinvariants hY (fun δ : ι => leviUnipotent F n β (dN δ))
    (fun δ => exists_compactOpen_leviUnipotent) (M := fun δ => levi F n (dN δ))
    (fun δ => leviJacquetRep δ.2.1 (jacquetRep F n β X))
    (fun δ m => ⟨δ.2.1.leviIncl F m, _, fun v => leviJacquetRep_mk _ _ m v⟩)
    (fun δ => hasFiniteLength_of_injective (jacquetStages X δ.2.1).toIntertwiningMap
      (fun a b hab => (jacquetStages X δ.2.1).toLinearEquiv.injective hab)
      (hasFiniteLength_jacquetRep_parabolicInd hτ hτc
        (let ⟨w', hw'⟩ := δ.2.2; ⟨w', fun a b => (hdN δ a b).trans (hw' a b)⟩))) ?_
  intro V' _ _ π _ hπ hsub
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have : Nontrivial V' := ⟨⟨v, 0, hv⟩⟩
  obtain ⟨δ', h', U, _, _, τ', hτ'i, hτ's, hτ'c, Φ, hΦ⟩ := exists_embedding_leviParabolicInd hπ
  have hq := surjective_leviFrobenius h' hπ Φ hΦ
  have hsubτ : IsSubquotient τ' (jacquetRep F n δ' X) :=
    ((IsSubquotient.of_surjective _ hq).trans (hsub.leviJacquetRep h' hY)).trans
      (IsSubquotient.of_injective (jacquetStages X h').toIntertwiningMap
        (fun a b hab => (jacquetStages X h').toLinearEquiv.injective hab))
  obtain ⟨w, hw, -⟩ := exists_piece_of_isSubquotient_jacquetRep hτ hτc hτ's hτ'c hsubτ
  have hrank : ∀ a b, δ' a = δ' b ↔ (rankFun δ' a : ℕ) = rankFun δ' b := fun a b =>
    eq_iff_eq_of_lt_iff (fun i j => (rankFun_lt_iff δ' i j).symm) a b
  let δ : ι := ⟨rankFun δ', fun i j hij => (rankFun_lt_iff δ' j i).2 (h' i j hij),
    w, fun a b => Fin.val_inj.symm.trans ((hrank a b).symm.trans (hw a b))⟩
  refine ⟨δ, ?_⟩
  have hN : leviUnipotent F n β (dN δ) = leviUnipotent F n β δ' := by
    simp only [leviUnipotent]
    rw [unipotentRadical_congr (rankFun_lt_iff δ')]
  rw [hN]
  obtain ⟨u, hu⟩ := exists_ne_zero_of_isIrreducible (ρ := τ')
  obtain ⟨y, hy⟩ := hq u
  exact ⟨y, 0, fun h => hu (by rw [← hy, h, map_zero])⟩

end Cuspidal

section Main

theorem hasFiniteLength_jacquetRep_of_isIrreducible {V : Type*} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) F) V} [π.IsIrreducible] (hπ : IsSmooth π) (β : Fin n → ℕ) :
    HasFiniteLength (jacquetRep F n β π) := by
  obtain ⟨γ, U, _, _, τ, hτi, hτs, hτc, -, Φ, hΦ⟩ := exists_embedding_parabolicInd hπ
  exact hasFiniteLength_of_injective (jacquetMap F n β Φ)
    (jacquetMap_injective hπ (isSmooth_parabolicInd τ) Φ hΦ β)
    (hasFiniteLength_jacquetRep_parabolicInd_of_isCuspidal hτs hτc β)

theorem hasFiniteLength_jacquetRep {V : Type*} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) F) V} (hπ : IsSmooth π) (hfl : HasFiniteLength π)
    (β : Fin n → ℕ) : HasFiniteLength (jacquetRep F n β π) :=
  hasFiniteLength_jacquetRep_of_factors hπ hfl β fun _ _ _ _ _ hπ' _ =>
    hasFiniteLength_jacquetRep_of_isIrreducible hπ' β

theorem hasFiniteLength_parabolicInd_of_isIrreducible {β : Fin n → ℕ} {W : Type*}
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (levi F n β) W} [ρ.IsIrreducible]
    (hρ : IsSmooth ρ) : HasFiniteLength (parabolicInd F n β ρ) := by
  obtain ⟨γ, h, X, _, _, τ, hτi, hτs, hτc, Φ, hΦ⟩ := exists_embedding_leviParabolicInd hρ
  have he : Injective (inductionStages τ h).toIntertwiningMap := fun a b hab =>
    (inductionStages τ h).toLinearEquiv.injective hab
  exact hasFiniteLength_of_injective
    ((inductionStages τ h).toIntertwiningMap.comp (parabolicIndMap Φ))
    (he.comp (parabolicIndMap_injective Φ hΦ))
    (hasFiniteLength_parabolicInd_of_isCuspidal hτs hτc)

theorem hasFiniteLength_parabolicInd {β : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (levi F n β) W} (hσ : IsSmooth σ) (hfl : HasFiniteLength σ) :
    HasFiniteLength (parabolicInd F n β σ) :=
  hasFiniteLength_parabolicInd_of_factors hσ hfl fun _ _ _ _ _ hρ _ =>
    hasFiniteLength_parabolicInd_of_isIrreducible hρ

end Main

end Parabolic

end GroundTheory.Automorphic
