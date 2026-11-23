import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

namespace GlobalTheory

theorem exists_algEquiv_comp_of_normal_rat {E K : Type} [Field E] [Field K] [CharZero E] [CharZero K]
    [Normal ℚ E] (φ ψ : E →+* K) : ∃ g : E ≃ₐ[ℚ] E, ∀ x, ψ x = φ (g x) := by
  letI : Algebra E K := φ.toAlgebra
  haveI : IsScalarTower ℚ E K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  refine ⟨AlgHom.restrictNormal' ψ.toRatAlgHom E, fun x => ?_⟩
  have := AlgHom.restrictNormal_commutes ψ.toRatAlgHom E x
  exact this.symm

theorem cmType_equiv_fixingSubgroup : ∀ (X : Formalism.L2.Col.Fields), X.Core → IsGalois ℚ X.E → ∃ (τ₀ : X.Tau) (H : Subgroup (X.E ≃ₐ[ℚ] X.E)) (γ : H ≃ X.Tau) (c : X.E ≃ₐ[ℚ] X.E), H.index = 2 ∧ (∀ g ∈ H, ∀ x ∈ X.Kq, g x = x) ∧ (∀ (h : H) (x : X.E), X.emb (γ h) x = X.emb τ₀ (h.1 x)) ∧ (∀ x, c x = star x) ∧ c ∉ H := by
  intro X hX hG
  classical
  have hpos : 0 < Fintype.card X.Tau := by
    rw [hX.card_Tau]; exact Module.finrank_pos
  obtain ⟨τ₀⟩ := Fintype.card_pos_iff.1 hpos
  let L : IntermediateField ℚ X.E := X.Kq.toIntermediateField (fun q => by
    intro τ τ'
    simp)
  have hL : Module.finrank ℚ L = 2 := hX.quad
  let H : Subgroup (X.E ≃ₐ[ℚ] X.E) := L.fixingSubgroup
  have hH : ∀ g, g ∈ H ↔ ∀ x ∈ X.Kq, g x = x := fun g => IntermediateField.mem_fixingSubgroup_iff L g
  have hidx : H.index = 2 := by
    rw [← hL]; exact (IntermediateField.finrank_eq_fixingSubgroup_index X.E L).symm
  have hcardG : Nat.card (X.E ≃ₐ[ℚ] X.E) = Fintype.card X.Tau * 2 := by
    rw [IsGalois.card_aut_eq_finrank, hX.card_Tau, ← hX.rankE, Module.finrank_mul_finrank]
  have hcardH : Nat.card X.Tau = Nat.card H := by
    have := H.card_mul_index
    rw [hidx, hcardG] at this
    rw [Nat.card_eq_fintype_card]
    omega
  choose g hg using fun τ => exists_algEquiv_comp_of_normal_rat (X.emb τ₀) (X.emb τ)
  have hgH : ∀ τ, g τ ∈ H := fun τ => (hH _).2 fun x hx => by
    apply (X.emb τ₀).injective
    rw [← hg]
    exact hx τ τ₀
  let δ : X.Tau → H := fun τ => ⟨g τ, hgH τ⟩
  have hδ : Function.Injective δ := by
    intro τ τ' h
    have h' : g τ = g τ' := congrArg Subtype.val h
    apply hX.emb_inj
    ext x
    rw [hg, hg τ', h']
  have hbij : Function.Bijective δ :=
    (Nat.bijective_iff_injective_and_card δ).2 ⟨hδ, hcardH⟩
  let e : X.Tau ≃ H := Equiv.ofBijective δ hbij
  have hγ : ∀ (h : H) (x : X.E), X.emb (e.symm h) x = X.emb τ₀ (h.1 x) := by
    intro h x
    have : g (e.symm h) = h.1 := congrArg Subtype.val (e.apply_symm_apply h)
    rw [hg, this]
  let c : X.E ≃ₐ[ℚ] X.E := AlgEquiv.ofRingEquiv (f := (starRingAut : RingAut X.E)) (fun q => by simp)
  have hc : ∀ x, c x = star x := fun x => rfl
  refine ⟨τ₀, H, e.symm, c, hidx, fun g hg => (hH g).1 hg, hγ, hc, fun hcH => ?_⟩
  apply hX.emb_ne (e.symm ⟨c, hcH⟩) τ₀
  ext x
  rw [hγ]
  rfl

end GlobalTheory
