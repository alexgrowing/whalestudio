import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

namespace GlobalTheory.RhoProd

theorem out_iff {G : Type} [Group G] (H : Subgroup G) (P : G → Prop)
    (hP : ∀ g h, h ∈ H → (P (g * h) ↔ P g)) (g : G) :
    P (Quotient.out (QuotientGroup.mk g : G ⧸ H)) ↔ P g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hh]; exact hP g h h.2

theorem card_prod {G G₁ G₂ : Type} [Group G] [Group G₁] [Group G₂]
    (H : Subgroup G) (H₁ : Subgroup G₁) (H₂ : Subgroup G₂) (e : G ≃* G₁ × G₂)
    (he : ∀ g, g ∈ H ↔ (e g).1 ∈ H₁ ∧ (e g).2 ∈ H₂)
    (P : G → Prop) (P₁ : G₁ → Prop) (P₂ : G₂ → Prop)
    (hP : ∀ g, P g ↔ P₁ (e g).1 ∧ P₂ (e g).2)
    (h₁ : ∀ g h, h ∈ H₁ → (P₁ (g * h) ↔ P₁ g)) (h₂ : ∀ g h, h ∈ H₂ → (P₂ (g * h) ↔ P₂ g)) :
    Nat.card {k : G ⧸ H // P (Quotient.out k)} =
      Nat.card {k : G₁ ⧸ H₁ // P₁ (Quotient.out k)} * Nat.card {k : G₂ ⧸ H₂ // P₂ (Quotient.out k)} := by
  let E : G ⧸ H ≃ (G₁ ⧸ H₁) × (G₂ ⧸ H₂) :=
    (Quotient.congr e.toEquiv (by
      intro a b
      show QuotientGroup.leftRel H a b ↔ (QuotientGroup.leftRel H₁).prod (QuotientGroup.leftRel H₂) (e a) (e b)
      rw [Setoid.prod_apply, QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, he]
      simp [map_mul, map_inv])).trans (Setoid.prodQuotientEquiv _ _).symm
  have hE : ∀ g : G, E (QuotientGroup.mk g) = (QuotientGroup.mk (e g).1, QuotientGroup.mk (e g).2) := by
    intro g; rfl
  have hPi : ∀ g h, h ∈ H → (P (g * h) ↔ P g) := by
    intro g h hh
    rw [hP, hP, map_mul, Prod.fst_mul, Prod.snd_mul]
    exact and_congr (h₁ _ _ ((he h).1 hh).1) (h₂ _ _ ((he h).1 hh).2)
  rw [← Nat.card_prod]
  refine Nat.card_congr ((E.subtypeEquiv ?_).trans (Equiv.subtypeProdEquivProd))
  intro k
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective k
  rw [hE, out_iff H₁ P₁ h₁, out_iff H₂ P₂ h₂, ← hP]
  exact out_iff H P hPi g

variable {K : UQ}

def torusEquiv (B₁ B₂ : InvAlg K) : (B₁.prod B₂).T ≃* B₁.T × B₂.T where
  toFun t := (⟨Units.map (RingHom.fst B₁.A B₂.A).toMonoidHom (show (B₁.A × B₂.A)ˣ from t.1),
      congrArg Prod.fst t.2⟩,
    ⟨Units.map (RingHom.snd B₁.A B₂.A).toMonoidHom (show (B₁.A × B₂.A)ˣ from t.1),
      congrArg Prod.snd t.2⟩)
  invFun s := ⟨show (B₁.A × B₂.A)ˣ from MulEquiv.prodUnits.symm ((s.1 : B₁.Aˣ), (s.2 : B₂.Aˣ)),
      Prod.ext s.1.2 s.2.2⟩
  left_inv t := by
    apply Subtype.ext; apply Units.ext; rfl
  right_inv s := by
    ext <;> rfl
  map_mul' a b := by
    ext <;> rfl

theorem inv_mul_int (B : InvAlg K) (w : B.A) (g h : B.T)
    (hh : h ∈ (intUnits K.O B.A).subgroupOf B.T) :
    IsIntegral K.O ((((g * h : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w : B.A) ↔
      IsIntegral K.O ((((g : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w : B.A) := by
  rw [Subgroup.mem_subgroupOf] at hh
  obtain ⟨hi, hi'⟩ := hh
  have e1 : ((((g * h : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w : B.A) =
      ((((h : B.T) : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * ((((g : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w) := by
    simp [mul_inv_rev, Units.val_mul, mul_assoc]
  have e2 : ((((g : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w : B.A) =
      (((h : B.T) : B.Aˣ) : B.A) * ((((g * h : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w) := by
    rw [e1, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  constructor
  · intro H; rw [e2]; exact hi.mul H
  · intro H; rw [e1]; exact hi'.mul H

theorem rho_prod : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (w₁ : B₁.A) (w₂ : B₂.A),
    (B₁.prod B₂).rho ((w₁, w₂) : B₁.A × B₂.A) = B₁.rho w₁ * B₂.rho w₂ := by
  intro K B₁ B₂ w₁ w₂
  unfold InvAlg.rho
  refine card_prod ((intUnits K.O (B₁.prod B₂).A).subgroupOf (B₁.prod B₂).T) _ _ (torusEquiv B₁ B₂) ?_
    (fun g : (B₁.prod B₂).T => IsIntegral K.O ((((g : (B₁.prod B₂).Aˣ)⁻¹ : (B₁.prod B₂).Aˣ) * (show (B₁.prod B₂).A from (w₁, w₂)) : (B₁.prod B₂).A)))
    (fun g : B₁.T => IsIntegral K.O ((((g : B₁.Aˣ)⁻¹ : B₁.Aˣ) * w₁ : B₁.A)))
    (fun g : B₂.T => IsIntegral K.O ((((g : B₂.Aˣ)⁻¹ : B₂.Aˣ) * w₂ : B₂.A)))
    ?_ (inv_mul_int B₁ w₁) (inv_mul_int B₂ w₂)
  · intro g
    simp only [Subgroup.mem_subgroupOf]
    show (IsIntegral K.O (show B₁.A × B₂.A from ((g : (B₁.prod B₂).Aˣ) : (B₁.prod B₂).A)) ∧ IsIntegral K.O (show B₁.A × B₂.A from (((g : (B₁.prod B₂).Aˣ)⁻¹ : (B₁.prod B₂).Aˣ) : (B₁.prod B₂).A))) ↔ _
    rw [IsIntegral.pair_iff, IsIntegral.pair_iff]
    exact ⟨fun ⟨⟨a, b⟩, ⟨c, d⟩⟩ => ⟨⟨a, c⟩, ⟨b, d⟩⟩, fun ⟨⟨a, c⟩, ⟨b, d⟩⟩ => ⟨⟨a, b⟩, ⟨c, d⟩⟩⟩
  · intro g
    show IsIntegral K.O (show B₁.A × B₂.A from ((((g : (B₁.prod B₂).Aˣ)⁻¹ : (B₁.prod B₂).Aˣ) : (B₁.prod B₂).A) * (show (B₁.prod B₂).A from (w₁, w₂)))) ↔ _
    rw [IsIntegral.pair_iff]
    exact Iff.rfl

end GlobalTheory.RhoProd
