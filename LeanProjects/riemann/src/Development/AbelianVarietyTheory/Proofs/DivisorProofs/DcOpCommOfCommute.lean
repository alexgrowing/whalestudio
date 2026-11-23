import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsDCOfMemDoubleCoset
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiInvolutionOfChars
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalFamilyOrthogonalDecomposition

noncomputable section

open Formalism.IndefR.Bridge Formalism.L2.Col

namespace GlobalTheory.HeckeParts

section Grp

variable {G : Type} [Group G] {J Q L : Subgroup G}

def Splits (Q J L : Subgroup G) : Prop :=
  ∀ κ ∈ Q, ∃ k₁ ∈ J, ∃ k₂, k₁ ∈ L ∧ κ = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l

def RInv (J : Subgroup G) (F : G → ℂ) : Prop := ∀ k ∈ J, ∀ h, F (h * k) = F h

theorem Splits.self (h : Splits Q J L) (hJ : J ≤ Q) :
    ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l := by
  intro k hk
  obtain ⟨k₁, h₁, k₂, hL, e, hc⟩ := h k (hJ hk)
  refine ⟨k₁, h₁, k₂, ?_, hL, e, hc⟩
  have : k₂ = k₁⁻¹ * k := by rw [e]; group
  rw [this]
  exact J.mul_mem (J.inv_mem h₁) hk

theorem RInv.one {F : G → ℂ} (h : RInv J F) (k : J) (g : G) : F (g * k) = (((1 : J →* ℂˣ) k : ℂˣ) : ℂ) • F g := by
  simp [h k k.2 g]

theorem isDC_of_splits (hs : Splits Q J L) (hJ : J ≤ Q) {x : G} (hx : x ∈ L) {A : Finset G} (hA : ∀ a ∈ A, a ∈ L)
    {K : Set G} (hK : ∀ g, g ∈ K ↔ g ∈ J ∧ g ∈ L) (h1 : ∀ γ ∈ A, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * x * k₂)
    (h2 : ∀ y, (∃ k₁ ∈ K, ∃ k₂ ∈ K, y = k₁ * x * k₂) → ∃! γ, γ ∈ A ∧ γ⁻¹ * y ∈ K) : IsDC J x A := by
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨k₁, h₁, k₂, h₂, e⟩ := h1 a ha
    exact ⟨⟨k₁, ((hK _).1 h₁).1⟩, ⟨k₂, ((hK _).1 h₂).1⟩, e⟩
  · rintro g ⟨k, k', rfl⟩
    obtain ⟨k₁, h₁, k₂, h₂, hL, e, hc⟩ := hs.self hJ k k.2
    have key : ∀ a : G, a⁻¹ * ((k : G) * x * k') = a⁻¹ * (k₁ * x * 1) * (k₂ * k') := by
      intro a
      rw [e, mul_assoc k₁ k₂ x, (hc x hx).eq]; group
    have hm : k₂ * (k' : G) ∈ J := J.mul_mem h₂ k'.2
    refine (existsUnique_congr fun a => and_congr_right fun ha => ?_).1
      (h2 _ ⟨k₁, (hK _).2 ⟨h₁, hL⟩, 1, (hK _).2 ⟨J.one_mem, L.one_mem⟩, rfl⟩)
    rw [key, J.mul_mem_cancel_right hm, hK]
    exact and_iff_left (L.mul_mem (L.inv_mem (hA a ha)) (L.mul_mem (L.mul_mem hL hx) L.one_mem))

theorem dcOp_eq_rInv {x x' : G} {A A' : Finset G} (hA : IsDC J x A) (hA' : IsDC J x' A')
    (hx : ∃ k₁ k₂ : J, x' = (k₁ : G) * x * k₂) {F : G → ℂ} (hF : RInv J F) :
    dcOp A F = dcOp A' F ∧ RInv J (dcOp A F) := by
  have := GlobalTheory.HkB.dcOp_eq_and_level J ⊤ 1 x x' A A' F
    (fun k hk => ⟨k, hk, 1, J.one_mem, trivial, (mul_one k).symm, fun l _ => Commute.one_left l⟩)
    (fun _ _ => rfl) (fun _ _ => trivial) (fun _ _ => trivial) hA hA' hx hF.one
  exact ⟨this.1, fun k hk h => by simpa using this.2 ⟨k, hk⟩ h⟩

theorem dcOp_rInv {x : G} {A : Finset G} (hA : IsDC J x A) {F : G → ℂ} (hF : RInv J F) : RInv J (dcOp A F) :=
  (dcOp_eq_rInv hA hA ⟨1, 1, by simp⟩ hF).2

theorem dcOp_translate (hs : Splits Q J L) {x : G} {A : Finset G} (hA : IsDC J x A) (hL : ∀ a ∈ A, a ∈ L)
    {F : G → ℂ} (hF : RInv J F) {κ : G} (hκ : κ ∈ Q) (h : G) :
    dcOp A F (h * κ) = dcOp A (fun g => F (g * κ)) h := by
  obtain ⟨k₁, h₁, k₂, hl, rfl, hc⟩ := hs κ hκ
  rw [← (hc k₁ hl).eq, ← mul_assoc, dcOp_rInv hA hF k₁ h₁]
  refine Finset.sum_congr rfl fun a ha => ?_
  show F (h * k₂ * a) = F (h * a * (k₂ * k₁))
  rw [← mul_assoc, hF k₁ h₁, mul_assoc, (hc a (hL a ha)).eq, mul_assoc]

theorem dcOp_comm_of_commute {A B : Finset G} (h : ∀ a ∈ A, ∀ b ∈ B, Commute a b) (F : G → ℂ) :
    dcOp A (dcOp B F) = dcOp B (dcOp A F) := by
  funext g
  simp only [dcOp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun a ha => ?_
  rw [mul_assoc, (h a ha b hb).eq, mul_assoc]

end Grp

section Normal

variable {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem exists_lift {X : Type} [AddCommGroup X] [Module ℂ X] {e : E →ₗ[ℂ] X} (he : Function.Injective e)
    (T : X →ₗ[ℂ] X) (hT : ∀ x, T (e x) ∈ LinearMap.range e) : ∃ t : Module.End ℂ E, ∀ x, e (t x) = T (e x) := by
  choose f hf using hT
  exact ⟨⟨⟨f, fun x y => he (by rw [map_add, hf, hf, hf, map_add, map_add])⟩,
    fun a x => he (by rw [RingHom.id_apply, map_smul, hf, hf, map_smul, map_smul])⟩, hf⟩

end Normal

end GlobalTheory.HeckeParts

end
