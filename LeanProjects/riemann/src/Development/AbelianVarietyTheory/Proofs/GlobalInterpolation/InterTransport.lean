import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.ThetaMove.Transport

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem opU_comp (e : V ≃ₗ[ℂ] V') {H : Sesq V} {H' : Sesq V'} (hH : ∀ x y, H' (e x) (e y) = H x y)
    (F : V' → ℂ) (x z : V) : opU H x (fun w => F (e w)) z = opU H' (e x) F (e z) := by
  simp only [opU, hH, map_add]

def subEquiv (e : V ≃ₗ[ℂ] V') {Λ : AddSubgroup V} {Λ' : AddSubgroup V'} (h : ∀ x, x ∈ Λ ↔ e x ∈ Λ') : Λ ≃+ Λ' where
  toFun x := ⟨e x, (h _).1 x.2⟩
  invFun y := ⟨e.symm y, (h _).2 (by simp)⟩
  left_inv x := by simp
  right_inv y := by simp
  map_add' x y := by simp

def quotEquiv (e : V ≃ₗ[ℂ] V') {Λ₁ Λ₂ : AddSubgroup V} {Λ₁' Λ₂' : AddSubgroup V'} (h₁ : ∀ x, x ∈ Λ₁ ↔ e x ∈ Λ₁')
    (h₂ : ∀ x, x ∈ Λ₂ ↔ e x ∈ Λ₂') : (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) ≃+ (Λ₂' ⧸ Λ₁'.addSubgroupOf Λ₂') :=
  QuotientAddGroup.congr _ _ (subEquiv e h₂) (by
    ext y
    obtain ⟨x, rfl⟩ := (subEquiv e h₂).surjective y
    exact (AddSubgroup.mem_map_iff_mem (f := (subEquiv e h₂ : Λ₂ →+ Λ₂')) (subEquiv e h₂).injective).trans (h₁ _))

theorem term_add {H : Sesq V} {α : V → ℂ} (hH : IsHerm H) {A₁ A₂ : AddSubgroup V} (hd : IsSelfDual H A₂)
    (hs : IsSemiChar H A₂ α) {F : V → ℂ} (hF : F ∈ fixedBy H α A₁) {a s : V} (ha : a ∈ A₂) (hs₂ : s ∈ A₂)
    (hs₁ : s ∈ A₁) (z : V) : α (a + s) * opU H (a + s) F z = α a * opU H a F z := by
  rw [GlobalTheory.ThetaInter.alpha_opU_add hH hd hs ha hs₂, ← GlobalTheory.ThetaInter.opU_mul]
  congr 2
  funext w
  exact hF s hs₁ w

theorem inter_transport : ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (e : V ≃ₗ[ℂ] V') (H : Sesq V) (H' : Sesq V') (α : V → ℂ) (α' : V' → ℂ) (Λ₁ Λ₂ : AddSubgroup V) (Λ₁' Λ₂' : AddSubgroup V') (θ' : V' → ℂ), (∀ x y, H' (e x) (e y) = H x y) → (∀ x, x ∈ Λ₁ ↔ e x ∈ Λ₁') → (∀ x, x ∈ Λ₂ ↔ e x ∈ Λ₂') → (∀ x ∈ Λ₂, α x = α' (e x)) → IsHerm H' → IsSelfDual H' Λ₂' → IsSemiChar H' Λ₂' α' → (IsSelfDual H Λ₂ ∧ IsSemiChar H Λ₂ α ∧ ∀ F' ∈ fixedBy H' α' Λ₂', (fun z => F' (e z)) ∈ fixedBy H α Λ₂) ∧ (θ' ∈ fixedBy H' α' Λ₁' → relIdx Λ₁' Λ₂' ≠ 0 → inter H α Λ₁ Λ₂ (fun z => θ' (e z)) = fun z => inter H' α' Λ₁' Λ₂' θ' (e z)) := by
  intro V V' _ _ _ _ e H H' α α' Λ₁ Λ₂ Λ₁' Λ₂' θ' hH h₁ h₂ hα hh hd hs
  have hE : ∀ x y, altE H x y = altE H' (e x) (e y) := fun x y => by simp only [altE, hH]
  refine ⟨⟨?_, ⟨fun x hx => ?_, fun x hx y hy => ?_⟩, fun F hF x hx z => ?_⟩, fun hθ _ => ?_⟩
  · ext x
    rw [h₂ x]
    conv_rhs => rw [← hd]
    constructor
    · intro h y hy
      obtain ⟨y, rfl⟩ := e.surjective y
      rw [← hE]
      exact h y ((h₂ y).2 hy)
    · intro h y hy
      rw [hE]
      exact h _ ((h₂ y).1 hy)
  · rw [hα x hx]; exact hs.1 _ ((h₂ x).1 hx)
  · rw [hα _ (Λ₂.add_mem hx hy), hα x hx, hα y hy, map_add, hE]
    exact hs.2 _ ((h₂ x).1 hx) _ ((h₂ y).1 hy)
  · rw [opU_comp e hH, hα x hx]
    exact hF _ ((h₂ x).1 hx) _
  · funext z
    have hc : relIdx Λ₁ Λ₂ = relIdx Λ₁' Λ₂' := Nat.card_congr (quotEquiv e h₁ h₂).toEquiv
    rw [inter, inter, hc, ← finsum_comp_equiv (quotEquiv e h₁ h₂).toEquiv]
    congr 1
    refine finsum_congr fun c => ?_
    rw [opU_comp e hH, hα _ (Quotient.out c).2]
    have hm : -(subEquiv e h₂ (Quotient.out c)) + Quotient.out ((quotEquiv e h₁ h₂).toEquiv c) ∈
        Λ₁'.addSubgroupOf Λ₂' := by
      rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
      conv_rhs => rw [← QuotientAddGroup.out_eq' c]
      rfl
    have := term_add hh hd hs hθ (subEquiv e h₂ (Quotient.out c)).2
      (-(subEquiv e h₂ (Quotient.out c)) + Quotient.out ((quotEquiv e h₁ h₂).toEquiv c)).2
      (AddSubgroup.mem_addSubgroupOf.1 hm) (e z)
    rw [← AddSubgroup.coe_add, add_neg_cancel_left] at this
    exact this.symm

end GlobalTheory.ThetaMove.Transport
