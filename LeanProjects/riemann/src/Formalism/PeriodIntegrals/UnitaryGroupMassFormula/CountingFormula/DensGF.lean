import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensAtGoodOf

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S IsDedekindDomain
open Classical ValuativeRel

def piO {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E) (ϖ : 𝒪[F]) : L.O :=
  ⟨algebraMap F E ϖ, (L.O_def _).2 (by
    rw [show algebraMap F E (ϖ : F) = algebraMap 𝒪[F] E ϖ from
      (IsScalarTower.algebraMap_apply 𝒪[F] F E ϖ).symm]
    exact isIntegral_algebraMap)⟩

def FLocO : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E), IsNonarchimedeanLocalField F → CharZero F →
    (∀ x : E, x ≠ 0 → IsUnit x) → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      (∀ x ∈ L.O, (¬ ∃ z ∈ L.O, x = algebraMap F E ϖ * z) → ∃ y ∈ L.O, x * y = 1) ∧
      (∀ x : E, ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ L.O) ∧
      (∀ x ∈ L.O, x ≠ 0 → ∃ k : ℕ, ∃ u ∈ L.O, (∃ w ∈ L.O, u * w = 1) ∧ x = algebraMap F E ϖ ^ k * u)

def FResField : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E), IsNonarchimedeanLocalField F → CharZero F →
    (∀ x : E, x ≠ 0 → IsUnit x) → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      (Ideal.span {piO L ϖ}).IsMaximal ∧
      Nat.card (L.O ⧸ Ideal.span {piO L ϖ}) = Nat.card 𝓀[F] ^ 2 ∧
      ∀ x y : L.O, (y : E) = L.cj x →
        Ideal.Quotient.mk (Ideal.span {piO L ϖ}) y =
          Ideal.Quotient.mk (Ideal.span {piO L ϖ}) x ^ Nat.card 𝓀[F]

def FLatBasis : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E), IsNonarchimedeanLocalField F →
    CharZero F → (∀ x : E, x ≠ 0 → IsUnit x) →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ →
      ∃ b : Fin (Module.finrank E V) → V, (∀ k, b k ∈ Λ) ∧ LinearIndependent E b ∧
        (∀ x ∈ Λ, ∃ c : Fin (Module.finrank E V) → E, (∀ k, c k ∈ M.L.O) ∧ x = ∑ k, c k • b k) ∧
        ∃ Q : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) E, (∀ k l, Q k l ∈ M.L.O) ∧
          Q * Matrix.of (fun k l => H.h (b k) (b l)) = 1

def FCount : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E), IsNonarchimedeanLocalField F →
    CharZero F → ∀ ϖ : 𝒪[F], Irreducible ϖ →
    (∀ x ∈ M.L.O, (¬ ∃ z ∈ M.L.O, x = algebraMap F E ϖ * z) → ∃ y ∈ M.L.O, x * y = 1) →
    (∀ x : E, ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ M.L.O) →
    (∀ x ∈ M.L.O, x ≠ 0 → ∃ k : ℕ, ∃ u ∈ M.L.O, (∃ w ∈ M.L.O, u * w = 1) ∧ x = algebraMap F E ϖ ^ k * u) →
    ∀ (k : Type) [Field k] [Fintype k] (r : M.L.O →+* k), Function.Surjective r →
      (∀ x : M.L.O, r x = 0 ↔ ∃ z ∈ M.L.O, (x : E) = algebraMap F E ϖ * z) →
      Fintype.card k = Nat.card 𝓀[F] ^ 2 →
      (∀ x y : M.L.O, (y : E) = M.L.cj x → r y = r x ^ Nat.card 𝓀[F]) →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ →
      ∀ b : Fin (Module.finrank E V) → V, (∀ k, b k ∈ Λ) → LinearIndependent E b →
        (∀ x ∈ Λ, ∃ c : Fin (Module.finrank E V) → E, (∀ k, c k ∈ M.L.O) ∧ x = ∑ k, c k • b k) →
        ∀ Q : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) E, (∀ k l, Q k l ∈ M.L.O) →
          Q * Matrix.of (fun k l => H.h (b k) (b l)) = 1 →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G₀ : Matrix ι ι E), (∀ a b, G₀ a b ∈ M.L.O) →
        (∀ a b, G₀ b a = M.L.cj (G₀ a b)) → (∃ y ∈ M.L.O, G₀.det * y = 1) →
        Fintype.card ι ≤ Module.finrank E V →
          H.dens ϖ Λ G₀ = Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[F]) (-1)
            (Module.finrank E V) (Fintype.card ι) 0

theorem locDensField_of (h1 : FLocO) (h2 : FResField) (h3 : FLatBasis) (h4 : FCount) :
    LocDensField := by
  intro F E _ _ _ _ _ _ _ M hF hC hU V _ _ H Λ hSD ϖ hϖ ι _ _ G₀ hG1 hG2 hG3 hcard
  obtain ⟨a1, a2, a3⟩ := h1 F E M.L hF hC hU ϖ hϖ
  obtain ⟨hmax, hcardk, hfrob⟩ := h2 F E M.L hF hC hU ϖ hϖ
  obtain ⟨b, hbΛ, hbli, hbspan, Q, hQ, hQb⟩ := h3 F E M hF hC hU V H Λ hSD
  have := hF
  have := hmax

  let _ : Field (M.L.O ⧸ Ideal.span {piO M.L ϖ}) := Ideal.Quotient.field _
  have hfin : Finite (M.L.O ⧸ Ideal.span {piO M.L ϖ}) := by
    have hpos : 0 < Nat.card (M.L.O ⧸ Ideal.span {piO M.L ϖ}) := by
      rw [hcardk]
      exact pow_pos Nat.card_pos 2
    exact (Nat.card_pos_iff.mp hpos).2
  let _ : Fintype (M.L.O ⧸ Ideal.span {piO M.L ϖ}) := Fintype.ofFinite _
  refine h4 F E M hF hC ϖ hϖ a1 a2 a3 (M.L.O ⧸ Ideal.span {piO M.L ϖ}) (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective ?_ ?_ ?_ V H Λ hSD b hbΛ hbli hbspan Q hQ hQb ι G₀ hG1 hG2 hG3 hcard
  · intro x
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, by simp [piO, mul_comm]⟩
    · rintro ⟨z, hz, hx⟩
      refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
      simp [piO, hx, mul_comm]
  · rw [Fintype.card_eq_nat_card, hcardk]
  · intro x y hxy
    exact hfrob x y hxy

end PI.UnitaryGroupMassFormula.CntFormula
