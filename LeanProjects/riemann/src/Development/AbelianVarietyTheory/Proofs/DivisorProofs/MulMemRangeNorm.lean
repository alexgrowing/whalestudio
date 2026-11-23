import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportC
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp.NormIndex

open Neutral.B1

theorem mul_eq_one_of_card_two {G : Type} [Group G] [Finite G] (h : Nat.card G = 2) {a b : G}
    (ha : a ≠ 1) (hb : b ≠ 1) : a * b = 1 := by
  classical
  have hab : b = a := by
    by_contra hne
    haveI := Fintype.ofFinite G
    have : ({1, a, b} : Finset G).card ≤ Nat.card G := by
      rw [Nat.card_eq_fintype_card]; exact Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm ha, Ne.symm hb]),
      Finset.card_pair (Ne.symm hne), h] at this
    omega
  subst hab
  have := pow_card_eq_one' (G := G) (x := b)
  rw [h, pow_two] at this
  exact this

theorem mul_mem_range_norm (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (x y : Fˣ)
    (hx : x ∉ (Units.map (Algebra.norm F : E →* F)).range)
    (hy : y ∉ (Units.map (Algebra.norm F : E →* F)).range) :
    x * y ∈ (Units.map (Algebra.norm F : E →* F)).range := by
  obtain ⟨b, -, -⟩ := hE.basis
  have h2 : Module.finrank F E = 2 := by rw [Module.finrank_eq_card_basis b]; simp
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  haveI : IsGalois F E := Algebra.IsQuadraticExtension.isGalois F E
  let φ : E →ₐ[F] AlgebraicClosure F := IsAlgClosed.lift
  let L : IntermediateField F (AlgebraicClosure F) := φ.fieldRange
  let e : E ≃ₐ[F] L := AlgEquiv.ofInjectiveField φ
  haveI : FiniteDimensional F L := LinearEquiv.finiteDimensional e.toLinearEquiv
  haveI : IsGalois F L := IsGalois.of_algEquiv e
  have hL2 : Module.finrank F L = 2 := e.toLinearEquiv.finrank_eq.symm.trans h2
  have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by
    rw [← hL2, ← IsGalois.card_aut_eq_finrank]
  have hab : IsFiniteAbelian F L :=
    { finiteDimensional := inferInstance
      isGalois := inferInstance
      comm := fun a b' => by
        haveI : Fact (Nat.card (L ≃ₐ[F] L)).Prime := ⟨hcard ▸ Nat.prime_two⟩
        haveI := isCyclic_of_prime_card (α := L ≃ₐ[F] L) (p := Nat.card (L ≃ₐ[F] L)) rfl
        exact IsCyclic.commGroup.mul_comm a b' }
  obtain ⟨Art, hArt⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.artin_reciprocity_char_zero F
  obtain ⟨-, hker⟩ := hArt.2.2.2.2 L hab
  have hN : (Units.map (Algebra.norm F : E →* F)).range = normGroup F L := by
    ext z
    simp only [normGroup, MonoidHom.mem_range]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨Units.map (e : E →* L) w, Units.ext (Algebra.norm_eq_of_algEquiv e (w : E))⟩
    · rintro ⟨w, rfl⟩
      exact ⟨Units.map (e.symm : L →* E) w, Units.ext (Algebra.norm_eq_of_algEquiv e.symm (w : L))⟩
  rw [hN, ← hker] at hx hy ⊢
  rw [MonoidHom.mem_ker] at hx hy ⊢
  rw [map_mul]
  haveI : Finite (L ≃ₐ[F] L) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact mul_eq_one_of_card_two hcard hx hy

end GlobalTheory.KSp.NormIndex
