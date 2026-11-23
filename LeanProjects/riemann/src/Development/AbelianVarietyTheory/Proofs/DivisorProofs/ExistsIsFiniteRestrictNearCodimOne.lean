import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightEqOneIffClosureDimProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoheightOneNotMemOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FiniteNearCodimOne

theorem le_one_of_add_eq {c : ℕ∞} {s t : WithBot ℕ∞} {D : ℕ} (h₁ : (c : WithBot ℕ∞) + s = D)
    (h₂ : ((1 : ℕ∞) : WithBot ℕ∞) + t = D) (hts : t ≤ s) : c ≤ 1 := by
  induction t using WithBot.recBotCoe with
  | bot => rw [WithBot.add_bot] at h₂; exact absurd h₂.symm (WithBot.natCast_ne_bot _)
  | coe t =>
    have h₃ : (c : WithBot ℕ∞) + t ≤ ((1 : ℕ∞) : WithBot ℕ∞) + t :=
      (add_le_add le_rfl hts).trans (h₁.trans h₂.symm).le
    have h₄ : 1 + t = (D : ℕ∞) := by exact_mod_cast h₂
    have ht : t ≠ ⊤ := by rintro rfl; rw [add_top] at h₄; exact ENat.natCast_ne_top _ h₄.symm
    have h₅ : c + t ≤ 1 + t := by exact_mod_cast h₃
    exact (ENat.add_le_add_iff_right ht).1 h₅

theorem coheight_eq_zero_iff {X : Scheme.{0}} [IsIntegral X] (x : X) :
    Order.coheight x = 0 ↔ x = genericPoint X := by
  rw [Order.coheight_eq_zero]
  constructor
  · intro h
    have h' : x ⤳ genericPoint X := h (show x ≤ genericPoint X from genericPoint_specializes x)
    exact (h'.antisymm (genericPoint_specializes x)).eq
  · rintro rfl b _
    exact genericPoint_specializes b

theorem exists_isFinite_restrict_of_coheight_eq_one : ∀ (F : Type) [Field F] (X Y : Scheme.{0})
    [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (D : ℕ), IsProjOver p →
    topologicalKrullDim X = (D : ℕ) → IsProjOver q → topologicalKrullDim Y = D →
    ∀ π : Y ⟶ X, π ≫ p = q → π (genericPoint Y) = genericPoint X → ∀ z : X,
    Order.coheight z = 1 → ∃ U : X.Opens, z ∈ U ∧ IsFinite (π ∣_ U) := by
  intro F _ X Y _ _ p q D hp hX hq hY π hπ hη z hz
  have : IsProper p := by
    obtain ⟨N, c, hc, rfl⟩ := hp
    have := isProper_str F N
    infer_instance
  have : IsProper q := by
    obtain ⟨N, c, hc, rfl⟩ := hq
    have := isProper_str F N
    infer_instance
  have : IsProper (π ≫ p) := by rw [hπ]; infer_instance
  have : IsProper π := IsProper.of_comp π p
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian Y := {}
  have hzne : z ≠ genericPoint X := fun h => by
    rw [(coheight_eq_zero_iff z).2 h] at hz
    exact zero_ne_one hz
  have hw : ∀ w : Y, π w = z → Order.coheight w = 1 := by
    intro w hwz
    have h₁ := (FieldDimCoheight.coheight_add_dim_closure_eq F Y q w).trans hY
    have h₂ := (FieldDimCoheight.coheight_add_dim_closure_eq F X p z).trans hX
    rw [hz] at h₂
    have h₃ := PosBaseChange.dim_image_le π.isClosedMap (isClosed_closure (s := ({w} : Set Y)))
    rw [← π.isClosedMap.closure_image_eq_of_continuous π.continuous, Set.image_singleton, hwz] at h₃
    refine le_antisymm (le_one_of_add_eq h₁ h₂ h₃) (Order.one_le_iff_ne_zero.2 fun h0 => ?_)
    rw [(coheight_eq_zero_iff w).1 h0] at hwz
    exact hzne (hwz.symm.trans hη)
  have hfin : (π ⁻¹' {z}).Finite := by
    let U : Y.Opens := π ⁻¹ᵁ ⟨(closure ({z} : Set X))ᶜ, isClosed_closure.isOpen_compl⟩
    have hU : genericPoint Y ∈ U := by
      show π (genericPoint Y) ∈ (closure ({z} : Set X))ᶜ
      rw [hη]
      intro hc
      exact hzne ((specializes_iff_mem_closure.2 hc).antisymm (genericPoint_specializes z)).eq
    refine (Mix.finite_coheight_one_notMem_open Y U hU).subset fun w hwz => ⟨hw w hwz, fun hwU => ?_⟩
    have hwU' : π w ∈ (closure ({z} : Set X))ᶜ := hwU
    exact hwU' (by rw [show π w = z from hwz]; exact subset_closure rfl)
  exact exists_isFinite_morphismRestrict_of_finite_preimage_singleton π z hfin

end GlobalTheory.FiniteNearCodimOne
