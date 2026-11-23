import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitaryPrecedes

theorem not_precedes_of_unitary : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ Δ Δ' : Segment (w.adicCompletion E), (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).eig φ, ‖α‖ = 1) → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((rc Δ'.first).lpTw (((Δ'.len : ℝ) - 1) / 2)).eig φ, ‖α‖ = 1) → ¬ Δ.Precedes Δ' := by
  intro E Ω _ _ _ _ _ A w h rc hrc Δ Δ' hΔ hΔ' hP
  obtain ⟨a, ha, ε, -, H⟩ := hrc
  obtain ⟨hL, j, hj, hfirst⟩ := hP
  have hy' : rc Δ'.first = (rc Δ.first).lpTw (j : ℝ) := by
    rw [hfirst, ← H.nu_eq]
    norm_cast
  have hdeg : deg (frob h) = 1 := deg_frob
  have hcard : Multiset.card ((rc Δ.first).eig (frob h)) = Δ.d := by
    rw [WD.card_eig, H.dim]
    rfl
  obtain ⟨β, hβ⟩ := Multiset.card_pos_iff_exists_mem.1 (hcard ▸ Δ.d_pos)
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  set q : ℝ := ((normV w : ℕ) : ℝ) with hqdef
  have hn : ∀ s : ℝ, ‖((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)‖ = q ^ s := by
    intro s
    rw [← coe_qPow, norm_qPow]
  have h1 := hΔ (frob h) hdeg (β * ((normV w : ℕ) : ℂ) ^ (((((Δ.len : ℝ) - 1) / 2 : ℝ)) : ℂ))
    (by rw [GlobalTheory.RowTie.EigTwist.eig_lpTw _ hdeg]; exact Multiset.mem_map_of_mem _ hβ)
  have h2 := hΔ' (frob h) hdeg (β * ((normV w : ℕ) : ℂ) ^ (((j : ℕ) : ℝ) : ℂ) *
      ((normV w : ℕ) : ℂ) ^ (((((Δ'.len : ℝ) - 1) / 2 : ℝ)) : ℂ))
    (by
      rw [hy', GlobalTheory.RowTie.EigTwist.eig_lpTw _ hdeg, GlobalTheory.RowTie.EigTwist.eig_lpTw _ hdeg]
      exact Multiset.mem_map_of_mem _ (Multiset.mem_map_of_mem _ hβ))
  rw [norm_mul, hn] at h1
  rw [norm_mul, norm_mul, hn, hn] at h2
  have hb : ‖β‖ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have heq : q ^ (((Δ.len : ℝ) - 1) / 2) = q ^ (((j : ℕ) : ℝ) + (((Δ'.len : ℝ) - 1) / 2)) := by
    rw [Real.rpow_add (by linarith)]
    apply mul_left_cancel₀ hb
    rw [h1, ← mul_assoc, h2]
  have hexp : ((Δ.len : ℝ) - 1) / 2 = ((j : ℕ) : ℝ) + (((Δ'.len : ℝ) - 1) / 2) := by
    rcases lt_trichotomy (((Δ.len : ℝ) - 1) / 2) (((j : ℕ) : ℝ) + (((Δ'.len : ℝ) - 1) / 2)) with hlt | heq' | hgt
    · exact absurd heq (Real.rpow_lt_rpow_of_exponent_lt hq hlt).ne
    · exact heq'
    · exact absurd heq (Real.rpow_lt_rpow_of_exponent_lt hq hgt).ne'
  have hlen : Δ.len = Δ'.len + 2 * j := by
    have : (Δ.len : ℝ) = Δ'.len + 2 * j := by linarith
    exact_mod_cast this
  apply hL.2.2
  intro x hx
  rw [Segment.mem_carrier] at hx ⊢
  obtain ⟨b, hb', rfl⟩ := hx
  refine ⟨j + b, by omega, ?_⟩
  rw [hfirst, IrrGL.nu_nu]
  push_cast
  rfl

end GlobalTheory.UnitaryPrecedes
