import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviFactorOfUnipotentDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV.NodeApply

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

theorem levi_eq_mul_cf (u u' : BlockIx (r + s) r → Ad E) (m m' : GA E r × GA E s) (k k' : Kinf E (r + s))
    (c c' : GL (Fin (r + s)) (Af E)) (hc : c ∈ KO E (r + s)) (hc' : c' ∈ KO E (r + s))
    (h : unip u * lev (Ad E) r s m * cf (r + s) k c = unip u' * lev (Ad E) r s m' * cf (r + s) k' c') :
    ∃ (k₁ : Kinf E r) (c₁ : GL (Fin r) (Af E)) (k₂ : Kinf E s) (c₂ : GL (Fin s) (Af E)),
      c₁ ∈ KO E r ∧ c₂ ∈ KO E s ∧ m' = (m.1 * cf r k₁ c₁, m.2 * cf s k₂ c₂) := by
  obtain ⟨v, hv⟩ := lev_mul_unip (m⁻¹) (-u + u')
  have hu : (unip u : GA E (r + s))⁻¹ = unip (-u) := by
    rw [inv_eq_iff_mul_eq_one, ← D.unip_add', add_neg_cancel, unip_zero]
  have key : unip v * lev (Ad E) r s (m⁻¹ * m') = cf (r + s) (k * k'⁻¹) (c * c'⁻¹) := by
    rw [← cf_mul, ← cf_inv, map_mul, ← mul_assoc, ← hv, D.unip_add', map_inv, ← hu]
    have h2 : unip u' * lev (Ad E) r s m' =
        unip u * lev (Ad E) r s m * cf (r + s) k c * (cf (r + s) k' c')⁻¹ := by
      rw [h]; group
    rw [mul_assoc (lev (Ad E) r s m)⁻¹, mul_assoc (unip u)⁻¹, h2]
    group
  obtain ⟨k₁, c₁, k₂, c₂, h₁, h₂, hm⟩ := GlobalTheory.T.levi_factor_of_unipotent_decomp v (m⁻¹ * m') _ _
    (mul_mem hc (inv_mem hc')) key
  refine ⟨k₁, c₁, k₂, c₂, h₁, h₂, ?_⟩
  calc m' = m * (m⁻¹ * m') := (mul_inv_cancel_left m m').symm
    _ = _ := by rw [hm]; rfl

theorem nodeFn_apply : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ), FlatFn e₁ → FlatFn e₂ → ∀ (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s)) (c : GL (Fin (r + s)) (Af E)), c ∈ KO E (r + s) → nodeFn e₁ e₂ (unip u * lev (Ad E) r s m * cf (r + s) k c) = e₁ m.1 * e₂ m.2 := by
  intro E _ _ _ r s e₁ e₂ f₁ f₂ u m k c hc
  obtain ⟨k', c', hc', hx'⟩ :=
    (exists_iw (unip u * lev (Ad E) r s m * cf (r + s) k c)).choose_spec.choose_spec
  obtain ⟨k₁, c₁, k₂, c₂, h₁, h₂, hm⟩ := levi_eq_mul_cf u _ m _ k k' c c' hc hc' hx'
  have hl : leviOf (unip u * lev (Ad E) r s m * cf (r + s) k c) =
      (m.1 * cf r k₁ c₁, m.2 * cf s k₂ c₂) := hm
  rw [nodeFn, hl, f₁.rinv _ _ _ h₁, f₂.rinv _ _ _ h₂]

end GlobalTheory.CompanionTheory.LimV.NodeApply

end
