import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocHypSplit

theorem finite_of_subset_mul {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (T K' : Subgroup G)
    (hK' : IsOpen (K' : Set G)) (D : Set G) (hD : IsCompact D)
    (P : G → Prop) (hP : ∀ x, P x → ∃ t ∈ T, ∃ d ∈ D, x = t * d) :
    {q : DoubleCoset.Quotient (T : Set G) (K' : Set G) | P (Quotient.out q)}.Finite := by
  obtain ⟨s, hs⟩ := compact_covered_by_mul_left_translates hD
    (show (interior (K' : Set G)).Nonempty from ⟨1, hK'.interior_eq.symm ▸ K'.one_mem⟩)
  refine (s.finite_toSet.image fun g => DoubleCoset.mk T K' g⁻¹).subset ?_
  intro q hq
  obtain ⟨t, ht, d, hd, hx⟩ := hP _ hq
  have := hs hd
  simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at this
  obtain ⟨g, hg, hgd⟩ := this
  refine ⟨g, hg, ?_⟩
  rw [← DoubleCoset.out_eq' T K' q, DoubleCoset.eq]
  exact ⟨t, ht, g * d, hgd, by simp [hx, mul_assoc]⟩

open scoped Pointwise in

theorem finite_doubleCosets_split : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (σ : H →* H) (K : Subgroup H) (d d' : H) (f : H × H → ℂ)
  (C₁ C₂ : Set H), Continuous σ → (∀ g, σ (σ g) = g) → IsOpen (K : Set H) → IsCompact (K : Set H) → (∀ k ∈ K, σ k ∈ K) →
  IsCompact C₁ → IsCompact C₂ → (∀ y, f y ≠ 0 → y.1 ∈ C₁ ∧ y.2 ∈ C₂) →
  (∀ C : Set H, IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) (d * σ d') : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * (d * σ d') * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
  {q : DoubleCoset.Quotient (twCent (swTw σ) (d, d') : Set (H × H)) (K.prod K : Set (H × H)) |
    ∃ k ∈ K.prod K, f ((Quotient.out q * k)⁻¹ * (d, d') * swTw σ (Quotient.out q * k)) ≠ 0}.Finite := by
  intro H _ _ _ σ K d d' f C₁ C₂ hσc hσ hKo hKc _ hC₁ hC₂ hf hfin
  have hC : IsCompact (C₁ * σ '' C₂) := hC₁.mul (hC₂.image hσc)
  have hSf := hfin _ hC
  set S := {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) (d * σ d') : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * (d * σ d') * MonoidHom.id H (Quotient.out q * k) ∈ C₁ * σ '' C₂} with hS
  have hR : IsCompact ((fun q => Quotient.out q) '' S : Set H) := (hSf.image _).isCompact
  set A : Set H := ((fun q => Quotient.out q) '' S : Set H) * (K : Set H) with hAdef
  have hA : IsCompact A := hR.mul hKc
  set B : Set H := σ '' ((fun a => d⁻¹ * a) '' A * C₁) with hBdef
  have hB : IsCompact B := ((hA.image (continuous_const.mul continuous_id)).mul hC₁).image hσc
  have hKKo : IsOpen ((K.prod K : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_prod]; exact hKo.prod hKo
  have hKKc : IsCompact ((K.prod K : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_prod]; exact hKc.prod hKc
  have hD : IsCompact ((fun p : (H × H) × (H × H) => p.1 * p.2⁻¹) ''
      ((A ×ˢ B) ×ˢ ((K.prod K : Subgroup (H × H)) : Set (H × H)))) :=
    ((hA.prod hB).prod hKKc).image (continuous_fst.mul continuous_snd.inv)
  have key : ∀ y₁ y₂ : H, y₁⁻¹ * d * σ y₂ ∈ C₁ → y₂⁻¹ * d' * σ y₁ ∈ C₂ →
      ∃ t ∈ twCent (swTw σ) (d, d'), ∃ a ∈ A, ∃ b ∈ B, ((y₁, y₂) : H × H) = t * (a, b) := by
    intro y₁ y₂ h₁ h₂
    have hN : y₁⁻¹ * (d * σ d') * y₁ ∈ C₁ * σ '' C₂ := by
      refine Set.mem_mul.2 ⟨_, h₁, _, ⟨_, h₂, rfl⟩, ?_⟩
      simp only [map_mul, map_inv, hσ]
      group
    obtain ⟨h, k, hh, hk, e⟩ := DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id H) (d * σ d')) K y₁
    have ez : Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id H) (d * σ d')) K y₁) * k⁻¹ = h * y₁ := by
      rw [e, mul_inv_cancel_right]
    have hh' : h * (d * σ d') = d * σ d' * h := hh
    have hq : DoubleCoset.mk (twCent (MonoidHom.id H) (d * σ d')) K y₁ ∈ S := by
      refine ⟨k⁻¹, inv_mem hk, ?_⟩
      rw [ez, MonoidHom.id_apply]
      have : (h * y₁)⁻¹ * (d * σ d') * (h * y₁) = y₁⁻¹ * (d * σ d') * y₁ := by
        rw [_root_.mul_inv_rev, mul_assoc, ← mul_assoc (d * σ d') h y₁, ← hh']
        group
      rw [this]; exact hN
    have hw : h * y₁ ∈ A := by
      rw [← ez]
      exact Set.mem_mul.2 ⟨_, ⟨_, hq, rfl⟩, _, inv_mem hk, rfl⟩
    have ht := (mem_twCent_swTw σ hσ d d' (h⁻¹, d' * σ h⁻¹ * d'⁻¹)).2 ⟨inv_mem hh, rfl⟩
    set t₂ := d' * σ h⁻¹ * d'⁻¹ with ht₂
    have e₁ : h⁻¹ * d = d * σ t₂ := congrArg Prod.fst ht
    have e₂ : d⁻¹ * h * d = (σ t₂)⁻¹ := by
      have : σ t₂ = d⁻¹ * (h⁻¹ * d) := by rw [e₁]; group
      rw [this]; group
    refine ⟨(h⁻¹, t₂), ht, h * y₁, hw, t₂⁻¹ * y₂,
      ⟨(d⁻¹ * (h * y₁)) * (y₁⁻¹ * d * σ y₂), Set.mem_mul.2 ⟨_, ⟨_, hw, rfl⟩, _, h₁, rfl⟩, ?_⟩, ?_⟩
    · have : d⁻¹ * (h * y₁) * (y₁⁻¹ * d * σ y₂) = (d⁻¹ * h * d) * σ y₂ := by group
      rw [this, e₂, map_mul, map_inv, hσ, hσ]
    · ext <;> simp
  refine finite_of_subset_mul (twCent (swTw σ) (d, d')) (K.prod K) hKKo _ hD
    (fun x => ∃ k ∈ K.prod K, f ((x * k)⁻¹ * (d, d') * swTw σ (x * k)) ≠ 0) ?_
  rintro x ⟨k, hk, hx⟩
  obtain ⟨t, ht, a, ha, b, hb, e⟩ := key (x * k).1 (x * k).2 (hf _ hx).1 (hf _ hx).2
  have e' : x * k = t * (a, b) := e
  refine ⟨t, ht, (a, b) * k⁻¹, ⟨(((a, b)), k), ⟨⟨ha, hb⟩, hk⟩, rfl⟩, ?_⟩
  rw [← mul_assoc, ← e', mul_inv_cancel_right]

end GlobalTheory.CompanionTheory.LocHypSplit

end
