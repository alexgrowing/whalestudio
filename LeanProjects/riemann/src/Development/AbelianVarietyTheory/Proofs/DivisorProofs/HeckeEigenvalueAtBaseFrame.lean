import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueInvEqStar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralHeckeElementExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteCountableGQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.HeckeUnitary

theorem isDC_central {G : Type} [Group G] (J : Subgroup G) {z : G} (hz : ∀ g, Commute z g) :
    Bridge.IsDC J z {z} := by
  refine ⟨fun a ha => ⟨1, 1, by simpa using ha⟩, ?_⟩
  rintro g ⟨k₁, k₂, rfl⟩
  refine ⟨z, ⟨Finset.mem_singleton_self z, ?_⟩, fun y hy => Finset.mem_singleton.1 hy.1⟩
  rw [← (hz k₁).eq, mul_assoc, inv_mul_cancel_left]
  exact J.mul_mem k₁.2 k₂.2

theorem isDC_mul_central {G : Type} [Group G] [DecidableEq G] (J : Subgroup G) {z α : G} (hz : ∀ g, Commute z g)
    {R : Finset G} (h : Bridge.IsDC J α R) : Bridge.IsDC J (α * z) (R.image (· * z)) := by
  have e : ∀ k₁ k₂ : G, k₁ * (α * z) * k₂ = k₁ * α * k₂ * z := fun k₁ k₂ => by
    simp only [mul_assoc, (hz k₂).eq]
  have e' : ∀ a g : G, (a * z)⁻¹ * (g * z) = a⁻¹ * g := fun a g => by
    rw [mul_inv_rev, mul_assoc, ← mul_assoc a⁻¹, ← (hz (a⁻¹ * g)).eq, inv_mul_cancel_left]
  constructor
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨k₁, k₂, rfl⟩ := h.1 b hb
    exact ⟨k₁, k₂, (e _ _).symm⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    obtain ⟨a, ⟨ha, ha'⟩, hu⟩ := h.2 _ ⟨k₁, k₂, rfl⟩
    rw [e]
    refine ⟨a * z, ⟨Finset.mem_image_of_mem _ ha, by rwa [e']⟩, ?_⟩
    rintro y ⟨hy, hy'⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
    rw [e'] at hy'
    rw [hu b ⟨hb, hy'⟩]

theorem star_eigenvalue_mul : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank) (PP : Pl D.host.E) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (c : ℕ → ℂ) (T : MMap M), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → IsBaseFrame V β Λ N → ((N : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → (∀ P', P' ∈ L.Pg ∨ P' ∈ L.Q → P' ≠ PP ∧ ¬ IsConjPl P' PP) → Bridge.SplitOff PP ∅ → T ∈ Mult θ M (levG V β L : Set (GA D V)) (fun _ => 1) → ipM M μ 𝓕 T T ≠ 0 → (∀ k ≤ V.rank, ∀ α R, IsHeckeAt V PP k α → Bridge.IsDC (levG V β L) α⁻¹ R → heckeOn M R T = c k • T) → c V.rank ≠ 0 ∧ ∀ k ≤ V.rank, star (c k) * c V.rank = c (V.rank - k) := by
  intro D V S θ M β Λ N L PP μ 𝓕 c T hμ h𝓕 hβ hN hL hsp hT hip hc
  classical
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : SecondCountableTopology (GA D V) := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).2.1
  have : Countable (GQ V) := (GlobalTheory.RationalCountable.discrete_countable_GQ D V).2
  have : μ.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ
  have hT' := (GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ T).1 hT
  have hex : ∃ a, IsMultIP M μ 𝓕 T T a := by
    by_contra hne
    exact hip (by unfold ipM; rw [dif_neg hne])
  have hIP := ipM_spec M μ 𝓕 T T hex
  choose v hv hv0 using fun τ => (Submodule.ne_bot_iff _).1 (GlobalTheory.GardingVec.sm_ne_bot D V S M τ)
  let w : M.Vec := fun τ => ⟨v τ, hv τ⟩
  obtain ⟨hint, hval⟩ := hIP w w
  have hne : ∫ g in 𝓕, star (T w g) * T w g ∂μ ≠ 0 := by
    rw [hval]
    exact mul_ne_zero hip (Finset.prod_ne_zero_iff.2 fun τ _ => inner_self_ne_zero.2 (hv0 τ))
  obtain ⟨g₀, hg₀⟩ : ∃ g, T w g ≠ 0 := by
    by_contra h0
    push Not at h0
    exact hne (by simp [h0])
  have hc' : ∀ k ≤ V.rank, ∀ α R, IsHeckeAt V PP k α → Bridge.IsDC (levG V β L) α⁻¹ R →
      ∀ g, ∑ γ ∈ R, T w (g * γ) = c k * T w g := fun k hk α R h1 h2 g =>
    congrArg (fun T' : MMap M => T' w g) (hc k hk α R h1 h2)
  obtain ⟨z, hz, hzn, hk⟩ := GlobalTheory.T.central_hecke_element_exists V β Λ N L PP hβ hN hL hsp
  have hz' : ∀ g, Commute z⁻¹ g := fun g => (hz g).inv_left
  have hcen : ∀ g, T w (g * z⁻¹) = c V.rank * T w g := fun g => by
    simpa using hc' V.rank le_rfl z {z⁻¹} hzn (isDC_central _ hz') g
  have hn : c V.rank ≠ 0 := fun h0 => hg₀ (by simpa [h0] using hcen (g₀ * z))
  refine ⟨hn, fun k hkn => ?_⟩
  obtain ⟨α, R, R', h1, h2, h3, h4, h5⟩ := hk k hkn
  have h6 : ∀ g, ∑ γ ∈ R', T w (g * γ) = c (V.rank - k) / c V.rank * T w g := fun g => by
    have := hc' (V.rank - k) (Nat.sub_le _ _) (z * α⁻¹) (R'.image (· * z⁻¹)) h2
      (by rw [mul_inv_rev, inv_inv]; exact isDC_mul_central _ hz' h4) g
    rw [Finset.sum_image (fun a _ b _ hab => mul_right_cancel hab)] at this
    simp only [← mul_assoc, hcen, ← Finset.mul_sum] at this
    rw [div_mul_eq_mul_div, ← this, mul_div_cancel_left₀ _ hn]
  have h7 := GlobalTheory.DoubleCosetAdjoint.eigenvalue_inv_eq_star μ (GQ V) (levG V β L) 𝓕 (T w) α⁻¹ R R' (c k)
    (c (V.rank - k) / c V.rank) h𝓕 (hT'.aut w).cont (hT'.aut w).left
    (fun k hk g => by simpa using hT'.lev w k hk g) hint hne h3 (by rwa [inv_inv]) h5
    (hc' k hkn α R h1 h3) h6
  rw [h7, div_mul_cancel₀ _ hn]

end GlobalTheory.HeckeUnitary

end
