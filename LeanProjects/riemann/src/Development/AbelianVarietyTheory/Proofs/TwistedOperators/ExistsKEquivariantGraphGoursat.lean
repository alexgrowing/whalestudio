import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

namespace GlobalTheory.KStableGraph

theorem exists_partner {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {S S' U : Submodule ℂ H}
    (hS : Formalism.MainNotions.S.IsKStableOn ε ρ S) (hS' : Formalism.MainNotions.S.IsKStableOn ε ρ S')
    (hU : Formalism.MainNotions.S.IsKStableOn ε ρ U)
    (irr : ∀ T : Submodule ℂ H, T ≤ S → Formalism.MainNotions.S.IsKStableOn ε ρ T → T = ⊥ ∨ T = S)
    (hle : U ≤ S ⊔ S') (hUS' : U ⊓ S' = ⊥) (hU0 : U ≠ ⊥) :
    ∀ s ∈ S, ∃ s' ∈ S', s + s' ∈ U := by
  have hT : Formalism.MainNotions.S.IsKStableOn ε ρ (S ⊓ (U ⊔ S')) := by
    intro g hg v hv
    obtain ⟨hvS, hvU⟩ := Submodule.mem_inf.mp hv
    obtain ⟨u, hu, t, ht, rfl⟩ := Submodule.mem_sup.mp hvU
    refine Submodule.mem_inf.mpr ⟨hS g hg _ hvS, ?_⟩
    rw [map_add]
    exact Submodule.add_mem_sup (hU g hg u hu) (hS' g hg t ht)
  rcases irr _ inf_le_left hT with h | h
  · exfalso
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp (hle hu)
    have hsT : s ∈ S ⊓ (U ⊔ S') := by
      refine Submodule.mem_inf.mpr ⟨hs, ?_⟩
      have : s = u - t := by rw [← hst]; abel
      rw [this]
      exact Submodule.sub_mem_sup hu ht
    rw [h] at hsT
    have hs0 : s = 0 := (Submodule.mem_bot ℂ).mp hsT
    have hut : u = t := by rw [← hst, hs0, zero_add]
    have : u ∈ U ⊓ S' := Submodule.mem_inf.mpr ⟨hu, hut ▸ ht⟩
    rw [hUS'] at this
    exact hu0 ((Submodule.mem_bot ℂ).mp this)
  · intro s hs
    have hs' : s ∈ S ⊓ (U ⊔ S') := h.symm ▸ hs
    obtain ⟨u, hu, t, ht, hut⟩ := Submodule.mem_sup.mp (Submodule.mem_inf.mp hs').2
    refine ⟨-t, S'.neg_mem ht, ?_⟩
    have : s + -t = u := by rw [← hut]; abel
    rw [this]; exact hu

theorem exists_kMap_onto : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S S' U : Submodule ℂ H), Formalism.MainNotions.S.IsKStableOn ε ρ S → Formalism.MainNotions.S.IsKStableOn ε ρ S' → Formalism.MainNotions.S.IsKStableOn ε ρ U → (∀ T : Submodule ℂ H, T ≤ S → Formalism.MainNotions.S.IsKStableOn ε ρ T → T = ⊥ ∨ T = S) → (∀ T : Submodule ℂ H, T ≤ S' → Formalism.MainNotions.S.IsKStableOn ε ρ T → T = ⊥ ∨ T = S') → S ⊓ S' = ⊥ → U ≤ S ⊔ S' → U ⊓ S = ⊥ → U ⊓ S' = ⊥ → U ≠ ⊥ → ∃ φ : H →ₗ[ℂ] H, (∀ k ∈ Formalism.REAL.Kset ε, ∀ u ∈ S, φ (ρ k u) = ρ k (φ u)) ∧ S.map φ = S' := by
  intro n ε H _ _ ρ S S' U hS hS' hU irrS irrS' hSS' hle hUS hUS' hU0
  have ex := exists_partner hS hS' hU irrS hle hUS' hU0
  have ex' := exists_partner hS' hS hU irrS' (by rwa [sup_comm]) hUS hU0
  have uniq : ∀ s ∈ S, ∀ a ∈ S', ∀ b ∈ S', s + a ∈ U → s + b ∈ U → a = b := by
    intro s _ a ha b hb h1 h2
    have h3 := U.sub_mem h1 h2
    rw [add_sub_add_left_eq_sub] at h3
    have : a - b ∈ U ⊓ S' := Submodule.mem_inf.mpr ⟨h3, S'.sub_mem ha hb⟩
    rw [hUS'] at this
    exact sub_eq_zero.mp ((Submodule.mem_bot ℂ).mp this)
  choose g hg using ex
  let f : S →ₗ[ℂ] S' :=
    { toFun := fun x => ⟨g x x.2, (hg x x.2).1⟩
      map_add' := fun x y => by
        apply Subtype.ext
        show g ((x + y : S) : H) (x + y).2 = g x x.2 + g y y.2
        refine uniq _ (x + y).2 _ (hg _ _).1 _ (S'.add_mem (hg x x.2).1 (hg y y.2).1) (hg _ _).2 ?_
        have := U.add_mem (hg x x.2).2 (hg y y.2).2
        rw [Submodule.coe_add]
        convert this using 1
        abel
      map_smul' := fun c x => by
        apply Subtype.ext
        show g ((c • x : S) : H) (c • x).2 = c • g x x.2
        refine uniq _ (c • x).2 _ (hg _ _).1 _ (S'.smul_mem c (hg x x.2).1) (hg _ _).2 ?_
        have := U.smul_mem c (hg x x.2).2
        rw [Submodule.coe_smul]
        convert this using 1
        rw [smul_add] }
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl S
  let φ : H →ₗ[ℂ] H := S'.subtype ∘ₗ f ∘ₗ S.projectionOnto C hC
  have hφ : ∀ u (hu : u ∈ S), φ u = g u hu := by
    intro u hu
    have := Submodule.linearProjOfIsCompl_apply_left hC ⟨u, hu⟩
    change ((f (S.projectionOnto C hC ((⟨u, hu⟩ : S) : H)) : S') : H) = _
    rw [this]
    rfl
  refine ⟨φ, ?_, ?_⟩
  · intro k hk u hu
    have hku : ρ k u ∈ S := hS k hk u hu
    rw [hφ _ hku, hφ u hu]
    refine uniq _ hku _ (hg _ hku).1 _ (hS' k hk _ (hg u hu).1) (hg _ hku).2 ?_
    rw [← map_add]
    exact hU k hk _ (hg u hu).2
  · apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      rw [hφ u hu]
      exact (hg u hu).1
    · intro s' hs'
      obtain ⟨s, hs, hsU⟩ := ex' s' hs'
      refine Submodule.mem_map.mpr ⟨s, hs, ?_⟩
      rw [hφ s hs]
      exact uniq s hs _ (hg s hs).1 s' hs' (hg s hs).2 (by rwa [add_comm])

end GlobalTheory.KStableGraph
