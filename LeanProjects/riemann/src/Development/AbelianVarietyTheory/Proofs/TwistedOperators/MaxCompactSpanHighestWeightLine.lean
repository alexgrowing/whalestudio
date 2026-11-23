import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactTypeInCompactStableSubmodule
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.URepCompRed
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

namespace GlobalTheory.KSpanHighest

theorem kset_mul {n : ℕ} {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Formalism.REAL.Kset ε)
    (hb : b ∈ Formalism.REAL.Kset ε) : a * b ∈ Formalism.REAL.Kset ε := by
  rw [(Formalism.REAL.kFacts n ε).2.2.2.2] at ha hb ⊢
  exact ⟨GlobalTheory.KTypeExists.inUJ_mul ha.1 hb.1, Submonoid.mul_mem _ ha.2 hb.2⟩

theorem kset_of_mul {n : ℕ} {ε : Fin n → Bool} {k x : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε)
    (hx : Formalism.REAL.inUJ ε x) (hkx : k * x ∈ Formalism.REAL.Kset ε) : x ∈ Formalism.REAL.Kset ε := by
  rw [(Formalism.REAL.kFacts n ε).2.2.2.2] at hk hkx ⊢
  refine ⟨hx, ?_⟩
  have e : x = star k * (k * x) := by
    rw [← Matrix.mul_assoc, Unitary.star_mul_self_of_mem hk.2, Matrix.one_mul]
  rw [e]
  exact Submonoid.mul_mem _ (Unitary.star_mem hk.2) hkx.2

theorem kspan_highest : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ → (∀ v, ContinuousOn (fun g => ρ g v) (Formalism.MainNotions.S.UJset ε)) → (∀ k ∈ Formalism.REAL.Kset ε, ∀ v, ‖ρ k v‖ = ‖v‖) → ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → Formalism.MainNotions.S.IsKStableOn ε ρ S → ∀ (Λ : Fin n → ℝ) (w : H), w ∈ S → w ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ Λ w → (∀ a b : Fin n, a < b → ε a = ε b → ∀ x ∈ S, Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ (Λ + Formalism.REAL.root a b) x → x = 0) → (∀ (μ : Fin n → ℝ) (x : H), x ∈ Submodule.span ℂ ((fun k => ρ k w) '' Formalism.REAL.Kset ε) → x ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ x → Formalism.MainNotions.S.CDom ε μ Λ) ∧ (∀ x ∈ Submodule.span ℂ ((fun k => ρ k w) '' Formalism.REAL.Kset ε), Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ Λ x → ∃ c : ℂ, x = c • w) := by
  intro n ε H _ _ ρ hρ hcont hiso S hfd hS Λ w hw _ hΛ hkill
  classical
  have hKU : ∀ g ∈ Formalism.REAL.Kset ε, g ∈ Formalism.MainNotions.S.UJset ε := fun g hg => (Formalism.REAL.kFacts n ε).1 g hg
  let πS : Matrix (Fin n) (Fin n) ℂ → (S →L[ℂ] S) := fun g =>
    if hg : g ∈ Formalism.REAL.Kset ε then
      LinearMap.toContinuousLinearMap ((ρ g).toLinearMap.restrict (p := S) (q := S) (fun v hv => hS g hg v hv))
    else 0
  have hπ : ∀ g ∈ Formalism.REAL.Kset ε, ∀ v : S, ((πS g v : S) : H) = ρ g v := by
    intro g hg v
    simp [πS, hg]
  have hπ0 : ∀ g, g ∉ Formalism.REAL.Kset ε → πS g = 0 := fun g hg => by simp [πS, hg]
  have h1K : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.REAL.Kset ε := by
    rw [(Formalism.REAL.kFacts n ε).2.2.2.2]
    exact ⟨by simp [Formalism.REAL.inUJ], Submonoid.one_mem _⟩
  have h1 : πS 1 = 1 := by
    ext v
    rw [hπ 1 h1K v, hρ.1]
    rfl
  have hmulK : ∀ a ∈ Formalism.REAL.Kset ε, ∀ b ∈ Formalism.REAL.Kset ε, πS (a * b) = (πS a).comp (πS b) := by
    intro a ha b hb
    ext v
    rw [hπ _ (kset_mul ha hb), ContinuousLinearMap.comp_apply, hπ a ha, hπ b hb, hρ.2 a (hKU a ha) b (hKU b hb)]
    rfl
  have hK : ∀ k ∈ Formalism.REAL.Kset ε, ∀ x, Formalism.REAL.inUJ ε x → πS (k * x) = πS k * πS x := by
    intro k hk x hx
    by_cases hxK : x ∈ Formalism.REAL.Kset ε
    · exact hmulK k hk x hxK
    · have : k * x ∉ Formalism.REAL.Kset ε := fun h => hxK (kset_of_mul hk hx h)
      rw [hπ0 _ this, hπ0 _ hxK, mul_zero]
  have hU : ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.Kset ε) πS := by
    refine ⟨⟨h1, hmulK⟩, ?_, ?_⟩
    · intro g hg v
      rw [← Submodule.norm_coe, hπ g hg v, hiso g hg, Submodule.norm_coe]
    · intro v
      have hc : ContinuousOn (fun g => ((πS g v : S) : H)) (Formalism.REAL.Kset ε) :=
        ((hcont (v : H)).mono hKU).congr fun g hg => hπ g hg v
      exact (Topology.IsInducing.subtypeVal.continuousOn_iff).2 hc
  obtain ⟨E, hR, hUn, hder, -⟩ := ReciprocityTheory.ChartRestriction.DS.HW.uRepCompRed n ε S πS hU
  have hE : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inK ε Z → ∀ v : S,
      HasDerivAt (fun t : ℝ => πS (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0 := by
    intro Z hZ v
    have := hder Z hZ v
    simpa [ReciprocityTheory.ChartRestriction.DS.actM, LinearMap.sum_apply, LinearMap.smul_apply] using this
  have hwt : ∀ (μ : Fin n → ℝ) (v : S), IsWtOn (Formalism.REAL.Kset ε) πS μ v ↔ IsWtOn (Formalism.REAL.Kset ε) ρ μ (v : H) :=
    fun μ v => forall₂_congr fun θ hθ => by rw [← hπ _ hθ, ← Submodule.coe_smul, Subtype.coe_inj]
  set w' : S := ⟨w, hw⟩ with hw'
  have hwE : IsWeight E Λ w' := GlobalTheory.KTypeExists.isWeight_of_isWtOnK E hE Λ w' ((hwt Λ w').2 hΛ)
  have hhi : KHighest ε E Λ w' := by
    refine ⟨hwE, fun a b hab he => ?_⟩
    have h2 := GlobalTheory.KTypeExists.isWtOn_of_isWeightK h1 hK E hE _ _ (compact_weight_shift hR hwE he)
    have h3 : Λ + Pi.single a 1 - Pi.single b 1 = Λ + Formalism.REAL.root a b := by
      simp [Formalism.REAL.root, add_sub_assoc]
    rw [h3, hwt] at h2
    exact Subtype.ext (hkill a b hab he _ (E a b w').2 h2)
  have hst := GlobalTheory.KTypeExists.stable_of_derivedK h1 hK E hE _ (compact_span_stable (ε := ε) (F := E) w')
  have hspan : Submodule.span ℂ ((fun k => ρ k w) '' Formalism.REAL.Kset ε) ≤ (kSpan ε E w').map S.subtype := by
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨πS g w', hst g hg w' (mem_compact_span_self w'), hπ g hg w'⟩
  refine ⟨?_, ?_⟩
  · intro μ x hx hx0 hxw
    obtain ⟨y, hy, rfl⟩ := hspan hx
    exact GlobalTheory.KTypeExists.cdom_of_mem_kSpan E Λ μ w' y hR hUn hhi hy
      (fun h => hx0 (by rw [h]; rfl)) (GlobalTheory.KTypeExists.isWeight_of_isWtOnK E hE μ y ((hwt μ y).2 hxw))
  · intro x hx hxw
    obtain ⟨y, hy, rfl⟩ := hspan hx
    obtain ⟨heq, hline⟩ := compact_lowering_holds S n ε E Λ w' hR hhi
    obtain ⟨c, hc⟩ := hline y (heq ▸ hy) (GlobalTheory.KTypeExists.isWeight_of_isWtOnK E hE Λ y ((hwt Λ y).2 hxw))
    exact ⟨c, by rw [hc]; rfl⟩

end GlobalTheory.KSpanHighest
