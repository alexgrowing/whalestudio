import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.JumpStepOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.MemRangeOfSol
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InstCommRingBcris
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalV GlobalTheory.HTLink GlobalTheory.HodgeCoh GlobalTheory.EtC GlobalTheory.Pst
open UpperTheory.Gal.Int.Geo GlobalTheory.WeilDeligne GlobalTheory.HeckeGal
open Matrix

namespace PositivityTheory.AutomorphicGaloisHodgeTate.G8

theorem occMove_σC_alg {l : ℕ} [Fact l.Prime] (g : GQ l) (x : Qbar l) :
    Formalism.Per.σC g (algebraMap (Qbar l) ℂ_[l] x) = algebraMap (Qbar l) ℂ_[l] (g x) := by
  exact GlobalTheory.RingBasics.σC_coe g x

theorem OccMove_holds : OccMove := by
  intro l _ K a
  refine ⟨?_, ?_⟩
  · intro d₁ d₀ ρ₁ ρ₀ A hA hAρ ⟨S, z, hz, h⟩
    classical
    refine ⟨S ∪ Finset.univ.image (fun pq : Fin d₀ × Fin d₁ => A pq.1 pq.2),
      (A.map (algebraMap (Qbar l) ℂ_[l])) *ᵥ z,
      fun h0 => hz (map_injective (C := ℂ_[l]) A hA (by rw [h0, mulVec_zero])), fun σ hσ => ?_⟩
    have hS : ∀ x ∈ S, (σ : GQ l) x = x := fun x hx => hσ x (Finset.mem_union_left _ hx)
    have hAσ : (A.map (algebraMap (Qbar l) ℂ_[l])).map (Formalism.Per.σC (σ : GQ l)) = A.map (algebraMap (Qbar l) ℂ_[l]) := by
      ext p q
      simp only [Matrix.map_apply]
      rw [occMove_σC_alg, hσ _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨(p, q), Finset.mem_univ _, rfl⟩))]
    have key : (fun q => Formalism.Per.σC (σ : GQ l) ((A.map (algebraMap (Qbar l) ℂ_[l]) *ᵥ z) q)) =
        A.map (algebraMap (Qbar l) ℂ_[l]) *ᵥ fun q => Formalism.Per.σC (σ : GQ l) (z q) := by
      funext p
      rw [RingHom.map_mulVec, hAσ]
      rfl
    rw [key, mulVec_mulVec, ← Matrix.map_mul, hAρ, Matrix.map_mul, ← mulVec_mulVec, h σ hS, mulVec_smul]
  · intro d ρ₀ ρ c hc ⟨S, z, hz, h⟩
    classical
    have hT : (Finset.univ.filter fun q => z q ≠ 0).Nonempty := by
      obtain ⟨q, hq⟩ := Function.ne_iff.1 hz
      exact ⟨q, Finset.mem_filter.2 ⟨Finset.mem_univ _, hq⟩⟩
    obtain ⟨q₀, hq₀, hmax⟩ := Finset.exists_max_image _ c hT
    have hgt : ∀ q, c q₀ < c q → z q = 0 := fun q hq => by
      by_contra h0
      exact absurd (hmax q (Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩)) (not_le.2 hq)
    refine ⟨S, fun q => if c q = c q₀ then z q else 0, fun h0 => ?_, fun σ hσ => ?_⟩
    · have h1 : (if c q₀ = c q₀ then z q₀ else 0) = 0 := congrFun h0 q₀
      rw [if_pos rfl] at h1
      exact (Finset.mem_filter.1 hq₀).2 h1
    obtain ⟨hB, hρ⟩ := hc σ
    have hE := congrFun (h σ hσ)
    funext p
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply] at hE ⊢
    by_cases hp : c p = c q₀
    · rw [if_pos hp, ← hE p]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hρ]
      by_cases hq : c q = c q₀
      · rw [if_pos hq, if_pos (hp.trans hq.symm)]
      · rw [if_neg hq, map_zero, mul_zero]
        rcases lt_or_gt_of_ne hq with hlt | hgt'
        · rw [hB (lt_of_lt_of_eq hlt hp.symm), map_zero, zero_mul]
        · rw [hgt q hgt', map_zero, mul_zero]
    · rw [if_neg hp, smul_zero]
      refine Finset.sum_eq_zero fun q _ => ?_
      rw [hρ]
      by_cases hq : c q = c q₀
      · rw [if_neg (fun e => hp (e.trans hq)), map_zero, zero_mul]
      · rw [if_neg hq, map_zero, mul_zero]

end PositivityTheory.AutomorphicGaloisHodgeTate.G8

end
