import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SplitMul

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Far

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem farId [MeasurableSpace (KR n)] [BorelSpace (KR n)] (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) {ν : Measure (KR n)} {κ : KR n → ℂ} {N : ℕ}
    {yy : Fin N → GR n} {QQ : Fin N → PX m n} {M : ℂ → Matrix (Fin N) (Fin N) ℂ}
    (hν : IsFiniteMeasure ν) (hκ : Continuous κ)
    (hMid : ∀ (w : ℂ) (i : Fin N) (y' : GR n), ∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w *
        F0 p q e (y' * (k : GR n) * yy i)) ∂ν = (hLoc y' : ℂ) ^ w * ∑ j, M w i j * sL (QQ j) y')
    {z : ℂ} (hmaj : ∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧
      ∀ g ∈ C, ∀ q', ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z 1) g q'‖ ≤ u q')
    (g : G) (hsum : ∀ j, Summable fun q' => GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z (QQ j)) g q') (i : Fin N) :
    ∫ k, κ k * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z 1) (g * ι ((k : GR n) * yy i)) ∂ν =
      ∑ j, M (z - s₀) i j * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g := by
  classical
  haveI := hν
  have hcK : IsCompact (Set.range fun k : KR n => g * ι ((k : GR n) * yy i)) :=
    isCompact_range (continuous_const.mul (hG.ιcont.comp (continuous_subtype_val.mul continuous_const)))
  obtain ⟨u, hu, hbd⟩ := hmaj _ hcK
  obtain ⟨B, hB⟩ := (isCompact_univ (X := KR n)).exists_bound_of_continuousOn hκ.continuousOn
  let F : GlobalTheory.Eis.Cosets Pp Γ → KR n → ℂ := fun q' k =>
    κ k * GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z 1) (g * ι ((k : GR n) * yy i)) q'
  have hcont : ∀ q', Continuous (F q') := by
    intro q'
    have h := Far.cont_hz hD hL hG z (yy i) (GlobalTheory.Eis.term Pp Γ id g q')
    refine hκ.mul ?_
    simpa [GlobalTheory.Eis.term, mul_assoc] using h
  have hbound : ∀ q' k, ‖F q' k‖ ≤ B * u q' := by
    intro q' k
    rw [norm_mul]
    exact mul_le_mul (hB k trivial) (hbd _ ⟨k, rfl⟩ q') (norm_nonneg _)
      (le_trans (norm_nonneg _) (hB k trivial))
  have hint : ∀ q', Integrable (F q') ν := fun q' =>
    Integrable.mono' (integrable_const (B * u q')) (hcont q').aestronglyMeasurable
      (ae_of_all _ (hbound q'))
  have hsumm : Summable fun q' => ∫ k, ‖F q' k‖ ∂ν := by
    refine Summable.of_nonneg_of_le (fun q' => integral_nonneg fun _ => norm_nonneg _)
      (fun q' => integral_mono (hint q').norm (integrable_const (B * u q')) (hbound q'))
      ?_
    simp only [integral_const, smul_eq_mul]
    exact (hu.mul_left B).mul_left _
  have hq : ∀ q', ∫ k, F q' k ∂ν =
      ∑ j, M (z - s₀) i j * GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z (QQ j)) g q' := by
    intro q'
    have h := Far.pointId hD hL hG hMid z i (GlobalTheory.Eis.term Pp Γ id g q')
    simpa [F, GlobalTheory.Eis.term, mul_assoc] using h
  have hzero : ∀ q', u q' = 0 → F q' = fun _ => 0 := by
    intro q' h0
    funext k
    have h1 := hbound q' k
    rw [h0, mul_zero] at h1
    exact norm_le_zero_iff.mp h1
  let S : Set (GlobalTheory.Eis.Cosets Pp Γ) := Function.support u
  haveI : Countable S := hu.countable_support.to_subtype
  have hout : ∀ q', q' ∉ S → u q' = 0 := fun q' h => Function.notMem_support.mp h
  have e1 : ∀ k, ∑' q', F q' k = ∑' q' : S, F q' k := by
    intro k
    refine (tsum_subtype_eq_of_support_subset ?_).symm
    intro q' hq'
    by_contra h
    apply hq'
    show F q' k = 0
    rw [hzero q' (hout q' h)]
  have e2 : ∑' q', ∫ k, F q' k ∂ν = ∑' q' : S, ∫ k, F q' k ∂ν := by
    refine (tsum_subtype_eq_of_support_subset ?_).symm
    intro q' hq'
    by_contra h
    apply hq'
    show ∫ k, F q' k ∂ν = 0
    rw [hzero q' (hout q' h)]
    simp
  have hL1 : ∫ k, κ k * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z 1) (g * ι ((k : GR n) * yy i)) ∂ν =
      ∫ k, ∑' q' : S, F q' k ∂ν := by
    congr 1
    funext k
    rw [← e1 k]
    simp only [F, GlobalTheory.Eis.cosetSum]
    rw [tsum_mul_left]
  have hswap : ∫ k, ∑' q' : S, F q' k ∂ν = ∑' q' : S, ∫ k, F q' k ∂ν :=
    (integral_tsum_of_summable_integral_norm (F := fun (q' : S) k => F q' k)
      (fun q' => hint q') (hsumm.subtype S)).symm
  rw [hL1, hswap, ← e2]
  simp_rw [hq]
  rw [Summable.tsum_finsetSum (fun j _ => (hsum j).mul_left _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tsum_mul_left]
  rfl

end PositivityTheory.Rg.Sw.AbsSt.Far

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem farRight : Iwa → CayleyBlocksInvertible → Mult → HolParam → FarRight := by
  intro hI hD hM _hH m n ε c t p q e sL ρ hL G _ _ _ _ _ _ Pp Γ ι s₀ Ht sec I Λ hG
  obtain ⟨σ, h1, h2, hmaj⟩ := Far.farHol hI hM hD hL hG
  refine ⟨σ, h1, h2, ?_⟩
  intro _ _ ν κ N yy QQ M hν hκ hMid z hzr g i
  exact Far.farId hD hL hG hν hκ hMid (hmaj z hzr) g (fun j => h2 (QQ j) g z hzr) i

end PositivityTheory.Rg.Sw.AbsSt
