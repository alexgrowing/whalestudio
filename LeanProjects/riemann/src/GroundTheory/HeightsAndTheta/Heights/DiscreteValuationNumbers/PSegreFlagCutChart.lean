import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutPreimage
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GenericProjClosureDivisor

noncomputable section

namespace SegreFlagCutChart

theorem exists_pow_mul_mem_of_mem_sup_map {R S F : Type*} [CommRing R] [CommRing S] [FunLike F S R]
    [RingHomClass F S R] (f : F) (A I : Ideal R) (J : Ideal S) (v : R) (hI : I ≤ A)
    (hJ : ∀ q ∈ J, ∃ n : ℕ, v ^ n * f q ∈ A) : ∀ x ∈ I ⊔ J.map f, ∃ n : ℕ, v ^ n * x ∈ A := by
  let T : Ideal R :=
    { carrier := {x | ∃ n : ℕ, v ^ n * x ∈ A}
      add_mem' := by
        rintro a b ⟨m, hm⟩ ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        have h : v ^ (m + n) * (a + b) = v ^ n * (v ^ m * a) + v ^ m * (v ^ n * b) := by ring
        rw [h]
        exact A.add_mem (A.mul_mem_left _ hm) (A.mul_mem_left _ hn)
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨n, hn⟩
        refine ⟨n, ?_⟩
        have h : v ^ n * (c • x) = c * (v ^ n * x) := by rw [smul_eq_mul]; ring
        rw [h]
        exact A.mul_mem_left _ hn }
  have hle : I ⊔ J.map f ≤ T :=
    sup_le (fun x hx => ⟨0, by simpa using hI hx⟩) (Ideal.map_le_iff_le_comap.2 fun q hq => hJ q hq)
  exact fun x hx => hle hx

end SegreFlagCutChart

open SegreFlagCutChart in

theorem SegreFlagCutChart.proof (hCS : SegreFlagCutChartSection.Statement)
    (hPre : SegreFlagCutPreimage.Statement) : SegreFlagCutChart.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk W hW hWr hPW hϖW
  classical

  choose c hc using fun j : K => hWr (some (some j))
  have nz : ∀ j, y ⟨j, c j⟩ ≠ 0 := by
    intro j h0
    refine hc j (hPW (mem_of_homog (isWeightedHomogeneous_X O _ _) ?_))
    rw [aeval_X]
    show algebraMap Ω Φ (y ⟨j, c j⟩) = 0
    rw [h0, map_zero]
  have hcne : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => nz j
  have hvW : (∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O)) ∉ W := fun hm => by
    obtain ⟨j, -, hj⟩ := hW.prod_mem_iff.mp hm
    exact hc j hj
  obtain ⟨-, dl, dm, l, μ, m, hμ, hl, hμh, hdeg, hval, hsat⟩ :=
    hCS O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk c hcne
  have hμW : μ ∉ W := by
    rw [hμ]
    intro hm
    obtain ⟨j, -, hj⟩ := hW.prod_mem_iff.mp hm
    exact hc j (hW.mem_of_pow_mem _ hj)
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  ·
    refine ⟨dl, dm, l, μ, _, hl, hμh, hdeg, hμW, hvW, hval, fun _ hlW => ?_, fun h => absurd h (lt_irrefl 0)⟩
    obtain ⟨j, hj⟩ := hWr none
    have hq : (X ⟨none, j⟩ : MvPolynomial (Σ o : Option K, bundleIdx (bundleIdx ι M) M' (secondFactorBlocks o)) O) ∈
        pointIdeal O (flagProjPt secondFactorBlocks y w e φ φ' t 0) := by
      refine mem_of_homog (isWeightedHomogeneous_X O _ _) ?_
      rw [aeval_X]
      show flagClosurePt y w e φ φ' t 0 ⟨none, j⟩ = 0
      simp [flagClosurePt, pairProjCoord, flagCoord]
    obtain ⟨n, hn⟩ := hsat _ hq
    have h1 := sup_le hPW ((Ideal.span_singleton_le_iff_mem W).2 hlW) hn
    rw [rename_X] at h1
    rcases hW.mem_or_mem h1 with h2 | h2
    · exact hvW (hW.mem_of_pow_mem _ h2)
    · exact hj h2
  ·
    obtain ⟨u₀, hu₀W, hu₀⟩ := hPre O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
      Φ e t ht k hk W hW hWr hPW hϖW
    refine ⟨dl, dm, l, μ, u₀ * ∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O), hl, hμh, hdeg,
      hμW, fun hm => ?_, hval, fun h => absurd h (Nat.pos_iff_ne_zero.mp hk0), fun _ q hq => ?_⟩
    · rcases hW.mem_or_mem hm with h | h
      · exact hu₀W h
      · exact hvW h
    · obtain ⟨n, hn⟩ := hu₀ q hq
      obtain ⟨m', hm'⟩ := exists_pow_mul_mem_of_mem_sup_map _ _ _ _ _ le_sup_left hsat _ hn
      refine ⟨n + m', ?_⟩
      have h : (u₀ * ∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O)) ^ (n + m') * q =
          u₀ ^ m' * (∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O)) ^ n *
            ((∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O)) ^ m' * (u₀ ^ n * q)) := by
        ring
      rw [h]
      exact Ideal.mul_mem_left _ _ hm'

end

end GroundTheory.Heights₂.Heights.NumbersDVR
