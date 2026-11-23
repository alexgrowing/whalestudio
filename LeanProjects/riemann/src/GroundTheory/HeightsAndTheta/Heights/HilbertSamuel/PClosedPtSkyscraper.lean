import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClosedPtSkyscraper
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClosedPtChartUnit
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace ClosedPtSkyscraper

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem cellMon_notMem {P : Ideal (MRingOver S ι)} (hP : P.IsPrime) {J : ∀ k, Finset (ι k)}
    (hJ : ∀ k, ∀ i ∈ J k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P) {u : MRingOver S ι} (hu : u ∈ KH.cellMon S J) :
    u ∉ P := by
  induction hu using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    exact hJ k i hi
  | one => exact (Ideal.ne_top_iff_one P).mp hP.ne_top
  | mul f f' _ _ hf hf' => exact fun h => (hP.mem_or_mem h).elim hf hf'

theorem loc_eq_zero {N : Type} [AddCommGroup N] [Module (MRingOver S ι) N] {P : Ideal (MRingOver S ι)}
    (hkill : ∀ p ∈ P, ∀ n : N, p • n = 0) {J : ∀ k, Finset (ι k)}
    (hJ : ∃ k, ∃ i ∈ J k, (X ⟨k, i⟩ : MRingOver S ι) ∈ P) (x : LocalizedModule (KH.cellMon S J) N) :
    x = 0 := by
  obtain ⟨k, i, hi, hX⟩ := hJ
  induction x using LocalizedModule.induction_on with
  | h n w =>
    rw [← LocalizedModule.zero_mk (1 : KH.cellMon S J), LocalizedModule.mk_eq]
    refine ⟨⟨X ⟨k, i⟩, Submonoid.subset_closure ⟨k, i, hi, rfl⟩⟩, ?_⟩
    simp only [one_smul, smul_zero]
    rw [Submonoid.smul_def]
    exact hkill _ hX n

end ClosedPtSkyscraper

theorem ClosedPtSkyscraper.proof (hU : ClosedPtChartUnit.Statement) : ClosedPtSkyscraper.Statement := by
  classical
  intro S _ K _ _ ι _ _ N _ _ _ _ 𝓝 P d h𝓝 hP hkill I hI y hy
  obtain ⟨m, s, a, hsa, hm, rfl⟩ := GenSESStep.locPart_normal h𝓝 hy
  have hsP : (s : MRingOver S ι) ∉ P := ClosedPtSkyscraper.cellMon_notMem hP.1.1 hI s.2

  have hcong : ∀ p q : MRingOver S ι, p - q ∈ P → ∀ n : N, p • n = q • n := fun p q h n =>
    sub_eq_zero.mp (by rw [← sub_smul]; exact hkill _ h n)

  have hinv : ∀ J : ∀ k, Finset (ι k), (∀ k, (J k).Nonempty) →
      (∀ k, ∀ i ∈ J k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P) →
      ∃ t ∈ KH.cellMon S J, ∃ (g : MRingOver S ι) (b : K → ℕ),
        IsMultiHomog t (a + b) ∧ IsMultiHomog g b ∧ t - g * s ∈ P :=
    fun J hne hJ => hU S K ι P hP J hne hJ s a hsa hsP
  choose t ht g b htb hgb htg using hinv
  let z : KH.CechC S ι N 0 := fun J =>
    if hJ : ∀ k, ∀ i ∈ J.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P then
      LocalizedModule.mk (g J.1 J.2.1 hJ • m) ⟨t J.1 J.2.1 hJ, ht J.1 J.2.1 hJ⟩
    else 0

  have hagree : ∀ (J : KH.Cell K ι 0) (hJ : ∀ k, ∀ i ∈ J.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P)
      (u h' t' : MRingOver S ι), u - h' * s ∈ P →
      (u * t' * g J.1 J.2.1 hJ) • m = (h' * t' * t J.1 J.2.1 hJ) • m := by
    intro J hJ u h' t' hu
    refine hcong _ _ ?_ m
    have := sub_mem (P.mul_mem_right (t' * g J.1 J.2.1 hJ) hu) (P.mul_mem_left (h' * t') (htg J.1 J.2.1 hJ))
    convert this using 1
    ring
  refine ⟨z, ⟨Submodule.mem_pi.mpr fun J _ => ?_, LinearMap.mem_ker.mpr (funext fun E => ?_)⟩, ?_⟩
  ·
    by_cases hJ : ∀ k, ∀ i ∈ J.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P
    · simp only [z, dif_pos hJ]
      refine GenSESStep.mk_mem_locPart _ _ (a + b J.1 J.2.1 hJ) (htb J.1 J.2.1 hJ) ?_
      have e : (d + fun k => ((a + b J.1 J.2.1 hJ) k : ℤ)) =
          (d + fun k => (a k : ℤ)) + fun k => (b J.1 J.2.1 hJ k : ℤ) := by
        funext k
        simp only [Pi.add_apply, Nat.cast_add]
        ring
      rw [e]
      exact h𝓝.2 _ _ _ _ (hgb J.1 J.2.1 hJ) hm
    · simp only [z, dif_neg hJ]
      exact zero_mem _
  ·
    obtain ⟨J₁, J₂, h₁, h₂, σ, -, hD⟩ := GenTwistGenerated.cechD_zero_apply (S := S) (M := N) E
    rw [Pi.zero_apply, hD z]
    by_cases hE : ∀ k, ∀ i ∈ E.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P
    · have hJ₁ : ∀ k, ∀ i ∈ J₁.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P := fun k i hi => hE k i (h₁ k hi)
      have hJ₂ : ∀ k, ∀ i ∈ J₂.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P := fun k i hi => hE k i (h₂ k hi)
      obtain ⟨u, hu, h', -, -, -, huP⟩ := hU S K ι P hP E.1 E.2.1 hE s a hsa hsP
      simp only [z, dif_pos hJ₁, dif_pos hJ₂]
      rw [GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono h₁),
        GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono h₂)]
      have heq : LocalizedModule.mk (g J₁.1 J₁.2.1 hJ₁ • m)
            (⟨t J₁.1 J₁.2.1 hJ₁, GenTwistGenerated.cellMon_mono h₁ (ht J₁.1 J₁.2.1 hJ₁)⟩ : KH.cellMon S E.1) =
          LocalizedModule.mk (g J₂.1 J₂.2.1 hJ₂ • m)
            ⟨t J₂.1 J₂.2.1 hJ₂, GenTwistGenerated.cellMon_mono h₂ (ht J₂.1 J₂.2.1 hJ₂)⟩ := by
        refine LocalizedModule.mk_eq.mpr ⟨⟨u, hu⟩, ?_⟩
        simp only [Submonoid.smul_def, smul_smul]
        rw [← mul_assoc, ← mul_assoc, hagree J₁ hJ₁ u h' (t J₂.1 J₂.2.1 hJ₂) huP,
          hagree J₂ hJ₂ u h' (t J₁.1 J₁.2.1 hJ₁) huP]
        congr 1
        ring
      rw [heq, sub_self]
      exact zsmul_zero σ
    · push Not at hE
      exact ClosedPtSkyscraper.loc_eq_zero hkill hE _
  ·
    simp only [z, dif_pos hI]
    refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, smul_smul]
    exact (hcong _ _ (by rw [mul_comm]; exact htg I.1 I.2.1 hI) m).symm

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
