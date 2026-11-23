import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.RealPlaceAnalysis.QuotientSettingHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerRepK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqLowKOfLeLowKSub
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotCdomAdd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightDerivativeSumZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGardingKMap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KHighestEqSmulOfMinusKilled
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ChainBound

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.MultGap

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem proj_comm (hU : IsURepOn (Kset ε) σ) {W : Submodule ℂ H} [W.HasOrthogonalProjection]
    (hW : IsKStableOn ε σ W) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (x : H) :
    W.starProjection (σ k x) = σ k (W.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hW k hk _ (W.starProjection_apply_mem x))
    fun w hw => ?_
  rw [← map_sub, FormF.inner_rep_K hU hk]
  exact W.starProjection_inner_eq_zero x _ (hW _ (Kset_star ε hk) w hw)

theorem orth_of_ne (hU : IsURepOn (Kset ε) σ) {Λ μ : Fin n → ℝ} {S T : Submodule ℂ H}
    (hS : IsKTypeOf ε σ Λ S) (hT : IsKTypeOf ε σ μ T) (hne : μ ≠ Λ) :
    ∀ x ∈ S, ∀ y ∈ T, ⟪x, y⟫_ℂ = 0 := by
  haveI := hT.1
  let Q : S →L[ℂ] H := T.starProjection.comp S.subtypeL
  by_cases hQ : Q = 0
  · intro x hx y hy
    have h1 : T.starProjection x = 0 := congrArg (fun A : S →L[ℂ] H => A ⟨x, hx⟩) hQ
    have h2 := T.starProjection_inner_eq_zero x y hy
    rwa [h1, sub_zero] at h2
  exfalso
  have hR := FormF.rangeType n ε Λ H σ S H σ Q hS (fun k hk x y hxy => by
    change T.starProjection (y : H) = σ k (T.starProjection (x : H))
    rw [hxy, proj_comm hU hT.2.1 hk]) hQ
  have hle : LinearMap.range (Q : S →ₗ[ℂ] H) ≤ T := by
    rintro _ ⟨x, rfl⟩
    exact T.starProjection_apply_mem _
  obtain ⟨v, hv, hv0, hvw⟩ := hR.2.2.2.1
  rcases hT.2.2.1 _ hle hR.2.1 with h | h
  · rw [h] at hv
    exact hv0 hv
  · obtain ⟨w, hw, hw0, hww⟩ := hT.2.2.2.1
    refine hne (GlobalTheory.LowHW.cdom_antisymm (ε := ε) (hR.2.2.2.2 μ w (h ▸ hw) hw0 hww)
      (hT.2.2.2.2 Λ v (hle hv) hv0 hvw))

theorem exists_orth (hU : IsURepOn (Kset ε) σ) {Λ : Fin n → ℝ} {S T : Submodule ℂ H}
    (hS : IsKTypeOf ε σ Λ S) (hT : IsKTypeOf ε σ Λ T) (hne : S ≠ T) :
    ∃ R : Submodule ℂ H, IsKTypeOf ε σ Λ R ∧ ∀ x ∈ R, ∀ y ∈ T, ⟪x, y⟫_ℂ = 0 := by
  haveI := hT.1
  let Q : S →L[ℂ] H := S.subtypeL - T.starProjection.comp S.subtypeL
  have hQa : ∀ x : S, Q x = (x : H) - T.starProjection (x : H) := fun x => rfl
  have hQ : Q ≠ 0 := by
    intro hQ
    have hle : S ≤ T := by
      intro x hx
      have h1 := hQa ⟨x, hx⟩
      rw [hQ] at h1
      have h2 : x = T.starProjection x := sub_eq_zero.1 h1.symm
      rw [h2]
      exact T.starProjection_apply_mem _
    rcases hT.2.2.1 _ hle hS.2.1 with h | h
    · obtain ⟨v, hv, hv0, -⟩ := hS.2.2.2.1
      rw [h] at hv
      exact hv0 hv
    · exact hne h
  refine ⟨_, FormF.rangeType n ε Λ H σ S H σ Q hS (fun k hk x y hxy => by
    rw [hQa, hQa, hxy, proj_comm hU hT.2.1 hk, map_sub]) hQ, ?_⟩
  rintro _ ⟨x, rfl⟩ y hy
  exact T.starProjection_inner_eq_zero x y hy

theorem exists_gap {lam : Fin n → ℝ} (hl : StrictAnti lam)
    (h : ∀ a b : Fin n, ε a ≠ ε b → 2 * (n : ℝ) < |lam a - lam b|) :
    ∃ g : ℝ, (∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) ∧ 2 * (n : ℝ) < g := by
  have key : ∀ᶠ g in nhdsWithin (2 * (n : ℝ)) (Set.Ioi (2 * (n : ℝ))),
      ∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b := by
    simp only [Filter.eventually_all]
    intro a b hab he
    have h1 := h a b he
    rw [abs_of_pos (sub_pos.2 (hl hab))] at h1
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds ((eventually_lt_nhds h1).mono fun g hg => hg.le)
  exact (key.and self_mem_nhdsWithin).exists

theorem kSpan_smul_le {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (c : ℂ)
    (u : V) : kSpan ε E (c • u) ≤ kSpan ε E u :=
  sInf_le_sInf fun S hS => ⟨S.smul_mem c hS.1, hS.2⟩

theorem cas_mem_cyc {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)
    (u : V) : Cas E u ∈ cyc E u := by
  rw [cyc, Submodule.mem_sInf]
  intro W hW
  simp only [Cas, LinearMap.sum_apply, Module.End.mul_apply]
  exact W.sum_mem fun a _ => W.sum_mem fun b _ => hW.2 _ _ _ (hW.2 _ _ _ hW.1)

theorem cas_kHighest {V : Type} [AddCommGroup V] [Module ℂ V] {E : Fin n → Fin n → Module.End ℂ V}
    (hE : GlRel E) {μ : Fin n → ℝ} {u : V} (hu : KHighest ε E μ u) : KHighest ε E μ (Cas E u) := by
  have hc : ∀ a b, E a b (Cas E u) = Cas E (E a b u) := fun a b =>
    (congrArg (fun A : Module.End ℂ V => A u) ((casCentral _ n ε E hE).1 a b)).symm
  exact ⟨fun a => by rw [hc, hu.1 a, map_smul], fun a b h1 h2 => by rw [hc, hu.2 a b h1 h2, map_zero]⟩

theorem cas_real {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {E : Fin n → Fin n → Module.End ℂ V}
    (hE : GlRel E) (hU : IsUnitary ε E) {μ : Fin n → ℝ} {u : V} (hu : KHighest ε E μ u) (hu0 : u ≠ 0) {c : ℂ}
    (hc : Cas E u = c • u) : ∃ r : ℝ, Cas E u = (r : ℂ) • u := by
  have h := wdCas V n ε E μ u hE hU hu
  rw [hc, inner_smul_right, inner_self_eq_norm_sq_to_K] at h
  generalize ((nsq (μ + rhoC ε) - nsq (rhoC ε)) * ‖u‖ ^ 2 -
      ∑ a, ∑ b, (if ε a = ε b then 0 else ‖E a b u‖ ^ 2) : ℝ) = t at h
  refine ⟨t / ‖u‖ ^ 2, ?_⟩
  have hn : ((‖u‖ : ℝ) : ℂ) ≠ 0 := by simpa using hu0
  rw [hc]
  congr 1
  push_cast
  rw [← h, eq_div_iff (pow_ne_zero 2 hn)]
  rfl

theorem isKTypeOf_lowKSub : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ → (∀ a b : Fin n, ε a ≠ ε b → 2 * (n : ℝ) < |lam a - lam b|) → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) := by
  intro n ε lam H _ _ σ hl hDS hgap
  obtain ⟨hc, -, hU, hirr, -, ⟨S0, hS0⟩, -⟩ := id hDS
  have hK := FormF.URep_K hU
  obtain ⟨V, E, S, hD, hS, hSV⟩ := GlobalTheory.SmoothKType.exists_isDer_kType n ε _ H σ S0 hU hS0
  obtain ⟨hk1, hk2⟩ := GlobalTheory.Jet.KType.kType_iff n ε H σ V E hU hD
  obtain ⟨v, hv, hv0, hvw⟩ := hS.2.2.2.1
  obtain ⟨u, rfl⟩ : ∃ u : V, (u : H) = v := ⟨⟨v, hSV hv⟩, rfl⟩
  have hu0 : u ≠ 0 := fun h => hv0 (by rw [h]; rfl)
  obtain ⟨huH, huS, hufd⟩ := hk2 _ S u hS hSV hv hu0 hvw
  obtain ⟨g, hg1, hg2⟩ := exists_gap hl.1 hgap
  have hm : ∀ x ∈ cyc E u, KHighest ε E (lowK ε lam) x → ∃ c : ℂ, x = c • u :=
    GlobalTheory.Jet.kHighest_eq_smul_of_minus_killed V n ε E lam g u hD.1 hD.2.1 huH hufd hg1 hg2
      (GlobalTheory.Jet.Schmid.mul_vminus_eq_zero n ε H σ V E lam u hl hDS hD huH hufd)
  obtain ⟨c, hcu⟩ := hm _ (cas_mem_cyc E u) (cas_kHighest hD.1 huH)
  obtain ⟨r, hr⟩ := cas_real hD.1 hD.2.1 huH hu0 hcu
  have hdense := GlobalTheory.CycDense.cyc_dense n ε H σ V E _ r u hU hD hirr hu0 huH hufd hr
  obtain ⟨-, -, hst, -, hpc, hcp, hfd⟩ := pfilFacts V n ε E u hD.1
  have huniq : ∀ T : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) T → T = S := by
    intro T hT
    by_contra hne
    obtain ⟨R, hR, hRS⟩ := exists_orth hK hT hS hne
    obtain ⟨w, hw, hw0, -⟩ := hR.2.2.2.1
    refine hw0 (hdense.eq_zero_of_inner_left ℂ fun y hy => ?_)
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨j, hj⟩ := hcp z hz
    haveI := hfd hufd j
    obtain ⟨m, x, μ, hx, -, hsup⟩ := kDecomp V n ε E _ (hfd hufd j) (glRel_kRel ε E hD.1)
      (isUnitary_kUnit ε E hD.2.1) (hst j)
    have hle : pfil ε E u j ≤ LinearMap.ker ((innerSL ℂ w : H →L[ℂ] ℂ).toLinearMap ∘ₗ V.subtype) := by
      rw [← hsup]
      refine iSup_le fun i y hy => ?_
      change ⟪w, (y : H)⟫_ℂ = 0
      by_cases hμ : μ i = lowK ε lam
      · obtain ⟨d, hd⟩ := hm (x i) (hpc j (hx i).1) (hμ ▸ (hx i).2.2)
        rw [hd] at hy
        exact hRS w hw _ (huS ▸ ⟨y, kSpan_smul_le E d u hy, rfl⟩)
      · have hfi : FiniteDimensional ℂ (kSpan ε E (x i)) :=
          Submodule.finiteDimensional_of_le (S₂ := pfil ε E u j) (sInf_le ⟨(hx i).1, hst j⟩)
        exact orth_of_ne hK hR (hk1 _ _ (hx i).2.1 (hx i).2.2 hfi) hμ w hw _ ⟨y, hy, rfl⟩
    exact hle hj
  have : lowKSub ε lam σ = S := le_antisymm (sSup_le fun T hT => (huniq T hT).le) (le_sSup hS)
  rw [this]
  exact hS

end GlobalTheory.Jet.MultGap
