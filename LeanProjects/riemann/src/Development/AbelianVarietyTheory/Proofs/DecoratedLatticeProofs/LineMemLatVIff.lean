import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpImageIntegralMatrixMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeWithPrescribedSplitComponen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitLine

open GlobalTheory.FinPl GlobalTheory.FinPl.FrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_ofSplit (q : SplitPt D k) (x : D.host.E) : (ofSplit q).pr x = q.pr (incA D x) := rfl

theorem eq_sec_add_cA (q : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = q.v)) :
    a = q.sec (q.pr a) + cA D (q.sec (q.pr (cA D a))) := by
  rw [q.sec_pr, q.sec_pr, RingHom.map_mul, cA_cA, ← add_mul, (idem_iff q a).1 ha]

theorem pr_mem_of_int (q : SplitPt D k) {a : AE D} (ha : finPart D a ∈ intAE D) : q.pr a ∈ 𝒪[k] := by
  rw [q.int_iff, q.sec_pr, RingHom.map_mul]
  exact mul_mem_intAE (e_mem_intAt q).2 ha

theorem mem_intAt_iff_pr (q : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = q.v)) :
    a ∈ intAt D (· = q.v) ↔ q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k] := by
  refine ⟨fun h => ⟨pr_mem_of_int q h.2, pr_mem_of_int q ((cA_int_iff a).2 h.2)⟩, fun h => ⟨ha, ?_⟩⟩
  rw [eq_sec_add_cA q ha, RingHom.map_add]
  exact add_mem ((q.int_iff _).1 h.1) ((cA_int_iff _).2 ((q.int_iff _).1 h.2))

theorem single_int {Y' : Type} [DecidableEq Y'] (m₁ : Y') (i : Y') : (Pi.single m₁ (1 : k) : Y' → k) i ∈ 𝒪[k] := by
  by_cases hi : i = m₁
  · subst hi; rw [Pi.single_eq_same]; exact one_mem _
  · rw [Pi.single_eq_of_ne hi]; exact zero_mem _

variable {Y : Type} [Fintype Y] [DecidableEq Y]

theorem wpart {q : SplitPt D k} {S : HSp D} {L : Lat S} {F : Frame k S.rank Y} {u : Fin S.rank → D.host.E} {c : k} {m₀ : Y}
    (hI : IntIn q S F L) (hc : valuation k c = 1) (hu : ∀ r, c * (ofSplit q).pr (u r) = F.β r m₀) (x : k) :
    (fun r => q.sec (x * (ofSplit q).pr (u r))) ∈ latV S L (· = q.v) ↔ x ∈ 𝒪[k] := by
  have hc0 : c ≠ 0 := by rintro rfl; rw [map_zero] at hc; exact zero_ne_one hc
  have e : (fun r => q.sec (x * (ofSplit q).pr (u r))) =
      fun r => q.sec ((F.β *ᵥ Pi.single m₀ (x / c)) r) := by
    funext r
    congr 1
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single m₀ (fun b _ hb => by rw [Pi.single_eq_of_ne hb, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same, ← hu r]
    field_simp
  rw [e, ← hI (Pi.single m₀ (x / c))]
  constructor
  · intro h
    have h1 := h m₀
    rw [Pi.single_eq_same, Valuation.mem_integer_iff, map_div₀, hc, div_one] at h1
    exact (Valuation.mem_integer_iff _ _).2 h1
  · intro h i
    by_cases hi : i = m₀
    · subst hi
      rw [Pi.single_eq_same, Valuation.mem_integer_iff, map_div₀, hc, div_one]
      exact (Valuation.mem_integer_iff _ _).1 h
    · rw [Pi.single_eq_of_ne hi]; exact zero_mem _

theorem wbar {q : SplitPt D k} {S : HSp D} {L : Lat S} {F : Frame k S.rank Y} {u : Fin S.rank → D.host.E}
    (hL : IsSelfDualC S L) (hI : IntIn q S F L)
    (hb : ∀ m, ∑ r, F.β r m * (ofSplit q).pr (star ((S.gram *ᵥ u) r)) ∈ 𝒪[k])
    (hb1 : ∃ m, valuation k (∑ r, F.β r m * (ofSplit q).pr (star ((S.gram *ᵥ u) r))) = 1) (A : k) :
    (fun r => cA D (q.sec (A * (ofSplit q).pr (star (u r))))) ∈ latV S L (· = q.v) ↔ A ∈ 𝒪[k] := by
  have ht : ∀ i, (ofSplit q).pr (star ((S.gram *ᵥ u) i)) =
      ∑ j, q.pr (cA D (incA D (S.gram i j))) * (ofSplit q).pr (star (u j)) := by
    intro i
    simp only [pr_ofSplit, Matrix.mulVec, dotProduct, star_sum, star_mul', map_sum, map_mul, cA_incA]
  have hsum : ∀ x : Fin S.rank → k,
      ∑ i, ∑ j, x i * q.pr (cA D (incA D (S.gram i j))) * (A * (ofSplit q).pr (star (u j))) =
      A * ∑ m, (F.γ *ᵥ x) m * ∑ r, F.β r m * (ofSplit q).pr (star ((S.gram *ᵥ u) r)) := by
    intro x
    have h1 : ∑ i, ∑ j, x i * q.pr (cA D (incA D (S.gram i j))) * (A * (ofSplit q).pr (star (u j))) =
        A * ∑ i, x i * (ofSplit q).pr (star ((S.gram *ᵥ u) i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ht i, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h1]
    congr 1
    have hx : x = F.β *ᵥ (F.γ *ᵥ x) := by rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
    generalize F.γ *ᵥ x = y at hx ⊢
    subst hx
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun r _ => ?_)
    ring
  rw [csec_mem_iff hL]
  simp only [hsum]
  obtain ⟨m₁, hm₁⟩ := hb1
  constructor
  · intro h
    have hx : (fun i => q.sec ((F.β *ᵥ Pi.single m₁ (1 : k)) i)) ∈ latV S L (· = q.v) :=
      (hI _).1 (single_int (k := k) m₁)
    have h2 := h _ hx
    rw [Matrix.mulVec_mulVec, F.γβ, Matrix.one_mulVec,
      Finset.sum_eq_single m₁ (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_mul])
        (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same, one_mul,
      Valuation.mem_integer_iff, map_mul, hm₁, mul_one] at h2
    exact (Valuation.mem_integer_iff _ _).2 h2
  · intro hA x hx
    have hy := (hI (F.γ *ᵥ x)).2 (by rwa [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec])
    exact mul_mem hA (sum_mem fun m _ => mul_mem (hy m) (hb m))

theorem line_mem_latV_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (Y : Type) [Fintype Y] [DecidableEq Y]
    (F : Frame k S.rank Y) (u : Fin S.rank → D.host.E) (c : k) (m₀ : Y),
    IsSelfDualC S L → IntIn q S F L → valuation k c = 1 → (∀ r, c * (ofSplit q).pr (u r) = F.β r m₀) →
    (∀ m, ∑ r, F.β r m * (ofSplit q).pr (star ((S.gram *ᵥ u) r)) ∈ 𝒪[k]) →
    (∃ m, valuation k (∑ r, F.β r m * (ofSplit q).pr (star ((S.gram *ᵥ u) r))) = 1) →
    ∀ a ∈ GlobalTheory.FinPl.idAt D (· = q.v),
      ((fun r => a * incA D (u r)) ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = q.v)) := by
  intro D k _ _ _ _ q S L Y _ _ F u c m₀ hL hI hc hu hb hb1 a ha
  have hy : (fun r => a * incA D (u r)) = (fun r => q.sec (q.pr a * (ofSplit q).pr (u r))) +
      (fun r => cA D (q.sec (q.pr (cA D a) * (ofSplit q).pr (star (u r))))) := by
    funext r
    rw [Pi.add_apply]
    conv_lhs => rw [eq_sec_add_cA q ha]
    rw [add_mul, sec_mul_right]
    congr 1
    have e : incA D (u r) = cA D (incA D (star (u r))) := by rw [cA_incA, star_star]
    rw [e, ← RingHom.map_mul, sec_mul_right]
    rfl
  rw [hy]
  refine (decomp hL (fun r => q.pr a * (ofSplit q).pr (u r))
    (fun r => q.pr (cA D a) * (ofSplit q).pr (star (u r)))).trans ?_
  rw [mem_intAt_iff_pr q ha]
  exact and_congr (wpart hI hc hu _) (wbar hL hI hb hb1 _)

end GlobalTheory.SplitLine

end
