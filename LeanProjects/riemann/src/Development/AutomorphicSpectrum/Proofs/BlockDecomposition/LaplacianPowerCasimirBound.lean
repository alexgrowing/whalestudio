import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevOperatorFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionNormBound

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.LapSec

open GlobalTheory.CompanionTheory.FcSmooth (Lap)
open GlobalTheory.CompanionTheory.SobSecK (Rw_congr Rw_smooth)
open GlobalTheory.CompanionTheory.SobOpsPf (Rw_add Rw_post sob_congr sob_smul sob_sum sob_bs sob_Om sob_post Om_smooth)

variable {n : ℕ}

section Words

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Lap_eq (f : Mat n → V) (g : Mat n) : Lap f g = -∑ p, Rw [p, p] f g := rfl

theorem Lap_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) : ContDiffOn ℝ ∞ (Lap f) (GLs n) := by
  have h : ContDiffOn ℝ ∞ (fun g => ∑ p, Rw [p, p] f g) (GLs n) :=
    ContDiffOn.sum fun p _ => Rw_smooth [p, p] hf
  exact h.neg

theorem Lap_congr {f f' : Mat n → V} (e : Set.EqOn f f' (GLs n)) : Set.EqOn (Lap f) (Lap f') (GLs n) := by
  intro g hg
  simp only [Lap_eq]
  exact congrArg Neg.neg (Finset.sum_congr rfl fun p _ => Rw_congr [p, p] e hg)

theorem Lap_add {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n)) :
    Set.EqOn (Lap (f + f')) (Lap f + Lap f') (GLs n) := by
  intro g hg
  simp only [Lap_eq, Pi.add_apply]
  rw [← neg_add, ← Finset.sum_add_distrib]
  exact congrArg Neg.neg (Finset.sum_congr rfl fun p _ => Rw_add [p, p] hf hf' hg)

theorem Lap_post (A : V →L[ℂ] V) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Lap fun y => A (f y)) (fun y => A (Lap f y)) (GLs n) := by
  intro g hg
  simp only [Lap_eq, map_neg, map_sum]
  exact congrArg Neg.neg (Finset.sum_congr rfl fun p _ => Rw_post [p, p] A hf hg)

theorem iter_smooth (j : ℕ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Lap^[j] f) (GLs n) := by
  induction j generalizing f with
  | zero => exact hf
  | succ j ih => exact ih (Lap_smooth hf)

theorem iter_congr (j : ℕ) {f f' : Mat n → V} (e : Set.EqOn f f' (GLs n)) :
    Set.EqOn (Lap^[j] f) (Lap^[j] f') (GLs n) := by
  induction j generalizing f f' with
  | zero => exact e
  | succ j ih => exact ih (Lap_congr e)

theorem iter_add (j : ℕ) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hf' : ContDiffOn ℝ ∞ f' (GLs n)) :
    Set.EqOn (Lap^[j] (f + f')) (Lap^[j] f + Lap^[j] f') (GLs n) := by
  induction j generalizing f f' with
  | zero => intro x _; rfl
  | succ j ih =>
    intro x hx
    exact (iter_congr j (Lap_add hf hf') hx).trans (ih (Lap_smooth hf) (Lap_smooth hf') hx)

end Words

section Sob

variable [MeasurableSpace (G n)] {μ : Measure (G n)} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem sob_Lap {f : Mat n → V} (hf : Sob μ f) : Sob μ (Lap f) :=
  sob_congr (f := (-1 : ℂ) • ∑ p, Rd (bs p) (Rd (bs p) f))
    (sob_smul _ (sob_sum _ hf fun p => sob_bs p (sob_bs p hf))) fun g _ => by
      simp [Lap]

theorem sob_iter (j : ℕ) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Lap^[j] f) := by
  induction j generalizing f with
  | zero => exact hf
  | succ j ih => exact ih (sob_Lap hf)

theorem cls_add {F F' : Mat n → V} (h : MemLp (fun y : G n => F y.val) 2 μ)
    (h' : MemLp (fun y : G n => F' y.val) 2 μ) : cls μ (F + F') = cls μ F + cls μ F' := by
  rw [GlobalTheory.CompanionTheory.SecBd.cls_eq μ h, GlobalTheory.CompanionTheory.SecBd.cls_eq μ h', GlobalTheory.CompanionTheory.SecBd.cls_eq μ (f := F + F') (h.add h')]
  exact MemLp.toLp_add h h'

end Sob

theorem om_mem (hR : RCalc) (E : KMod n) {f : Mat n → E.V} (hf : f ∈ CE E) : Om f ∈ CE E := by
  have h1 := (hR n).2.1 E f hf true 2
  have h2 := (hR n).2.1 E f hf false 2
  refine ⟨Om_smooth hf.1, fun g hg k => ?_⟩
  simp only [Om, Pi.smul_apply, Pi.add_apply, h1.2 g hg k, h2.2 g hg k, map_add, map_smul]

theorem strong [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) (Q : E.V →L[ℂ] E.V) (hR : RCalc)
    (hL : ∀ f ∈ CE E, ∀ g ∈ GLs n, Lap f g = -Om f g + Q (f g)) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Mat n → E.V, Sob μ f → IsSec E f → ∀ B : E.V →L[ℂ] E.V,
      ‖cls μ (Lap^[j] fun y => B (f y))‖ ≤ C * ‖B‖ * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f)‖ := by
  induction j with
  | zero =>
    refine ⟨1, zero_le_one, fun f hS _ B => ?_⟩
    have hm : MemLp (fun y : G n => B (f y.val)) 2 μ := (sob_post B hS).2 []
    have h := GlobalTheory.CompanionTheory.SecBd.norm_le_of_ae μ (f := f) (hS.2 []) (cls μ fun y => B (f y)) B
      (GlobalTheory.CompanionTheory.SecBd.cls_ae μ hm)
    simpa using h
  | succ j ih =>
    obtain ⟨C, hC, ih⟩ := ih
    refine ⟨C * (1 + ‖Q‖), by positivity, fun f hS hsec B => ?_⟩
    have hCE : f ∈ CE E := ⟨hS.1, hsec⟩
    have hOS := sob_Om hS
    have hOC := om_mem hR E hCE
    let a : Mat n → E.V := fun y => (-B) (Om f y)
    let b : Mat n → E.V := fun y => (B * Q) (f y)
    have ha : Sob μ a := sob_post _ hOS
    have hb : Sob μ b := sob_post _ hS
    have e1 : Set.EqOn (Lap fun y => B (f y)) (a + b) (GLs n) := fun g hg => by
      refine (Lap_post B hS.1 hg).trans ?_
      show B (Lap f g) = (-B) (Om f g) + (B * Q) (f g)
      rw [hL f hCE g hg]
      simp
    have e2 : Set.EqOn (Lap^[j + 1] fun y => B (f y)) (Lap^[j] a + Lap^[j] b) (GLs n) := fun g hg =>
      (iter_congr j e1 hg).trans (iter_add j ha.1 hb.1 hg)
    have mA : MemLp (fun y : G n => (Lap^[j] a) y.val) 2 μ := (sob_iter j ha).2 []
    have mB : MemLp (fun y : G n => (Lap^[j] b) y.val) 2 μ := (sob_iter j hb).2 []
    have e3 : cls μ (Lap^[j + 1] fun y => B (f y)) = cls μ (Lap^[j] a) + cls μ (Lap^[j] b) := by
      rw [← cls_add mA mB]
      exact (GlobalTheory.CompanionTheory.SecBd.cls_congr μ (f := Lap^[j] a + Lap^[j] b) (mA.add mB)
        fun g hg => (e2 hg).symm).symm
    have b1 : ‖cls μ (Lap^[j] a)‖ ≤ C * ‖-B‖ * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] (Om f))‖ :=
      ih (Om f) hOS hOC.2 (-B)
    have b2 : ‖cls μ (Lap^[j] b)‖ ≤ C * ‖B * Q‖ * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f)‖ :=
      ih f hS hsec (B * Q)
    set S := ∑ i ∈ range (j + 1 + 1), ‖cls μ (Om^[i] f)‖ with hSdef
    have s1 : ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] (Om f))‖ ≤ S := by
      have e := Finset.sum_range_succ' (fun i => ‖cls μ (Om^[i] f)‖) (j + 1)
      rw [hSdef, e]
      exact le_add_of_nonneg_right (norm_nonneg _)
    have s2 : ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f)‖ ≤ S := by
      rw [hSdef, Finset.sum_range_succ _ (j + 1)]
      exact le_add_of_nonneg_right (norm_nonneg _)
    have hBQ : ‖B * Q‖ ≤ ‖B‖ * ‖Q‖ := norm_mul_le _ _
    have c1 : C * ‖-B‖ * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] (Om f))‖ ≤ C * ‖B‖ * S := by
      rw [norm_neg]
      exact mul_le_mul_of_nonneg_left s1 (by positivity)
    have c2 : C * ‖B * Q‖ * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f)‖ ≤ C * (‖B‖ * ‖Q‖) * S := by
      have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
      exact mul_le_mul (mul_le_mul_of_nonneg_left hBQ hC) s2
        (Finset.sum_nonneg fun _ _ => norm_nonneg _) (by positivity)
    rw [e3]
    calc _ ≤ ‖cls μ (Lap^[j] a)‖ + ‖cls μ (Lap^[j] b)‖ := norm_add_le _ _
      _ ≤ C * ‖B‖ * S + C * (‖B‖ * ‖Q‖) * S := add_le_add (b1.trans c1) (b2.trans c2)
      _ = C * (1 + ‖Q‖) * ‖B‖ * S := by ring

theorem sectionBound : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (Q : E.V →L[ℂ] E.V), LgFacts → Unimod → RCalc → ClsFacts →
    (∀ f ∈ CE E, ∀ g ∈ GLs n, GlobalTheory.CompanionTheory.FcSmooth.Lap f g = -Om f g + Q (f g)) →
    ∀ j : ℕ, ∃ C : ℝ, ∀ f : Mat n → E.V, Sob μ f → IsSec E f →
      ‖cls μ (GlobalTheory.CompanionTheory.FcSmooth.Lap^[j] f)‖ ≤ C * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f)‖ := by
  intro n _ _ μ _ E Q _ _ hR _ hL j
  obtain ⟨C, -, h⟩ := strong μ E Q hR hL j
  refine ⟨C * ‖(1 : E.V →L[ℂ] E.V)‖, fun f hS hs => ?_⟩
  simpa only [ContinuousLinearMap.one_apply] using h f hS hs 1

end GlobalTheory.CompanionTheory.LapSec
