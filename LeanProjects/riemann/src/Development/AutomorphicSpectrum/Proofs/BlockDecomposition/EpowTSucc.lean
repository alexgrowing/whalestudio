import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.Ibp

variable {n : ℕ}

theorem isOpen_GLs : IsOpen (GLs n) := by
  exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const

theorem val_mem (y : G n) : y.val ∈ GLs n := by
  show Matrix.det y.val ≠ 0
  exact (Matrix.isUnits_det_units y).ne_zero

section Loc

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_congr (X : Mat n) {f g : Mat n → V} (h : Set.EqOn f g (GLs n)) :
    Set.EqOn (Rd X f) (Rd X g) (GLs n) := by
  intro y hy
  show fderiv ℝ f y (y * X) = fderiv ℝ g y (y * X)
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hy) h)]

theorem Eu_congr (s : Bool) (a b : Fin n) {f g : Mat n → V} (h : Set.EqOn f g (GLs n)) :
    Set.EqOn (Eu s a b f) (Eu s a b g) (GLs n) := by
  intro y hy
  unfold Eu
  simp only [Pi.smul_apply, Pi.add_apply]
  rw [Rd_congr _ h hy, Rd_congr _ h hy]

theorem diffAt {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {y : Mat n} (hy : y ∈ GLs n) :
    DifferentiableAt ℝ f y :=
  (hf.contDiffAt (isOpen_GLs.mem_nhds hy)).differentiableAt (by simp)

theorem Rd_add (X : Mat n) {f g : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hg : ContDiffOn ℝ ∞ g (GLs n)) : Set.EqOn (Rd X (f + g)) (Rd X f + Rd X g) (GLs n) := by
  intro y hy
  have e := (((diffAt hf hy).hasFDerivAt).add ((diffAt hg hy).hasFDerivAt)).fderiv
  show fderiv ℝ (f + g) y (y * X) = fderiv ℝ f y (y * X) + fderiv ℝ g y (y * X)
  exact congrArg (fun L => L (y * X)) e

theorem sm_sum {ι : Type} (t : Finset ι) (F : ι → Mat n → V)
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (GLs n)) : ContDiffOn ℝ ∞ (∑ i ∈ t, F i) (GLs n) := by
  rw [Finset.sum_fn]
  exact ContDiffOn.sum fun i _ => hF i

theorem Rd_zero (X : Mat n) : Rd X (0 : Mat n → V) = 0 := by
  funext y
  simp [Rd]

theorem Eu_zero (s : Bool) (a b : Fin n) : Eu s a b (0 : Mat n → V) = 0 := by
  simp [Eu, Rd_zero]

theorem Eu_add (s : Bool) (a b : Fin n) {f g : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hg : ContDiffOn ℝ ∞ g (GLs n)) :
    Set.EqOn (Eu s a b (f + g)) (Eu s a b f + Eu s a b g) (GLs n) := by
  intro y hy
  unfold Eu
  simp only [Pi.smul_apply, Pi.add_apply]
  rw [Rd_add _ hf hg hy, Rd_add _ hf hg hy]
  simp only [Pi.add_apply, smul_add]
  abel

theorem Eu_sum (s : Bool) (a b : Fin n) {ι : Type} (t : Finset ι) (F : ι → Mat n → V)
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (GLs n)) :
    Set.EqOn (Eu s a b (∑ i ∈ t, F i)) (∑ i ∈ t, Eu s a b (F i)) (GLs n) := by
  classical
  induction t using Finset.induction_on with
  | empty => intro y _; simp [Eu_zero]
  | insert i t hi ih =>
    intro y hy
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      Eu_add s a b (hF i) (sm_sum t F hF) hy]
    simp only [Pi.add_apply, ih hy]

theorem Cpt_zero : Cpt (0 : Mat n → V) := ⟨0, fun _ _ _ => rfl⟩

theorem Cpt_add {f g : Mat n → V} (hf : Cpt f) (hg : Cpt g) : Cpt (f + g) := by
  obtain ⟨R1, h1⟩ := hf
  obtain ⟨R2, h2⟩ := hg
  refine ⟨max R1 R2, fun y hy hR => ?_⟩
  rw [Pi.add_apply, h1 y hy (lt_of_le_of_lt (le_max_left _ _) hR),
    h2 y hy (lt_of_le_of_lt (le_max_right _ _) hR), add_zero]

theorem Cpt_smul (c : ℂ) {f : Mat n → V} (hf : Cpt f) : Cpt (c • f) := by
  obtain ⟨R, h⟩ := hf
  exact ⟨R, fun y hy hR => by rw [Pi.smul_apply, h y hy hR, smul_zero]⟩

theorem Cpt_sum {ι : Type} (t : Finset ι) (F : ι → Mat n → V) (hF : ∀ i, Cpt (F i)) :
    Cpt (∑ i ∈ t, F i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using Cpt_zero
  | insert i t hi ih =>
    rw [Finset.sum_insert hi]
    exact Cpt_add (hF i) ih

theorem Cpt_Rd (hL : LgFacts) (X : Mat n) {f : Mat n → V} (hf : Cpt f) : Cpt (Rd X f) := by
  obtain ⟨R, hR⟩ := hf
  refine ⟨R, fun y hy hy' => ?_⟩
  have hc : ContinuousOn lg (GLs n) := ((hL n).2.2.2.1).continuousOn
  have hev : f =ᶠ[nhds y] (fun _ => (0 : V)) := by
    have h1 : ∀ᶠ z in nhds y, z ∈ GLs n := isOpen_GLs.mem_nhds hy
    have h2 : ∀ᶠ z in nhds y, R < lg z :=
      (hc.continuousAt (isOpen_GLs.mem_nhds hy)).preimage_mem_nhds (Ioi_mem_nhds hy')
    filter_upwards [h1, h2] with z hz1 hz2
    exact hR z hz1 hz2
  show fderiv ℝ f y (y * X) = 0
  rw [hev.fderiv_eq]
  simp

theorem Cpt_Eu (hL : LgFacts) (s : Bool) (a b : Fin n) {f : Mat n → V} (hf : Cpt f) :
    Cpt (Eu s a b f) :=
  Cpt_smul _ (Cpt_add (Cpt_Rd hL _ hf) (Cpt_smul _ (Cpt_Rd hL _ hf)))

theorem sm_Rd (hR : RCalc) (X : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Rd X f) (GLs n) :=
  ((hR n).1 V f hf).1 X

theorem sm_Eu (hR : RCalc) (s : Bool) (a b : Fin n) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) : ContDiffOn ℝ ∞ (Eu s a b f) (GLs n) :=
  ((sm_Rd hR _ hf).add ((sm_Rd hR _ hf).const_smul _)).const_smul _

theorem sm_Epow (hR : RCalc) (s : Bool) (m : ℕ) (a b : Fin n) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) : ContDiffOn ℝ ∞ (Epow s m a b f) (GLs n) := by
  induction m generalizing a b with
  | zero =>
    rw [Epow.eq_1]
    dsimp only
    split_ifs
    · exact hf
    · exact contDiffOn_const
  | succ m ih =>
    show ContDiffOn ℝ ∞ (Epow s (Nat.succ m) a b f) (GLs n)
    rw [Epow.eq_2]
    exact sm_sum _ _ fun c => sm_Eu hR _ _ _ (ih _ _)

theorem sm_EpowT (hR : RCalc) (s : Bool) (m : ℕ) (a b : Fin n) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) : ContDiffOn ℝ ∞ (EpowT s m a b f) (GLs n) := by
  induction m generalizing a b with
  | zero =>
    rw [EpowT.eq_1]
    dsimp only
    split_ifs
    · exact hf
    · exact contDiffOn_const
  | succ m ih =>
    show ContDiffOn ℝ ∞ (EpowT s (Nat.succ m) a b f) (GLs n)
    rw [EpowT.eq_2]
    exact sm_sum _ _ fun c => sm_Eu hR _ _ _ (ih _ _)

theorem Cpt_Epow (hL : LgFacts) (s : Bool) (m : ℕ) (a b : Fin n) {f : Mat n → V} (hf : Cpt f) :
    Cpt (Epow s m a b f) := by
  induction m generalizing a b with
  | zero =>
    rw [Epow.eq_1]
    dsimp only
    split_ifs
    · exact hf
    · exact Cpt_zero
  | succ m ih =>
    show Cpt (Epow s (Nat.succ m) a b f)
    rw [Epow.eq_2]
    exact Cpt_sum _ _ fun c => Cpt_Eu hL _ _ _ (ih _ _)

theorem EpowT_succ' (hR : RCalc) (s : Bool) (m : ℕ) (a b : Fin n) {h : Mat n → V}
    (hh : ContDiffOn ℝ ∞ h (GLs n)) :
    Set.EqOn (EpowT s (m + 1) b a h) (∑ c, EpowT s m b c (Eu s a c h)) (GLs n) := by
  induction m generalizing b with
  | zero =>
    intro y _
    show EpowT s (Nat.succ 0) b a h y = _
    rw [EpowT.eq_2]
    simp only [EpowT.eq_1, Finset.sum_apply]
    rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
    all_goals first
      | (simp; done)
      | (intro c _ hc; simp [hc, Ne.symm hc, Eu_zero])
  | succ m ih =>
    intro y hy
    show EpowT s (Nat.succ (m + 1)) b a h y = _
    rw [EpowT.eq_2]
    simp only [Finset.sum_apply]
    have key : ∀ c, Eu s c b (EpowT s (m + 1) c a h) y =
        ∑ d, Eu s c b (EpowT s m c d (Eu s a d h)) y := by
      intro c
      rw [Eu_congr s c b (ih c) hy,
        Eu_sum s c b Finset.univ _ (fun d => sm_EpowT hR s m c d (sm_Eu hR s a d hh)) hy,
        Finset.sum_apply]
    rw [Finset.sum_congr rfl (fun c _ => key c), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    show _ = EpowT s (Nat.succ m) b d (Eu s a d h) y
    simp only [EpowT.eq_2, Finset.sum_apply]

end Loc

end GlobalTheory.CompanionTheory.WaveMult.Ibp
