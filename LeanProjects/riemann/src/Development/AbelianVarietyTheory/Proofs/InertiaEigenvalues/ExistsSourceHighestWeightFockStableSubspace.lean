import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKHwMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.NHwExist

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LowestKType GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators MvPolynomial

variable {D : D7} {n m : ℕ}

lemma sop_eq (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin n) :
    (sop w τ a b : Module.End ℂ (PolF D m n)) =
      ∑ i, (raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) i a *
        lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) i b +
        if a = b then (1 / 2 : ℂ) • 1 else 0) := by
  classical
  unfold GlobalTheory.LowestKType.sop GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp

lemma term_lt (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin n) (i : Fin m) (hi : (i : ℕ) < w.p τ)
    (P : PolF D m n) :
    (raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) i a *
        lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) i b) P =
      X (τ, i, a) * pderiv (τ, i, b) P := by
  classical
  simp [raiO, lowO, sgn, hi]

lemma term_ge (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin n) (i : Fin m) (hi : ¬ (i : ℕ) < w.p τ)
    (P : PolF D m n) :
    (raiO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) i a *
        lowO τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) i b) P =
      -(pderiv (τ, i, a) (X (τ, i, b) * P)) := by
  classical
  simp [raiO, lowO, sgn, hi]

lemma mono1 (u v : FVar D m n) (α : FVar D m n →₀ ℕ) (c : ℂ) :
    (X u * pderiv v (monomial α c) : PolF D m n) = monomial (Finsupp.single u 1 + (α - Finsupp.single v 1)) (c * α v) := by
  classical
  rw [pderiv_monomial, X, monomial_mul, one_mul]

lemma mono2 (u v : FVar D m n) (α : FVar D m n →₀ ℕ) (c : ℂ) :
    (pderiv u (X v * monomial α c) : PolF D m n) =
      monomial (Finsupp.single v 1 + α - Finsupp.single u 1) (c * ((Finsupp.single v 1 + α : FVar D m n →₀ ℕ) u)) := by
  classical
  rw [X, monomial_mul, one_mul, pderiv_monomial]

def lamM (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a : Fin n) (α : FVar D m n →₀ ℕ) : ℂ :=
  ∑ i : Fin m, ((if (i : ℕ) < w.p τ then (α (τ, i, a) : ℂ) else -((α (τ, i, a) : ℂ) + 1)) + 1 / 2)

lemma diag_X (v : FVar D m n) (α : FVar D m n →₀ ℕ) (c : ℂ) :
    (X v * pderiv v (monomial α c) : PolF D m n) = (α v : ℂ) • monomial α c := by
  classical
  rw [mono1]
  by_cases h : α v = 0
  · simp [h]
  · have : Finsupp.single v 1 + (α - Finsupp.single v 1) = α := by
      rw [add_comm]; exact tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h))
    rw [this, smul_monomial, smul_eq_mul, mul_comm]

lemma diag_D (v : FVar D m n) (α : FVar D m n →₀ ℕ) (c : ℂ) :
    (pderiv v (X v * monomial α c) : PolF D m n) = ((α v : ℂ) + 1) • monomial α c := by
  classical
  rw [mono2, add_tsub_cancel_left, smul_monomial]
  simp [Finsupp.single_apply]
  ring_nf

lemma sop_diag (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a : Fin n) (α : FVar D m n →₀ ℕ) (c : ℂ) :
    sop w τ a a (monomial α c : PolF D m n) = lamM w τ a α • monomial α c := by
  classical
  rw [sop_eq, LinearMap.sum_apply]
  unfold lamM
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.add_apply]
  by_cases hi : (i : ℕ) < w.p τ
  · rw [term_lt w τ a a i hi, diag_X]
    simp [hi, add_smul]
  · rw [term_ge w τ a a i hi, diag_D]
    simp [hi, add_smul, neg_smul]

lemma coeff_sop_diag (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a : Fin n) (P : PolF D m n)
    (β : FVar D m n →₀ ℕ) : coeff β (sop w τ a a P) = lamM w τ a β * coeff β P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [sop_diag, coeff_smul, coeff_monomial, smul_eq_mul]
    split_ifs with h
    · rw [h]
    · simp
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

def gV (w : GlobalTheory.ExportSeries.Weight D n) (v : FVar D m n) : ℤ :=
  (if (v.2.1 : ℕ) < w.p v.1 then 1 else -1) * ((n : ℤ) - (v.2.2 : ℕ))

def ht (w : GlobalTheory.ExportSeries.Weight D n) (α : FVar D m n →₀ ℕ) : ℤ := ∑ v, gV w v * (α v : ℤ)

lemma ht_add (w : GlobalTheory.ExportSeries.Weight D n) (α β : FVar D m n →₀ ℕ) : ht w (α + β) = ht w α + ht w β := by
  unfold ht; simp [mul_add, Finset.sum_add_distrib]

lemma ht_single (w : GlobalTheory.ExportSeries.Weight D n) (u : FVar D m n) : ht w (Finsupp.single u 1) = gV w u := by
  classical
  unfold ht; simp [Finsupp.single_apply]

lemma ht_sub (w : GlobalTheory.ExportSeries.Weight D n) (α : FVar D m n →₀ ℕ) (v : FVar D m n) (h : 1 ≤ α v) :
    ht w (α - Finsupp.single v 1) = ht w α - gV w v := by
  have e : α - Finsupp.single v 1 + Finsupp.single v 1 = α := tsub_add_cancel_of_le (Finsupp.single_le_iff.2 h)
  have h2 := congrArg (ht w) e
  rw [ht_add, ht_single] at h2
  linarith

lemma ht_move (w : GlobalTheory.ExportSeries.Weight D n) (α : FVar D m n →₀ ℕ) (u v : FVar D m n) (h : 1 ≤ α v) :
    ht w (Finsupp.single u 1 + (α - Finsupp.single v 1)) = ht w α + (gV w u - gV w v) := by
  rw [ht_add, ht_single, ht_sub w α v h]; ring

lemma sop_off_mono (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin n) (hab : a ≠ b)
    (α β : FVar D m n →₀ ℕ) (c : ℂ) (hβ : β ∈ (sop w τ a b (monomial α c : PolF D m n)).support) :
    ht w β = ht w α + ((b : ℕ) - (a : ℕ) : ℤ) := by
  classical
  rw [sop_eq, LinearMap.sum_apply] at hβ
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (support_sum hβ)
  rw [LinearMap.add_apply] at hi
  simp only [hab, if_false, LinearMap.zero_apply, add_zero] at hi
  by_cases hp : (i : ℕ) < w.p τ
  · rw [term_lt w τ a b i hp, mono1, support_monomial] at hi
    split_ifs at hi with h0
    · simp at hi
    · rw [Finset.mem_singleton] at hi
      subst hi
      have h1 : 1 ≤ α (τ, i, b) := by
        rcases Nat.eq_zero_or_pos (α (τ, i, b)) with h | h
        · simp [h] at h0
        · exact h
      rw [ht_move w α _ _ h1]
      simp [gV, hp]
  · rw [term_ge w τ a b i hp, support_neg, mono2, support_monomial] at hi
    split_ifs at hi with h0
    · simp at hi
    · rw [Finset.mem_singleton] at hi
      subst hi
      have hne : ((τ, i, b) : FVar D m n) ≠ (τ, i, a) := by
        intro h; apply hab; simp only [Prod.mk.injEq] at h; exact h.2.2.symm
      have hu : ((Finsupp.single ((τ, i, b) : FVar D m n) 1 + α : FVar D m n →₀ ℕ) (τ, i, a)) = α (τ, i, a) := by
        simp [Finsupp.single_apply, hne]
      rw [hu] at h0
      have h1 : 1 ≤ α (τ, i, a) := by
        rcases Nat.eq_zero_or_pos (α (τ, i, a)) with h | h
        · simp [h] at h0
        · exact h
      rw [add_tsub_assoc_of_le (Finsupp.single_le_iff.2 h1), ht_move w α _ _ h1]
      simp [gV, hp]

lemma sop_off (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin n) (hab : a ≠ b)
    (P : PolF D m n) (β : FVar D m n →₀ ℕ) (hβ : β ∈ (sop w τ a b P).support) :
    ∃ α ∈ P.support, ht w β = ht w α + ((b : ℕ) - (a : ℕ) : ℤ) := by
  classical
  rw [as_sum P, map_sum] at hβ
  obtain ⟨α, hα, h⟩ := Finset.mem_biUnion.1 (support_sum hβ)
  exact ⟨α, hα, sop_off_mono w τ a b hab α β _ h⟩

def Pure (w : GlobalTheory.ExportSeries.Weight D n) (Q : PolF D m n) : Prop :=
  ∀ (τ : D.what₂.Tau) (a : Fin n), ∀ α ∈ Q.support, ∀ β ∈ Q.support, lamM w τ a α = lamM w τ a β

def wtZ (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a : Fin n) (α : FVar D m n →₀ ℕ) : ℤ :=
  ∑ i : Fin m, (if (i : ℕ) < w.p τ then (1 : ℤ) else -1) * (α (τ, i, a) : ℤ)

lemma ht_eq (w : GlobalTheory.ExportSeries.Weight D n) (α : FVar D m n →₀ ℕ) :
    ht w α = ∑ τ, ∑ a : Fin n, ((n : ℤ) - (a : ℕ)) * wtZ w τ a α := by
  unfold ht wtZ gV
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma lamM_eq (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a : Fin n) (α : FVar D m n →₀ ℕ) :
    lamM w τ a α = (wtZ w τ a α : ℂ) + ∑ i : Fin m, ((if (i : ℕ) < w.p τ then (0 : ℂ) else -1) + 1 / 2) := by
  unfold lamM wtZ
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

lemma ht_of_lam (w : GlobalTheory.ExportSeries.Weight D n) (α β : FVar D m n →₀ ℕ)
    (h : ∀ τ a, lamM w τ a α = lamM w τ a β) : ht w α = ht w β := by
  rw [ht_eq, ht_eq]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => ?_
  have h1 := h τ a
  rw [lamM_eq, lamM_eq, add_left_inj] at h1
  rw [Int.cast_inj.1 h1]

lemma purify (w : GlobalTheory.ExportSeries.Weight D n) (V : Submodule ℂ (PolF D m n))
    (hV : ∀ P ∈ V, ∀ (τ : D.what₂.Tau) (a b : Fin n), sop w τ a b P ∈ V) :
    ∀ (k : ℕ) (P : PolF D m n), P.support.card ≤ k → P ∈ V → ∀ α0 ∈ P.support,
      ∃ Q ∈ V, α0 ∈ Q.support ∧ Pure w Q := by
  classical
  intro k
  induction k with
  | zero =>
    intro P hc _ α0 hα0
    rw [Nat.le_zero, Finset.card_eq_zero] at hc
    simp [hc] at hα0
  | succ k ih =>
    intro P hc hPV α0 hα0
    by_cases hP : Pure w P
    · exact ⟨P, hPV, hα0, hP⟩
    simp only [Pure, not_forall] at hP
    obtain ⟨τ, a, α, hα, β, hβ, hne⟩ := hP
    obtain ⟨γ, hγ, hγne⟩ : ∃ γ ∈ P.support, lamM w τ a γ ≠ lamM w τ a α0 := by
      by_cases h : lamM w τ a α = lamM w τ a α0
      · exact ⟨β, hβ, fun h' => hne (h.trans h'.symm)⟩
      · exact ⟨α, hα, h⟩
    set R := sop w τ a a P - lamM w τ a γ • P with hR
    have hcoeff : ∀ δ, coeff δ R = (lamM w τ a δ - lamM w τ a γ) * coeff δ P := by
      intro δ; rw [hR, coeff_sub, coeff_smul, coeff_sop_diag, smul_eq_mul]; ring
    have hRV : R ∈ V := V.sub_mem (hV P hPV τ a a) (V.smul_mem _ hPV)
    have hsub : R.support ⊆ P.support.erase γ := by
      intro δ hδ
      rw [mem_support_iff, hcoeff] at hδ
      rw [Finset.mem_erase, mem_support_iff]
      refine ⟨fun h => ?_, fun h => hδ (by rw [h, mul_zero])⟩
      subst h; exact hδ (by rw [sub_self, zero_mul])
    have hcard : R.support.card ≤ k := by
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hγ] at this
      omega
    have hα0R : α0 ∈ R.support := by
      rw [mem_support_iff, hcoeff]
      exact mul_ne_zero (sub_ne_zero.2 (Ne.symm hγne)) (mem_support_iff.1 hα0)
    exact ih R hcard hRV α0 hα0R

lemma exists_F (V : Submodule ℂ (PolF D m n)) [FiniteDimensional ℂ V] :
    ∃ F : Finset (FVar D m n →₀ ℕ), ∀ P ∈ V, P.support ⊆ F := by
  classical
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional V).2 inferInstance
  refine ⟨s.biUnion fun P => P.support, fun P hP => ?_⟩
  rw [← hs] at hP
  induction hP using Submodule.span_induction with
  | mem x hx => exact Finset.subset_biUnion_of_mem (fun P : PolF D m n => P.support) hx
  | zero => simp
  | add x y _ _ hx hy => exact (support_add).trans (Finset.union_subset hx hy)
  | smul c x _ hx => exact (support_smul).trans hx

lemma pure_eigen (w : GlobalTheory.ExportSeries.Weight D n) (Q : PolF D m n) (hQ : Pure w Q) (α : FVar D m n →₀ ℕ)
    (hα : α ∈ Q.support) (τ : D.what₂.Tau) (a : Fin n) : sop w τ a a Q = lamM w τ a α • Q := by
  classical
  ext γ
  rw [coeff_sop_diag, coeff_smul, smul_eq_mul]
  by_cases hγ : coeff γ Q = 0
  · rw [hγ, mul_zero, mul_zero]
  · rw [hQ τ a γ (mem_support_iff.2 hγ) α hα]

end GlobalTheory.NHwExist

open GlobalTheory.NHwExist in

theorem GlobalTheory.exists_nHw_of_fockS_stable : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (V : Submodule ℂ (PolF D m n)), FiniteDimensional ℂ V → V ≠ ⊥ → (∀ P ∈ V, ∀ (τ : D.what₂.Tau) (a b : Fin n), GlobalTheory.LowestKType.sop w τ a b P ∈ V) → ∃ P ∈ V, P ≠ 0 ∧ ∃ lam : D.what₂.Tau → Fin n → ℂ, GlobalTheory.LowestKType.IsNHw w lam P := by
  classical
  intro D n m w V hfin hne hst
  obtain ⟨F, hF⟩ := exists_F V
  obtain ⟨B, hB⟩ : ∃ B : ℤ, ∀ α ∈ F, ht w α ≤ B :=
    ⟨∑ α ∈ F, |ht w α|, fun α hα =>
      (le_abs_self _).trans (Finset.single_le_sum (fun x _ => abs_nonneg (ht w x)) hα)⟩
  have key : ∀ k : ℕ, ∀ Q ∈ V, Pure w Q → ∀ α ∈ Q.support, B - ht w α ≤ k →
      ∃ P ∈ V, P ≠ 0 ∧ ∃ lam : D.what₂.Tau → Fin n → ℂ, GlobalTheory.LowestKType.IsNHw w lam P := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro Q hQ hpure α hα hk
      by_cases hr : ∀ (τ : D.what₂.Tau) (a b : Fin n), a < b → GlobalTheory.LowestKType.sop w τ a b Q = 0
      · refine ⟨Q, hQ, fun h => by simp [h] at hα, fun τ a => lamM w τ a α, hr, fun τ a => ?_⟩
        exact pure_eigen w Q hpure α hα τ a
      · simp only [not_forall] at hr
        obtain ⟨τ, a, b, hab, hne⟩ := hr
        obtain ⟨β, hβ⟩ : (GlobalTheory.LowestKType.sop w τ a b Q).support.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]; exact hne
        obtain ⟨α', hα', hht⟩ := sop_off w τ a b (ne_of_lt hab) Q β hβ
        have heq : ht w α' = ht w α := ht_of_lam w α' α (fun τ a => hpure τ a α' hα' α hα)
        obtain ⟨Q', hQ'V, hβQ', hpure'⟩ :=
          purify w V hst _ _ le_rfl (hst Q hQ τ a b) β hβ
        have hβB : ht w β ≤ B := hB β (hF Q' hQ'V hβQ')
        have hab' : (a : ℕ) < (b : ℕ) := hab
        exact ih (B - ht w β).toNat (by omega) Q' hQ'V hpure' β hβQ' (Int.self_le_toNat _)
  obtain ⟨P, hPV, hP0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨α0, hα0⟩ : P.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]; exact hP0
  obtain ⟨Q, hQV, hα0Q, hpure⟩ := purify w V hst _ P le_rfl hPV α0 hα0
  exact key (B - ht w α0).toNat Q hQV hpure α0 hα0Q (Int.self_le_toNat _)
