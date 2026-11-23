import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFirstActionMatrixUnitEq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Sl2NonnegWeightOfHighestWeightVector
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZRYRCover
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

namespace GlobalTheory.JointDict
open GlobalTheory.LowestKType GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators MvPolynomial GlobalTheory.Capelli
variable {D : D7} {n m : ℕ}

theorem raiO_apply (p : ℕ) (τ : D.what₂.Tau) (i : Fin m) (j : Fin n) (Q : PolF D m n) :
    raiO τ (fun _ : Fin n => true) (fun k : Fin m => decide ((k : ℕ) < p)) i j Q =
      if (i : ℕ) < p then X (τ, i, j) * Q else -pderiv (τ, i, j) Q := by
  unfold raiO sgn
  by_cases h : (i : ℕ) < p <;> simp [h]

theorem lowO_apply (p : ℕ) (τ : D.what₂.Tau) (i : Fin m) (j : Fin n) (Q : PolF D m n) :
    lowO τ (fun _ : Fin n => true) (fun k : Fin m => decide ((k : ℕ) < p)) i j Q =
      if (i : ℕ) < p then pderiv (τ, i, j) Q else X (τ, i, j) * Q := by
  unfold lowO sgn
  by_cases h : (i : ℕ) < p <;> simp [h]

theorem kop_apply (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m) (P : PolF D m n) :
    kop w τ a b P = ∑ j, raiO τ (fun _ : Fin n => true) (fun k : Fin m => decide ((k : ℕ) < w.p τ)) a j
        (lowO τ (fun _ : Fin n => true) (fun k : Fin m => decide ((k : ℕ) < w.p τ)) b j P) +
      if a = b then ((n : ℂ) / 2) • P else 0 := by
  unfold kop GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp only [Matrix.single_apply_same, one_smul, LinearMap.sum_apply, LinearMap.add_apply,
      Module.End.mul_apply, Finset.sum_add_distrib]
    congr 1
    split_ifs with h
    · subst h
      simp only [LinearMap.smul_apply, Module.End.one_apply, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      congr 1
      ring
    · simp
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp

theorem sop_apply (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin n) (P : PolF D m n) :
    sop w τ a b P = ∑ i, raiO τ (fun _ : Fin n => true) (fun k : Fin m => decide ((k : ℕ) < w.p τ)) i a
        (lowO τ (fun _ : Fin n => true) (fun k : Fin m => decide ((k : ℕ) < w.p τ)) i b P) +
      if a = b then ((m : ℂ) / 2) • P else 0 := by
  unfold sop GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp only [Matrix.single_apply_same, one_smul, LinearMap.sum_apply, LinearMap.add_apply,
      Module.End.mul_apply, Finset.sum_add_distrib]
    congr 1
    split_ifs with h
    · subst h
      simp only [LinearMap.smul_apply, Module.End.one_apply, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      congr 1
      ring
    · simp
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp

end GlobalTheory.JointDict

namespace GlobalTheory.JointDict
open GlobalTheory.LowestKType GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators MvPolynomial GlobalTheory.Capelli GlobalTheory.HarmLine
variable {D : D7} {n m : ℕ}

theorem sum_split {M : Type*} [AddCommMonoid M] (m p : ℕ) (f : Fin m → M) :
    ∑ i, f i = ∑ c : Fin (min p m), f ⟨c, lt_of_lt_of_le c.2 (min_le_right _ _)⟩ +
      ∑ d : Fin (m - p), f ⟨m - 1 - d, by have := d.2; omega⟩ := by
  let g : Fin (min p m) ⊕ Fin (m - p) → Fin m := Sum.elim
    (fun c => ⟨c, lt_of_lt_of_le c.2 (min_le_right _ _)⟩) (fun d => ⟨m - 1 - d, by have := d.2; omega⟩)
  have hg : Function.Bijective g := by
    constructor
    · rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩) h <;>
        simp only [g, Sum.elim_inl, Sum.elim_inr, Fin.mk.injEq] at h <;>
        first | (congr 1; ext; simp only; omega) | (exfalso; have := min_le_left p m; omega)
    · rintro ⟨i, hi⟩
      by_cases h : i < p
      · exact ⟨Sum.inl ⟨i, lt_min h hi⟩, rfl⟩
      · refine ⟨Sum.inr ⟨m - 1 - i, by omega⟩, ?_⟩
        simp only [g, Sum.elim_inr, Fin.mk.injEq]
        omega
  rw [← Fintype.sum_bijective g hg (f ∘ g) f (fun _ => rfl), Fintype.sum_sum_type]
  rfl

end GlobalTheory.JointDict

namespace GlobalTheory.JointDict
open GlobalTheory.LowestKType GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators MvPolynomial GlobalTheory.Capelli GlobalTheory.HarmLine
variable {D : D7} {n m : ℕ}

theorem term_lt (p : ℕ) (τ : D.what₂.Tau) (i l : Fin m) (j k : Fin n) (hi : (i : ℕ) < p) (hl : (l : ℕ) < p)
    (P : PolF D m n) :
    raiO τ (fun _ : Fin n => true) (fun k : Fin m => decide ((k : ℕ) < p)) i j
      (lowO τ (fun _ : Fin n => true) (fun k : Fin m => decide ((k : ℕ) < p)) l k P) =
      X (τ, i, j) * pderiv (τ, l, k) P := by
  rw [lowO_apply, raiO_apply, if_pos hi, if_pos hl]

theorem term_ge (p : ℕ) (τ : D.what₂.Tau) (i l : Fin m) (j k : Fin n) (hi : ¬ (i : ℕ) < p) (hl : ¬ (l : ℕ) < p)
    (P : PolF D m n) :
    raiO τ (fun _ : Fin n => true) (fun k : Fin m => decide ((k : ℕ) < p)) i j
      (lowO τ (fun _ : Fin n => true) (fun k : Fin m => decide ((k : ℕ) < p)) l k P) =
      -(X (τ, l, k) * pderiv (τ, i, j) P) - if i = l ∧ j = k then P else 0 := by
  classical
  rw [lowO_apply, raiO_apply, if_neg hi, if_neg hl, pderiv_X_mul']
  by_cases h : i = l ∧ j = k
  · obtain ⟨rfl, rfl⟩ := h; simp; ring
  · rw [if_neg h, if_neg (by rintro ⟨⟩; exact h ⟨rfl, rfl⟩)]; ring

theorem term_mix (p : ℕ) (τ : D.what₂.Tau) (i l : Fin m) (j k : Fin n) (hi : ¬ (i : ℕ) < p) (hl : (l : ℕ) < p)
    (P : PolF D m n) :
    raiO τ (fun _ : Fin n => true) (fun k : Fin m => decide ((k : ℕ) < p)) i j
      (lowO τ (fun _ : Fin n => true) (fun k : Fin m => decide ((k : ℕ) < p)) l k P) =
      -pderiv (τ, i, j) (pderiv (τ, l, k) P) := by
  rw [lowO_apply, raiO_apply, if_neg hi, if_pos hl]

theorem sop_eq (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin n) (P : PolF D m n) :
    sop w τ a b P = mixedOp ℂ (Prod.mk τ ∘ zR m n (w.p τ)) (Prod.mk τ ∘ yR m n (w.p τ)) a b P +
      if a = b then ((m : ℂ) / 2 - ((m - w.p τ : ℕ) : ℂ)) • P else 0 := by
  rw [sop_apply, sum_split m (w.p τ), mixedOp_apply]
  rw [Finset.sum_congr rfl fun c _ => term_lt (w.p τ) τ _ _ a b
    (lt_of_lt_of_le c.2 (min_le_left _ _)) (lt_of_lt_of_le c.2 (min_le_left _ _)) P]
  rw [Finset.sum_congr rfl fun d _ => term_ge (w.p τ) τ _ _ a b
    (by have := d.2; simp only; omega) (by have := d.2; simp only; omega) P]
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Function.comp_apply, zR, yR, true_and]
  split_ifs with h
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, sub_smul]
    abel
  · simp only [h, false_and, if_false, Finset.sum_const_zero, sub_zero, add_zero]
    abel
end GlobalTheory.JointDict

namespace GlobalTheory.JointDict
open GlobalTheory.LowestKType GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators MvPolynomial GlobalTheory.Capelli GlobalTheory.HarmLine
variable {D : D7} {n m : ℕ}

def zRow (p : ℕ) (c : Fin (min p m)) : Fin m := ⟨c, lt_of_lt_of_le c.2 (min_le_right _ _)⟩

def yRow (p : ℕ) (d : Fin (m - p)) : Fin m := ⟨m - 1 - d, by have := d.2; omega⟩

theorem zRow_lt (p : ℕ) (c : Fin (min p m)) : ((zRow p c : Fin m) : ℕ) < p :=
  lt_of_lt_of_le c.2 (min_le_left _ _)

theorem yRow_ge (p : ℕ) (d : Fin (m - p)) : ¬ ((yRow p d : Fin m) : ℕ) < p := by
  have := d.2; simp only [yRow]; omega

theorem fockTargetMatrixUnit_first_block_eq_capelli (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (c c' : Fin (min (w.p τ) m)) (P : PolF D m n) :
    kop w τ (zRow (w.p τ) c) (zRow (w.p τ) c') P =
      rowOp ℂ (Prod.mk τ ∘ zR m n (w.p τ)) c c' P + if c = c' then ((n : ℂ) / 2) • P else 0 := by
  rw [kop_apply, rowOp_apply]
  rw [Finset.sum_congr rfl fun j _ => term_lt (w.p τ) τ _ _ j j (zRow_lt _ c) (zRow_lt _ c') P]
  congr 1
  have : (zRow (w.p τ) c : Fin m) = zRow (w.p τ) c' ↔ c = c' := by
    simp only [zRow, Fin.mk.injEq, Fin.val_inj]
  simp only [this]

theorem kop_y (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (d d' : Fin (m - w.p τ)) (P : PolF D m n) :
    kop w τ (yRow (w.p τ) d') (yRow (w.p τ) d) P =
      -rowOp ℂ (Prod.mk τ ∘ yR m n (w.p τ)) d d' P - if d = d' then ((n : ℂ) / 2) • P else 0 := by
  rw [kop_apply, rowOp_apply]
  rw [Finset.sum_congr rfl fun j _ => term_ge (w.p τ) τ _ _ j j (yRow_ge _ d') (yRow_ge _ d) P]
  have : (yRow (w.p τ) d' : Fin m) = yRow (w.p τ) d ↔ d = d' := by
    have := d.2; have := d'.2
    simp only [yRow, Fin.mk.injEq]
    constructor
    · intro h; ext; omega
    · rintro rfl; rfl
  simp only [this, and_true, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  split_ifs with h
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]
    have e : ((n : ℂ) • P) = ((n : ℂ) / 2) • P + ((n : ℂ) / 2) • P := by rw [← add_smul]; ring_nf
    rw [e]
    simp only [Function.comp_apply, yR, yRow]
    abel
  · simp only [Finset.sum_const_zero, sub_zero, add_zero, Function.comp_apply, yR, yRow]

theorem kop_yz (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (c : Fin (min (w.p τ) m)) (d : Fin (m - w.p τ))
    (P : PolF D m n) :
    kop w τ (yRow (w.p τ) d) (zRow (w.p τ) c) P =
      -∑ j, pderiv ((Prod.mk τ ∘ zR m n (w.p τ)) (c, j)) (pderiv ((Prod.mk τ ∘ yR m n (w.p τ)) (d, j)) P) := by
  rw [kop_apply]
  rw [Finset.sum_congr rfl fun j _ => term_mix (w.p τ) τ _ _ j j (yRow_ge _ d) (zRow_lt _ c) P]
  have hne : (yRow (w.p τ) d : Fin m) ≠ zRow (w.p τ) c := by
    intro h; have := congrArg Fin.val h; have := yRow_ge (w.p τ) d; have := zRow_lt (w.p τ) c; omega
  rw [if_neg hne, add_zero, Finset.sum_neg_distrib]
  rw [neg_inj]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [GlobalTheory.Capelli.pderiv_swap]
  rfl

end GlobalTheory.JointDict

namespace GlobalTheory.JointDict
open GlobalTheory.LowestKType GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators MvPolynomial GlobalTheory.Capelli GlobalTheory.HarmLine

theorem jointTop_of_lowestKType (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (lam : D.what₂.Tau → Fin n → ℂ)
    (P : PolF D m n) (hH : IsHarm w P) (hN : IsNHw w lam P) (hK : IsKHw w P) (τ : D.what₂.Tau) :
    ∃ (α : Fin (min (w.p τ) m) → ℂ) (β : Fin (m - w.p τ) → ℂ),
      GlobalTheory.CompactHarm.JointTop (Prod.mk τ ∘ zR m n (w.p τ)) (Prod.mk τ ∘ yR m n (w.p τ))
        (fun a => lam τ a - (m : ℂ) / 2 + ((m - w.p τ : ℕ) : ℂ)) α β P := by
  obtain ⟨e, he⟩ : ∃ e : Fin m → ℂ, ∀ a, kop w τ a a P = e a • P :=
    ⟨fun a => (hK.2 τ a).choose, fun a => (hK.2 τ a).choose_spec⟩
  refine ⟨fun c => e (zRow (w.p τ) c) - (n : ℂ) / 2, fun d => -e (yRow (w.p τ) d) - (n : ℂ) / 2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have h := hN.1 τ i j hij
    rw [sop_eq, if_neg hij.ne, add_zero] at h
    exact h
  · intro i
    have h := hN.2 τ i
    rw [sop_eq, if_pos rfl] at h
    rw [eq_sub_of_add_eq h, ← sub_smul]
    congr 1
    ring
  · intro c c' hcc
    have h := hK.1 τ (zRow _ c) (zRow _ c') (iff_of_true (zRow_lt _ c) (zRow_lt _ c'))
      (by rw [Fin.lt_def] at hcc ⊢; exact hcc)
    rw [fockTargetMatrixUnit_first_block_eq_capelli, if_neg hcc.ne, add_zero] at h
    exact h
  · intro c
    have h := he (zRow _ c)
    rw [fockTargetMatrixUnit_first_block_eq_capelli, if_pos rfl] at h
    rw [eq_sub_of_add_eq h, ← sub_smul]
  · intro d d' hdd
    have h := hK.1 τ (yRow _ d') (yRow _ d) (iff_of_false (yRow_ge _ d') (yRow_ge _ d))
      (by have := d.2; have := d'.2; rw [Fin.lt_def] at hdd ⊢; simp only [yRow]; omega)
    rw [kop_y, if_neg hdd.ne, sub_zero, neg_eq_zero] at h
    exact h
  · intro d
    have h := he (yRow _ d)
    rw [kop_y, if_pos rfl] at h
    have h2 : rowOp ℂ (Prod.mk τ ∘ yR m n (w.p τ)) d d P = -(e (yRow (w.p τ) d) • P) - ((n : ℂ) / 2) • P := by
      rw [← h]; abel
    rw [h2, sub_smul, neg_smul]
  · intro c d
    have h := hH τ (yRow _ d) (zRow _ c) (not_lt.1 (yRow_ge _ d)) (zRow_lt _ c)
    rw [kop_yz, neg_eq_zero] at h
    exact h

end GlobalTheory.JointDict
