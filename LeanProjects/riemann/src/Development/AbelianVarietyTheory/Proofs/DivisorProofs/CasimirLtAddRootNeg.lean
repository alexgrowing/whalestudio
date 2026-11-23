import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicHomogeneousOfKType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMinimalKTypeSecondMember
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDualPairSwapSymmetryStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open Formalism.BasicNotions.TH MvPolynomial

namespace GlobalTheory.SteepSmall

theorem coeff_diag {σ : Type*} (A : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) (w : (σ →₀ ℕ) → ℂ)
    (hA : ∀ α, A (monomial α 1) = w α • monomial α 1) (g : MvPolynomial σ ℂ) (α : σ →₀ ℕ) :
    coeff α (A g) = w α * coeff α g := by
  classical
  induction g using MvPolynomial.induction_on' with
  | monomial u a =>
    have h : monomial u a = a • monomial u (1 : ℂ) := by rw [smul_monomial, smul_eq_mul, mul_one]
    rw [h, map_smul, hA, coeff_smul, coeff_smul, smul_eq_mul, smul_eq_mul, coeff_smul, smul_eq_mul,
      coeff_monomial]
    by_cases h' : u = α
    · subst h'; simp; ring
    · simp [h']
  | add p q hp hq => simp [map_add, coeff_add, hp, hq, mul_add]

theorem eig_supp {σ : Type*} (A : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) (w : (σ →₀ ℕ) → ℂ)
    (hA : ∀ α, A (monomial α 1) = w α • monomial α 1) (g : MvPolynomial σ ℂ) (c : ℂ)
    (hg : A g = c • g) {α : σ →₀ ℕ} (hα : α ∈ g.support) : w α = c := by
  have h1 := coeff_diag A w hA g α
  rw [hg, coeff_smul, smul_eq_mul] at h1
  have h2 : coeff α g ≠ 0 := mem_support_iff.1 hα
  exact (mul_right_cancel₀ h2 h1).symm

theorem homog_of_harmVec {P' Q' R S : ℕ} {x : ℚ} {μ : Ix R S → ℚ} {f : Pol P' Q' R S}
    (hf : GlobalTheory.RealLift.IsHarmVec x μ f) :
    ∃ d : ℕ, (d : ℚ) = degW (cPair P' Q') μ ∧ f ∈ homog (Ix P' Q' × Ix R S) d := by
  obtain ⟨hh, -, hw0, hw⟩ := hf
  obtain ⟨s1, -, -⟩ := GlobalTheory.T.fock_dualPair_swap_symmetry R S P' Q'
  set e := GlobalTheory.FockAlg.MinSecond.swapPol R S P' Q'
  have h1 : ∀ Z v, e (fockAct1 R S P' Q' Z v) = fockAct2 P' Q' R S Z (e v) := s1
  have hsymm := GlobalTheory.FockAlg.MinSecond.symm_equivariant e _ _ h1
  have hhw : e.symm f ∈ hwSub (fockAct1 R S P' Q') μ :=
    GlobalTheory.FockAlg.MinFirst.hw_map e.symm.toLinearMap (fun Z _ v => hsymm Z v) hw
  have hot := GlobalTheory.FockAlg.MinFirst.ofType_of_hw hhw
  have h2 := GlobalTheory.FockAlg.MinSecond.ofType_equiv e _ _ h1 μ _ hot
  rw [e.apply_symm_apply] at h2
  exact (GlobalTheory.FockAlg.harmonic_homog_of_type P' Q' R S).2 μ f hw0 h2 hh

end GlobalTheory.SteepSmall

namespace GlobalTheory.SteepSmall
open Formalism.BasicNotions.TH MvPolynomial

theorem mono_eqs {P' Q' R S : ℕ} {x : ℚ} {μ : Ix R S → ℚ} {f : Pol P' Q' R S}
    (hf : GlobalTheory.RealLift.IsHarmVec x μ f) {α : Ix P' Q' × Ix R S →₀ ℕ} (hα : α ∈ f.support) :
    (∀ i : Fin P', (∑ k : Fin R, (α (.inl i, .inl k) : ℚ)) - (∑ l : Fin S, (α (.inl i, .inr l) : ℚ)) +
      cPair R S = x) ∧
    (∀ j : Fin Q', (∑ l : Fin S, (α (.inr j, .inr l) : ℚ)) - (∑ k : Fin R, (α (.inr j, .inl k) : ℚ)) -
      cPair R S = x) ∧
    (∀ k : Fin R, (∑ i : Fin P', (α (.inl i, .inl k) : ℚ)) - (∑ j : Fin Q', (α (.inr j, .inl k) : ℚ)) =
      shiftNu (cPair P' Q') μ (.inl k)) ∧
    (∀ l : Fin S, (∑ j : Fin Q', (α (.inr j, .inr l) : ℚ)) - (∑ i : Fin P', (α (.inl i, .inr l) : ℚ)) =
      shiftNu (cPair P' Q') μ (.inr l)) := by
  have hrow : ∀ a : Ix P' Q', (∑ c, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) = (x : ℂ) := by
    intro a
    have hK := hf.2.1 (Eab a a) (GlobalTheory.FockAlg.MinFirst.isKC_diag _)
    have h := eig_supp _ _ (fun β => cartan1 (r := R) (s := S) a β) f _ hK hα
    rw [h, Eab, Matrix.trace_single_eq_same, mul_one]
  have hcol : ∀ c : Ix R S, (∑ a, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) = ((μ c : ℚ) : ℂ) := by
    intro c
    have hw := ((GlobalTheory.FockAlg.MinFirst.mem_hwSub _ _ _).1 hf.2.2.2).1 c
    exact eig_supp _ _ (fun β => cartan2 (p := P') (q := Q') c β) f _ (sub_eq_zero.1 hw) hα
  refine ⟨fun i => ?_, fun j => ?_, fun k => ?_, fun l => ?_⟩
  · have h := hrow (.inl i)
    simp only [Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul, Finset.sum_neg_distrib,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    apply Rat.cast_injective (α := ℂ)
    push_cast [cPair]
    linear_combination h
  · have h := hrow (.inr j)
    simp only [Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul, Finset.sum_neg_distrib,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    apply Rat.cast_injective (α := ℂ)
    push_cast [cPair]
    linear_combination h
  · have h := hcol (.inl k)
    simp only [Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul, Finset.sum_neg_distrib,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    apply Rat.cast_injective (α := ℂ)
    push_cast [cPair, shiftNu]
    linear_combination h
  · have h := hcol (.inr l)
    simp only [Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul, Finset.sum_neg_distrib,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    apply Rat.cast_injective (α := ℂ)
    push_cast [cPair, shiftNu]
    linear_combination h

end GlobalTheory.SteepSmall

namespace GlobalTheory.SteepSmall
open Formalism.BasicNotions.TH MvPolynomial

theorem det_kill {σ : Type*} {n : ℕ} (φ : Fin n × Fin n → σ) (hφ : Function.Injective φ)
    (g : Fin n → MvPolynomial σ ℂ) (h : ∀ m, ∑ i, X (φ (m, i)) * g i = 0) : ∀ i, g i = 0 := by
  classical
  let M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ) :=
    (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).map (rename φ)
  have hdet : M.det ≠ 0 := by
    have h1 : M.det = rename φ (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det := by
      rw [AlgHom.map_det]; rfl
    rw [h1]
    intro h0
    apply Matrix.det_mvPolynomialX_ne_zero (Fin n) ℂ
    exact rename_injective φ hφ (by rw [h0, map_zero])
  have hM : M.mulVec g = 0 := by
    funext m
    simpa [M, Matrix.mulVec, dotProduct, Matrix.mvPolynomialX] using h m
  have h2 : (M.adjugate * M).mulVec g = 0 := by
    rw [← Matrix.mulVec_mulVec, hM, Matrix.mulVec_zero]
  rw [Matrix.adjugate_mul] at h2
  intro i
  have h3 := congrFun h2 i
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply] at h3
  exact h3.resolve_left hdet

theorem pderiv_eq_zero_of {σ : Type*} (f : MvPolynomial σ ℂ) (v : σ)
    (h : ∀ α ∈ f.support, α v = 0) : pderiv v f = 0 := by
  classical
  rw [f.as_sum, map_sum]
  refine Finset.sum_eq_zero fun α hα => ?_
  rw [pderiv_monomial, h α hα]
  simp

theorem support_zero_of_pderiv {σ : Type*} (f : MvPolynomial σ ℂ) (v : σ)
    (h : pderiv v f = 0) : ∀ α ∈ f.support, α v = 0 := by
  classical
  intro α hα
  have hd := coeff_diag (LinearMap.mulLeft ℂ (X v) ∘ₗ (pderiv v).toLinearMap) (fun β => ((β v : ℕ) : ℂ))
    (fun β => by simpa using Formalism.BasicNotions.TH.X_mul_pderiv_monomial v β) f α
  have h0 : (LinearMap.mulLeft ℂ (X v) ∘ₗ (pderiv v).toLinearMap) f = 0 := by simp [h]
  rw [h0, coeff_zero] at hd
  have hc : coeff α f ≠ 0 := mem_support_iff.1 hα
  have := (mul_eq_zero.1 hd.symm).resolve_right hc
  exact_mod_cast this

end GlobalTheory.SteepSmall

namespace GlobalTheory.SteepSmall
open Formalism.BasicNotions.TH MvPolynomial

theorem cauchy_u {P' Q' R S : ℕ} (Q : ℕ) (hS : Q + P' ≤ S) (f : Pol P' Q' R S) (l₀ : Fin S)
    (hl₀ : (l₀ : ℕ) < Q) (ht : ∀ α ∈ f.support, ∀ j l, α (.inr j, .inr l) = 0)
    (hE : ∀ l' : Fin S, Q ≤ (l' : ℕ) → fockAct2 P' Q' R S (Eab (.inr l₀) (.inr l')) f = 0) :
    ∀ α ∈ f.support, ∀ i, α (.inl i, .inr l₀) = 0 := by
  classical
  have hpt : ∀ j l, pderiv ((.inr j, .inr l) : Ix P' Q' × Ix R S) f = 0 :=
    fun j l => pderiv_eq_zero_of f _ (fun α hα => ht α hα j l)
  have key : ∀ l' : Fin S, l₀ ≠ l' → fockAct2 P' Q' R S (Eab (.inr l₀) (.inr l')) f =
      -∑ i : Fin P', X ((.inl i, .inr l') : Ix P' Q' × Ix R S) * pderiv (.inl i, .inr l₀) f := by
    intro l' hne
    rw [fockAct2_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
    simp [omE, raiB, lowB, linePos, hne, Derivation.leibniz, pderiv_X_of_ne, hpt, Finset.sum_neg_distrib]
  have hg := det_kill (n := P')
    (fun mi => ((.inl mi.2, .inr ⟨Q + mi.1, by omega⟩) : Ix P' Q' × Ix R S))
    (by
      intro x y hxy
      simp only [Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, Fin.mk.injEq] at hxy
      exact Prod.ext (Fin.ext (by omega)) hxy.1)
    (fun i => pderiv (.inl i, .inr l₀) f)
    (fun m => by
      have h1 := hE ⟨Q + m, by omega⟩ (by simp)
      rw [key _ (by intro h; rw [Fin.ext_iff] at h; simp at h; omega)] at h1
      simpa using h1)
  intro α hα i
  exact support_zero_of_pderiv f _ (hg i) α hα

theorem cauchy_w {P' Q' R S : ℕ} (P : ℕ) (hR : P + Q' ≤ R) (f : Pol P' Q' R S) (k₀ : Fin R)
    (hk₀ : (k₀ : ℕ) < P) (hs : ∀ α ∈ f.support, ∀ i k, α (.inl i, .inl k) = 0)
    (hE : ∀ k' : Fin R, P ≤ (k' : ℕ) → fockAct2 P' Q' R S (Eab (.inl k₀) (.inl k')) f = 0) :
    ∀ α ∈ f.support, ∀ j, α (.inr j, .inl k₀) = 0 := by
  classical
  have hps : ∀ i k, pderiv ((.inl i, .inl k) : Ix P' Q' × Ix R S) f = 0 :=
    fun i k => pderiv_eq_zero_of f _ (fun α hα => hs α hα i k)
  have key : ∀ k' : Fin R, k₀ ≠ k' → fockAct2 P' Q' R S (Eab (.inl k₀) (.inl k')) f =
      -∑ j : Fin Q', X ((.inr j, .inl k') : Ix P' Q' × Ix R S) * pderiv (.inr j, .inl k₀) f := by
    intro k' hne
    rw [fockAct2_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
    simp [omE, raiB, lowB, linePos, hne, Derivation.leibniz, pderiv_X_of_ne, hps, Finset.sum_neg_distrib]
  have hg := det_kill (n := Q')
    (fun mj => ((.inr mj.2, .inl ⟨P + mj.1, by omega⟩) : Ix P' Q' × Ix R S))
    (by
      intro x y hxy
      simp only [Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, Fin.mk.injEq] at hxy
      exact Prod.ext (Fin.ext (by omega)) hxy.1)
    (fun j => pderiv (.inr j, .inl k₀) f)
    (fun m => by
      have h1 := hE ⟨P + m, by omega⟩ (by simp)
      rw [key _ (by intro h; rw [Fin.ext_iff] at h; simp at h; omega)] at h1
      simpa using h1)
  intro α hα j
  exact support_zero_of_pderiv f _ (hg j) α hα

end GlobalTheory.SteepSmall

namespace GlobalTheory.SteepSmall
open Formalism.BasicNotions.TH MvPolynomial

theorem abs_le_add_of_sub {s w ν : ℚ} (hs : 0 ≤ s) (hw : 0 ≤ w) (h : s - w = ν) : |ν| ≤ s + w := by
  rw [← h]; exact abs_le.2 ⟨by linarith, by linarith⟩

theorem col_min {P' Q' R S : ℕ} {x : ℚ} {μ : Ix R S → ℚ} {f : Pol P' Q' R S}
    (hf : GlobalTheory.RealLift.IsHarmVec x μ f) {α : Ix P' Q' × Ix R S →₀ ℕ} (hα : α ∈ f.support) :
    (∀ k : Fin R, (∑ i : Fin P', (α (.inl i, .inl k) : ℚ)) =
        (|shiftNu (cPair P' Q') μ (.inl k)| + shiftNu (cPair P' Q') μ (.inl k)) / 2 ∧
      (∑ j : Fin Q', (α (.inr j, .inl k) : ℚ)) =
        (|shiftNu (cPair P' Q') μ (.inl k)| - shiftNu (cPair P' Q') μ (.inl k)) / 2) ∧
    (∀ l : Fin S, (∑ j : Fin Q', (α (.inr j, .inr l) : ℚ)) =
        (|shiftNu (cPair P' Q') μ (.inr l)| + shiftNu (cPair P' Q') μ (.inr l)) / 2 ∧
      (∑ i : Fin P', (α (.inl i, .inr l) : ℚ)) =
        (|shiftNu (cPair P' Q') μ (.inr l)| - shiftNu (cPair P' Q') μ (.inr l)) / 2) := by
  set ν := shiftNu (cPair P' Q') μ with hν
  obtain ⟨-, -, hK, hL⟩ := mono_eqs hf hα
  obtain ⟨d, hd, hmem⟩ := homog_of_harmVec hf
  have hhom : IsHomogeneous f d := (mem_homogeneousSubmodule d f).1 hmem
  have hdeg := hhom (mem_support_iff.1 hα)
  have hw1 : (Finsupp.weight 1) α = ∑ c, α c := by
    simp [Finsupp.weight_apply, Finsupp.sum_fintype]
  rw [hw1] at hdeg
  have hsum : (∑ c : Ix P' Q' × Ix R S, (α c : ℚ)) = ∑ c : Ix R S, |ν c| := by
    rw [hν, ← degW, ← hd, ← hdeg]; push_cast; rfl
  rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_sum_type] at hsum
  simp only [Fintype.sum_sum_type] at hsum
  have hk : ∀ k : Fin R, |ν (.inl k)| ≤ (∑ i : Fin P', (α (.inl i, .inl k) : ℚ)) +
      ∑ j : Fin Q', (α (.inr j, .inl k) : ℚ) := fun k =>
    abs_le_add_of_sub (Finset.sum_nonneg fun _ _ => by positivity)
      (Finset.sum_nonneg fun _ _ => by positivity) (hK k)
  have hl : ∀ l : Fin S, |ν (.inr l)| ≤ (∑ j : Fin Q', (α (.inr j, .inr l) : ℚ)) +
      ∑ i : Fin P', (α (.inl i, .inr l) : ℚ) := fun l =>
    abs_le_add_of_sub (Finset.sum_nonneg fun _ _ => by positivity)
      (Finset.sum_nonneg fun _ _ => by positivity) (hL l)
  have s1 := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hk k
  have s2 := Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => hl l
  have hl' : ∀ l : Fin S, (∑ i : Fin P', (α (.inl i, .inr l) : ℚ)) + ∑ j : Fin Q', (α (.inr j, .inr l) : ℚ) =
      (∑ j : Fin Q', (α (.inr j, .inr l) : ℚ)) + ∑ i : Fin P', (α (.inl i, .inr l) : ℚ) := fun l => add_comm _ _
  simp only [hl'] at hsum
  have e1 := (Finset.sum_eq_sum_iff_of_le fun k (_ : k ∈ Finset.univ) => hk k).1 (by linarith)
  have e2 := (Finset.sum_eq_sum_iff_of_le fun l (_ : l ∈ Finset.univ) => hl l).1 (by linarith)
  refine ⟨fun k => ?_, fun l => ?_⟩
  · have h1 := e1 k (Finset.mem_univ _); have h2 := hK k
    constructor <;> linarith
  · have h1 := e2 l (Finset.mem_univ _); have h2 := hL l
    constructor <;> linarith

end GlobalTheory.SteepSmall

namespace GlobalTheory.SteepSmall
open Formalism.BasicNotions.TH MvPolynomial

theorem row_sums {P' Q' R S : ℕ} {x : ℚ} {μ : Ix R S → ℚ} {f : Pol P' Q' R S}
    (hf : GlobalTheory.RealLift.IsHarmVec x μ f) {α : Ix P' Q' × Ix R S →₀ ℕ} (hα : α ∈ f.support) :
    (∑ k : Fin R, (|shiftNu (cPair P' Q') μ (.inl k)| + shiftNu (cPair P' Q') μ (.inl k)) / 2) -
      (∑ l : Fin S, (|shiftNu (cPair P' Q') μ (.inr l)| - shiftNu (cPair P' Q') μ (.inr l)) / 2) +
      P' * cPair R S = P' * x ∧
    (∑ l : Fin S, (|shiftNu (cPair P' Q') μ (.inr l)| + shiftNu (cPair P' Q') μ (.inr l)) / 2) -
      (∑ k : Fin R, (|shiftNu (cPair P' Q') μ (.inl k)| - shiftNu (cPair P' Q') μ (.inl k)) / 2) -
      Q' * cPair R S = Q' * x := by
  obtain ⟨hI, hJ, -, -⟩ := mono_eqs hf hα
  obtain ⟨hK, hL⟩ := col_min hf hα
  constructor
  · have h := Finset.sum_congr rfl fun i (_ : i ∈ (Finset.univ : Finset (Fin P'))) => hI i
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_comm, Finset.sum_comm (f := fun i l => (α (.inl i, .inr l) : ℚ))] at h
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    rw [← Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => (hK k).1,
      ← Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => (hL l).2]
    linarith
  · have h := Finset.sum_congr rfl fun j (_ : j ∈ (Finset.univ : Finset (Fin Q'))) => hJ j
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_comm, Finset.sum_comm (f := fun j k => (α (.inr j, .inl k) : ℚ))] at h
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    rw [← Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => (hL l).1,
      ← Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => (hK k).2]
    linarith

theorem sum_ite_lt (n m : ℕ) (h : m ≤ n) (c : ℚ) :
    ∑ l : Fin n, (if (l : ℕ) < m then (0 : ℚ) else c) = ((n - m : ℕ) : ℚ) * c := by
  rw [Fin.sum_univ_eq_sum_range (fun l => if l < m then (0 : ℚ) else c) n, Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le m) h,
    Finset.sum_congr rfl (fun l hl => if_pos (Finset.mem_Ico.1 hl).2),
    Finset.sum_congr rfl (fun l hl => if_neg (by have := (Finset.mem_Ico.1 hl).1; omega))]
  simp

theorem casK_lr {R S : ℕ} (μ : Ix R S → ℚ) (k : Fin R) (l : Fin S) :
    GlobalTheory.RealLift.casK (GlobalTheory.RealLift.addRoot μ (.inl k) (.inr l)) = GlobalTheory.RealLift.casK μ + 2 * μ (.inl k) + 1 -
      2 * μ (.inr l) + 1 + ((R : ℚ) - 1 - 2 * (k : ℕ)) - ((S : ℚ) - 1 - 2 * (l : ℕ)) := by
  simp only [GlobalTheory.RealLift.casK, GlobalTheory.RealLift.addRoot, Fintype.sum_sum_type, Sum.inl.injEq,
    reduceCtorEq, if_false, Sum.inr.injEq]
  have e1 : ∀ i : Fin R, (μ (.inl i) + (if i = k then 1 else 0) - 0) ^ 2 =
      μ (.inl i) ^ 2 + (if i = k then 2 * μ (.inl i) + 1 else 0) := by intro i; split_ifs <;> ring
  have e2 : ∀ j : Fin S, (μ (.inr j) + 0 - (if j = l then 1 else 0)) ^ 2 =
      μ (.inr j) ^ 2 + (if j = l then -2 * μ (.inr j) + 1 else 0) := by intro j; split_ifs <;> ring
  have e3 : ∀ i : Fin R, (μ (.inl i) + (if i = k then 1 else 0) - 0) * ((R : ℚ) - 1 - 2 * (i : ℕ)) =
      μ (.inl i) * ((R : ℚ) - 1 - 2 * (i : ℕ)) + (if i = k then (R : ℚ) - 1 - 2 * (i : ℕ) else 0) := by
    intro i; split_ifs <;> ring
  have e4 : ∀ j : Fin S, (μ (.inr j) + 0 - (if j = l then 1 else 0)) * ((S : ℚ) - 1 - 2 * (j : ℕ)) =
      μ (.inr j) * ((S : ℚ) - 1 - 2 * (j : ℕ)) - (if j = l then (S : ℚ) - 1 - 2 * (j : ℕ) else 0) := by
    intro j; split_ifs <;> ring
  simp only [e1, e2, e3, e4, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

theorem casK_rl {R S : ℕ} (μ : Ix R S → ℚ) (l : Fin S) (k : Fin R) :
    GlobalTheory.RealLift.casK (GlobalTheory.RealLift.addRoot μ (.inr l) (.inl k)) = GlobalTheory.RealLift.casK μ + 2 * μ (.inr l) + 1 -
      2 * μ (.inl k) + 1 + ((S : ℚ) - 1 - 2 * (l : ℕ)) - ((R : ℚ) - 1 - 2 * (k : ℕ)) := by
  simp only [GlobalTheory.RealLift.casK, GlobalTheory.RealLift.addRoot, Fintype.sum_sum_type, Sum.inl.injEq,
    reduceCtorEq, if_false, Sum.inr.injEq]
  have e1 : ∀ i : Fin R, (μ (.inl i) + 0 - (if i = k then 1 else 0)) ^ 2 =
      μ (.inl i) ^ 2 + (if i = k then -2 * μ (.inl i) + 1 else 0) := by intro i; split_ifs <;> ring
  have e2 : ∀ j : Fin S, (μ (.inr j) + (if j = l then 1 else 0) - 0) ^ 2 =
      μ (.inr j) ^ 2 + (if j = l then 2 * μ (.inr j) + 1 else 0) := by intro j; split_ifs <;> ring
  have e3 : ∀ i : Fin R, (μ (.inl i) + 0 - (if i = k then 1 else 0)) * ((R : ℚ) - 1 - 2 * (i : ℕ)) =
      μ (.inl i) * ((R : ℚ) - 1 - 2 * (i : ℕ)) - (if i = k then (R : ℚ) - 1 - 2 * (i : ℕ) else 0) := by
    intro i; split_ifs <;> ring
  have e4 : ∀ j : Fin S, (μ (.inr j) + (if j = l then 1 else 0) - 0) * ((S : ℚ) - 1 - 2 * (j : ℕ)) =
      μ (.inr j) * ((S : ℚ) - 1 - 2 * (j : ℕ)) + (if j = l then (S : ℚ) - 1 - 2 * (j : ℕ) else 0) := by
    intro j; split_ifs <;> ring
  simp only [e1, e2, e3, e4, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

end GlobalTheory.SteepSmall

namespace GlobalTheory.SteepSmall
open Formalism.BasicNotions.TH MvPolynomial

theorem steep_small : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ →
    ∀ a b : Formalism.BasicNotions.TH.Ix R S, ¬ Formalism.BasicNotions.TH.sameBlock a b → ∀ f : Formalism.BasicNotions.TH.Pol P' Q' R S,
    GlobalTheory.RealLift.IsHarmVec (-((κ : ℚ) / 2))
      (fun c => GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b c - (κ : ℚ) / 2) f →
    GlobalTheory.RealLift.casK (GlobalTheory.RealLift.lam P Q R S κ) + ((R + S : ℕ) : ℚ) <
      GlobalTheory.RealLift.casK (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b) := by
  intro P Q P' Q' R S κ hN a b hab f hf
  obtain ⟨hR, hS, hSP, hSQ, hev, hκe, hlt⟩ := hN
  subst hR hS
  have hκ2 : ((P + Q' + (Q + P') : ℕ) : ℤ) + 2 ≤ κ := by
    obtain ⟨n, hn⟩ := hev
    obtain ⟨m, hm⟩ := hκe
    have hn' : ((P + Q' + (Q + P') : ℕ) : ℤ) = (n : ℤ) + n := by exact_mod_cast hn
    omega
  have hκq : ((P : ℚ) + Q' + (Q + P')) + 2 ≤ (κ : ℚ) := by
    have := (Int.cast_le (R := ℚ)).2 hκ2
    push_cast at this
    linarith
  set Λ := GlobalTheory.RealLift.lam P Q (P + Q') (Q + P') κ with hΛ
  set μ := fun c => GlobalTheory.RealLift.addRoot Λ a b c - (κ : ℚ) / 2 with hμ
  obtain ⟨α, hα⟩ : ∃ α, α ∈ f.support := by
    obtain ⟨d, hd⟩ := ne_zero_iff.1 hf.2.2.1
    exact ⟨d, mem_support_iff.2 hd⟩
  have hnu_l : ∀ k : Fin (P + Q'), shiftNu (cPair P' Q') μ (.inl k) =
      (if (k : ℕ) < P then 0 else -((κ : ℚ) / 2 - cPair (P + Q') (Q + P'))) +
        ((if (Sum.inl k : Ix (P + Q') (Q + P')) = a then 1 else 0) -
          (if (Sum.inl k : Ix (P + Q') (Q + P')) = b then 1 else 0)) := by
    intro k
    simp only [shiftNu, hμ, GlobalTheory.RealLift.addRoot, hΛ, GlobalTheory.RealLift.lam, cPair]
    split_ifs <;> push_cast <;> ring
  have hnu_r : ∀ l : Fin (Q + P'), shiftNu (cPair P' Q') μ (.inr l) =
      (if (l : ℕ) < Q then 0 else -((κ : ℚ) / 2 + cPair (P + Q') (Q + P'))) +
        ((if (Sum.inr l : Ix (P + Q') (Q + P')) = a then 1 else 0) -
          (if (Sum.inr l : Ix (P + Q') (Q + P')) = b then 1 else 0)) := by
    intro l
    simp only [shiftNu, hμ, GlobalTheory.RealLift.addRoot, hΛ, GlobalTheory.RealLift.lam, cPair]
    split_ifs <;> push_cast <;> ring
  have hA : 1 ≤ (κ : ℚ) / 2 + cPair (P + Q') (Q + P') := by
    simp only [cPair]; push_cast; linarith
  have hB : 1 ≤ (κ : ℚ) / 2 - cPair (P + Q') (Q + P') := by
    simp only [cPair]; push_cast; linarith
  have hw := (GlobalTheory.FockAlg.MinFirst.mem_hwSub _ _ _).1 hf.2.2.2
  rcases a with k₀ | l₀ <;> rcases b with k₁ | l₁
  · exact (hab trivial).elim
  ·
    have hνl : ∀ k : Fin (P + Q'), shiftNu (cPair P' Q') μ (.inl k) =
        (if (k : ℕ) < P then 0 else -((κ : ℚ) / 2 - cPair (P + Q') (Q + P'))) + (if k = k₀ then 1 else 0) := by
      intro k; rw [hnu_l]; simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false]; ring
    have hνr : ∀ l : Fin (Q + P'), shiftNu (cPair P' Q') μ (.inr l) =
        (if (l : ℕ) < Q then 0 else -((κ : ℚ) / 2 + cPair (P + Q') (Q + P'))) - (if l = l₁ then 1 else 0) := by
      intro l; rw [hnu_r]; simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false]; ring
    have hνr0 : ∀ l, shiftNu (cPair P' Q') μ (.inr l) ≤ 0 := by
      intro l; rw [hνr l]; split_ifs <;> linarith
    have hk0 : (k₀ : ℕ) < P := by
      by_contra hk
      obtain ⟨h1, -⟩ := row_sums hf hα
      have e1 : ∀ k, (|shiftNu (cPair P' Q') μ (.inl k)| + shiftNu (cPair P' Q') μ (.inl k)) / 2 = 0 := by
        intro k
        have : shiftNu (cPair P' Q') μ (.inl k) ≤ 0 := by
          rw [hνl k]
          split_ifs with hc hd hd
          · subst hd; exact absurd hc hk
          · linarith
          · linarith
          · linarith
        rw [abs_of_nonpos this]; ring
      have e2 : ∀ l, (|shiftNu (cPair P' Q') μ (.inr l)| - shiftNu (cPair P' Q') μ (.inr l)) / 2 =
          (if (l : ℕ) < Q then 0 else ((κ : ℚ) / 2 + cPair (P + Q') (Q + P'))) + (if l = l₁ then 1 else 0) := by
        intro l
        rw [abs_of_nonpos (hνr0 l), hνr l]
        split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun k _ => e1 k), Finset.sum_congr rfl (fun l _ => e2 l),
        Finset.sum_add_distrib, sum_ite_lt (Q + P') Q (by omega), Finset.sum_ite_eq'] at h1
      simp only [Finset.sum_const_zero, Finset.mem_univ, if_true, Nat.add_sub_cancel_left] at h1
      have : (-1 : ℚ) = 0 := by linear_combination h1
      norm_num at this
    have ht : ∀ β ∈ f.support, ∀ j l, β (.inr j, .inr l) = 0 := by
      intro β hβ j l
      have h := ((col_min hf hβ).2 l).1
      rw [abs_of_nonpos (hνr0 l), show ∀ v : ℚ, (-v + v) / 2 = 0 from fun v => by ring] at h
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1 h j (Finset.mem_univ _)
      exact_mod_cast this
    have hl0 : Q ≤ (l₁ : ℕ) := by
      by_contra hl
      push Not at hl
      have hE : ∀ l' : Fin (Q + P'), Q ≤ (l' : ℕ) →
          fockAct2 P' Q' (P + Q') (Q + P') (Eab (.inr l₁) (.inr l')) f = 0 := by
        intro l' hl'
        exact hw.2 _ _ (show l₁ < l' from Fin.lt_def.2 (by omega))
      have hz := cauchy_u Q (by omega) f l₁ hl ht hE α hα
      have h := ((col_min hf hα).2 l₁).2
      rw [hνr l₁] at h
      simp only [hz, Nat.cast_zero, Finset.sum_const_zero, if_pos hl, if_pos rfl] at h
      norm_num at h
    rw [casK_lr]
    simp only [hΛ, GlobalTheory.RealLift.lam, if_pos hk0, if_neg (not_lt.2 hl0), cPair]
    have hk' : ((k₀ : ℕ) : ℚ) + 1 ≤ P := by exact_mod_cast hk0
    have hl' : (Q : ℚ) ≤ ((l₁ : ℕ) : ℚ) := by exact_mod_cast hl0
    push_cast
    linarith
  ·
    have hνl : ∀ k : Fin (P + Q'), shiftNu (cPair P' Q') μ (.inl k) =
        (if (k : ℕ) < P then 0 else -((κ : ℚ) / 2 - cPair (P + Q') (Q + P'))) - (if k = k₁ then 1 else 0) := by
      intro k; rw [hnu_l]; simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false]; ring
    have hνr : ∀ l : Fin (Q + P'), shiftNu (cPair P' Q') μ (.inr l) =
        (if (l : ℕ) < Q then 0 else -((κ : ℚ) / 2 + cPair (P + Q') (Q + P'))) + (if l = l₀ then 1 else 0) := by
      intro l; rw [hnu_r]; simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false]; ring
    have hνl0 : ∀ k, shiftNu (cPair P' Q') μ (.inl k) ≤ 0 := by
      intro k; rw [hνl k]; split_ifs <;> linarith
    have hl0 : (l₀ : ℕ) < Q := by
      by_contra hl
      obtain ⟨-, h1⟩ := row_sums hf hα
      have e1 : ∀ l, (|shiftNu (cPair P' Q') μ (.inr l)| + shiftNu (cPair P' Q') μ (.inr l)) / 2 = 0 := by
        intro l
        have : shiftNu (cPair P' Q') μ (.inr l) ≤ 0 := by
          rw [hνr l]
          split_ifs with hc hd hd
          · subst hd; exact absurd hc hl
          · linarith
          · linarith
          · linarith
        rw [abs_of_nonpos this]; ring
      have e2 : ∀ k, (|shiftNu (cPair P' Q') μ (.inl k)| - shiftNu (cPair P' Q') μ (.inl k)) / 2 =
          (if (k : ℕ) < P then 0 else ((κ : ℚ) / 2 - cPair (P + Q') (Q + P'))) + (if k = k₁ then 1 else 0) := by
        intro k
        rw [abs_of_nonpos (hνl0 k), hνl k]
        split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun l _ => e1 l), Finset.sum_congr rfl (fun k _ => e2 k),
        Finset.sum_add_distrib, sum_ite_lt (P + Q') P (by omega), Finset.sum_ite_eq'] at h1
      simp only [Finset.sum_const_zero, Finset.mem_univ, if_true, Nat.add_sub_cancel_left] at h1
      have : (-1 : ℚ) = 0 := by linear_combination h1
      norm_num at this
    have hs : ∀ β ∈ f.support, ∀ i k, β (.inl i, .inl k) = 0 := by
      intro β hβ i k
      have h := ((col_min hf hβ).1 k).1
      rw [abs_of_nonpos (hνl0 k), show ∀ v : ℚ, (-v + v) / 2 = 0 from fun v => by ring] at h
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 h i (Finset.mem_univ _)
      exact_mod_cast this
    have hk0 : P ≤ (k₁ : ℕ) := by
      by_contra hk
      push Not at hk
      have hE : ∀ k' : Fin (P + Q'), P ≤ (k' : ℕ) →
          fockAct2 P' Q' (P + Q') (Q + P') (Eab (.inl k₁) (.inl k')) f = 0 := by
        intro k' hk'
        exact hw.2 _ _ (show k₁ < k' from Fin.lt_def.2 (by omega))
      have hz := cauchy_w P (by omega) f k₁ hk hs hE α hα
      have h := ((col_min hf hα).1 k₁).2
      rw [hνl k₁] at h
      simp only [hz, Nat.cast_zero, Finset.sum_const_zero, if_pos hk, if_pos rfl] at h
      norm_num at h
    rw [casK_rl]
    simp only [hΛ, GlobalTheory.RealLift.lam, if_pos hl0, if_neg (not_lt.2 hk0), cPair]
    have hl' : ((l₀ : ℕ) : ℚ) + 1 ≤ Q := by exact_mod_cast hl0
    have hk' : (P : ℚ) ≤ ((k₁ : ℕ) : ℚ) := by exact_mod_cast hk0
    push_cast
    linarith
  · exact (hab trivial).elim

end GlobalTheory.SteepSmall

example : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ a b : Formalism.BasicNotions.TH.Ix R S, ¬ Formalism.BasicNotions.TH.sameBlock a b → ∀ f : Formalism.BasicNotions.TH.Pol P' Q' R S, GlobalTheory.RealLift.IsHarmVec (-((κ : ℚ) / 2)) (fun c => GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b c - (κ : ℚ) / 2) f → GlobalTheory.RealLift.casK (GlobalTheory.RealLift.lam P Q R S κ) + ((R + S : ℕ) : ℚ) < GlobalTheory.RealLift.casK (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b) :=
  GlobalTheory.SteepSmall.steep_small
