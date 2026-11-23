import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorOfCharCentral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeMatrixCharacterLeviBlockExists
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.CuspBlock GlobalTheory.JacLineSplit

noncomputable section

namespace GlobalTheory.JacLineSplit.Eigen

section Lagrange

open Polynomial

theorem chainLagrange_commute_aeval {V : Type} [AddCommGroup V] [Module ℂ V]
    {B T : Module.End ℂ V} (h : Commute B T) (p : ℂ[X]) : Commute B (aeval T p) := by
  induction p using Polynomial.induction_on with
  | C a => rw [aeval_C]; exact (Algebra.commutes a B).symm
  | add p q hp hq => rw [map_add]; exact hp.add_right hq
  | monomial n a _ =>
    rw [map_mul, map_pow, aeval_X, aeval_C]
    exact (Commute.symm (Algebra.commutes a B)).mul_right (h.pow_right (n + 1))

theorem chainLagrange_kill {V : Type} [AddCommGroup V] [Module ℂ V] (M : ℕ)
    (S : Fin (M + 1) → Submodule ℂ V) (hS0 : S 0 = ⊥)
    (T B : Module.End ℂ V) (hTB : Commute B T)
    (lam : ℕ → ℂ) (t : ℕ)
    (hT : ∀ k (hk : k < M), k ≠ t → ∀ v ∈ S ⟨k+1, by omega⟩, T v - lam k • v ∈ S ⟨k, by omega⟩)
    (hB : ∀ (ht : t < M), ∀ v ∈ S ⟨t+1, by omega⟩, B v ∈ S ⟨t, by omega⟩) :
    ∀ k (hk : k ≤ M), ∀ v ∈ S ⟨k, by omega⟩,
      (if k ≤ t then aeval T (∏ s ∈ Finset.range k, if s = t then 1 else (X - C (lam s)))
       else B * aeval T (∏ s ∈ Finset.range k, if s = t then 1 else (X - C (lam s)))) v = 0 := by
  intro k
  induction k with
  | zero =>
    intro hk v hv
    have h0 : (⟨0, by omega⟩ : Fin (M+1)) = 0 := rfl
    rw [h0, hS0] at hv
    have : v = 0 := by simpa using hv
    simp [this]
  | succ k ih =>
    intro hk v hv
    rw [Finset.prod_range_succ]
    by_cases hkt : k = t
    · subst hkt
      have hle : ¬ (k + 1 ≤ k) := by omega
      rw [if_neg hle, if_pos rfl, mul_one, Module.End.mul_apply]
      have hc : Commute B (aeval T (∏ s ∈ Finset.range k, if s = k then 1 else (X - C (lam s)))) :=
        chainLagrange_commute_aeval hTB _
      have := ih (by omega) (B v) (hB (by omega) v hv)
      rw [if_pos le_rfl] at this
      rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, this]
    · rw [if_neg hkt, map_mul, aeval_sub, aeval_X, aeval_C]
      have hw := hT k (by omega) hkt v hv
      have hw' : (T - algebraMap ℂ (Module.End ℂ V) (lam k)) v = T v - lam k • v := by
        simp [Module.algebraMap_end_apply]
      by_cases hkt' : k + 1 ≤ t
      · have h2 : k ≤ t := by omega
        have := ih (by omega) _ hw
        rw [if_pos h2] at this
        rw [if_pos hkt', Module.End.mul_apply, hw', this]
      · have h2 : ¬ k ≤ t := by omega
        have := ih (by omega) _ hw
        rw [if_neg h2] at this
        rw [if_neg hkt', ← mul_assoc, Module.End.mul_apply, hw', this]

theorem chainLagrange_basis_eq {M : ℕ} (lam : Fin M → ℂ) (t : Fin M) :
    Lagrange.basis Finset.univ lam t =
      C (∏ j ∈ Finset.univ.erase t, (lam t - lam j)⁻¹) *
        ∏ s ∈ Finset.range M, (if s = t.val then 1 else
          (X - C (if h : s < M then lam ⟨s, h⟩ else 0))) := by
  simp only [Lagrange.basis, Lagrange.basisDivisor]
  rw [Finset.prod_mul_distrib, ← map_prod C]
  congr 1
  rw [← Fin.prod_univ_eq_prod_range (fun s => if s = t.val then (1 : ℂ[X]) else
          (X - C (if h : s < M then lam ⟨s, h⟩ else 0))) M,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ t)]
  simp only [if_true, one_mul]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hjt : j ≠ t := Finset.ne_of_mem_erase hj
  have hjt' : (j : ℕ) ≠ t.val := fun h => hjt (Fin.ext h)
  simp [hjt', j.isLt]

theorem chain_split_simultaneous_eigen : ∀ {V ι : Type} [AddCommGroup V] [Module ℂ V] (M : ℕ)
    (S : Fin (M + 1) → Submodule ℂ V), S 0 = ⊥ → S (Fin.last M) = ⊤ →
    ∀ (T : Module.End ℂ V) (R : ι → Module.End ℂ V), (∀ y, Commute (R y) T) →
    ∀ (lam : Fin M → ℂ), Function.Injective lam → ∀ (nu : Fin M → ι → ℂ),
    (∀ t : Fin M, ∀ v ∈ S t.succ, T v - lam t • v ∈ S t.castSucc) →
    (∀ (t : Fin M) (y : ι), ∀ v ∈ S t.succ, R y v - nu t y • v ∈ S t.castSucc) →
    ∀ v : V, ∃ w : Fin M → V, v = ∑ t, w t ∧ ∀ t y, R y (w t) = nu t y • w t := by
  intro V ι _ _ M S hS0 hSt T R hR lam hlam nu hT hRS v
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    have hv : v ∈ S 0 := by
      have : S (Fin.last 0) = S 0 := rfl
      rw [← this, hSt]; exact Submodule.mem_top
    rw [hS0] at hv
    refine ⟨fun _ => 0, ?_, fun t => t.elim0⟩
    simpa using hv
  · refine ⟨fun t => aeval T (Lagrange.basis Finset.univ lam t) v, ?_, ?_⟩
    · have hsum : ∑ t, Lagrange.basis Finset.univ lam t = 1 :=
        Lagrange.sum_basis (fun a _ b _ h => hlam h) ⟨⟨0, hM⟩, Finset.mem_univ _⟩
      rw [← LinearMap.sum_apply, ← map_sum, hsum, map_one, Module.End.one_apply]
    · intro t y
      set lam' : ℕ → ℂ := fun s => if h : s < M then lam ⟨s, h⟩ else 0 with hlam'
      set B : Module.End ℂ V := R y - algebraMap ℂ (Module.End ℂ V) (nu t y) with hBdef
      have hBT : Commute B T := (hR y).sub_left (Algebra.commutes _ _)
      have hBv : ∀ u, B u = R y u - nu t y • u := fun u => by
        simp [hBdef, Module.algebraMap_end_apply]
      have key := chainLagrange_kill M S hS0 T B hBT lam' t.val
        (fun k hk _ u hu => by
          have := hT ⟨k, hk⟩ u hu
          simpa [hlam', hk] using this)
        (fun _ u hu => by rw [hBv]; exact hRS t y u hu)
        M le_rfl v (by
          have : S ⟨M, by omega⟩ = S (Fin.last M) := rfl
          rw [this, hSt]; exact Submodule.mem_top)
      rw [if_neg (by have := t.isLt; omega)] at key
      have hzero : B (aeval T (Lagrange.basis Finset.univ lam t) v) = 0 := by
        rw [chainLagrange_basis_eq, map_mul, aeval_C, Module.End.mul_apply,
          Module.algebraMap_end_apply, map_smul]
        rw [Module.End.mul_apply] at key
        simp only [hlam'] at key
        rw [key, smul_zero]
      rw [hBv, sub_eq_zero] at hzero
      exact hzero

end Lagrange

open GlobalTheory.LeviBlockExponentLocal GlobalTheory.SplitWeil

section SlopeTestRemainingChoices

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def thirdBlockScalar (N : ℕ) (x : kˣ) : Levi k (fun j : Fin 3 => Fin (tripSizes 1 (N - 2) N j)) :=
  MonoidHom.mulSingle (fun j : Fin 3 => GL (Fin (tripSizes 1 (N - 2) N j)) k) 2
    (Matrix.GeneralLinearGroup.scalar (Fin (tripSizes 1 (N - 2) N 2)) x)

variable {k}

theorem firstBlockScalar_apply (N : ℕ) (x : kˣ) (j : Fin 3) :
    firstBlockScalar k N x j = Matrix.GeneralLinearGroup.scalar _ (if j = 0 then x else 1) := by
  unfold firstBlockScalar
  by_cases h : j = 0
  · subst h; simp
  · rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h, if_neg h, map_one]

theorem thirdBlockScalar_apply (N : ℕ) (x : kˣ) (j : Fin 3) :
    thirdBlockScalar k N x j = Matrix.GeneralLinearGroup.scalar _ (if j = 2 then x else 1) := by
  unfold thirdBlockScalar
  by_cases h : j = 2
  · subst h; simp
  · rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h, if_neg h, map_one]

theorem comm_of_scalar {β : Type} {m' : β → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
    (x : Levi k m') (s : β → kˣ) (hx : ∀ j, x j = Matrix.GeneralLinearGroup.scalar (m' j) (s j))
    (y : Levi k m') : y * x = x * y := by
  funext j
  rw [Pi.mul_apply, Pi.mul_apply, hx j]
  ext1
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).symm.eq

theorem mem_relParab_of_scalar {β γ : Type} [Fintype β] [Fintype γ] [LinearOrder γ]
    {m' : β → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
    {c : β → γ → Type} [∀ j r, Fintype (c j r)] [∀ j r, DecidableEq (c j r)]
    (g : ∀ j, (Σ r, c j r) ≃ m' j) (x : Levi k m') (s : β → kˣ)
    (hx : ∀ j, x j = Matrix.GeneralLinearGroup.scalar (m' j) (s j)) : x ∈ relParab k g := by
  intro j _
  rw [hx j]
  refine mem_parab.2 fun a b hab => ?_
  have hne : a ≠ b := by rintro rfl; exact lt_irrefl _ hab
  simp [Matrix.GeneralLinearGroup.scalar, hne]

theorem firstBlockScalar_mem_relParab {N : ℕ} {γ : Type} [Fintype γ] [LinearOrder γ]
    {c : Fin 3 → γ → Type} [∀ j r, Fintype (c j r)] [∀ j r, DecidableEq (c j r)]
    (g : ∀ j, (Σ r, c j r) ≃ Fin (tripSizes 1 (N - 2) N j)) (x : kˣ) : firstBlockScalar k N x ∈ relParab k g :=
  mem_relParab_of_scalar g _ _ (firstBlockScalar_apply N x)

theorem thirdBlockScalar_mem_relParab {N : ℕ} {γ : Type} [Fintype γ] [LinearOrder γ]
    {c : Fin 3 → γ → Type} [∀ j r, Fintype (c j r)] [∀ j r, DecidableEq (c j r)]
    (g : ∀ j, (Σ r, c j r) ≃ Fin (tripSizes 1 (N - 2) N j)) (x : kˣ) : thirdBlockScalar k N x ∈ relParab k g :=
  mem_relParab_of_scalar g _ _ (thirdBlockScalar_apply N x)

theorem firstBlockScalar_comm (N : ℕ) (x : kˣ) (y : Levi k (fun j : Fin 3 => Fin (tripSizes 1 (N - 2) N j))) :
    y * firstBlockScalar k N x = firstBlockScalar k N x * y :=
  comm_of_scalar _ _ (firstBlockScalar_apply N x) y

theorem cellScalar_mul {α β : Type} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
    {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    {m' : β → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
    {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
    (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j) (χ' : Levi k m →* ℂˣ)
    (p q : relParab k g) : cellScalar f g χ' (p * q) = cellScalar f g χ' p * cellScalar f g χ' q := by
  simp only [cellScalar, map_mul, mul_inv]
  ac_rfl

end SlopeTestRemainingChoices

section Cell

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem relProj_firstBlockScalar {N : ℕ} {γ : Type} [Fintype γ] [LinearOrder γ]
    {c : Fin 3 → γ → Type} [∀ j r, Fintype (c j r)] [∀ j r, DecidableEq (c j r)]
    (g : ∀ j, (Σ r, c j r) ≃ Fin (tripSizes 1 (N - 2) N j)) (y : kˣ) (j : Fin 3) (r : γ) :
    relProj k g ⟨firstBlockScalar k N y, firstBlockScalar_mem_relParab g y⟩ j r =
      Matrix.GeneralLinearGroup.scalar _ (if j = 0 then y else 1) := by
  ext p q
  refine (leviProj_apply k (g j) ⟨firstBlockScalar k N y j, firstBlockScalar_mem_relParab g y j trivial⟩ r p q).trans ?_
  show ((firstBlockScalar k N y j : GL (Fin (tripSizes 1 (N - 2) N j)) k) :
    Matrix (Fin (tripSizes 1 (N - 2) N j)) (Fin (tripSizes 1 (N - 2) N j)) k) _ _ = _
  rw [firstBlockScalar_apply]
  by_cases h : p = q
  · subst h; simp [Matrix.GeneralLinearGroup.scalar]
  · have h' : g j ⟨r, p⟩ ≠ g j ⟨r, q⟩ := by simpa using h
    simp [Matrix.GeneralLinearGroup.scalar, h, h']

theorem modExp_three_zero (m : Fin 3 → Type) [∀ a, Fintype (m a)] :
    modExp m 0 = (Fintype.card (m 1) : ℤ) + Fintype.card (m 2) := by
  simp [modExp, Finset.sum_filter, Fin.sum_univ_three]

theorem cellScalar_positionOne_pair {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a a' : ℕ) (χ : Fin 2 → kˣ →* ℂˣ)
    (b : SizeMatrix (fun j : Fin 2 => Fin (![a, a'] j))
      (fun j : Fin 3 => Fin (tripSizes 1 (a + a' - 2) (a + a') j)))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (![a, a'] i))
    (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (tripSizes 1 (a + a' - 2) (a + a') j)) (y : kˣ) (i : Fin 2)
    (hi : b.1 i 0 = 1) :
    ((cellScalar f g (pairChar k ![a, a'] χ) ⟨firstBlockScalar k (a + a') y, firstBlockScalar_mem_relParab g y⟩ : ℂˣ) : ℂ) =
      (χ i y : ℂ) * (absPow k ((1 - ((![a, a'] i : ℕ) : ℂ)) / 2) y : ℂ) := by
  have hy := relProj_firstBlockScalar (k := k) (N := a + a') g y
  set P := relProj k g ⟨firstBlockScalar k (a + a') y, firstBlockScalar_mem_relParab g y⟩ with hP
  have hcol : b.1 0 0 + b.1 1 0 = 1 := by
    have := b.2.2 0
    rw [Fintype.card_fin, Fin.sum_univ_two] at this
    simpa [tripSizes] using this
  have hrow : ∀ r, b.1 r 0 + b.1 r 1 + b.1 r 2 = ![a, a'] r := by
    intro r; have := b.2.1 r; simpa [Fin.sum_univ_three] using this
  have hdet : ∀ j r, Matrix.GeneralLinearGroup.det (P j r) = (if j = 0 then y else 1) ^ b.1 r j := by
    intro j r; rw [hy, det_scalar', Fintype.card_fin]
  have hA : relDeltaHalf k (fun j r => Fin (b.1 r j)) P = 1 := by
    rw [relDeltaHalf_apply]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [deltaHalf_apply, Fin.prod_univ_two, hdet, hdet, modExp_two_zero, modExp_two_one]
    split_ifs with h
    · subst h
      simp only [Fintype.card_fin]
      rcases (by omega : (b.1 0 0 = 0 ∧ b.1 1 0 = 1) ∨ (b.1 0 0 = 1 ∧ b.1 1 0 = 0)) with
        ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp [h0, h1]
    · simp
  have hB : ∀ r, deltaHalf k (fun j => Fin (b.1 r j)) (swapBlocks k (fun r j => Fin (b.1 r j)) P r) =
      absPow k ((modExp (fun j => Fin (b.1 r j)) 0 : ℂ) / 2) (y ^ b.1 r 0) := by
    intro r
    rw [deltaHalf_apply, Fin.prod_univ_three]
    show absPow k _ (Matrix.GeneralLinearGroup.det (P 0 r)) * absPow k _ (Matrix.GeneralLinearGroup.det (P 1 r)) *
      absPow k _ (Matrix.GeneralLinearGroup.det (P 2 r)) = _
    rw [hdet, hdet, hdet]; simp
  have hC : pairChar k ![a, a'] χ (relEmb k f (swapBlocks k (fun r j => Fin (b.1 r j)) P)) =
      χ 0 (y ^ b.1 0 0) * χ 1 (y ^ b.1 1 0) := by
    simp only [pairChar, Fin.prod_univ_two, MonoidHom.mul_apply, MonoidHom.comp_apply,
      Pi.evalMonoidHom_apply, detChar_apply, relEmb_apply, det_leviEmb]
    rw [Fin.prod_univ_three, Fin.prod_univ_three]
    show χ 0 (Matrix.GeneralLinearGroup.det (P 0 0) * Matrix.GeneralLinearGroup.det (P 1 0) *
      Matrix.GeneralLinearGroup.det (P 2 0)) * χ 1 (Matrix.GeneralLinearGroup.det (P 0 1) *
      Matrix.GeneralLinearGroup.det (P 1 1) * Matrix.GeneralLinearGroup.det (P 2 1)) = _
    simp [hdet]
  simp only [cellScalar]
  rw [hA, relDeltaHalf_apply, Fin.prod_univ_two, hB, hB, hC]
  have hrow' : ∀ r, b.1 r 0 = 1 →
      (modExp (fun j => Fin (b.1 r j)) 0 : ℂ) = ((![a, a'] r : ℕ) : ℂ) - 1 := by
    intro r hr
    rw [modExp_three_zero]
    simp only [Fintype.card_fin]
    have h1 := hrow r
    rw [hr] at h1
    have h2 : ((b.1 r 1 + b.1 r 2 : ℕ) : ℂ) = ((![a, a'] r : ℕ) : ℂ) - 1 := by
      rw [← h1]; push_cast; ring
    push_cast at h2 ⊢
    exact h2
  have hneg : ∀ A : ℂ, absPow k ((1 - A) / 2) y = (absPow k ((A - 1) / 2) y)⁻¹ := by
    intro A
    rw [show (1 - A) / 2 = -((A - 1) / 2) by ring, absPow_neg, MonoidHom.inv_apply]
  rw [hneg]
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
  · have h1 : b.1 1 0 = 0 := by omega
    rw [h1, pow_zero, map_one, map_one, hi, pow_one, ← hrow' 0 hi]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one]
    ring
  · have h0 : b.1 0 0 = 0 := by omega
    rw [h0, pow_zero, map_one, map_one, hi, pow_one, ← hrow' 1 hi]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one]
    ring

theorem relProj_thirdBlockScalar {N : ℕ} {γ : Type} [Fintype γ] [LinearOrder γ]
    {c : Fin 3 → γ → Type} [∀ j r, Fintype (c j r)] [∀ j r, DecidableEq (c j r)]
    (g : ∀ j, (Σ r, c j r) ≃ Fin (tripSizes 1 (N - 2) N j)) (y : kˣ) (j : Fin 3) (r : γ) :
    relProj k g ⟨thirdBlockScalar k N y, thirdBlockScalar_mem_relParab g y⟩ j r =
      Matrix.GeneralLinearGroup.scalar _ (if j = 2 then y else 1) := by
  ext p q
  refine (leviProj_apply k (g j) ⟨thirdBlockScalar k N y j, thirdBlockScalar_mem_relParab g y j trivial⟩ r p q).trans ?_
  show ((thirdBlockScalar k N y j : GL (Fin (tripSizes 1 (N - 2) N j)) k) :
    Matrix (Fin (tripSizes 1 (N - 2) N j)) (Fin (tripSizes 1 (N - 2) N j)) k) _ _ = _
  rw [thirdBlockScalar_apply]
  by_cases h : p = q
  · subst h; simp [Matrix.GeneralLinearGroup.scalar]
  · have h' : g j ⟨r, p⟩ ≠ g j ⟨r, q⟩ := by simpa using h
    simp [Matrix.GeneralLinearGroup.scalar, h, h']

theorem modExp_three_two (m : Fin 3 → Type) [∀ a, Fintype (m a)] :
    modExp m 2 = -((Fintype.card (m 0) : ℤ) + Fintype.card (m 1)) := by
  simp [modExp, Finset.sum_filter, Fin.sum_univ_three]

theorem cellScalar_positionThree_pair {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a a' : ℕ) (χ : Fin 2 → kˣ →* ℂˣ)
    (b : SizeMatrix (fun j : Fin 2 => Fin (![a, a'] j))
      (fun j : Fin 3 => Fin (tripSizes 1 (a + a' - 2) (a + a') j)))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (![a, a'] i))
    (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (tripSizes 1 (a + a' - 2) (a + a') j)) (y : kˣ) (i : Fin 2)
    (h : 2 ≤ a + a') (hi : b.1 i 2 = 1) :
    ((cellScalar f g (pairChar k ![a, a'] χ) ⟨thirdBlockScalar k (a + a') y, thirdBlockScalar_mem_relParab g y⟩ : ℂˣ) : ℂ) =
      (χ i y : ℂ) * (absPow k ((((![a, a'] i : ℕ) : ℂ) - 1) / 2) y : ℂ) := by
  have hy := relProj_thirdBlockScalar (k := k) (N := a + a') g y
  set P := relProj k g ⟨thirdBlockScalar k (a + a') y, thirdBlockScalar_mem_relParab g y⟩ with hP
  have hcol : b.1 0 2 + b.1 1 2 = 1 := by
    have := b.2.2 2
    rw [Fintype.card_fin, Fin.sum_univ_two] at this
    simp [tripSizes] at this
    omega
  have hrow : ∀ r, b.1 r 0 + b.1 r 1 + b.1 r 2 = ![a, a'] r := by
    intro r; have := b.2.1 r; simpa [Fin.sum_univ_three] using this
  have hdet : ∀ j r, Matrix.GeneralLinearGroup.det (P j r) = (if j = 2 then y else 1) ^ b.1 r j := by
    intro j r; rw [hy, det_scalar', Fintype.card_fin]
  have hA : relDeltaHalf k (fun j r => Fin (b.1 r j)) P = 1 := by
    rw [relDeltaHalf_apply]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [deltaHalf_apply, Fin.prod_univ_two, hdet, hdet, modExp_two_zero, modExp_two_one]
    split_ifs with h
    · subst h
      simp only [Fintype.card_fin]
      rcases (by omega : (b.1 0 2 = 0 ∧ b.1 1 2 = 1) ∨ (b.1 0 2 = 1 ∧ b.1 1 2 = 0)) with
        ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp [h0, h1]
    · simp
  have hB : ∀ r, deltaHalf k (fun j => Fin (b.1 r j)) (swapBlocks k (fun r j => Fin (b.1 r j)) P r) =
      absPow k ((modExp (fun j => Fin (b.1 r j)) 2 : ℂ) / 2) (y ^ b.1 r 2) := by
    intro r
    rw [deltaHalf_apply, Fin.prod_univ_three]
    show absPow k _ (Matrix.GeneralLinearGroup.det (P 0 r)) * absPow k _ (Matrix.GeneralLinearGroup.det (P 1 r)) *
      absPow k _ (Matrix.GeneralLinearGroup.det (P 2 r)) = _
    rw [hdet, hdet, hdet]; simp
  have hC : pairChar k ![a, a'] χ (relEmb k f (swapBlocks k (fun r j => Fin (b.1 r j)) P)) =
      χ 0 (y ^ b.1 0 2) * χ 1 (y ^ b.1 1 2) := by
    simp only [pairChar, Fin.prod_univ_two, MonoidHom.mul_apply, MonoidHom.comp_apply,
      Pi.evalMonoidHom_apply, detChar_apply, relEmb_apply, det_leviEmb]
    rw [Fin.prod_univ_three, Fin.prod_univ_three]
    show χ 0 (Matrix.GeneralLinearGroup.det (P 0 0) * Matrix.GeneralLinearGroup.det (P 1 0) *
      Matrix.GeneralLinearGroup.det (P 2 0)) * χ 1 (Matrix.GeneralLinearGroup.det (P 0 1) *
      Matrix.GeneralLinearGroup.det (P 1 1) * Matrix.GeneralLinearGroup.det (P 2 1)) = _
    simp [hdet]
  simp only [cellScalar]
  rw [hA, relDeltaHalf_apply, Fin.prod_univ_two, hB, hB, hC]
  have hrow' : ∀ r, b.1 r 2 = 1 →
      (modExp (fun j => Fin (b.1 r j)) 2 : ℂ) = 1 - ((![a, a'] r : ℕ) : ℂ) := by
    intro r hr
    rw [modExp_three_two]
    simp only [Fintype.card_fin]
    have h1 := hrow r
    rw [hr] at h1
    have h2 : ((b.1 r 0 + b.1 r 1 : ℕ) : ℂ) = ((![a, a'] r : ℕ) : ℂ) - 1 := by
      rw [← h1]; push_cast; ring
    push_cast at h2 ⊢
    rw [h2]; ring
  have hneg : ∀ A : ℂ, absPow k ((A - 1) / 2) y = (absPow k ((1 - A) / 2) y)⁻¹ := by
    intro A
    rw [show (A - 1) / 2 = -((1 - A) / 2) by ring, absPow_neg, MonoidHom.inv_apply]
  rw [hneg]
  rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
  · have h1 : b.1 1 2 = 0 := by omega
    rw [h1, pow_zero, map_one, map_one, hi, pow_one, ← hrow' 0 hi]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one]
    ring
  · have h0 : b.1 0 2 = 0 := by omega
    rw [h0, pow_zero, map_one, map_one, hi, pow_one, ← hrow' 1 hi]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one]
    ring

end Cell
end GlobalTheory.JacLineSplit.Eigen
end
