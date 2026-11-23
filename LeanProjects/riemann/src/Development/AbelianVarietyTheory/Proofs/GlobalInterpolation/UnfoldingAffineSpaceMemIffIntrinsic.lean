import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions

theorem eN_eq_single {F : Type} [Field F] {N i : ℕ} (h : i < N) :
    Loc.eN F N i = Pi.single (⟨i, h⟩ : Fin N) 1 := by
  funext l
  simp only [Loc.eN, Pi.single_apply, Fin.ext_iff]

theorem eN_eq_zero {F : Type} [Field F] {N i : ℕ} (h : ¬ i < N) : Loc.eN F N i = 0 := by
  funext l
  have hl : l.1 ≠ i := fun e => h (e ▸ l.2)
  simp only [Loc.eN, hl, if_false, Pi.zero_apply]

theorem inX_single {F : Type} [Field F] {n c : ℕ} (s : Fin (n + c)) (hs : s.1 < n) :
    Loc.inX F n c (Pi.single ⟨s.1, hs⟩ 1) = Pi.single s 1 := by
  funext l
  rw [inX_apply]
  by_cases hl : l.1 < n
  · simp only [hl, dif_pos, Pi.single_apply, Fin.ext_iff]
  · have hne : l ≠ s := fun e => hl (e ▸ hs)
    simp only [hl, dif_neg, not_false_eq_true, Pi.single_apply, hne, if_false]

theorem unfoldingAffineSpace_mem_iff_intrinsic : ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)), (∃ t : Loc.FC n' c' n c → F, x = Loc.xx1 xj t) ↔ ((∀ v, x (Loc.inX F n' c' v) = Loc.inX F n c (xj v)) ∧ x (Loc.eN F (n' + c') n') = Loc.eN F (n + c) n ∧ ∀ s : ℕ, x (Loc.eN F (n' + c') (n' + s)) - Loc.eN F (n + c) (n + s) ∈ Loc.Ufl F n c s) := by
  intro F _ n' c' n c hc hc' xj x
  subst hc'
  have hy : ∀ {a b : ℕ} (y : (Fin a → F) →ₗ[F] (Fin b → F)) (s : Fin a) (l : Fin b),
      y (Pi.single s 1) l = LinearMap.toMatrix' y l s := by
    intro a b y s l
    rw [LinearMap.toMatrix'_apply]
  have hM : ∀ (t : Loc.FC n' (c + 1) n c → F) (l : Fin (n + c)) (s : Fin (n' + (c + 1))),
      LinearMap.toMatrix' (Loc.xx1 xj t) l s =
        if hf : Loc.IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩
        else if hs : s.1 < n' then (if hl : l.1 < n then LinearMap.toMatrix' xj ⟨l.1, hl⟩ ⟨s.1, hs⟩ else 0)
        else if l.1 = n + (s.1 - n') then 1 else 0 := by
    intro t l s
    simp only [Loc.xx1, LinearMap.toMatrix'_toLin', Matrix.of_apply]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨fun v => ?_, ?_, ?_⟩
    · have hcomp : (Loc.xx1 xj t).comp (Loc.inX F n' (c + 1)) = (Loc.inX F n c).comp xj := by
        refine (Pi.basisFun F (Fin n')).ext fun a => ?_
        rw [Pi.basisFun_apply, LinearMap.comp_apply, LinearMap.comp_apply]
        have hi := inX_single (F := F) (n := n') (c := c + 1) (Fin.castAdd (c + 1) a) a.2
        simp only [Fin.val_castAdd, Fin.eta] at hi
        rw [hi]
        funext l
        rw [hy, hM, inX_apply]
        have hnf : ¬ Loc.IsFree n' n c l.1 (Fin.castAdd (c + 1) a).1 := by
          simp only [Loc.IsFree, Fin.val_castAdd]
          omega
        rw [dif_neg hnf, dif_pos (by simp only [Fin.val_castAdd]; exact a.2)]
        by_cases hl : l.1 < n
        · rw [dif_pos hl, dif_pos hl, hy]
          rfl
        · rw [dif_neg hl, dif_neg hl]
      exact LinearMap.congr_fun hcomp v
    · rw [eN_eq_single (show n' < n' + (c + 1) by omega)]
      funext l
      rw [hy, hM]
      have hnf : ¬ Loc.IsFree n' n c l.1 n' := by
        simp only [Loc.IsFree]
        omega
      rw [dif_neg hnf, dif_neg (lt_irrefl n'), Nat.sub_self, Nat.add_zero]
      simp only [Loc.eN]
    · intro s
      rw [mem_Ufl]
      intro l hl
      rw [Pi.sub_apply]
      by_cases hs : n' + s < n' + (c + 1)
      · rw [eN_eq_single hs, hy, hM]
        have hnf : ¬ Loc.IsFree n' n c l.1 (n' + s) := by
          have := l.2
          simp only [Loc.IsFree]
          omega
        rw [dif_neg hnf, dif_neg (Nat.not_lt.2 (Nat.le_add_right n' s))]
        change (if l.1 = n + (n' + s - n') then (1 : F) else 0) - _ = 0
        rw [Nat.add_sub_cancel_left]
        simp only [Loc.eN, sub_self]
      · rw [eN_eq_zero hs, map_zero]
        have hne : l.1 ≠ n + s := by
          have := l.2
          omega
        simp only [Loc.eN, hne, if_false, Pi.zero_apply, sub_zero]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun p => x (Pi.single p.1.2 1) p.1.1, ?_⟩
    refine (Pi.basisFun F (Fin (n' + (c + 1)))).ext fun s => ?_
    rw [Pi.basisFun_apply]
    funext l
    rw [hy (Loc.xx1 xj _), hM]
    by_cases hf : Loc.IsFree n' n c l.1 s.1
    · rw [dif_pos hf]
    rw [dif_neg hf]
    by_cases hs : s.1 < n'
    · rw [dif_pos hs, ← inX_single s hs, h1, inX_apply]
      by_cases hl : l.1 < n
      · rw [dif_pos hl, dif_pos hl, hy]
      · rw [dif_neg hl, dif_neg hl]
    rw [dif_neg hs]
    have hsj : s.1 = n' + (s.1 - n') := by omega
    have hsingle : (Pi.single s 1 : Fin (n' + (c + 1)) → F) = Loc.eN F (n' + (c + 1)) (n' + (s.1 - n')) := by
      rw [eN_eq_single (show n' + (s.1 - n') < n' + (c + 1) by omega)]
      congr 1
      exact Fin.ext hsj
    rw [hsingle]
    by_cases h0 : s.1 - n' = 0
    · rw [h0]
      change x (Loc.eN F (n' + (c + 1)) n') l = if l.1 = n then 1 else 0
      rw [h2]
      simp only [Loc.eN]
    · have hmem := (mem_Ufl).1 (h3 (s.1 - n')) l (by
        simp only [Loc.IsFree] at hf
        omega)
      rw [Pi.sub_apply, sub_eq_zero] at hmem
      rw [hmem]
      simp only [Loc.eN]

end GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions
