import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PtCellUniq
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellInv
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellGeo
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellFin
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.BridgeLemma

namespace Formalism.L2.SG.Pf.FinXP

section Mono

variable {K : Type} [Field K] [StarRing K] {n : ℕ}

def smono (π : Fin n → Fin n) (c ε : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  fun a b => (if b = π a then c a else 0) * ε b

private theorem matRel_smono_lemma (π : Fin n → Fin n) (hπ : ∀ a, π (π a) = a) (c ε : Fin n → K)
    (A A' : Matrix (Fin n) (Fin n) K) (a b : Fin n) :
    (Aᴴ * smono π c ε + smono π c ε * A') a b =
      star (A (π b) a) * (c (π b) * ε b) + c a * ε (π a) * A' (π a) b := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, smono]
  congr 1
  · rw [Finset.sum_eq_single (π b)]
    · rw [if_pos (hπ b).symm]
    · intro k _ hk
      rw [if_neg (fun h => hk (by rw [h, hπ])), zero_mul, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_single (π a)]
    · rw [if_pos rfl]
    · intro k _ hk
      rw [if_neg hk, zero_mul, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem matRel_smono (π : Fin n → Fin n) (hπ : ∀ a, π (π a) = a) (c ε : Fin n → K) (hc : ∀ a, c a ≠ 0)
    (hε : ∀ a, ε a ≠ 0) (hεs : ∀ (y : Fin n) (h : y.val + 1 < n), ε ⟨y.val + 1, h⟩ = -ε y)
    (hP : ∀ (y : Fin n) (h : y.val + 1 < n),
      ((π ⟨y.val + 1, h⟩).val + 1 = (π y).val ∧ c ⟨y.val + 1, h⟩ = c y) ∨ (π y).val < (π ⟨y.val + 1, h⟩).val) :
    MatRel (smono π c ε) := by
  intro A A' hA hA' hR
  have hE : ∀ a b, star (A (π b) a) * (c (π b) * ε b) + c a * ε (π a) * A' (π a) b = 0 := by
    intro a b
    rw [← matRel_smono_lemma π hπ c ε A A' a b, hR]
    rfl

  have hF1 : ∀ (y : Fin n) (h : y.val + 1 < n), ¬ ((π ⟨y.val + 1, h⟩).val + 1 = (π y).val) →
      A y ⟨y.val + 1, h⟩ = 0 ∧ A' y ⟨y.val + 1, h⟩ = 0 := by
    intro y h hn
    have hlt : (π y).val < (π ⟨y.val + 1, h⟩).val := by
      rcases hP y h with h1 | h1
      · exact absurd h1.1 hn
      · exact h1
    constructor
    · have e := hE ⟨y.val + 1, h⟩ (π y)
      rw [hπ, hA' _ _ (Fin.le_def.mpr hlt.le), mul_zero, add_zero] at e
      exact star_eq_zero.mp ((mul_eq_zero.mp e).resolve_right (mul_ne_zero (hc y) (hε (π y))))
    · have e := hE (π y) ⟨y.val + 1, h⟩
      rw [hπ, hA _ _ (Fin.le_def.mpr hlt.le), star_zero, zero_mul, zero_add] at e
      exact (mul_eq_zero.mp e).resolve_left (mul_ne_zero (hc _) (hε _))

  have hF2 : ∀ (y : Fin n) (h : y.val + 1 < n) (hs : (π ⟨y.val + 1, h⟩).val + 1 = (π y).val),
      A y ⟨y.val + 1, h⟩ = star (A' (π ⟨y.val + 1, h⟩)
        ⟨(π ⟨y.val + 1, h⟩).val + 1, by have := (π y).isLt; omega⟩) := by
    intro y h hs
    have hcc : c ⟨y.val + 1, h⟩ = c y := by
      rcases hP y h with h1 | h1
      · exact h1.2
      · exact absurd h1 (by omega)
    have hzs : (⟨(π ⟨y.val + 1, h⟩).val + 1, by have := (π y).isLt; omega⟩ : Fin n) = π y :=
      Fin.ext hs
    have hεz := hεs (π ⟨y.val + 1, h⟩) (by have := (π y).isLt; omega)
    rw [hzs] at hεz ⊢
    have e := hE ⟨y.val + 1, h⟩ (π y)
    rw [hπ, hcc, hεz] at e
    have e2 : c y * ε (π ⟨y.val + 1, h⟩) *
        (A' (π ⟨y.val + 1, h⟩) (π y) - star (A y ⟨y.val + 1, h⟩)) = 0 := by
      linear_combination e
    have h3 := (mul_eq_zero.mp e2).resolve_left (mul_ne_zero (hc y) (hε _))
    rw [sub_eq_zero.mp h3, star_star]
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : Fin n → Fin n, ∀ y, ψ y = if h : y.val + 1 < n then
      (if (π ⟨y.val + 1, h⟩).val + 1 = (π y).val then π ⟨y.val + 1, h⟩ else y) else y :=
    ⟨_, fun _ => rfl⟩
  have hψ : Function.Involutive ψ := by
    intro y
    by_cases h : y.val + 1 < n
    · by_cases hs : (π ⟨y.val + 1, h⟩).val + 1 = (π y).val
      · have hy : ψ y = π ⟨y.val + 1, h⟩ := by rw [hψdef, dif_pos h, if_pos hs]
        have h' : (π ⟨y.val + 1, h⟩).val + 1 < n := by have := (π y).isLt; omega
        have hzs : (⟨(π ⟨y.val + 1, h⟩).val + 1, h'⟩ : Fin n) = π y := Fin.ext hs
        have hs' : (π ⟨(π ⟨y.val + 1, h⟩).val + 1, h'⟩).val + 1 = (π (π ⟨y.val + 1, h⟩)).val := by
          rw [hzs, hπ, hπ]
        rw [hy, hψdef (π ⟨y.val + 1, h⟩), dif_pos h', if_pos hs', hzs, hπ]
      · have hy : ψ y = y := by rw [hψdef, dif_pos h, if_neg hs]
        rw [hy, hy]
    · have hy : ψ y = y := by rw [hψdef, dif_neg h]
      rw [hy, hy]
  have hg : ∀ y : Fin n, (if h : y.val + 1 < n then A y ⟨y.val + 1, h⟩ else 0) =
      star (if h : (ψ y).val + 1 < n then A' (ψ y) ⟨(ψ y).val + 1, h⟩ else 0) := by
    intro y
    by_cases h : y.val + 1 < n
    · by_cases hs : (π ⟨y.val + 1, h⟩).val + 1 = (π y).val
      · have hy : ψ y = π ⟨y.val + 1, h⟩ := by rw [hψdef, dif_pos h, if_pos hs]
        have h' : (π ⟨y.val + 1, h⟩).val + 1 < n := by have := (π y).isLt; omega
        rw [hy, dif_pos h, dif_pos h']
        exact hF2 y h hs
      · have hy : ψ y = y := by rw [hψdef, dif_pos h, if_neg hs]
        rw [hy, dif_pos h, dif_pos h, (hF1 y h hs).1, (hF1 y h hs).2, star_zero]
    · have hy : ψ y = y := by rw [hψdef, dif_neg h]
      rw [hy, dif_neg h, dif_neg h, star_zero]
  unfold supSum
  rw [Finset.sum_congr rfl (fun y _ => hg y), star_sum]
  exact Equiv.sum_comp (Function.Involutive.toPerm ψ hψ)
    (fun y => star (if h : y.val + 1 < n then A' y ⟨y.val + 1, h⟩ else 0))

end Mono

section PtStruct

variable {K : Type} [Field K]

theorem pperm_step (bs : List (K × ℕ)) (hpos : ∀ b ∈ bs, 1 ≤ b.2) (i : ℕ) (hi : i + 1 < (bs.map Prod.snd).sum) :
    (Formalism.L2.SG.PtCell.pperm bs (i + 1) + 1 = Formalism.L2.SG.PtCell.pperm bs i ∧
      Formalism.L2.SG.PtCell.pval bs (i + 1) = Formalism.L2.SG.PtCell.pval bs i) ∨
      Formalism.L2.SG.PtCell.pperm bs i < Formalism.L2.SG.PtCell.pperm bs (i + 1) := by
  induction bs generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    have hs : 1 ≤ s := hpos (t, s) List.mem_cons_self
    simp only [List.map_cons, List.sum_cons] at hi
    simp only [Formalism.L2.SG.PtCell.pperm, Formalism.L2.SG.PtCell.pval]
    by_cases h1 : i + 1 < s
    · left
      rw [if_pos h1, if_pos (by omega : i < s), if_pos h1, if_pos (by omega : i < s)]
      exact ⟨by omega, rfl⟩
    · by_cases h2 : i < s
      · right
        rw [if_pos h2, if_neg h1]
        omega
      · have h3 := ih (fun b hb => hpos b (List.mem_cons_of_mem _ hb)) (i - s) (by omega)
        rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2, show i + 1 - s = i - s + 1 by omega]
        rcases h3 with ⟨h4, h5⟩ | h4
        · exact Or.inl ⟨by omega, h5⟩
        · exact Or.inr (by omega)

theorem pinv_step {N : ℕ} (p : Point K N) (y : Fin N) (h : y.val + 1 < N) :
    ((Formalism.L2.SG.PtCell.pinv p ⟨y.val + 1, h⟩).val + 1 = (Formalism.L2.SG.PtCell.pinv p y).val ∧
      Formalism.L2.SG.PtCell.pval p.1 (y.val + 1) = Formalism.L2.SG.PtCell.pval p.1 y.val) ∨
      (Formalism.L2.SG.PtCell.pinv p y).val < (Formalism.L2.SG.PtCell.pinv p ⟨y.val + 1, h⟩).val := by
  have := pperm_step p.1 (fun b hb => (p.2.1 b hb).2) y.val (by rw [p.2.2]; exact h)
  simpa only [Formalism.L2.SG.PtCell.pinv] using this

end PtStruct

section Cell

variable {K : Type} [Field K] [StarRing K] {r : ℕ}

theorem matRel_ptSign (w : Point K (r + 1)) :
    MatRel (ptMat w * Matrix.diagonal (fun b : Fin (r + 1) => (-1 : K) ^ (r - b.val))) := by
  have heq : ptMat w * Matrix.diagonal (fun b : Fin (r + 1) => (-1 : K) ^ (r - b.val)) =
      smono (Formalism.L2.SG.PtCell.pinv w) (fun a => Formalism.L2.SG.PtCell.pval w.1 a.val)
        (fun b => (-1 : K) ^ (r - b.val)) := by
    ext a b
    rw [Matrix.mul_diagonal, Formalism.L2.SG.PtCell.ptMat_eq_mono]
    rfl
  rw [heq]
  apply matRel_smono
  · exact Formalism.L2.SG.PtCell.pinv_pinv w
  · intro a
    exact Formalism.L2.SG.PtCell.pval_ne w.1 (fun b hb => (w.2.1 b hb).1) a.val (by rw [w.2.2]; exact a.isLt)
  · intro a
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  · intro y h
    rw [show r - y.val = (r - (y.val + 1)) + 1 by have := y.isLt; omega, pow_succ]
    ring
  · intro y h
    exact pinv_step w y h

theorem matRel_conj {n : ℕ} {L M U : Matrix (Fin n) (Fin n) K} (hL : IsLoUni L) (hU : IsUpUni U) (hM : MatRel M) :
    MatRel (L * M * U) := by
  have hLt : IsUpUni Lᵀ := fun i j => ⟨fun h => (hL j i).1 h, fun h => (hL j i).2 h.symm⟩
  have hLinv : IsLoUni L⁻¹ := by
    have h1 := cinv_inv_up hLt
    rw [← Matrix.transpose_nonsing_inv] at h1
    intro i j
    exact ⟨fun h => (h1 j i).1 h, fun h => (h1 j i).2 h.symm⟩
  have hLd : IsUnit L.det := by
    have : L.det = 1 := by rw [← Matrix.det_transpose]; exact cinv_det_up hLt
    rw [this]
    exact isUnit_one
  have hUd : IsUnit U.det := by
    rw [cinv_det_up hU]
    exact isUnit_one
  have key : L⁻¹ * (L * M * U) * U⁻¹ = M := by
    rw [mul_assoc L M U, ← mul_assoc L⁻¹ L, Matrix.nonsing_inv_mul L hLd, one_mul, mul_assoc,
      Matrix.mul_nonsing_inv U hUd, mul_one]
  exact cell_inv K n L⁻¹ (L * M * U) U⁻¹ hLinv (cinv_inv_up hU) (by rw [key]; exact hM)

theorem matRel_of_cell (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (w : Point K (r + 1))
    (h : IsInCell (ZhatOM Z) w) : MatRel Z := by
  obtain ⟨L, U, hL, hU, hZ⟩ := h
  obtain ⟨D, hDdef⟩ : ∃ D : Matrix (Fin (r + 1)) (Fin (r + 1)) K,
      D = Matrix.diagonal (fun b : Fin (r + 1) => (-1 : K) ^ (r - b.val)) := ⟨_, rfl⟩
  have hsq : ∀ k : ℕ, (-1 : K) ^ k * (-1 : K) ^ k = 1 := fun k => by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hDD : D * D = 1 := by
    rw [hDdef, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext b
    exact hsq _
  have hZD : Z = ZhatOM Z * D := by
    ext a b
    rw [hDdef, Matrix.mul_diagonal]
    simp only [ZhatOM]
    linear_combination (-(Z a b)) * hsq (r - b.val)
  have hU' : IsUpUni (D * U * D) := by
    intro i j
    rw [hDdef]
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    refine ⟨fun h => by rw [(hU i j).1 h]; ring, fun h => ?_⟩
    subst h
    rw [(hU i i).2 rfl, mul_one]
    exact hsq _
  have key : Z = L * (ptMat w * D) * (D * U * D) := by
    calc Z = ZhatOM Z * D := hZD
      _ = L * ptMat w * U * D := by rw [hZ]
      _ = L * ptMat w * (D * D) * U * D := by rw [hDD, mul_one]
      _ = L * (ptMat w * D) * (D * U * D) := by simp only [mul_assoc]
  rw [key]
  have hP := matRel_ptSign w
  rw [← hDdef] at hP
  exact matRel_conj hL hU' hP

end Cell

section Geo

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem Xa_r (F : FlagG S r T) : F.Xa r = F.X := by
  unfold FlagG.Xa FlagG.X
  congr 1
  rw [← Set.image_univ]
  congr 1
  ext i
  simp [i.isLt]

theorem Y_fvec_mem (F : FlagG S r T) {Y : S.V →ₗ[E] S.V} (hY : Y ∈ F.LieN) (ρ : Fin (r + 1)) :
    Y (F.fvec ρ) ∈ F.Xa ρ.val := by
  have hz : F.z ∈ perpS S F.X := by
    show ∀ x ∈ F.X, S.hT x F.z = 0
    intro x hx
    unfold FlagG.X at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact F.z_orth a
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  by_cases hρ : ρ.val < r
  · have hf : F.fvec ρ = F.e ⟨ρ.val, hρ⟩ := by
      unfold FlagG.fvec
      exact Fin.snoc_castSucc (α := fun _ => S.V) F.z F.e ⟨ρ.val, hρ⟩
    rw [hf]
    have hmem : F.e ⟨ρ.val, hρ⟩ ∈ F.Xa (ρ.val + 1) := by
      unfold FlagG.Xa
      exact Submodule.subset_span ⟨⟨ρ.val, hρ⟩, by simp, rfl⟩
    have := hY.2.1 (ρ.val + 1) (by omega) (by omega) _ hmem
    simpa using this
  · have hρr : ρ = Fin.last r := Fin.ext (by have := ρ.isLt; simp only [Fin.val_last]; omega)
    have hf : F.fvec ρ = F.z := by
      rw [hρr]
      simp [FlagG.fvec]
    rw [hf, hρr, Fin.val_last, Xa_r]
    exact hY.2.2 F.z hz

theorem expand_Xa (F : FlagG S r T) (a : ℕ) {y : S.V} (hy : y ∈ F.Xa a) :
    y = ∑ i : Fin r, (if i.val < a then F.coefX y i else 0) • F.e i := by
  have hyX : y ∈ Submodule.span E (Set.range F.e) :=
    Submodule.span_mono (Set.image_subset_range _ _) hy
  obtain ⟨l, hl, hly⟩ := (Finsupp.mem_span_image_iff_linearCombination E).mp hy
  have hrep : F.e_indep.repr ⟨y, hyX⟩ = l := F.e_indep.repr_eq hly
  have hco : ∀ i, F.coefX y i = l i := by
    intro i
    unfold FlagG.coefX
    rw [dif_pos hyX, hrep]
  rw [Finsupp.mem_supported'] at hl
  conv_lhs => rw [← hly]
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hco]
  split_ifs with h
  · rfl
  · rw [hl i h, zero_smul]

def coefM (F : FlagG S r T) (Y : S.V →ₗ[E] S.V) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  fun d ρ => if hd : d.val < ρ.val then F.coefX (Y (F.fvec ρ)) ⟨d.val, by omega⟩ else 0

theorem coefM_strict (F : FlagG S r T) (Y : S.V →ₗ[E] S.V) : StrictUp (coefM F Y) := by
  intro a b h
  unfold coefM
  exact dif_neg (Fin.not_lt.mpr h)

theorem coefM_expand (F : FlagG S r T) {Y : S.V →ₗ[E] S.V} (hY : Y ∈ F.LieN) (ρ : Fin (r + 1)) :
    Y (F.fvec ρ) = ∑ d : Fin (r + 1), coefM F Y d ρ • F.fvec d := by
  rw [Fin.sum_univ_castSucc]
  have hlast : coefM F Y (Fin.last r) ρ = 0 := by
    unfold coefM
    exact dif_neg (by have := ρ.isLt; simp only [Fin.val_last]; omega)
  rw [hlast, zero_smul, add_zero]
  conv_lhs => rw [expand_Xa F ρ.val (Y_fvec_mem F hY ρ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfi : F.fvec (Fin.castSucc i) = F.e i := by
    unfold FlagG.fvec
    simp
  rw [hfi]
  unfold coefM
  by_cases h : i.val < ρ.val
  · rw [if_pos h, dif_pos (by simpa using h)]
    rfl
  · rw [if_neg h, dif_neg (by simpa using h)]

theorem coefM_supSum (F : FlagG S r T) (Y : S.V →ₗ[E] S.V) : supSum (coefM F Y) = F.ell Y := by
  unfold supSum FlagG.ell
  rw [Fin.sum_univ_castSucc, dif_neg (by simp), add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dif_pos (by simp)]
  unfold coefM
  rw [dif_pos (by simp)]
  rfl

theorem rel_of_matRel (K : Type) [Field K] [Algebra K E]
    (htr : ∀ x : E, algebraMap K E (Algebra.trace K E x) = x + star x)
    (F : FlagG S r T) (F' : FlagG S r T') (h : MatRel (Zhat F F')) : Relevant K F F' := by
  intro Y hY
  have hYF : Y ∈ F.LieN := hY.1
  have hYF' : Y ∈ F'.LieN := hY.2
  have hLie : Y ∈ LieU S := hYF.1
  have hR : (coefM F Y)ᴴ * Zhat F F' + Zhat F F' * coefM F' Y = 0 := by
    ext a b
    have e := hLie (F.fvec a) (F'.fvec b)
    rw [coefM_expand F hYF a, coefM_expand F' hYF' b] at e
    simp only [map_sum, map_smulₛₗ, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply] at e
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.zero_apply,
      Zhat, brS]
    rw [← e]
    congr 1
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hs := h (coefM F Y) (coefM F' Y) (coefM_strict F Y) (coefM_strict F' Y) hR
  rw [coefM_supSum, coefM_supSum] at hs
  unfold FlagG.dpsi
  rw [hs]
  apply (algebraMap K E).injective
  rw [htr, htr, star_star, add_comm]

theorem relevant_of_cell (K : Type) [Field K] [Algebra K E]
    (htr : ∀ x : E, algebraMap K E (Algebra.trace K E x) = x + star x)
    (F : FlagG S r T) (F' : FlagG S r T') (w : Point E (r + 1)) (h : IsInCell (ZhatOM (Zhat F F')) w) :
    Relevant K F F' := by
  exact rel_of_matRel K htr F F' (matRel_of_cell _ w h)

end Geo

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def AtPtRelevantAll : Prop :=
  ∀ (D : D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (t : Formalism.L2.SG.TermDef.Term D u u' F0 what₂)
    (w : Point D.host.E (D.R.rS + 1)), t.atPt w → t.relevant

theorem atPtRelevant_holds : AtPtRelevantAll := by
  intro D u u' F0 what₂ t w h
  obtain ⟨F', hrep, -, hcell⟩ := h
  exact ⟨F', hrep, relevant_of_cell D.host.F (tie_trace D.sp.cm) _ _ w hcell⟩

end Formalism.L2.SG.Pf.FinXP

end
