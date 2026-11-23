import Formalism.LocalToGlobal.Columns.RecLevelDiv
import Formalism.LocalToGlobal.Columns.RowFormsSym

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP St redAt redFn)

section ColsSym

open Formalism.BasicNotions (Ranks)

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem r_le_N_of_le {j : ℕ} (hj : R.m ≤ j + 1) : R.r ≤ R.N j := by
  have h1 := N_eq_blocks R j
  have h2 := Ranks.r_eq (R := R)
  rw [h1]
  generalize j * R.t = z at *
  omega

theorem colK_le_N (R : Ranks) (j : ℕ) : R.k ≤ R.N j := by
  rw [N_eq_blocks]
  exact le_add_right (Nat.le_add_right _ _)

theorem Y_eq_X_add {j : ℕ} (hj : j + 1 ≤ R.m) : R.r + j * R.t = R.N j + (R.m - 1 - j) := by
  have h1 := N_eq_blocks R j
  have h2 := Ranks.r_eq (R := R)
  rw [h1]
  generalize j * R.t = z at *
  omega

theorem r_le_Y {j : ℕ} (hj : j + 1 ≤ R.m) : R.r ≤ R.N j + (R.m - 1 - j) := by
  rw [← Y_eq_X_add hj]
  exact Nat.le_add_right _ _

def colLevSym (Ch : Chars X Pr R.m) (j : ℕ) : LevFam X.E X.K (R.N j) Pr.vGs := fun w =>
  if j = 0 then colLev Ch j w
  else if h1 : j + 1 < R.m then
    ⟨(HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS (r_le_Y (by omega))).comap
        (insGL (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) (R.m - 1 - j) R.k (R.N j + (R.m - 1 - j)) (colK_le_N R j) rfl),
      (lamJsym (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS (r_le_Y (by omega))).comp
        ((insGL (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) (R.m - 1 - j) R.k (R.N j + (R.m - 1 - j)) (colK_le_N R j) rfl).subgroupComap _)⟩
  else if hj : j + 1 = R.m then
    ⟨HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.r R.t j R.rS (r_le_N_of_le hj.ge),
      lamJsym (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.r R.t j R.rS (r_le_N_of_le hj.ge)⟩
  else
    ⟨HXmsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.r R.t R.m R.rS (r_le_N_of_le (by omega)),
      lamXmsym (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.r R.t R.m R.rS (r_le_N_of_le (by omega))⟩

@[reducible] def colGSDSym (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (u : Pr.Word) (j : ℕ) : GSD X.K :=
  formGSD (colVal W u j (Pr.vT u) Pr.vGs) (colLevSym Ch j)

variable (hc : Formalism.BasicNotions.CMData X.F X.E) (Ch : Chars X Pr R.m)

def colUSym (u : Pr.Word) (j : ℕ) : Subgroup (GL (Fin (R.N j)) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) :=
  levU hc (R.N j) (Pr.vT u) Pr.vGs (colLevSym Ch j).grp

def colTypSym (u : Pr.Word) (j : ℕ) : colUSym hc Ch u j →* X.Kˣ := levTyp (colLevSym Ch j).chr

end ColsSym

section SymTies

open Formalism.BasicNotions (Ranks)

variable {X : Fields} {Pr : Primes X} {R : Ranks} (hc : Formalism.BasicNotions.CMData X.F X.E) (Ch : Chars X Pr R.m)

theorem colLevSym_pred {j : ℕ} (hj : j + 1 = R.m) :
    colLevSym Ch j = parFam (r_le_N_of_le hj.ge) R.t j (rPsymF Ch) (fun w => extChi fun s => Ch.chi s w) := by
  funext w
  unfold colLevSym
  rw [if_neg (by have := R.two_le_m; omega), dif_neg (by omega), dif_pos hj]
  rfl

theorem colLevSym_top_H {j : ℕ} (hj : R.m ≤ j) (w : Pr.vGs) :
    (colLevSym Ch j w).H = HXmsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.r R.t R.m R.rS (r_le_N_of_le (by omega)) := by
  have h2 := R.two_le_m
  unfold colLevSym
  rw [if_neg (by omega), dif_neg (by omega), dif_neg (by omega)]

theorem colLevSym_top_lam {j : ℕ} (hj : R.m ≤ j) (w : Pr.vGs) (M : ↥(colLevSym Ch j w).H)
    (hM : M.1 ∈ HXmsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.r R.t R.m R.rS (r_le_N_of_le (by omega))) :
    (colLevSym Ch j w).lam M =
      lamXmsym (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.r R.t R.m R.rS (r_le_N_of_le (by omega)) ⟨M.1, hM⟩ := by
  have key : ∀ l : Lev (𝓞 X.E ⧸ w.1.asIdeal) X.K (R.N j), l = colLevSym Ch j w → ∀ (M' : ↥l.H) (hM' : M'.1 ∈ HXmsym
      (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.r R.t R.m R.rS (r_le_N_of_le (by omega))),
      l.lam M' = lamXmsym (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.r R.t R.m R.rS (r_le_N_of_le (by omega)) ⟨M'.1, hM'⟩ := by
    intro l hl M' hM'
    have hl' : l = ⟨HXmsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.r R.t R.m R.rS (r_le_N_of_le (by omega)),
        lamXmsym (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.r R.t R.m R.rS (r_le_N_of_le (by omega))⟩ := by
      rw [hl]; unfold colLevSym; rw [if_neg (by have := R.two_le_m; omega), dif_neg (by omega), dif_neg (by omega)]
    subst hl'
    rfl
  exact key _ rfl M hM

theorem N_pred_eq {j : ℕ} (hj : j + 1 = R.m) : R.N j = R.r + j * R.t := by
  have h := Y_eq_X_add (R := R) (j := j) (by omega)
  rw [show R.m - 1 - j = 0 by omega, add_zero] at h
  exact h.symm

theorem colUSym_eq_lev (u : Pr.Word) {j : ℕ} (hj : j + 1 = R.m) :
    colUSym hc Ch u j = Formalism.L2.DIV.lev hc 1 1
        (parDat (r_le_N_of_le hj.ge) R.t j (rPsymF Ch) (fun w => extChi fun s => Ch.chi s w)) ⊓
      ⨅ Q ∈ Pr.vT u, mirAt (F := X.F) (R.N j) Q := by
  unfold colUSym
  rw [colLevSym_pred Ch hj]
  exact levU_parFam_eq_lev_inf hc (r_le_N_of_le hj.ge) (t_pos R) (N_pred_eq hj) _ _ _

theorem colLevSym_zero : colLevSym Ch 0 = colLev Ch 0 := by
  funext w
  simp [colLevSym]

theorem colLevSym_mid_H {j : ℕ} (h0 : j ≠ 0) (h1 : j + 1 < R.m) (w : Pr.vGs) :
    (colLevSym Ch j w).H = (HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS (r_le_Y (by omega))).comap
      (insGL (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) (R.m - 1 - j) R.k (R.N j + (R.m - 1 - j)) (colK_le_N R j) rfl) := by
  unfold colLevSym
  rw [if_neg h0, dif_pos h1]

theorem colLevSym_mid_lam {j : ℕ} (h0 : j ≠ 0) (h1 : j + 1 < R.m) (w : Pr.vGs) (M : ↥(colLevSym Ch j w).H)
    (hM : insGL (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) (R.m - 1 - j) R.k (R.N j + (R.m - 1 - j)) (colK_le_N R j) rfl M.1 ∈
      HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS (r_le_Y (by omega))) :
    (colLevSym Ch j w).lam M = lamJsym (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS
      (r_le_Y (by omega)) ⟨_, hM⟩ := by
  have key : ∀ l : Lev (𝓞 X.E ⧸ w.1.asIdeal) X.K (R.N j), l = colLevSym Ch j w → ∀ (M' : ↥l.H) (hM' : insGL (𝓞 X.E ⧸ w.1.asIdeal) (R.N j)
      (R.m - 1 - j) R.k (R.N j + (R.m - 1 - j)) (colK_le_N R j) rfl M'.1 ∈
      HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS (r_le_Y (by omega))),
      l.lam M' = lamJsym (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS (r_le_Y (by omega)) ⟨_, hM'⟩ := by
    intro l hl M' hM'
    have hl' : l = ⟨(HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS (r_le_Y (by omega))).comap
          (insGL (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) (R.m - 1 - j) R.k (R.N j + (R.m - 1 - j)) (colK_le_N R j) rfl),
        (lamJsym (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS (r_le_Y (by omega))).comp
          ((insGL (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) (R.m - 1 - j) R.k (R.N j + (R.m - 1 - j)) (colK_le_N R j) rfl).subgroupComap _)⟩ := by
      rw [hl]; unfold colLevSym; rw [if_neg h0, dif_pos h1]
    subst hl'
    rfl
  exact key _ rfl M hM

end SymTies

section SymDivTies

variable {κ : Type} [CommRing κ] {K : Type} [Field K]

theorem HPsym_eq_unipSym (r k rS : ℕ) : HPsym κ r k rS = Formalism.L2.DIV.unipSym κ r rS k := by
  ext M
  show ((_ ∧ _) ∧ _) ↔ ((_ ∧ _) ∧ _)
  have e1 : (M : Matrix (Fin r) (Fin r) κ).BlockTriangular (fun i => fine r [] i.val) ↔
      (M : Matrix (Fin r) (Fin r) κ).BlockTriangular (fun i => i.val) := by
    have : (fun i : Fin r => fine r [] i.val) = (fun i => i.val) := funext fun i => fine_self_lt i.2
    rw [this]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨e1.mp h1, fun i => h2 i i.2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨e1.mpr h1, fun i _ => h2 i⟩, h3⟩

theorem HPsymF_eq_comap_unipSym (r k rS : ℕ) :
    HPsymF κ r k rS = (Formalism.L2.DIV.unipSym κ r rS k).comap (toSymOrd κ r k rS) := by
  rw [HPsymF, HPsym_eq_unipSym]

theorem sym_sum_split {r k rS : ℕ} (M : GL (Fin r) κ) :
    supSum r (SPsym r k rS) (M : Matrix (Fin r) (Fin r) κ) + offSum k rS (M : Matrix (Fin r) (Fin r) κ) =
      Formalism.L2.DIV.edgeSum (Formalism.L2.DIV.symEdge rS k) M := by
  unfold supSum offSum Formalism.L2.DIV.edgeSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj := j.2
  rcases Decidable.em (Formalism.L2.DIV.symEdge rS k i j) with hE | hE
  · rw [if_pos hE]
    unfold Formalism.L2.DIV.symEdge at hE
    simp only [SPsym, Finset.mem_filter, Finset.mem_range]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [if_neg hE]
    unfold Formalism.L2.DIV.symEdge at hE
    simp only [SPsym, Finset.mem_filter, Finset.mem_range]
    split_ifs <;> first | (exfalso; omega) | simp

theorem chiSym_eq_symHom (ψ : AddChar κ K) (r k rS : ℕ) (M : ↥(HPsym κ r k rS)) (hM : M.1 ∈ Formalism.L2.DIV.unipSym κ r rS k) :
    ((chiSym ψ r k rS M : Kˣ) : K) = ((Formalism.L2.DIV.addCharHom ψ (Formalism.L2.DIV.symHom κ r rS k) ⟨M.1, hM⟩ : Kˣ) : K) := by
  show ψ (supSum r (SPsym r k rS) (M.1 : Matrix (Fin r) (Fin r) κ)) * ψ (offSum k rS (M.1 : Matrix (Fin r) (Fin r) κ)) =
    ψ (Formalism.L2.DIV.edgeSum (Formalism.L2.DIV.symEdge rS k) M.1)
  rw [← AddChar.map_add_eq_mul, sym_sum_split]

def SPsymF (n k : ℕ) : Finset ℕ := (Finset.range (n - 1)).filter fun i => i + 1 ≠ k

theorem symEdge_symPerm_iff {n k rS : ℕ} (hn : n = k + 2 * rS + 1) (i j : Fin n) :
    Formalism.L2.DIV.symEdge rS k (symPerm n k rS i) (symPerm n k rS j) ↔
      (i.val + 1 = j.val ∧ j.val < n ∧ i.val ∈ SPsymF n k) := by
  have h : k + rS ≤ n := by omega
  unfold Formalism.L2.DIV.symEdge
  rw [symPerm_val h, symPerm_val h]
  simp only [SPsymF, Finset.mem_filter, Finset.mem_range]
  have hi := i.2
  have hj := j.2
  unfold symIdx
  split_ifs <;> omega

theorem chiSymF_val {n k rS : ℕ} (hn : n = k + 2 * rS + 1) (ψ : AddChar κ K) (M : ↥(HPsymF κ n k rS)) :
    ((chiSymF ψ n k rS M : Kˣ) : K) = ψ (supSum n (SPsymF n k) (M.1 : Matrix (Fin n) (Fin n) κ)) := by
  have hM : toSymOrd κ n k rS M.1 ∈ Formalism.L2.DIV.unipSym κ n rS k := by
    have := M.2
    rw [mem_HPsymF, HPsym_eq_unipSym] at this
    exact this
  rw [chiSymF_apply, chiSym_eq_symHom ψ n k rS _ hM]
  show ψ (Formalism.L2.DIV.edgeSum (Formalism.L2.DIV.symEdge rS k) (toSymOrd κ n k rS M.1)) = _
  congr 1
  unfold Formalism.L2.DIV.edgeSum supSum
  rw [← Equiv.sum_comp (symPerm n k rS)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp (symPerm n k rS)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toSymOrd_val']
  by_cases hE : Formalism.L2.DIV.symEdge rS k (symPerm n k rS i) (symPerm n k rS j)
  · rw [if_pos hE, if_pos ((symEdge_symPerm_iff hn i j).mp hE)]
  · rw [if_neg hE, if_neg (fun h => hE ((symEdge_symPerm_iff hn i j).mpr h))]

end SymDivTies

section SymRanks

open Formalism.BasicNotions (Ranks)

theorem r_eq_sym (R : Ranks) : R.r = R.k + 2 * R.rS + 1 := by
  have h1 := Ranks.r_eq (R := R)
  have h2 := Ranks.rS_two (R := R)
  omega

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)

theorem rPsymF_lam_val (w : {w // w ∈ Pr.vGs}) (M : ↥(rPsymF Ch w).H) :
    (((rPsymF Ch w).lam M : X.Kˣ) : X.K) =
      Ch.psi0 w (supSum R.r (SPsymF R.r R.k) (M.1 : Matrix (Fin R.r) (Fin R.r) (𝓞 X.E ⧸ w.1.asIdeal))) :=
  chiSymF_val (r_eq_sym R) (Ch.psi0 w) M

end SymRanks

end Formalism.L2.Col
