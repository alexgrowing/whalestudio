import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagBundle
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumSymm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace NumericalSegreProof

section Combinatorics

theorem sum_antidiagonalTuple_succ {A : Type*} [AddCommMonoid A] (i c : ℕ)
    (f : (Fin (i + 1) → ℕ) → A) :
    ∑ α ∈ Finset.Nat.antidiagonalTuple (i + 1) (c + 1), f α =
      ∑ α ∈ Finset.Nat.antidiagonalTuple i (c + 1), f (Fin.snoc α 0) +
        ∑ β ∈ Finset.Nat.antidiagonalTuple (i + 1) c,
          f (Function.update β (Fin.last i) (β (Fin.last i) + 1)) := by
  have hsum : ∀ (α : Fin (i + 1) → ℕ) (v : ℕ),
      ∑ j, Function.update α (Fin.last i) v j = ∑ j : Fin i, α (Fin.castSucc j) + v := by
    intro α v
    rw [Fin.sum_univ_castSucc]
    simp
  have hsum' : ∀ α : Fin (i + 1) → ℕ,
      ∑ j, α j = ∑ j : Fin i, α (Fin.castSucc j) + α (Fin.last i) := fun α =>
    Fin.sum_univ_castSucc α
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun α : Fin (i + 1) → ℕ => α (Fin.last i) = 0)]
  congr 1
  · refine Finset.sum_nbij' Fin.init (fun α => Fin.snoc α 0) ?_ ?_ ?_ ?_ ?_
    · intro α hα
      simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hα ⊢
      rw [hsum'] at hα
      simpa [Fin.init, hα.2] using hα.1
    · intro α hα
      simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hα ⊢
      refine ⟨?_, by simp⟩
      rw [hsum']
      simpa using hα
    · intro α hα
      simp only [Finset.mem_filter] at hα
      rw [← hα.2, Fin.snoc_init_self]
    · intro α _
      exact Fin.init_snoc _ _
    · intro α hα
      simp only [Finset.mem_filter] at hα
      rw [← hα.2, Fin.snoc_init_self]
  · have linv : ∀ α : Fin (i + 1) → ℕ, α (Fin.last i) ≠ 0 →
        Function.update (Function.update α (Fin.last i) (α (Fin.last i) - 1)) (Fin.last i)
          (Function.update α (Fin.last i) (α (Fin.last i) - 1) (Fin.last i) + 1) = α := by
      intro α hα
      rw [Function.update_self, Function.update_idem, Nat.sub_add_cancel (Nat.pos_of_ne_zero hα),
        Function.update_eq_self]
    refine Finset.sum_nbij' (fun α => Function.update α (Fin.last i) (α (Fin.last i) - 1))
      (fun β => Function.update β (Fin.last i) (β (Fin.last i) + 1)) ?_ ?_ ?_ ?_ ?_
    · intro α hα
      simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hα ⊢
      rw [hsum]
      rw [hsum'] at hα
      omega
    · intro β hβ
      simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hβ ⊢
      rw [hsum, Function.update_self]
      rw [hsum'] at hβ
      refine ⟨by omega, by omega⟩
    · intro α hα
      simp only [Finset.mem_filter] at hα
      exact linv α hα.2
    · intro β _
      simp
    · intro α hα
      simp only [Finset.mem_filter] at hα
      rw [linv α hα.2]

end Combinatorics

section Lists

variable {K : Type*} [DecidableEq K]

omit [DecidableEq K] in

theorem rootList_succ {i : ℕ} (x : Fin (i + 1) → K → ℤ) (α : Fin (i + 1) → ℕ) :
    rootList x α = rootList (fun j => x (Fin.castSucc j)) (Fin.init α) ++
      List.replicate (α (Fin.last i)) (x (Fin.last i)) := by
  unfold rootList
  rw [List.finRange_succ_last]
  simp [List.flatMap_append, Fin.init, List.flatMap_map]

omit [DecidableEq K] in
theorem rootList_snoc_zero {i : ℕ} (x : Fin (i + 1) → K → ℤ) (α : Fin i → ℕ) :
    rootList x (Fin.snoc α 0) = rootList (fun j => x (Fin.castSucc j)) α := by
  rw [rootList_succ, Fin.init_snoc, Fin.snoc_last]
  simp

omit [DecidableEq K] in
theorem rootList_update_last {i : ℕ} (x : Fin (i + 1) → K → ℤ) (β : Fin (i + 1) → ℕ) :
    rootList x (Function.update β (Fin.last i) (β (Fin.last i) + 1)) =
      rootList x β ++ [x (Fin.last i)] := by
  have hinit : Fin.init (Function.update β (Fin.last i) (β (Fin.last i) + 1)) = Fin.init β := by
    funext j
    simp [Fin.init]
  rw [rootList_succ, rootList_succ x β, hinit, Function.update_self, List.replicate_succ',
    List.append_assoc]

omit [DecidableEq K] in
theorem rootList_zero {n : ℕ} (x : Fin n → K → ℤ) : rootList x 0 = [] := by
  simp [rootList]

theorem intNumL_eq {ι : K → Type*} (F : Type*) [Field F] (P : Ideal (MRing ι F))
    (l : List (K → ℤ)) : intNumL F P l = eventualValue (l.foldr diffStep (hilbFn P)) := by
  unfold intNumL intNum mixedDiff
  rw [List.ofFn_get]

theorem intNumL_perm {ι : K → Type*} (F : Type*) [Field F] (P : Ideal (MRing ι F))
    {l l' : List (K → ℤ)} (h : l.Perm l') : intNumL F P l = intNumL F P l' := by
  rw [intNumL_eq, intNumL_eq, h.foldr_eq]

end Lists

def segreSide {K : Type*} [DecidableEq K] {ι : K → Type*} (F : Type*) [Field F]
    (P : Ideal (MRing ι F)) {i : ℕ} (x : Fin i → K → ℤ) (n : ℕ) (Y : List (K → ℤ)) : ℤ :=
  if i - 1 ≤ n then
    ∑ α ∈ Finset.Nat.antidiagonalTuple i (n - (i - 1)), intNumL F P (rootList x α ++ Y)
  else 0

theorem segreSide_succ {K : Type*} [DecidableEq K] {ι : K → Type*} (F : Type*) [Field F]
    (P : Ideal (MRing ι F)) {i : ℕ} (hi : 1 ≤ i) (x : Fin (i + 1) → K → ℤ) (m : ℕ)
    (Y : List (K → ℤ)) :
    segreSide F P x (m + 1) Y =
      segreSide F P (fun j => x (Fin.castSucc j)) m Y +
        segreSide F P x m (x (Fin.last i) :: Y) := by
  unfold segreSide
  simp only [Nat.add_sub_cancel]
  by_cases h : i ≤ m + 1
  · obtain ⟨c, hc⟩ : ∃ c, m + 1 = i + c := ⟨m + 1 - i, by omega⟩
    rw [if_pos h, if_pos (by omega), show m + 1 - i = c by omega, show m - (i - 1) = c by omega]
    rcases c with _ | c
    · rw [if_neg (by omega), add_zero, Finset.Nat.antidiagonalTuple_zero_right,
        Finset.Nat.antidiagonalTuple_zero_right, Finset.sum_singleton, Finset.sum_singleton,
        rootList_zero, rootList_zero]
    · rw [if_pos (by omega), show m - i = c by omega, sum_antidiagonalTuple_succ]
      congr 1
      · refine Finset.sum_congr rfl fun α _ => ?_
        rw [rootList_snoc_zero]
      · refine Finset.sum_congr rfl fun β _ => ?_
        rw [rootList_update_last, List.append_assoc, List.singleton_append]
  · rw [if_neg h, if_neg (by omega), if_neg (by omega), add_zero]

theorem zetaDeg_split {K : Type*} (a c : K → ℤ) :
    ((zetaDeg + liftDeg (c - a)) + liftDeg (a - c) : Option K → ℤ) = zetaDeg := by
  funext o
  cases o <;> simp [zetaDeg, liftDeg]

theorem truncCoord_of_le {N : ℕ} {Φ : Type*} [Zero Φ] (t : Fin N → Φ) {i : ℕ} (h : N ≤ i) :
    truncCoord t i = t := by
  funext j
  simp [truncCoord, lt_of_lt_of_le j.isLt h]

theorem intNumL_cons_add (hadd : FieldNumbers.IntNumAdd.Statement.{0}) (F : Type) [Field F]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P) (l : List (K → ℤ))
    (hd : FieldNumbers.relDim P = ((l.length + 1 : ℕ) : WithBot (WithTop ℤ))) (c c' : K → ℤ) :
    intNumL F P ((c + c') :: l) = intNumL F P (c :: l) + intNumL F P (c' :: l) := by
  have key : ∀ d, Function.update (c :: l).get (0 : Fin (l.length + 1)) d = (d :: l).get := by
    intro d
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · rw [Function.update_of_ne (Fin.succ_ne_zero j)]
      rfl
  have h := hadd F K ι P hP.multiHomog hP.relevant (l.length + 1) hd ((c :: l).get) 0 c c'
  rw [key, key, key] at h
  exact h

end NumericalSegreProof

open NumericalSegreProof in

theorem NumericalSegre.proof (hadd : FieldNumbers.IntNumAdd.Statement.{0})
    (hdim : FlagBundleDim.Statement) (hcut : FlagBundleCut.Statement)
    (hvan : FlagBundlePullbackVanish.Statement) (hbase : FlagBundleLineBase.Statement) :
    NumericalSegre.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hP hdimV N hN E _ _ B w b hflag M a φ hφ Φ _ _ t ht n Y hnY
  have claim : ∀ i : ℕ, 1 ≤ i → ∀ hi : i ≤ N, ∀ (n : ℕ) (Y : List (K → ℤ)),
      n + Y.length + 1 = e + i →
      intNumL F (projIdeal F y w φ (truncCoord t i)) (List.replicate n zetaDeg ++ Y.map liftDeg) =
        segreSide F (pointIdeal F y) (fun j : Fin i => a - b (Fin.castLE hi j)) n Y := by
    intro i hi1
    induction i, hi1 using Nat.le_induction with
    | base =>
      intro hi n Y hnY
      rw [hbase F Ω K ι y e hP hdimV N E B w b hflag M a φ hφ Φ t ht hi n Y (by omega)]
      simp [segreSide, Finset.Nat.antidiagonalTuple_one, rootList, List.finRange_succ]
      rfl
    | succ i hi1 ih =>
      intro hi n
      induction n with
      | zero =>
        intro Y hY
        rw [List.replicate_zero, List.nil_append,
          hvan F Ω K ι y e hP hdimV N E B w b hflag M a φ hφ Φ t ht (i + 1) (by omega) hi Y
            (by omega)]
        unfold segreSide
        rw [if_neg (by omega)]
      | succ m ihm =>
        intro Y hY
        set l := List.replicate m (zetaDeg : Option K → ℤ) ++ Y.map liftDeg with hl
        have hlen : l.length + 1 = e + i := by
          simp [hl]
          omega
        obtain ⟨hPi, hdi⟩ := hdim F Ω K ι y e hP hdimV N E B w b hflag M a φ hφ Φ t ht (i + 1)
          (by omega) hi
        rw [show e + (i + 1) - 1 = l.length + 1 by omega] at hdi
        rw [List.replicate_succ, List.cons_append, ← hl,
          ← zetaDeg_split a (b ⟨i, hi⟩), intNumL_cons_add hadd F _ hPi l hdi]
        have hc := hcut F Ω K ι y e hP hdimV N E B w b hflag M a φ hφ Φ t ht ⟨i, hi⟩ hi1 l hlen
        simp only at hc
        rw [hc, ih (by omega) m Y (by omega)]
        have hperm : (liftDeg (a - b ⟨i, hi⟩) :: l).Perm
            (List.replicate m zetaDeg ++ ((a - b ⟨i, hi⟩) :: Y).map liftDeg) := by
          rw [hl, List.map_cons]
          exact List.perm_middle.symm
        rw [intNumL_perm F _ hperm, ihm _ (by simp; omega), segreSide_succ F _ hi1]
        rfl
  rw [← truncCoord_of_le t (le_refl N), claim N hN (le_refl N) n Y (by omega)]
  rfl

end

end GroundTheory.Heights₂.Heights.NumbersDVR
