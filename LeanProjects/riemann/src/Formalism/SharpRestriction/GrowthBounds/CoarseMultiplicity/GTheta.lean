import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.OtherEFree

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.CovariantDegrees

theorem op_single_add {K σ : Type} [Field K] (a : σ) (b : ℕ) (f : σ →₀ ℕ) (ha : a ∉ f.support) (u : MvPolynomial σ K) :
    monomial (Finsupp.single a b + f) (1 : K) * divDer (Finsupp.single a b + f) u =
      cth a b (monomial f (1 : K) * divDer f u) := by
  classical
  ext μ
  rw [eig_one, coeff_cth, eig_one]
  have hd : Disjoint (Finsupp.single a b).support f.support := by
    refine Finset.disjoint_of_subset_left Finsupp.support_single_subset ?_
    rw [Finset.disjoint_singleton_left]
    exact ha
  rw [Finsupp.prod_add_index_of_disjoint hd, Finsupp.prod_single_index (by simp)]
  push_cast
  ring

section GlobalTheory

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)] {N r : ℕ} [NeZero r]

theorem op_SSt (D7 : Formalism.BasicNotions.D7) {D : BlockData N} (hT : TieOK D) (ν : BVar N r D.T.t →₀ ℕ) :
    (∀ v ∈ ν.support, OddV D v) → ∀ (thr thr' : Fin D.T.q → WithTop ℤ),
    (∀ k, thr k + (((ν.sum fun _ n => n : ℕ) : ℤ) : WithTop ℤ) ≤ thr' k) →
    ∀ u ∈ SSt O r D thr, monomial ν (1 : KK O) * divDer ν u ∈ SSt O r D thr' := by
  classical
  induction ν using Finsupp.induction with
  | zero =>
    intro _ thr thr' hthr u hu
    rw [divDer_zero]
    have : (monomial (0 : BVar N r D.T.t →₀ ℕ) (1 : KK O)) = 1 := rfl
    rw [this, one_mul]
    exact SSt_mono D (fun k => by simpa using hthr k) hu
  | single_add a b f ha hb ih =>
    intro hv thr thr' hthr u hu
    rw [op_single_add a b f ha]
    have hsum : ((Finsupp.single a b + f).sum fun _ n => n) = b + f.sum fun _ n => n := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    have hsupp : (Finsupp.single a b + f).support = insert a f.support := by
      rw [Finsupp.support_add_eq, Finsupp.support_single_ne_zero _ hb]
      · rfl
      · rw [Finsupp.support_single_ne_zero _ hb, Finset.disjoint_singleton_left]
        exact ha
    have h1 := ih (fun v hvf => hv v (by rw [hsupp]; exact Finset.mem_insert_of_mem hvf)) thr
      (fun k => thr k + (((f.sum fun _ n => n : ℕ) : ℤ) : WithTop ℤ)) (fun _ => le_rfl) u hu
    refine cth_SSt D7 hT b (fun k => ?_) a (hv a (by rw [hsupp]; exact Finset.mem_insert_self _ _)) h1
    refine le_trans (le_of_eq ?_) (hthr k)
    rw [hsum, add_assoc]
    push_cast
    rw [add_comm ((b : ℕ) : WithTop ℤ)]

end GlobalTheory

theorem tieOK_blockBase (p : ℕ) {r s : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (b : SegBlock s r) :
    TieOK (blockBase p S aTop aPlus b) where
  lt := by
    intro i
    have := (uTop S i).2
    show 2 * ((uTop S i : Fin s) : ℕ) + 1 < 2 * s + 1
    omega
  inj := by
    intro i i' h
    have h' : 2 * ((uTop S i : Fin s) : ℕ) = 2 * ((uTop S i' : Fin s) : ℕ) := h
    simp only [uTop] at h'
    exact Fin.ext (by omega)
  sep := by
    intro i i' h
    have h' : 2 * ((uTop S i : Fin s) : ℕ) + 1 = 2 * ((uTop S i' : Fin s) : ℕ) := h
    omega
  uW := by
    intro i
    have := (uTop S i).2
    constructor
    · show 2 * ((uTop S i : Fin s) : ℕ) ≠ 2 * s
      omega
    · show 2 * ((uTop S i : Fin s) : ℕ) + 1 ≠ 2 * s
      omega
  vecE := by
    intro i h
    show decide ((2 * ((uTop S i : Fin s) : ℕ) + 1) % 2 = 0) = false
    simp

theorem thr_shift (x : WithTop ℤ) (mm : ℝ) (n c4 : ℕ) (h : n ≤ c4) :
    x.map (fun y : ℤ => ⌊(y : ℝ) - mm⌋) + ((n : ℤ) : WithTop ℤ) ≤ x.map (fun y : ℤ => ⌊(y : ℝ) - (mm - (c4 : ℝ))⌋) := by
  cases x with
  | top => simp
  | coe y =>
    simp only [WithTop.map_coe]
    have e : (y : ℝ) - (mm - (c4 : ℝ)) = ((y : ℝ) - mm) + (c4 : ℝ) := by ring
    rw [e, Int.floor_add_natCast]
    have : ⌊(y : ℝ) - mm⌋ + (n : ℤ) ≤ ⌊(y : ℝ) - mm⌋ + (c4 : ℤ) := by omega
    exact_mod_cast this

theorem gThetaAt (D7 : Formalism.BasicNotions.D7) : GThetaAt := by
  intro C0 CE1 CE2 X _ O _ _ _ _ j b _ c T q hT mm u hu
  unfold gOp
  refine Submodule.sum_mem _ fun ν hν => Submodule.smul_mem _ _ ?_
  have hTie := tieOK_blockBase X.p (r := X.m) (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b
  refine op_SSt (O := O) (r := X.m) D7 hTie ν ?_
    (fun k => (segmentCapacities X.p (X.seg C0 CE1 CE2 j) b k).map (fun y : ℤ => ⌊(y : ℝ) - mm⌋))
    (fun k => (segmentCapacities X.p (X.seg C0 CE1 CE2 j) b k).map (fun y : ℤ => ⌊(y : ℝ) - (mm - 4 * (c : ℝ))⌋)) ?_ u hu
  · intro v hv
    have h := (hT ν hν).2 v hv
    rcases v with ⟨a, c'⟩ | ⟨l, s⟩
    · have h' : (a : ℕ) < 2 * segS X.TT j := h
      constructor
      · intro e
        have := congrArg Fin.val e
        simp only [Fin.val_castSucc] at this
        have h2 : ((blockBase X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b).uPos : ℕ) =
          2 * segS X.TT j := rfl
        omega
      · intro e
        have := congrArg Fin.val e
        simp only [Fin.val_last] at this
        omega
    · have h' : (l : ℕ) < (X.seg C0 CE1 CE2 j).t := h
      intro e
      have := congrArg Fin.val e
      have h2 : ((Fin.last (blockBase X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b).T.t :
        Fin _) : ℕ) = (X.seg C0 CE1 CE2 j).t := rfl
      omega
  · intro k
    have := thr_shift (segmentCapacities X.p (X.seg C0 CE1 CE2 j) b k) mm (ν.sum fun _ n => n) (4 * c) (hT ν hν).1
    have e : (((4 * c : ℕ) : ℕ) : ℝ) = 4 * (c : ℝ) := by push_cast; ring
    rw [e] at this
    exact this

end Formalism.MainNotions.ColumnSystems.Pf
