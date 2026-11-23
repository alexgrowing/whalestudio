import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
import Formalism.LocalToGlobal.Columns.LevGCount

noncomputable section

namespace GlobalTheory.Proof.levelCharacter_stepZero_typePrime

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

theorem supSum_range {κ : Type} [CommRing κ] {n a k : ℕ} (hn : k ≤ n) (ha : k ≤ a) (M : Matrix (Fin n) (Fin n) κ) (f : ℕ → κ)
    (hf : ∀ (i : ℕ) (h : i + 1 < k), f i = M ⟨i, by omega⟩ ⟨i + 1, by omega⟩) :
    supSum a (Finset.range (k - 1)) M = ∑ i ∈ Finset.range (k - 1), f i := by
  unfold supSum
  have h1 : ∀ i : Fin n, (∑ j : Fin n, if i.val + 1 = j.val ∧ j.val < a ∧ i.val ∈ Finset.range (k - 1) then M i j else 0) =
      if i.val ∈ Finset.range (k - 1) then f i.val else 0 := by
    intro i
    by_cases hi : i.val ∈ Finset.range (k - 1)
    · have hi' := Finset.mem_range.1 hi
      rw [if_pos hi, Finset.sum_eq_single (⟨i.val + 1, by omega⟩ : Fin n), if_pos ⟨rfl, by dsimp only; omega, hi⟩,
        hf _ (by omega)]
      · intro j _ hj
        exact if_neg fun h => hj (Fin.ext h.1.symm)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · simp [hi]
  rw [Finset.sum_congr rfl fun i _ => h1 i, Fin.sum_univ_eq_sum_range (fun i => if i ∈ Finset.range (k - 1) then f i else 0) n,
    ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

variable {E : Type} [Field E]

theorem entB_X (q : ℕ) {k n c i : ℕ} (hn : k ≤ n) (hi : i + 1 < k) (ex : ℕ → ℕ) (x : HomE E (n + c) (n + c)) :
    LocE.entB q k c n c n ex ex x i (i + 1) = Loc.atN (x (Loc.eN E (n + c) (i + 1))) i := by
  have e1 : LocE.fIdx k c n i = i := if_pos (by omega)
  have e2 : LocE.fIdx k c n (i + 1) = i + 1 := if_pos hi
  have e3 : LocE.scE n ex i = 0 := if_pos (by omega)
  have e4 : LocE.scE n ex (i + 1) = 0 := if_pos (by omega)
  unfold LocE.entB
  rw [e1, e2, e3, e4]
  simp

theorem symLevelFrameEntry_superdiag_second_block (q : ℕ) {k n c i : ℕ} (hi : i + 1 < c) (x : HomE E (n + c) (n + c)) :
    LocE.entB q k c n c n (fun i => i + 1) (fun i => i + 1) x (k + i) (k + i + 1) =
      (q : E) * Loc.atN (x (Loc.eN E (n + c) (n + i + 1))) (n + i) := by
  have e1 : LocE.fIdx k c n (k + i) = n + i := by
    unfold LocE.fIdx
    rw [if_neg (by omega), if_pos (by omega)]
    omega
  have e2 : LocE.fIdx k c n (k + i + 1) = n + i + 1 := by
    unfold LocE.fIdx
    rw [if_neg (by omega), if_pos (by omega)]
    omega
  have e3 : LocE.scE n (fun i => i + 1) (n + i + 1) - LocE.scE n (fun i => i + 1) (n + i) = 1 := by
    unfold LocE.scE
    rw [if_neg (by omega), if_neg (by omega)]
    beta_reduce
    omega
  unfold LocE.entB
  rw [e1, e2, e3, zpow_one, mul_comm]

theorem chrG_zero {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) (hs : cst.sharp = true)
    (hψ : ∀ a : X.E, IntAt P.1 a → cst.psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a)) :
    ChrG Ch sel mu cst 0 P 1 (colLev Ch 0 ⟨P.1, hP⟩) := by
  have hm := R.two_le_m
  have hN : R.N 0 = R.k := by simp [Ranks.N]
  have hc : R.r - R.k - 1 = cOf R 0 - 1 := by unfold Ranks.r cOf; omega
  have hl : colLev Ch 0 ⟨P.1, hP⟩ = ⟨HX (𝓞 X.E ⧸ P.1.asIdeal) (R.N 0) R.k R.t 0,
      lamX (Ch.psi0 ⟨P.1, hP⟩) (extChi fun s => Ch.chi s ⟨P.1, hP⟩) (R.N 0) R.k R.m R.t 0⟩ := if_pos (by omega)
  rw [hl]
  intro hbar g r hr hrg hg
  have hq : (qOf P.1 : X.E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  have hp0 : psi0P Ch P.1 = Ch.psi0 ⟨P.1, hP⟩ := dif_pos hP
  have hJ := hr.2
  simp only [Jat, hP, hs, if_true] at hJ
  have hst : r ∈ stabL X.E _ (LocE.lamY P.1 (qOf P.1) (R.N 0) (cOf R 0) fun i => i + 1) := by
    have h1 := hJ.1
    simpa using h1
  have hint := fun p p' => GlobalTheory.LastSteps.entB_int (P := P.1) R.k (x := r.toLinearMap) (fun y hy => (hst y).2 hy) p p'
  have ha := GlobalTheory.Mem.LevFin.intAt_n1Arg_G hq r hst
  have h2 : ∑ i ∈ Finset.range (R.r - R.k - 1), LocE.entB (qOf P.1) R.k (cOf R 0) (R.N 0) (cOf R 0) (R.N 0)
      (fun i => i + 1) (fun i => i + 1) r.toLinearMap (R.k + i) (R.k + i + 1) = (qOf P.1 : X.E) * Loc.n1Arg r := by
    rw [hc, Loc.n1Arg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have := Finset.mem_range.1 hi
    exact symLevelFrameEntry_superdiag_second_block _ (by omega) _
  have h3 : cst.psi P (Loc.n1Arg r) = psi0P Ch P.1 (redP P.1 ((qOf P.1 : X.E) * Loc.n1Arg r)) := by
    rw [← hψ _ ha, mul_div_cancel_left₀ _ hq]
  have h4 : ((lamX (Ch.psi0 ⟨P.1, hP⟩) (extChi fun s => Ch.chi s ⟨P.1, hP⟩) (R.N 0) R.k R.m R.t 0 hbar : X.Kˣ) : X.K) =
      Ch.psi0 ⟨P.1, hP⟩ (supSum R.k (Finset.range (R.k - 1)) hbar.1.1) := by
    show ((lamGen _ _ _ R.k [] (SX R.k R.m 0) hbar : X.Kˣ) : X.K) = _
    rw [lamGen_nil, SX_zero]
    rfl
  refine h4.trans ?_
  simp only [chiInv, lamRow, hP, hs, if_true, LocE.lamGBS, LocE.lamGvS, inv_one, one_mul, mul_one, Finset.range_zero,
    Finset.prod_empty]
  rw [h2, h3, hp0, reduction_add (GlobalTheory.TopStep.intAt_sum _ fun i _ => hint _ _) ha, AddChar.map_add_eq_mul,
    GlobalTheory.TopStep.reduction_sum₂ _ fun i _ => hint _ _, mul_comm, mul_inv_cancel_right₀ (AddChar.val_isUnit _ _).ne_zero]
  congr 1
  refine supSum_range hN.ge le_rfl _ _ fun i hi => ?_
  have hi1 : i + 1 < R.N 0 := by omega
  have hi0 : i < R.N 0 := by omega
  have he : Loc.eN X.E (R.N 0 + cOf R 0) (i + 1) = Loc.inX X.E (R.N 0) (cOf R 0) (Loc.eN X.E (R.N 0) (i + 1)) := by
    funext l
    rw [GlobalTheory.QNormal.inX_apply]
    unfold Loc.eN
    split_ifs <;> first | rfl | omega
  have hv : redV P.1 (Loc.eN X.E (R.N 0) (i + 1)) = Pi.single ⟨i + 1, hi1⟩ 1 := by
    funext l
    simp only [redV, Loc.eN, Pi.single_apply, Fin.ext_iff]
    split_ifs
    · exact GlobalTheory.TopStep.reduction_one₂
    · exact GlobalTheory.TopStep.reduction_zero
  have h5 := congrFun (hg _ (GlobalTheory.GO.ChRoot.eN_mem (i := i + 1))) ⟨i, hi0⟩
  rw [hv, Matrix.mulVec_single_one] at h5
  rw [entB_X _ hN.ge hi, he, LinearEquiv.coe_coe, hrg, Loc.atN, dif_pos (by omega), GlobalTheory.QNormal.inX_apply, dif_pos hi0]
  exact h5

end GlobalTheory.Proof.levelCharacter_stepZero_typePrime

end
