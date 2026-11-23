import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.NormFockLe
import Formalism.MahlerMeasure.MahlerMeasureProofs.GamLead
import Formalism.MahlerMeasure.MahlerMeasureProofs.SSDirect
import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.SmulMemOfNorm

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset Formalism.GM Formalism.GM.M.PhiIntegrality Formalism.MainNotions.G.SymmetricFormBlocks
open scoped Nat

section Lat

variable (p : ℕ) [hp : Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

theorem Ljj_le (S : Submodule ℤ_[p] (MvPolynomial (M.BVar N r G.T.t) ℚ_[p])) (j : Fin G.T.t → ℕ) (jp : ℕ)
    (h : ∀ y ∈ M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr, ∀ g ∈ M.XiPolZ p N r G.T.t (G.B - jp),
      rename (M.chainEmb N r G.T.t) y * g ∈ S) : Ljj p (r := r) G j jp ≤ S := by
  unfold Ljj
  rw [Submodule.span_le]
  rintro x ⟨y, hy, g, hg, rfl⟩
  exact h y hy g hg

theorem Ljj_int (j : Fin G.T.t → ℕ) (jp : ℕ) (v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
    (hv : v ∈ Ljj p (r := r) G j jp) : Bnd 1 v := by
  have h := Ljj_le p G (M.IntPol p (M.BVar N r G.T.t)) j jp
    (fun y hy g hg => M.intPol_mul' (M.intPol_rename' _ hy.2.2) hg.2) hv
  exact (Formalism.InvariantFactorPaths.KP.LL.intPol_iff_bnd v).1 h

def dJ (j : Fin G.T.t → ℕ) (jp : ℕ) (a : Fin (N + 1)) : ℕ :=
  chDeg (G.lettersAt j jp) a + (if Fin.last N = a then G.B - jp else 0)

theorem Ljj_hom (a : Fin (N + 1)) (j : Fin G.T.t → ℕ) (jp : ℕ) (v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
    (hv : v ∈ Ljj p (r := r) G j jp) : IsWeightedHomogeneous (wL (r := r) G a) v (dJ G j jp a) := by
  have key : Ljj p (r := r) G j jp ≤
      (weightedHomogeneousSubmodule ℚ_[p] (wL (r := r) G a) (dJ G j jp a)).restrictScalars ℤ_[p] := by
    refine Ljj_le p G _ j jp ?_
    intro y hy g hg
    exact (hom_chain p G a _ y hy.2.1).mul (hom_xi p G a _ g hg)
  exact key hv

theorem prod_dJ (j : Fin G.T.t → ℕ) (jp : ℕ) : ∏ a, (dJ G j jp a)! = degFact G j jp := by
  unfold dJ degFact chDeg
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro a0 _
    simp [Fin.castSucc_inj, (Fin.castSucc_lt_last a0).ne']
  · simp [Fin.castSucc_ne_last]

theorem lettersAt_le (j : Fin G.T.t → ℕ) (jp : ℕ) (a0 : Fin N) : (G.lettersAt j jp).deg a0 ≤ G.LL.deg a0 := by
  unfold M.BlockData.lettersAt
  exact le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)

theorem dJ_le (A : ℕ) (hdeg : ∀ x, G.LL.deg x ≤ 2 * A) (hBa : G.B ≤ 2 * A) (j : Fin G.T.t → ℕ) (jp : ℕ)
    (a : Fin (N + 1)) : dJ G j jp a ≤ 2 * A := by
  unfold dJ chDeg
  by_cases ha : Fin.last N = a
  · subst ha
    simp [Fin.castSucc_ne_last]
    omega
  · rw [if_neg ha]
    obtain ⟨a0, rfl⟩ : ∃ a0, Fin.castSucc a0 = a := Fin.exists_castSucc_eq.2 (Ne.symm ha)
    have h1 := lettersAt_le G j jp a0
    have h2 := hdeg a0
    simp [Fin.castSucc_inj]
    omega

theorem log_le_lgN (A x : ℕ) (hx : x ≤ 8 * A + r) : Nat.log p x + 1 ≤ lgN p A r := by
  unfold lgN
  have h1 := Nat.log_mono_right (b := p) hx
  omega

theorem Ljj_val (A : ℕ) (hdeg : ∀ x, G.LL.deg x ≤ 2 * A) (hBa : G.B ≤ 2 * A) (j : Fin G.T.t → ℕ) (jp : ℕ)
    (v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) (hv : v ∈ Ljj p (r := r) G j jp) :
    ∀ m ∈ v.support, padicValNat p (degFact G j jp) ≤
      padicValNat p (m.prod fun _ i => i !) + ((N + 1) * r + (G.T.t + 1) * 2) * lgN p A r := by
  intro m hm
  rw [← prod_dJ G j jp]
  have hw : ∀ a, Finsupp.weight (wL (r := r) G a) m = dJ G j jp a :=
    fun a => Ljj_hom p G a j jp v hv (mem_support_iff.mp hm)
  refine val_letters_le p G m (dJ G j jp) hw (lgN p A r) (fun a => ?_)
  have h1 := dJ_le G A hdeg hBa j jp a
  have h2 := log_le_lgN p (r := r) A (dJ G j jp a) (by omega)
  omega

theorem lettersAt_uPos (hB : G.BlockOK) (j : Fin G.T.t → ℕ) (jp : ℕ) :
    (G.lettersAt j jp).deg G.uPos = G.LL.deg G.uPos - jp := by
  obtain ⟨-, hpos, -, -⟩ := hB
  have hz : (∑ i : Fin G.T.t, if (G.uPos : ℕ) = G.T.pos i ∨ (G.uPos : ℕ) = G.T.pos i + 1 then j i else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => if_neg (by have := hpos i; omega)
  unfold M.BlockData.lettersAt
  simp [hz]

theorem Ljj_biHom (hB : G.BlockOK) (j : Fin G.T.t → ℕ) (jp : ℕ) (v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
    (hv : v ∈ Ljj p (r := r) G j jp) :
    BiHom (fun c => (Sum.inl (Fin.castSucc G.uPos, c) : M.BVar N r G.T.t)) (fun c => M.xiVar N r G.T.t c)
      (G.LL.deg G.uPos - jp) (G.B - jp) v := by
  have h1 := Formalism.InvariantFactorPaths.KP.LL.biHom_plus (p := p) (r := r) (D := G) j jp v hv
  rw [lettersAt_uPos G hB j jp] at h1
  exact h1

end Lat

end Formalism.MainNotions.G.GramWindowAlt

end
