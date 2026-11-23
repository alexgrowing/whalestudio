import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Formalism.LocalToGlobal.Columns.RecLevelLocP
import Formalism.LocalToGlobal.Columns.RecLevelCls
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaCharSymMulInvEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelGroupReductionStepZeroTypePrime

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.LastGrp

open GlobalTheory.SymLevelInv LocE Loc

theorem posSym_eq_symIdx (k rS x : ℕ) : posSym k rS x = symIdx k rS x := by
  unfold posSym symIdx
  split_ifs <;> omega

theorem symmetric_level_bound_le (k rS s : ℕ) : bd5 k rS s ≤ s := by
  unfold bd5
  split_ifs <;> omega

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem inJSym_of_mat (hq : q ≠ 0) (hP : (q : 𝓞 E) ∈ P.asIdeal) {k rS r t n : ℕ} (hr : r = rSym k rS) (ht : 0 < t) (hn : r ≤ n)
    {g : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)} (hg : g ∈ JGsym P q k rS r t n 0) {κ : Type} [Field κ]
    (e : (𝓞 E ⧸ P.asIdeal) →+* κ) (M : Matrix (Fin n) (Fin n) κ) (hM : ∀ i j : Fin n, M i j = e (redP P (mat g i j))) :
    InJSym k rS t false M := by
  subst hr
  have hr' : k + rS < rSym k rS := by
    unfold rSym
    omega
  refine ⟨fun x y h => ?_, fun x hx => ?_, fun x y hx hy => ?_, fun h => by simp at h⟩
  · have hxy : x.1 ≠ y.1 := fun h' => by rw [h'] at h; omega
    by_cases hy : y.1 < rSym k rS
    · have key : bd5 k rS (symIdx k rS y.1) ≤ symIdx k rS x.1 := by
        refine (symmetric_level_bound_le _ _ _).trans ?_
        rw [lvSym_of_lt hy, posSym_eq_symIdx] at h
        by_cases hx : x.1 < rSym k rS
        · rw [lvSym_of_lt hx, posSym_eq_symIdx] at h
          exact h.le
        · have h1 := symIdx_lt hr'.le hy
          have h2 := symIdx_cases k rS x.1
          omega
      rw [hM, mat_col hq hP hr' hn hg x.1 y.1 x.2 hy key, if_neg hxy, map_zero]
    · have hx : ¬ x.1 < rSym k rS := by
        intro hx
        have h1 := lvSym_of_ge (t := t) hy
        rw [lvSym_of_lt hx] at h
        have h2 := posSym_lt hx
        omega
      unfold lvSym at h
      rw [if_neg hy, if_neg hx] at h
      have h1 : (y.1 - rSym k rS) / t + 1 ≤ (x.1 - rSym k rS) / t := by omega
      have h2 := Nat.lt_mul_div_succ (y.1 - rSym k rS) ht
      have h3 := Nat.div_mul_le_self (x.1 - rSym k rS) t
      have h4 := Nat.mul_le_mul_right t h1
      rw [mul_comm] at h2
      rw [hM, mat_blk hq hP hr' hg ((y.1 - rSym k rS) / t + 1) x.1 y.1 x.2 (by omega) (by omega), map_zero]
  · rw [hM, mat_col hq hP hr' hn hg x.1 x.1 x.2 hx (symmetric_level_bound_le _ _ _), if_pos rfl, map_one]
  · have hyr : y.1 < rSym k rS := by omega
    have key : bd5 k rS (symIdx k rS y.1) ≤ symIdx k rS x.1 := by
      rw [hy]
      unfold bd5 symIdx
      split_ifs <;> omega
    rw [hM, mat_col hq hP hr' hn hg x.1 y.1 x.2 hyr key, if_neg (by omega), map_zero]

theorem inJSym_of_prX (hq : q ≠ 0) (hP : (q : 𝓞 E) ∈ P.asIdeal) {k rS r t n c : ℕ} (hc : c = 0) (hr : r = rSym k rS) (ht : 0 < t)
    (hn : r ≤ n) {ρ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hρ : ρ ∈ JGsym P q k rS r t n c) {g : Sp E n ≃ₗ[E] Sp E n}
    (hx : ∀ x, ρ (Loc.inX E n c x) = Loc.inX E n c (g x)) {κ : Type} [Field κ] (e : (𝓞 E ⧸ P.asIdeal) →+* κ)
    (M : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) (hM : ∀ x ∈ stdAt E n P, redV P (g x) = M.mulVec (redV P x)) :
    InJSym k rS t false (M.map e) := by
  subst hc
  refine inJSym_of_mat hq hP hr ht hn hρ e _ fun i j => ?_
  have h6 := congrFun (hM _ (TopStep.single_mem_stdAt j)) i
  rw [TopStep.redV_single, Matrix.mulVec_single_one] at h6
  have h7 : mat ρ i.1 j.1 = g (Pi.single j 1) i := by
    have h8 : eN E (n + 0) j.1 = Loc.inX E n 0 (Pi.single j 1) := by
      funext l
      rw [CongLevel.inX_apply, dif_pos (show l.1 < n from l.2)]
      unfold Loc.eN
      simp [Pi.single_apply, Fin.ext_iff]
    unfold mat atN
    rw [dif_pos (show i.1 < n + 0 from i.2), h8, hx, CongLevel.inX_apply, dif_pos i.2]
  rw [Matrix.map_apply, h7]
  exact congrArg e h6.symm

end GlobalTheory.Mem.LastGrp

theorem GlobalTheory.Mem.LastGrp.levG_le_JSymG : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → cst.sharp = true → ∀ (j : ℕ), j + 1 = R.m → ∀ (b : L.β j) (w : {w // w ∈ Pr.vGs}) (κ : Type) [Field κ] (e : (𝓞 X.E ⧸ w.1.asIdeal) ≃+* κ) (M : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)), M ∈ (L.levG j b w).H → Matrix.GeneralLinearGroup.map e.toRingHom M ∈ JSymG κ (R.N j) R.k (rSD R) R.t false := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hSel hL hs j hj b w κ _ e M hM
  letI : StarRing X.E := X.starE
  have hm := hL.hm
  obtain rfl : j = m2 + 1 := by omega
  have hc : cOf R (m2 + 1) = 0 := by
    unfold cOf
    omega
  have hq : qOf w.1 ≠ 0 := fun h => TopStep.qOf_ne_zero (P := w.1) (by rw [h]; simp)
  have hP : ((qOf w.1 : ℕ) : 𝓞 X.E) ∈ w.1.asIdeal := Ideal.absNorm_mem _
  have hr : R.r = rSym R.k (rSD R) := by
    obtain ⟨a, ha⟩ := R.m_even
    unfold Ranks.r rSym rSD
    omega
  have ht : 0 < R.t := by
    have := R.three_m_lt_t
    omega
  have hn : R.r ≤ R.N (m2 + 1) := by
    unfold Ranks.r Ranks.N
    rw [mul_add, mul_one]
    omega
  have key : ∀ A : GL (Fin (R.N (m2 + 1))) (𝓞 X.E ⧸ w.1.asIdeal), A ∈ (L.levG (m2 + 1) b w).H →
      InJSym R.k (rSD R) R.t false ((A.1).map e.toRingHom) := by
    intro A hA
    obtain ⟨g, hg, hred⟩ := (hL.grpG _ b w A).1 hA
    unfold prCat at hg
    rw [hL.last_h] at hg
    obtain ⟨ρ, hρ, hx⟩ := hg
    have hJ : ρ ∈ Jat (Pr := Pr) cst.sharp (m2 + 1) w.1 := by simpa [Loc.Cbe] using hρ.2
    unfold Jat at hJ
    rw [if_pos w.2, if_pos hs] at hJ
    exact inJSym_of_prX hq hP hc hr ht hn hJ hx e.toRingHom A.1 hred
  refine ⟨key M hM, ?_⟩
  rw [← map_inv]
  exact key _ (inv_mem hM)
