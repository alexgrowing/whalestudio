import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeMulOnSymmetricLevelAtTypePrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaCharSymMulInvEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Formalism.LocalToGlobal.Columns.RecLevelLocP
import Formalism.LocalToGlobal.Columns.RecLevelCls
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Proof.LastStepChar

open Loc LocE GlobalTheory.SymLevelInv

theorem sum_sd {κ : Type} [AddCommMonoid κ] {n a k : ℕ} (hk : 1 ≤ k) (hka : k < a) (ha : a ≤ n)
    (N : Matrix (Fin n) (Fin n) κ) (f : ℕ → ℕ → κ) (hf : ∀ x y (hx : x < n) (hy : y < n), N ⟨x, hx⟩ ⟨y, hy⟩ = f x y) :
    (∑ x : Fin n, ∑ y : Fin n, if (x : ℕ) + 1 = y ∧ (y : ℕ) < a ∧ (y : ℕ) ≠ k then N x y else 0) =
      ∑ i ∈ Finset.range (k - 1), f i (i + 1) + ∑ i ∈ Finset.range (a - k - 1), f (k + i) (k + i + 1) := by
  have h1 : ∀ x : Fin n, (∑ y : Fin n, if (x : ℕ) + 1 = y ∧ (y : ℕ) < a ∧ (y : ℕ) ≠ k then N x y else 0) =
      if (x : ℕ) + 1 < a ∧ (x : ℕ) + 1 ≠ k then f x (x + 1) else 0 := by
    intro x
    by_cases hx : (x : ℕ) + 1 < a ∧ (x : ℕ) + 1 ≠ k
    · rw [if_pos hx, Finset.sum_eq_single (⟨x.1 + 1, by omega⟩ : Fin n), if_pos ⟨rfl, hx.1, hx.2⟩, hf]
      · intro y _ hy
        exact if_neg fun h => hy (Fin.ext h.1.symm)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [if_neg hx]
      refine Finset.sum_eq_zero fun y _ => if_neg fun h => hx ?_
      obtain ⟨h1, h2, h3⟩ := h
      omega
  rw [Finset.sum_congr rfl fun x _ => h1 x,
    Fin.sum_univ_eq_sum_range (fun x => if x + 1 < a ∧ x + 1 ≠ k then f x (x + 1) else 0) n]
  have e : n = (k - 1) + (1 + ((a - k - 1) + (n - (a - 1)))) := by omega
  rw [e, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_one]
  rw [if_neg (by omega), zero_add, Finset.sum_eq_zero (s := Finset.range (n - (a - 1))), add_zero]
  · congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [if_pos (by omega)]
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [if_pos (by omega), show k - 1 + (1 + i) = k + i by omega]
  · intro i hi
    rw [if_neg (by omega)]

section Loc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem red_mat {n : ℕ} (g : Sp E n ≃ₗ[E] Sp E n) (r : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0))
    (hrg : ∀ x, r (Loc.inX E n 0 x) = Loc.inX E n 0 (g x)) (M : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal))
    (hred : ∀ x ∈ stdAt E n P, redV P (g x) = M.mulVec (redV P x)) (p p' : ℕ) (hp : p < n) (hp' : p' < n) :
    redP P (mat r p p') = M ⟨p, hp⟩ ⟨p', hp'⟩ := by
  have he : Loc.eN E (n + 0) p' = Loc.inX E n 0 (Loc.eN E n p') := by
    funext l
    rw [GlobalTheory.QNormal.inX_apply, dif_pos (show (l : ℕ) < n from l.2)]
    rfl
  have hv : redV P (Loc.eN E n p') = Pi.single ⟨p', hp'⟩ 1 := by
    funext l
    simp only [redV, Loc.eN, Pi.single_apply, Fin.ext_iff]
    split_ifs
    · exact reduction_one' P
    · exact redP_zero' P
  have h5 := congrFun (hred _ (GlobalTheory.GO.ChRoot.eN_mem (i := p'))) ⟨p, hp⟩
  rw [hv, Matrix.mulVec_single_one] at h5
  unfold mat
  rw [he, hrg, Loc.atN, dif_pos (show p < n + 0 from hp), GlobalTheory.QNormal.inX_apply, dif_pos hp]
  exact h5

theorem lam_loc {K : Type} [Field K] (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ₀ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {κ : Type} [Field κ] (e : (𝓞 E ⧸ P.asIdeal) ≃+* κ) (σ : K →+* ℂ) (ψ : AddChar κ ℂ) (χ : ℕ → MulChar κ ℂ)
    {k rS r t nb n c : ℕ} (hc : c = 0) (hr : r = k + 2 * rS + 1) (hk : 1 ≤ k) (hn : r + nb * t ≤ n)
    (hψ : ∀ a, ψ (e a) = σ (ψ₀ a)) (hχ : ∀ i, i < nb → ∀ a : (𝓞 E ⧸ P.asIdeal)ˣ, χ i (e a) = σ ((χ₀ i a : Kˣ) : K))
    (g : Sp E n ≃ₗ[E] Sp E n) (h : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (hh : h ∈ JGsym P (qOf P) k rS r t n c)
    (hhg : ∀ x, h (Loc.inX E n c x) = Loc.inX E n c (g x)) (M : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal))
    (hred : ∀ x ∈ stdAt E n P, redV P (g x) = M.mulVec (redV P x)) :
    σ (lamGBS (qOf P) ψ₀ χ₀ k r t nb n c h.toLinearMap) = Formalism.L2.Forms.lamSym ψ χ k rS t nb (M.map e) := by
  subst hc hr
  have hM := red_mat g h hhg M hred
  have hrn : k + 2 * rS + 1 ≤ n := le_trans (Nat.le_add_right _ _) hn
  unfold lamGBS lamGvS Formalism.L2.Forms.lamSym Formalism.L2.Forms.lamJ Formalism.L2.Forms.rSym
  rw [map_mul]
  congr 1
  · rw [redP_superdiag (by omega) hrn hh, ← hψ, map_add, map_sum, map_sum]
    congr 1
    refine (sum_sd hk (by omega) hrn _ (fun x y => e (redP P (mat h x y))) fun x y hx hy => ?_).symm
    rw [Matrix.map_apply, hM x y hx hy]
  · rw [map_prod]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hi' : k + 2 * rS + 1 + i * t + t ≤ n := by
      have : (i + 1) * t ≤ nb * t := Nat.mul_le_mul_right t hi
      rw [add_mul, one_mul] at this
      omega
    have hb : Formalism.L2.Forms.blkMat (k + 2 * rS + 1) t i (M.map e) =
        e.toRingHom.mapMatrix (Matrix.of fun s s' : Fin t => redP P (mat h (k + 2 * rS + 1 + i * t + s.1) (k + 2 * rS + 1 + i * t + s'.1))) := by
      ext s s'
      have := s.2
      have := s'.2
      unfold Formalism.L2.Forms.blkMat Formalism.L2.Forms.entN
      rw [dif_pos ⟨by omega, by omega⟩, Matrix.map_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
        hM (k + 2 * rS + 1 + i * t + s.1) (k + 2 * rS + 1 + i * t + s'.1) (by omega) (by omega)]
      rfl
    rw [hb, ← RingHom.map_det]
    unfold unitV
    rw [redP_det_blk hi' hh]
    split_ifs with hu
    · rw [← hχ i hi, IsUnit.unit_spec]
      rfl
    · rw [map_zero, MulChar.map_nonunit]
      exact fun h' => hu ((isUnit_map_iff e _).1 h')

end Loc

end GlobalTheory.Proof.LastStepChar

theorem GlobalTheory.Proof.LastStepChar.chr_last : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → cst.sharp = true → ∀ (j : ℕ), j + 1 = R.m → ∀ (b : L.β j) (w : {w // w ∈ Pr.vGs}) (κ : Type) [Field κ] (e : (𝓞 X.E ⧸ w.1.asIdeal) ≃+* κ) (σ : X.K →+* ℂ) (ψ : AddChar κ ℂ) (χ : ℕ → MulChar κ ℂ), (∀ c, ψ (e c) = σ (Ch.psi0 w c)) → (∀ (s : Fin R.m) (c : (𝓞 X.E ⧸ w.1.asIdeal)ˣ), χ s.1 (e c) = σ ((Ch.chi s w c : X.Kˣ) : X.K)) → ∀ M : (L.levG j b w).H, σ (((L.levG j b w).lam M : X.Kˣ) : X.K) = lamSym ψ χ R.k (rSD R) R.t j (M.1.1.map e) := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hsel hL hsh j hj b w κ _ e σ ψ χ hψ hχ M
  have hm := hL.hm
  obtain rfl : j = m2 + 1 := by omega
  obtain ⟨g, hg, hred⟩ := (hL.grpG (m2 + 1) b w M.1).1 M.2
  obtain ⟨r, hrC, hrg⟩ := hg
  have hlam := hL.chrG (m2 + 1) b w M g r hrC hrg hred
  rw [hlam]
  rw [hL.last_h] at hrC ⊢
  have hc : cOf R (m2 + 1) = 0 := by unfold cOf; omega
  have hJ0 : r ∈ Jat (Pr := Pr) (R := R) cst.sharp (m2 + 1) w.1 := by
    unfold Loc.Cbe at hrC
    rw [Subgroup.mem_inf, Subgroup.mem_comap] at hrC
    simpa using hrC.2
  unfold Jat at hJ0
  rw [if_pos w.2, hsh, if_pos rfl] at hJ0
  have hn1 : Loc.n1Arg r = 0 := by
    unfold Loc.n1Arg
    rw [show cOf R (m2 + 1) - 1 = 0 by omega, Finset.sum_range_zero]
  unfold chiInv
  rw [hn1, hL.cst_ok.psi_int _ _ (GlobalTheory.SymLevelInv.intAt_zero _), inv_one, one_mul]
  unfold lamRow
  simp only [if_pos w.2, hsh, if_true]
  rw [inv_one, one_mul, mul_one]
  have hk := R.m_add_three_le_k
  have hr : R.r = R.k + 2 * R.rS + 1 := by
    obtain ⟨a, ha⟩ := R.m_even
    unfold Ranks.r Ranks.rS
    omega
  have hn : R.r + (m2 + 1) * R.t ≤ R.N (m2 + 1) := by
    unfold Ranks.r Ranks.N
    rw [mul_add, mul_one]
    omega
  refine lam_loc (psi0P Ch w.1) (chiP Ch w.1) e σ ψ χ hc hr (by omega) hn (fun a => ?_) (fun i hi a => ?_) g r hJ0 hrg M.1.1 hred
  · rw [hψ]
    unfold psi0P
    rw [dif_pos w.2]
  · rw [hχ ⟨i, by omega⟩ a]
    unfold chiP chiAt extChi
    rw [dif_pos w.2]
    simp only [dif_pos (show i < R.m by omega)]

end
