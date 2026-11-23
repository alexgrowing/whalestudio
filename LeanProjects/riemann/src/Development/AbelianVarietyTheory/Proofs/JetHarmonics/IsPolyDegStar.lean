import Mathlib
import Formalism.HermitianCurvature.StatementD
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.StatementU
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPolyDegPrW
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.OmgMulLeft
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HpkConjTranspose
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.OmgEquivariant

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace GlobalTheory.WigSh.OmgContr

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

variable {N : ℕ}

private lemma star_eval_eq_eval₂_starRingEnd {σ : Type*} (x : σ → ℂ) (q : MvPolynomial σ ℂ) :
    star (MvPolynomial.eval x q) = MvPolynomial.eval₂ (starRingEnd ℂ) (fun v => star (x v)) q := by
  induction q using MvPolynomial.induction_on with
  | C c => simp
  | add p₁ p₂ h₁ h₂ => simp [h₁, h₂]
  | mul_X p v hp => simp [hp]

theorem isPolyDeg_star {a : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg a P) :
    U.IsPolyDeg a (fun g => star (P g)) := by
  obtain ⟨q, hq, hP⟩ := h
  refine ⟨MvPolynomial.rename Sum.swap (MvPolynomial.map (starRingEnd ℂ) q), ?_, ?_⟩
  · exact (MvPolynomial.totalDegree_rename_le _ _).trans
      (le_trans (by
        unfold MvPolynomial.totalDegree
        exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)) hq)
  · intro g
    show star (P g) = _
    rw [hP g, MvPolynomial.eval_rename, MvPolynomial.eval_map, star_eval_eq_eval₂_starRingEnd]
    congr 1
    funext v
    cases v <;> simp

theorem isPolyDeg_pow {a : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg a P) (n : ℕ) :
    U.IsPolyDeg (n * a) (fun g => P g ^ n) := by
  obtain ⟨q, hq, hP⟩ := h
  refine ⟨q ^ n, (MvPolynomial.totalDegree_pow q n).trans (Nat.mul_le_mul_left n hq), ?_⟩
  intro g
  simp [hP g]

theorem isPolyDeg_prod {ι : Type*} (s : Finset ι) (d : ι → ℕ) {P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ}
    (h : ∀ i, U.IsPolyDeg (d i) (P i)) : U.IsPolyDeg (∑ i ∈ s, d i) (fun g => ∏ i ∈ s, P i g) := by
  choose q hq hP using h
  refine ⟨∏ i ∈ s, q i, (MvPolynomial.totalDegree_finsetProd s q).trans (Finset.sum_le_sum fun i _ => hq i), ?_⟩
  intro g
  simp [hP]

private lemma isPolyDeg_const (c : ℂ) (a : ℕ) : U.IsPolyDeg (N := N) a (fun _ => c) :=
  ⟨MvPolynomial.C c, by simp, fun g => by simp⟩

private lemma exists_pow_mul_mul_mem_subring {a b : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg a P)
    (hQ : U.IsPolyDeg b Q) : U.IsPolyDeg (a + b) (fun g => P g * Q g) := by
  obtain ⟨p, hp, hPe⟩ := hP
  obtain ⟨q, hq, hQe⟩ := hQ
  exact ⟨p * q, (MvPolynomial.totalDegree_mul p q).trans (Nat.add_le_add hp hq), fun g => by simp [hPe, hQe]⟩

private lemma exists_pow_mul_finset_sum_mem_subring {ι : Type*} (s : Finset ι) {a : ℕ} {P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ}
    (h : ∀ i ∈ s, U.IsPolyDeg a (P i)) : U.IsPolyDeg a (fun g => ∑ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPolyDeg_const (N := N) 0 a
  | insert j s hj ih =>
    have hj' := h j (Finset.mem_insert_self j s)
    have hs := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    obtain ⟨p, hp, hPe⟩ := hj'
    obtain ⟨q, hq, hQe⟩ := hs
    refine ⟨p + q, (MvPolynomial.totalDegree_add p q).trans (max_le hp hq), fun g => ?_⟩
    have e := hQe g
    simp only at e
    show ∑ i ∈ insert j s, P i g = _
    rw [Finset.sum_insert hj, MvPolynomial.eval_add, ← hPe g, ← e]

private lemma mono_lemma {a b : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg a P) (hab : a ≤ b) :
    U.IsPolyDeg b P := by
  obtain ⟨q, hq, hP⟩ := h
  exact ⟨q, hq.trans hab, hP⟩

theorem isPolyDeg_eval {σ : Type*} {a d : ℕ} (f : Matrix (Fin N) (Fin N) ℂ → σ → ℂ)
    (hf : ∀ i, U.IsPolyDeg a (fun g => f g i)) (q : MvPolynomial σ ℂ) (hq : q.totalDegree ≤ d) :
    U.IsPolyDeg (d * a) (fun g => MvPolynomial.eval (f g) q) := by
  classical
  have expand : (fun g => MvPolynomial.eval (f g) q) =
      fun g => ∑ m ∈ q.support, q.coeff m * ∏ i ∈ m.support, f g i ^ m i := by
    funext g
    rw [MvPolynomial.eval_eq]
  rw [expand]
  refine exists_pow_mul_finset_sum_mem_subring _ fun m hm => ?_
  have hdeg : (∑ i ∈ m.support, m i) * a ≤ d * a := by
    apply Nat.mul_le_mul_right
    exact (MvPolynomial.le_totalDegree hm).trans hq
  refine mono_lemma ?_ hdeg
  have hprod : U.IsPolyDeg (∑ i ∈ m.support, m i * a) (fun g => ∏ i ∈ m.support, f g i ^ m i) :=
    isPolyDeg_prod m.support (fun i => m i * a) (fun i => isPolyDeg_pow (hf i) (m i))
  rw [Finset.sum_mul]
  simpa using exists_pow_mul_mul_mem_subring (isPolyDeg_const (q.coeff m) 0) hprod

end GlobalTheory.WigSh.OmgContr

namespace GlobalTheory.WigSh

open OmgContr

theorem wigMap_omg : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (π'' : Mx k r → (Wq' →L[ℂ] Wq')) (d : ℕ) (A : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → GlobalTheory.WigSh.WigMap k r z' π'' π' d A → (∃ (t : ℕ) (c : Fin t → Mx k r → ℂ) (L : Fin t → (Wq' →L[ℂ] Wq)), (∀ i, Formalism.FourierDecayAlt.U.IsPolyDeg (d * (r + 1)) (c i)) ∧ ∀ g, A (GlobalTheory.WigSh.omg k r z z' g) = ∑ i, c i g • L i) ∧ ∀ g ∈ UH (Hpk k r), ∀ p : Formalism.FourierDecayAlt.B.SS k r, Matrix.of p.1.1 ∈ UWset k r z → Matrix.of p.1.2 ∈ Formalism.QuantumDeterminants.Nset k r → Matrix.of p.2.1 ∈ UWset k r z' → Matrix.of p.2.2 ∈ Formalism.QuantumDeterminants.Nset k r → (A (GlobalTheory.WigSh.omg k r z z' (Formalism.FourierDecayAlt.B.sgs p g))).comp (π'' (Matrix.of p.2.1)⁻¹) = (π' (Matrix.of p.2.1)⁻¹).comp (A (GlobalTheory.WigSh.omg k r z z' g)) := by
  intro Wq _ _ Wq' _ _ k r z z' π' π'' d A hz hTz hz' hTz' hA
  obtain ⟨⟨t, q, Lm, hq, hAe⟩, hAeq, -, -⟩ := hA
  refine ⟨⟨t, fun i g => MvPolynomial.eval
      (Sum.elim (GlobalTheory.WigSh.omg k r z z' g) (fun j => star (GlobalTheory.WigSh.omg k r z z' g j))) (q i), Lm, ?_, ?_⟩, ?_⟩
  · intro i
    refine isPolyDeg_eval (N := 2 * r + k + 1)
      (fun g => Sum.elim (GlobalTheory.WigSh.omg k r z z' g) (fun j => star (GlobalTheory.WigSh.omg k r z z' g j))) ?_ (q i) (hq i)
    rintro (j | j)
    · exact GlobalTheory.WigSh.omg_isPolyDeg k r z z' j
    · exact isPolyDeg_star (GlobalTheory.WigSh.omg_isPolyDeg k r z z' j)
  · intro g
    exact hAe _
  · intro g hg p h1 h2 h3 h4
    have hn : (Matrix.of p.1.2)⁻¹ * g ∈ UH (Hpk k r) :=
      Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv h2.1) hg
    have hG : (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 ∈ UH (Hpk k r) :=
      Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hn h4.1
    have hs : Formalism.FourierDecayAlt.B.sgs p g =
        (Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) * Matrix.of p.2.1 := by
      simp only [Formalism.FourierDecayAlt.B.sgs, Matrix.mul_assoc]
    have hom : GlobalTheory.WigSh.omg k r z z' (Formalism.FourierDecayAlt.B.sgs p g) =
        (Matrix.of p.2.1)⁻¹ *ᵥ GlobalTheory.WigSh.omg k r z z' g := by
      rw [hs, GlobalTheory.WigSh.omg_equivariant k r z z' _ _ _ hz hTz hz' hTz' hG h1 h3,
        GlobalTheory.WigSh.omg_mul_N k r z z' _ _ hz hz' hn h4, GlobalTheory.WigSh.OmLeftN.omg_left_N k r z z' g _ hz hz' hg h2]
    rw [hom]
    exact hAeq _ (GlobalTheory.WigSh.OmgEquiv.inv_mem h3) _

end GlobalTheory.WigSh
