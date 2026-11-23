import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThEquivPOf

open NumberField IsDedekindDomain MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H

section Omega

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem TE.contDiff_opU_top (H : Sesq (VCx ι a b)) (x : VCx ι a b) (F : VCx ι a b → ℂ) (hF : ContDiff ℂ ⊤ F) :
    ContDiff ℂ ⊤ (opU H x F) := by
  unfold opU
  have h1 : ContDiff ℂ ⊤ fun z : VCx ι a b => F (z + x) := hF.comp (contDiff_id.add contDiff_const)
  have h2 : ContDiff ℂ ⊤ fun z : VCx ι a b => H z x :=
    (LinearMap.toContinuousLinearMap (H.flip x)).contDiff
  exact h1.mul (Complex.contDiff_exp.comp (((contDiff_const.mul h2)).sub contDiff_const))

theorem TE.contDiff_sumU_top (H : Sesq (VCx ι a b)) (α : VCx ι a b → ℂ) (S : Finset (VCx ι a b)) (F : VCx ι a b → ℂ)
    (hF : ContDiff ℂ ⊤ F) : ContDiff ℂ ⊤ (sumU H α S F) := by
  unfold sumU
  exact ContDiff.sum fun x _ => contDiff_const.mul (TE.contDiff_opU_top H x F hF)

theorem indOmega_of {X : Fields} (A : Amb X) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ) (h : A.EOmega a b) :
    A.IndOmega a b Sall D := by
  intro N N' c x hR
  unfold Amb.thInd xiInd xiS
  exact contDiff_const.mul (contDiff_const.mul (TE.contDiff_opU_top _ _ _ (TE.contDiff_sumU_top _ _ _ _ (h N N' hR.1 hR.2.1))))

end Omega

section Wt

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

theorem even_rankN (R : Ranks) (j : ℕ) : Even (R.N j) := by
  unfold Ranks.N
  exact R.k_even.add (Even.mul_left R.t_odd.add_one j)

theorem wtLaw_step (u : Pr.Word) {i : ℕ} (hi : i < R.m) (e : X.Tau → ℤ) (he : ∀ τ, (e τ : ℚ) = (W.hc u τ).e ⟨i, hi⟩) :
    WtLaw (W.lamTrue u i) (W.lamTrue u (i + 1)) (nuLast W u i) e := by
  have hNi : 0 < R.N i := R.N_pos i
  have hNi1 : 0 < R.N (i + 1) := R.N_pos _
  have hlt : R.N i < R.N (i + 1) := by unfold Ranks.N; rw [Nat.succ_mul]; omega
  refine ⟨fun τ => ?_, fun τ => ?_⟩
  · rw [nuLast_eq W u i hi τ]
    have h1 : (W.nuW u (i + 1) τ).detShift = (W.nuW u (i + 1) τ).w ⟨R.N i - 1, by rw [Nat.add_sub_cancel]; omega⟩ := by
      unfold DomWeight.detShift
      exact dif_pos hNi
    have h2 : (W.lamTrue u i τ).detShift = (W.lamTrue u i τ).w ⟨R.N i - 1, by omega⟩ := by
      unfold DomWeight.detShift
      exact dif_pos hNi
    have h3 := Wts.nuW_eq_true W u hi τ ⟨R.N i - 1, by omega⟩
    unfold sExp' at h3
    rw [← he τ] at h3
    rw [h1, h2]
    obtain ⟨q, hq⟩ := even_rankN R (i + 1)
    have hq2 : R.N (i + 1) / 2 = q := by omega
    have hq3 : (R.N (i + 1) : ℚ) = q + q := by exact_mod_cast hq
    have h5 : ((((W.nuW u (i + 1) τ).w ⟨R.N i - 1, by rw [Nat.add_sub_cancel]; omega⟩ + (q : ℤ) - e τ : ℤ)) : ℚ) =
        (((W.lamTrue u i τ).w ⟨R.N i - 1, by omega⟩ : ℤ) : ℚ) := by
      push_cast
      rw [h3, hq3]
      ring
    rw [hq2]
    exact_mod_cast h5
  · have h2 : (W.lamTrue u (i + 1) τ).detShift = (W.lamTrue u (i + 1) τ).w ⟨R.N (i + 1) - 1, by omega⟩ := by
      unfold DomWeight.detShift
      exact dif_pos hNi1
    have h3 := Wts.lamTrue_new W u hi τ (⟨R.N (i + 1) - 1, by omega⟩ : Fin (R.N (i + 1)))
      (show ¬ (R.N (i + 1) - 1 < R.N i) by omega)
    unfold sExp at h3
    rw [← he τ, Nat.add_sub_cancel] at h3
    rw [h2]
    obtain ⟨q, hq⟩ := even_rankN R i
    have hq2 : R.N i / 2 = q := by omega
    have hq3 : (R.N i : ℚ) = q + q := by exact_mod_cast hq
    have h5 : (((e τ - (q : ℤ) : ℤ)) : ℚ) = ((-(W.lamTrue u (i + 1) τ).w ⟨R.N (i + 1) - 1, by omega⟩ : ℤ) : ℚ) := by
      push_cast
      rw [h3, hq3]
      ring
    rw [hq2]
    exact_mod_cast h5

end Wt

section Step

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (A : Amb X) (u : Pr.Word)

theorem thEquivP_stepT_of {i : ℕ} (hi : i < R.m) (e : X.Tau → ℤ) (he : ∀ τ, (e τ : ℚ) = (W.hc u τ).e ⟨i, hi⟩)
    (hrat : A.JetsRat (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u))
    (hE : A.EOmega (R.N i) (R.N (i + 1)))
    (hInd : A.ThIndEq (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u))
    (hChi : A.ChiLaw (R.N i) (R.N (i + 1)))
    (hMa : MuProdLaw (R.N i) sel (rowSG Pr sel mu) (mUof Ch mu i) (muAtT Ch sel mu cst i) e)
    (hMb : MuProdLaw (R.N (i + 1)) sel (rowSG Pr sel mu) (mUof Ch mu i) (muAtT Ch sel mu cst i) e) :
    ThEquivP (stepT W Ch sel mu cst A u i (W.lamTrue u (i + 1))) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u i).rho (colValF W sel mu u (i + 1)).rho :=
  thEquivP_of A (Sall sel mu u) (rowSG Pr sel mu) (cAof sel mu cst * cBof sel mu cst u) sel (mUof Ch mu i) (muAtT Ch sel mu cst i)
    (W.lamTrue u i) (W.lamTrue u (i + 1)) (nuLast W u i) e (jet_in_weight_space_chain W u hi) hrat (indOmega_of A _ _ _ _ hE) hInd hChi hMa hMb
    (wtLaw_step W u hi e he)

theorem top_cast {m2 : ℕ} (hm : R.m = m2 + 2) :
    (ThEquivP (stepT W Ch sel mu cst A u (m2 + 1) (W.lamTrue u R.m)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
        (colValF W sel mu u (m2 + 1)).rho (colVal W u R.m (Pr.vT u) (rowSG Pr sel mu)).rho ↔
      ThEquivP (stepT W Ch sel mu cst A u (m2 + 1) (W.lamTrue u (m2 + 1 + 1))) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
        (colValF W sel mu u (m2 + 1)).rho (colValF W sel mu u (m2 + 1 + 1)).rho) ∧
    (A.AnaStep (R.N (m2 + 1)) (R.N R.m) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) ↔
      A.AnaStep (R.N (m2 + 1)) (R.N (m2 + 1 + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)) := by
  have gen : ∀ k, k = m2 + 1 + 1 →
      (ThEquivP (stepT W Ch sel mu cst A u (m2 + 1) (W.lamTrue u k)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
          (colValF W sel mu u (m2 + 1)).rho (colVal W u k (Pr.vT u) (rowSG Pr sel mu)).rho ↔
        ThEquivP (stepT W Ch sel mu cst A u (m2 + 1) (W.lamTrue u (m2 + 1 + 1))) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
          (colValF W sel mu u (m2 + 1)).rho (colValF W sel mu u (m2 + 1 + 1)).rho) ∧
      (A.AnaStep (R.N (m2 + 1)) (R.N k) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) ↔
        A.AnaStep (R.N (m2 + 1)) (R.N (m2 + 1 + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)) := by
    intro k hk
    subst hk
    exact ⟨Iff.rfl, Iff.rfl⟩
  exact gen R.m hm

end Step

end Formalism.L2.Ker
