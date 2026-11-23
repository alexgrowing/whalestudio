import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SubstitutionAdjoint

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

namespace GlobalTheory.DetIndexPf

theorem val_det_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {r : ℕ}
    (A C : Matrix (Fin r) (Fin r) K)
    (h : localization₂ w.asIdeal (Submodule.span (𝓞 K) (Set.range fun j : Fin r => fun a : Fin r => A a j)) ≤
      localization₂ w.asIdeal (Submodule.span (𝓞 K) (Set.range fun j : Fin r => fun a : Fin r => C a j))) :
    w.valuation K A.det ≤ w.valuation K C.det := by
  have key : ∀ j : Fin r, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∃ c : Fin r → 𝓞 K,
      ∑ k, c k • (fun a : Fin r => C a k) = s • (fun a : Fin r => A a j) := by
    intro j
    have h1 : (fun a : Fin r => A a j) ∈
        localization₂ w.asIdeal (Submodule.span (𝓞 K) (Set.range fun j : Fin r => fun a : Fin r => A a j)) :=
      ⟨1, w.asIdeal.primeCompl.one_mem, by
        rw [one_smul]; exact Submodule.subset_span ⟨j, rfl⟩⟩
    obtain ⟨s, hs, hx⟩ := h h1
    exact ⟨s, hs, (Submodule.mem_span_range_iff_exists_fun _).1 hx⟩
  choose s hs c hc using key
  have e : A * Matrix.diagonal (fun j => algebraMap (𝓞 K) K (s j)) =
      C * (algebraMap (𝓞 K) K).mapMatrix (Matrix.of fun k j => c j k) := by
    ext a j
    have := congrFun (hc j) a
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def] at this
    rw [mul_comm, ← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [mul_comm]
  have e2 := congrArg (fun M => w.valuation K (Matrix.det M)) e
  simp only [Matrix.det_mul, Matrix.det_diagonal, map_mul, map_prod, ← RingHom.map_det] at e2
  have h1 : ∏ j, w.valuation K (algebraMap (𝓞 K) K (s j)) = 1 :=
    Finset.prod_eq_one fun j _ => (w.valuation_eq_one_iff_notMem).2 (hs j)
  rw [h1, mul_one] at e2
  rw [e2]
  exact mul_le_of_le_one_right' (w.valuation_le_one _)

theorem detIndex : DetIndex := by
  intro K _ _ w r B B' M' i q _ hM hB
  set C : Matrix (Fin r) (Fin r) K :=
    (B : Matrix (Fin r) (Fin r) K) * Matrix.diagonal (fun j => if j = i then q else 1) with hC
  have hd : C.det = q * (B : Matrix (Fin r) (Fin r) K).det := by
    rw [hC, Matrix.det_mul, Matrix.det_diagonal, mul_comm]
    simp
  have hf : (fun j : Fin r => fun α : Fin r =>
      (if j = i then q else 1) * (B : Matrix (Fin r) (Fin r) K) α j) = fun j : Fin r => fun α : Fin r => C α j := by
    funext j α
    rw [hC, Matrix.mul_diagonal, mul_comm]
  rw [hf] at hM
  have he := hB.symm.trans hM
  rw [← hd]
  exact le_antisymm (val_det_le w _ _ he.le) (val_det_le w _ _ he.ge)

end GlobalTheory.DetIndexPf
