import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E]

theorem fst_idemS (S : Finset (HeightOneSpectrum (𝓞 E))) : (idemS S : Ad E).1 = 1 := rfl

open Classical in
theorem pLoc_pFin_idemS (S : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 E)) :
    pLoc E w (pFin E (idemS S)) = if w ∈ S then 1 else 0 := rfl

theorem prS_apply (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (g : GA E a) (i j : Fin a) :
    (prS S a g : Matrix (Fin a) (Fin a) (Ad E)) i j =
      (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - idemS S * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j +
        idemS S * (g : Matrix (Fin a) (Fin a) (Ad E)) i j := rfl

theorem prO_apply (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (g : GA E a) (i j : Fin a) :
    (prO S a g : Matrix (Fin a) (Fin a) (Ad E)) i j =
      (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (1 - idemS S) * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j +
        (1 - idemS S) * (g : Matrix (Fin a) (Fin a) (Ad E)) i j := rfl

theorem pLoc_pFin_idemS_of_not_mem {S : Finset (HeightOneSpectrum (𝓞 E))} {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ S) :
    pLoc E w (pFin E (idemS S)) = 0 := by
  classical
  rw [pLoc_pFin_idemS]; simp [hw]

theorem pLoc_pFin_one_sub_idemS_of_mem {S : Finset (HeightOneSpectrum (𝓞 E))} {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ S) :
    pLoc E w (pFin E (1 - idemS S)) = 0 := by
  classical
  rw [map_sub, map_sub, map_one, map_one, pLoc_pFin_idemS]; simp [hw]

theorem one_sub_idemS_mul_eq_zero {S : Finset (HeightOneSpectrum (𝓞 E))} {x : Ad E}
    (h : ∀ w ∉ S, pLoc E w (pFin E x) = 0) : (1 - idemS S) * x = 0 := by
  refine Prod.ext ?_ (Subtype.ext (funext fun w => ?_))
  · change (1 - (idemS S : Ad E).1) * x.1 = 0
    rw [fst_idemS, sub_self, zero_mul]
  · change pLoc E w (pFin E ((1 - idemS S) * x)) = pLoc E w (pFin E 0)
    rw [map_mul, map_mul, map_zero, map_zero]
    by_cases hw : w ∈ S
    · rw [pLoc_pFin_one_sub_idemS_of_mem hw, zero_mul]
    · rw [h w hw, mul_zero]

theorem pLoc_pFin_one_apply (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (i j : Fin a) :
    pLoc E w (pFin E ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j)) = (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j := by
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

theorem pLoc_pFin_apply_of_mem_supS {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))} {g : GA E a}
    (hg : g ∈ GlobalTheory.JSW.supS E a S) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ S) (i j : Fin a) :
    pLoc E w (pFin E ((g : Matrix (Fin a) (Fin a) (Ad E)) i j)) = (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j := by
  have h := congrArg (fun x : GL (Fin a) (w.adicCompletion E) => (x : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) (hg w hw)
  exact h

theorem one_sub_idemS_mul_sub_eq_zero {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))} {g : GA E a}
    (hg : g ∈ GlobalTheory.JSW.supS E a S) (i j : Fin a) :
    (1 - idemS S) * ((g : Matrix (Fin a) (Fin a) (Ad E)) i j - (1 : Matrix (Fin a) (Fin a) (Ad E)) i j) = 0 :=
  one_sub_idemS_mul_eq_zero fun w hw => by
    rw [map_sub, map_sub, pLoc_pFin_apply_of_mem_supS hg hw, pLoc_pFin_one_apply, sub_self]

theorem prS_prO_supS (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) :
    (∀ g ∈ GlobalTheory.JSW.supS E a S, prS S a g = g ∧ prO S a g = 1) ∧ ∀ g, prS S a g ∈ GlobalTheory.JSW.supS E a S := by
  refine ⟨fun g hg => ⟨?_, ?_⟩, fun g w hw => ?_⟩
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [prS_apply]
    linear_combination (-1 : Ad E) * one_sub_idemS_mul_sub_eq_zero hg i j
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [prO_apply]
    change _ = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
    linear_combination (one_sub_idemS_mul_sub_eq_zero hg i j)
  · refine Units.ext (Matrix.ext fun i j => ?_)
    change pLoc E w (pFin E ((prS S a g : Matrix (Fin a) (Fin a) (Ad E)) i j)) = (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j
    rw [prS_apply, map_add, map_sub, map_mul, map_mul, map_add, map_sub, map_mul, map_mul,
      pLoc_pFin_idemS_of_not_mem hw, pLoc_pFin_one_apply]
    ring

end GlobalTheory.SchurExt
