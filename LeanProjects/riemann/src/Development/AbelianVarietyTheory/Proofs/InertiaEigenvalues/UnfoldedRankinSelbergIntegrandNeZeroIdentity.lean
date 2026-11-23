import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.RSCell

theorem bInt_tl_last_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (F : GA E (m + 1) → ℂ) (Φ : (Fin (m + 1) → Cinf E) → ℂ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T), (∀ w, l₀.1 w (Fin.last m) = 0) →
    GlobalTheory.JSW.whit F (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 → Φ (Pi.single (Fin.last m) 1) ≠ 0 → ∀ x : ℝ, GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 := by
  intro E _ _ _ m T ϖ F Φ J l₀ hl hW hΦ x
  have h0 : Finsupp.mapRange (fun y : Fin (m+1) → ℤ => y (Fin.last m)) rfl l₀.1 = 0 := by
    ext w; simp [hl w]
  have hadl : GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun y : Fin (m+1) → ℤ => y (Fin.last m)) rfl l₀.1) = 1 := by
    rw [h0]; apply Units.ext; apply FiniteAdeleRing.ext; intro v
    simp [GlobalTheory.CellDec.adl]; rfl
  have hrow : (GlobalTheory.CellDec.tl (m+1) ϖ l₀.1).val (Fin.last m) = Pi.single (Fin.last m) 1 := by
    rw [GlobalTheory.CellDec.tl_eq_diagT, GlobalTheory.SmGL.val_diagT]
    funext j
    simp [Matrix.diagonal_apply, Pi.single_apply, hadl, eq_comm]
  set g := GlobalTheory.CellDec.tl (m+1) ϖ l₀.1 with hg
  have hpi : (fun i => pInf E ((Pi.single (Fin.last m) (1 : Ad E) : Fin (m+1) → Ad E) i)) = Pi.single (Fin.last m) 1 := by
    funext i; by_cases h : i = Fin.last m
    · subst h; simp
    · simp [h]
  have hpf : (fun i => pFin E ((Pi.single (Fin.last m) (1 : Ad E) : Fin (m+1) → Ad E) i)) = Pi.single (Fin.last m) 1 := by
    funext i; by_cases h : i = Fin.last m
    · subst h; simp
    · simp [h]
  have hlat : (0 : Fin (m+1) → Af E) ∈ GlobalTheory.ThetaPoisson.latt (m+1) J := fun i => zero_mem _
  have hpsi : GlobalTheory.RSTheta.rsPsi (Fin.last m) (GlobalTheory.JSW.whit F) (GlobalTheory.JSW.whit F) Φ J (Pi.single (Fin.last m) 1) g (g.val (Fin.last m))
      = GlobalTheory.JSW.whit F g * (starRingEnd ℂ) (GlobalTheory.JSW.whit F g) * Φ (Pi.single (Fin.last m) 1) := by
    rw [hrow, GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, hpi, hpf, sub_self, Set.indicator_of_mem hlat,
      GlobalTheory.RSTheta.rsInf, GlobalTheory.RSTheta.rowGL_single, map_one, inv_one, mul_one]
    simp
  rw [bInt, hpsi]
  refine mul_ne_zero ?_ ?_
  · rw [enorm_ne_zero]
    exact mul_ne_zero (mul_ne_zero hW (by simpa using hW)) hΦ
  · rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.rpow_pos_of_pos (ideleModule E _).2 x

end GlobalTheory.RSCell
