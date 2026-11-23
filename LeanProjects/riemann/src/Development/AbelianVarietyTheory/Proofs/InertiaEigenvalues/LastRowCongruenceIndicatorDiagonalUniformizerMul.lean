import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellLintegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRankinSelbergSchurTermFinsuppEulerProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.CellLastRow

open GlobalTheory.CellDec GlobalTheory.ZEul

variable {E : Type} [Field E] [NumberField E]

theorem one_lt_v_zpow {v : HeightOneSpectrum (𝓞 E)} {ϖ : v.adicCompletion E} (h : IsUnifV E v ϖ) {a : ℤ}
    (ha : a < 0) : 1 < Valued.v (ϖ ^ a) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = -((n + 1 : ℕ) : ℤ) := ⟨(-a - 1).toNat, by omega⟩
  have h0 : ϖ ≠ 0 := fun e => by simp [IsUnifV, e] at h
  have h1 : Valued.v ϖ < 1 := by
    rw [h]; exact (by decide : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1)
  rw [zpow_neg, zpow_natCast, map_inv₀, map_pow]
  have hp : Valued.v ϖ ^ (n + 1) < 1 := pow_lt_one₀ zero_le' h1 (Nat.succ_ne_zero n)
  have hp0 : Valued.v ϖ ^ (n + 1) ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).2 h0)
  exact (one_lt_inv₀ (zero_lt_iff.2 hp0)).2 hp

end GlobalTheory.CellLastRow

namespace GlobalTheory.CellLastRow

open GlobalTheory.CellDec GlobalTheory.ZEul

theorem indN_lastRow_tl : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ N : ℕ,
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) →
    (∀ z z' : Af E, (∀ v ∈ S, z v = z' v) → (∀ v ∉ S, z v ∈ v.adicCompletionIntegers E) →
        (∀ v ∉ S, z' v ∈ v.adicCompletionIntegers E) → (z ∈ GlobalTheory.RSJ.natLat E N ↔ z' ∈ GlobalTheory.RSJ.natLat E N)) →
    ∀ (l : GlobalTheory.CellDec.abelian₂ E (m + 1) S), ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S,
    ((∀ w, 0 ≤ l.1 w (Fin.last m)) →
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) i)) =
        GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i))) ∧
    ((∃ w, l.1 w (Fin.last m) < 0) →
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) i)) = 0) := by
  intro E _ _ _ m S ϖ hϖ N hlat hloc l g hg
  obtain ⟨u, hu, k, hk, rfl⟩ := hg
  have hk' : ∀ v ∉ S, compV E (m + 1) v k ∈ GlobalTheory.LFun.KGL v (m + 1) := by
    simpa only [US, Subgroup.mem_iInf, Subgroup.mem_comap] using hk
  set c : (Af E)ˣ := adl ϖ (Finsupp.mapRange (fun x : Fin (m + 1) → ℤ => x (Fin.last m)) rfl l.1) with hc
  have hev : ∀ (x : Af E) v, x v = pLoc E v x := fun _ _ => rfl
  have hcv : ∀ v, pLoc E v (c : Af E) = ((ϖ v ^ l.1 v (Fin.last m) : (v.adicCompletion E)ˣ) : v.adicCompletion E) := by
    intro v
    change ((ϖ v ^ (Finsupp.mapRange (fun x : Fin (m + 1) → ℤ => x (Fin.last m)) rfl l.1) v :
      (v.adicCompletion E)ˣ) : v.adicCompletion E) = _
    rw [Finsupp.mapRange_apply]
  have hrow : ∀ i, lastRow (u * k) i = (k : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) i := by
    intro i
    have := congrFun (GlobalTheory.RSLocalPart.single_vecMul_unip (ℓ := Fin.last m) (fun j => Fin.le_last j) hu k) i
    simpa [lastRow, Units.val_mul, Matrix.single_one_vecMul] using this
  have hrow' : ∀ i, GlobalTheory.RSJ.pFin E (lastRow (tl (m + 1) ϖ l.1 * (u * k)) i) =
      (c : Af E) * GlobalTheory.RSJ.pFin E (lastRow (u * k) i) := by
    intro i
    simp only [lastRow, tl_eq_diagT, Units.val_mul, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_mul, map_mul]
    congr 1
    change GlobalTheory.RSJ.pFin E (1 - sFin E 1 + sFin E (c : Af E)) = _
    rw [map_add, map_sub, map_one]
    change 1 - 1 + (c : Af E) = _
    ring
  have hcomp : ∀ v i, pLoc E v (GlobalTheory.RSJ.pFin E (lastRow (u * k) i)) = (compV E (m + 1) v k).val (Fin.last m) i := by
    intro v i; rw [hrow]; rfl
  have hint : ∀ v ∉ S, ∀ i j, (compV E (m + 1) v k).val i j ∈ v.adicCompletionIntegers E := by
    intro v hv i j
    obtain ⟨k0, hk0⟩ := hk' v hv
    rw [← hk0]
    exact (k0.val i j).2
  have hinv : ∀ v ∉ S, ∀ i j, ((compV E (m + 1) v k)⁻¹).val i j ∈ v.adicCompletionIntegers E := by
    intro v hv i j
    obtain ⟨k0, hk0⟩ := hk' v hv
    rw [← hk0, ← map_inv]
    exact ((k0⁻¹).val i j).2
  have hδ : ∀ v (i : Fin (m + 1)), pLoc E v (if (i : ℕ) + 1 = m + 1 then (1 : Af E) else 0) ∈ v.adicCompletionIntegers E := by
    intro v i
    split_ifs
    · rw [map_one]; exact one_mem _
    · rw [map_zero]; exact zero_mem _
  refine ⟨fun hpos => ?_, fun ⟨w, hw⟩ => ?_⟩
  · have key : ∀ i : Fin (m + 1),
        (GlobalTheory.RSJ.pFin E (lastRow (tl (m + 1) ϖ l.1 * (u * k)) i) - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈
          GlobalTheory.RSJ.natLat E N ↔
        GlobalTheory.RSJ.pFin E (lastRow (u * k) i) - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈ GlobalTheory.RSJ.natLat E N) := by
      intro i
      refine (hloc _ _ (fun v hv => ?_) (fun v hv => ?_) (fun v hv => ?_)).symm
      · rw [hev, hev, map_sub, map_sub, hrow', map_mul, hcv, l.2 v hv]
        simp
      · rw [hev, map_sub, hcomp]
        exact sub_mem (hint v hv _ _) (hδ v i)
      · rw [hev, map_sub, hrow', map_mul, hcomp, hcv]
        refine sub_mem (mul_mem ?_ (hint v hv _ _)) (hδ v i)
        rw [Units.val_zpow_eq_zpow_val, ← Int.toNat_of_nonneg (hpos v), zpow_natCast]
        exact pow_mem (GlobalTheory.LFun.mem_Ov_of_isUnifV (hϖ v)) _
    unfold GlobalTheory.RSJ.indN
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (fun i => (key i).1 (h1 i)) h2
    · exact absurd (fun i => (key i).2 (h2 i)) h1
    · rfl
  · have hwS : w ∉ S := fun h => by
      have h0 := l.2 w h
      rw [h0] at hw
      exact lt_irrefl _ hw
    have hex : ∃ j, ¬ Valued.v ((compV E (m + 1) w k).val (Fin.last m) j) < 1 := by
      by_contra hcon
      push_neg at hcon
      have h1 : ((compV E (m + 1) w k).val * ((compV E (m + 1) w k)⁻¹).val) (Fin.last m) (Fin.last m) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
      rw [Matrix.mul_apply] at h1
      have h2 : Valued.v (∑ j, (compV E (m + 1) w k).val (Fin.last m) j * ((compV E (m + 1) w k)⁻¹).val j (Fin.last m)) < 1 := by
        refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
        rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (hcon j) (hinv w hwS j (Fin.last m))
      rw [h1, map_one] at h2
      exact lt_irrefl _ h2
    obtain ⟨j, hj⟩ := hex
    have hj1 : Valued.v ((compV E (m + 1) w k).val (Fin.last m) j) = 1 :=
      le_antisymm (hint w hwS _ _) (not_lt.1 hj)
    unfold GlobalTheory.RSJ.indN
    rw [if_neg]
    intro hall
    have hz := hlat _ (hall j) w
    dsimp only at hz
    rw [hev, map_sub, hrow', map_mul, hcomp, hcv] at hz
    have ha := add_mem hz (hδ w j)
    rw [sub_add_cancel, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hj1, mul_one,
      Units.val_zpow_eq_zpow_val] at ha
    exact not_le.2 (one_lt_v_zpow (hϖ w) hw) ha

end GlobalTheory.CellLastRow
