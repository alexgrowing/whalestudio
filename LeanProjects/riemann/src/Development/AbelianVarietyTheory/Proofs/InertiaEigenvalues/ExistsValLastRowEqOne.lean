import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellLintegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGlobalWhittakerCoefficientGLAdeles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsuppVanishingOnEquivComplProd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenAdelicUnipotentTimesIntegralOutsideSet
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulSupSFinGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SuperDiagBlockGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerCommuteOfOneOff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerEqProdLocalDiagonal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdelicAbsDetPowDiagonalUniformizerMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfNotAntitoneInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCutOperatorTransferAdelicWhittaker
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenKGLInvEntries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedIntegrandMeasurableInvariantBounded
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergLocalTermEqSphericalWhittakerProduc
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.CellEvalNM

open GroundTheory.Automorphic.FourierWhittaker (blockGL blockMat blockMat_apply coe_blockGL)

variable {E : Type} [Field E] [NumberField E]

theorem map_blockGL' {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) {j n : ℕ} (hj : j ≤ n)
    (g : GL (Fin j) R) :
    Matrix.GeneralLinearGroup.map p (blockGL hj g) = blockGL hj (Matrix.GeneralLinearGroup.map p g) := by
  ext a b
  simp [blockMat_apply]
  split_ifs <;> simp

theorem blockGL_finGL {j n : ℕ} (hj : j ≤ n) (k : GL (Fin j) (Af E)) :
    blockGL hj (finGL E j k) = finGL E n (blockGL hj k) := by
  have hf : ∀ (N : ℕ) (k : GL (Fin N) (Af E)) (a b : Fin N), ((finGL E N k : GA E N) : Matrix (Fin N) (Fin N) (Ad E)) a b =
      (1 : Matrix (Fin N) (Fin N) (Ad E)) a b - sFin E ((1 : Matrix (Fin N) (Fin N) (Af E)) a b) +
        sFin E ((k : Matrix (Fin N) (Fin N) (Af E)) a b) := fun N k a b => rfl
  apply Units.ext
  ext a b
  rw [coe_blockGL, blockMat_apply, hf, coe_blockGL, blockMat_apply]
  split_ifs with h1 h2 h3 <;> simp only [hf, Matrix.one_apply, Fin.ext_iff] <;> split_ifs <;> first | (simp; done) | (exfalso; omega) | (exfalso; simp_all; done) | (simp only [map_zero]; abel)

theorem blockGL_mem_KGL (w : HeightOneSpectrum (𝓞 E)) {j n : ℕ} (hj : j ≤ n) {y : GL (Fin j) (w.adicCompletion E)}
    (hy : y ∈ KGL w j) : blockGL hj y ∈ KGL w n := by
  rw [GlobalTheory.HenQ.Basic.mem_KGL_iff] at hy ⊢
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · rw [coe_blockGL, blockMat_apply]
    split_ifs
    · exact hy.1 _ _
    · exact zero_mem _
    · exact one_mem _
    · exact zero_mem _
  · rw [← map_inv, coe_blockGL, blockMat_apply]
    split_ifs
    · exact hy.2 _ _
    · exact zero_mem _
    · exact one_mem _
    · exact zero_mem _

end GlobalTheory.CellEvalNM

namespace GlobalTheory.CellEvalNM

open GroundTheory.Automorphic.FourierWhittaker (blockGL blockMat blockMat_apply coe_blockGL)

theorem eq_zero_of_comp_diag (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ)
    (w : HeightOneSpectrum (𝓞 E))
    (hψ : ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w)
    (ϖw : (w.adicCompletion E)ˣ) (hϖ : IsUnifV E w (ϖw : w.adicCompletion E)) (W : GA E N → ℂ)
    (hWN : ∀ u ∈ GlobalTheory.JSW.NA E N, ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g)
    (hWK : ∀ k ∈ KGL w N, ∀ g, W (g * finGL E N (locGL E N w k)) = W g)
    (e : Fin N → ℤ) (he : ¬ Antitone e) (P : GA E N)
    (hP : ((GlobalTheory.CellDec.compV E N w P : GL (Fin N) (w.adicCompletion E)) : Matrix (Fin N) (Fin N) (w.adicCompletion E)) =
      Matrix.diagonal fun a => ((ϖw ^ e a : (w.adicCompletion E)ˣ) : w.adicCompletion E)) :
    W P = 0 := by
  set D := GlobalTheory.CellDec.compV E N w P with hD
  set P' := P * (finGL E N (locGL E N w D))⁻¹ with hP'
  have hP'w : Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) P' = 1 := by
    change GlobalTheory.CellDec.compV E N w P' = 1
    rw [hP', map_mul, map_inv, GlobalTheory.CellDec.compV_finGL_locGL_same, ← hD, mul_inv_cancel]
  have htt : P' * finGL E N (locGL E N w D) = P := by rw [hP', inv_mul_cancel_right]
  let f : GL (Fin N) (w.adicCompletion E) → ℂ := fun g => W (P' * finGL E N (locGL E N w g))
  have hfD : f D = W P := by simp only [f]; rw [htt]
  have hfN : ∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin N), ∀ g,
      f (u * g) = GlobalTheory.JSW.psiLocChar w (GlobalTheory.Whittaker.superDiag u) * f g := by
    intro u hu g
    simp only [f]
    rw [map_mul, map_mul, ← mul_assoc P', GlobalTheory.JSW.commute_finGL_locGL w hP'w, mul_assoc,
      hWN _ (GlobalTheory.JSW.CutTransfer.finGL_locGL_mem_NA' w hu), GlobalTheory.JSW.CutTransfer.psiN_finGL_locGL]
    rfl
  have hfK : ∀ g, ∀ k ∈ KGL w N, f (g * k) = f g := by
    intro g k hk
    simp only [f]
    rw [map_mul, map_mul, ← mul_assoc]
    exact hWK k hk _
  have h := GlobalTheory.WhitTorus.eq_zero_of_not_antitone_int E w N (GlobalTheory.JSW.psiLocChar w) hψ f hfN hfK ϖw hϖ e he D hP
  rwa [hfD] at h

variable {E : Type} [Field E] [NumberField E]

theorem lastRow_diag_mul {m : ℕ} (d : Fin (m + 1) → (Ad E)ˣ) (g : GA E (m + 1)) :
    GlobalTheory.ZEul.lastRow (GlobalTheory.SmGL.diagT (Ad E) (Fin (m + 1)) d * g) =
      fun j => ((d (Fin.last m) : Ad E)) * GlobalTheory.ZEul.lastRow g j := by
  funext j
  simp only [GlobalTheory.ZEul.lastRow, Units.val_mul, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_mul]

theorem exists_val_lastRow_eq_one (w : HeightOneSpectrum (𝓞 E)) {m : ℕ} {k : GL (Fin (m + 1)) (w.adicCompletion E)}
    (hk : k ∈ KGL w (m + 1)) : ∃ j, Valued.v ((k : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j) = 1 := by
  rw [GlobalTheory.HenQ.Basic.mem_KGL_iff] at hk
  by_contra hne
  push_neg at hne
  have hlt : ∀ j, Valued.v ((k : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j) < 1 :=
    fun j => lt_of_le_of_ne (hk.1 _ _) (hne j)
  have h1 : ((k : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) * ((k⁻¹ : GL (Fin (m + 1)) (w.adicCompletion E)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E))) (Fin.last m) (Fin.last m) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
  rw [Matrix.mul_apply] at h1
  have h2 : Valued.v (∑ j, (k : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j *
      ((k⁻¹ : GL (Fin (m + 1)) (w.adicCompletion E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) j (Fin.last m)) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [map_mul]
    calc _ ≤ Valued.v ((k : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j) * 1 :=
          by gcongr; exact hk.2 _ _
      _ < 1 := by rw [mul_one]; exact hlt j
  rw [h1, map_one] at h2
  exact lt_irrefl _ h2

end GlobalTheory.CellEvalNM

namespace GlobalTheory.CellEvalNM

open GlobalTheory.RSnmUnf

theorem padNat_self {j : ℕ} (l : Fin j → ℕ) : padNat (n := j) l = l := by
  funext i; simp [padNat]

theorem sphW_pad (q : ℕ) (hq : 0 < q) {j n : ℕ} (hj : j ≤ n) (α : Fin n → ℂ) (v : Fin j → ℤ) (h0 : ∀ i, 0 ≤ v i)
    (hv : Antitone v) :
    sphW q α (padNat fun i => (v i).toNat) =
      (((q : ℝ) ^ (-((GlobalTheory.CellDec.wtS j v : ℝ) + ((n : ℝ) - j) * ∑ i, (v i : ℝ)) / 2) : ℝ) : ℂ) *
        schurAt (padNat fun i => (v i).toNat) α := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hl : Antitone (padNat (n := n) fun i => (v i).toNat) := by
    intro a b hab
    have hab' : (a : ℕ) ≤ b := hab
    simp only [padNat]
    split_ifs with h1 h2 h2
    · exact Int.toNat_le_toNat (hv (show (⟨a, h2⟩ : Fin j) ≤ ⟨b, h1⟩ from hab'))
    · omega
    · exact Nat.zero_le _
    · exact le_rfl
  have hcast : ∀ i, (((v i).toNat : ℕ) : ℂ) = ((v i : ℤ) : ℂ) := by
    intro i
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (h0 i)]
  have hc : (∑ i : Fin n, (((n : ℂ) - 1 - 2 * (i : ℕ)) * ((padNat (n := n) (fun i => (v i).toNat) i : ℕ) : ℂ))) =
      ∑ i : Fin j, (((n : ℂ) - 1 - 2 * (i : ℕ)) * (v i : ℂ)) := by
    symm
    refine Fintype.sum_of_injective (Fin.castLE hj) (Fin.castLE_injective hj) _ _ ?_ ?_
    · intro i hi
      have hij : ¬ (i : ℕ) < j := fun h => hi ⟨⟨i, h⟩, rfl⟩
      simp [padNat, hij]
    · intro i
      simp [padNat, hcast]
  rw [sphW, if_pos hl, hc, Complex.ofReal_cpow hqR.le, GlobalTheory.ZEulLocal.wtS_eq_sum]
  congr 2
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem localTerm_mixed (q : ℕ) (hq : 0 < q) {j n : ℕ} (hj : j ≤ n) (α : Fin n → ℂ) (β : Fin j → ℂ) (x y : ℝ)
    (hy : y = x - ((n : ℝ) - j) / 2) (v : Fin j → ℤ) (h0 : ∀ i, 0 ≤ v i) (hv : Antitone v) :
    (((q : ℝ) ^ GlobalTheory.CellDec.wtS j v : ℝ) : ℂ) *
      (sphW q α (padNat fun i => (v i).toNat) * conj (sphW q β (fun i => (v i).toNat))) *
      (((q : ℝ) ^ (-y * ∑ i, (v i : ℝ)) : ℝ) : ℂ) = rsTermNM q α β x v := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hβ := sphW_pad q hq le_rfl β v h0 hv
  rw [padNat_self] at hβ
  have key2 : (((q : ℝ) ^ (-x * ∑ i, (v i : ℝ)) : ℝ) : ℂ) = ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, (v i).toNat) := by
    have e : (q : ℂ) ^ (-(x : ℂ)) = (((q : ℝ) ^ (-x) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hqR.le]
      push_cast
      rfl
    rw [e, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul hqR.le]
    congr 3
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    exact_mod_cast (Int.toNat_of_nonneg (h0 i)).symm
  rw [sphW_pad q hq hj α v h0 hv, hβ, rsTermNM, if_pos ⟨h0, hv⟩, ← key2, map_mul, Complex.conj_ofReal]
  set s : ℝ := ∑ i, (v i : ℝ)
  set A : ℝ := (q : ℝ) ^ (-((GlobalTheory.CellDec.wtS j v : ℝ) + ((n : ℝ) - j) * s) / 2) with hA
  set A' : ℝ := (q : ℝ) ^ (-((GlobalTheory.CellDec.wtS j v : ℝ) + ((j : ℝ) - j) * s) / 2) with hA'
  have key : (q : ℝ) ^ GlobalTheory.CellDec.wtS j v * (A * A') * (q : ℝ) ^ (-y * s) = (q : ℝ) ^ (-x * s) := by
    rw [hA, hA', ← Real.rpow_intCast, ← Real.rpow_add hqR, ← Real.rpow_add hqR, ← Real.rpow_add hqR, hy]
    congr 1
    ring
  rw [← key]
  push_cast
  ring

theorem localTerm_diag (q : ℕ) (hq : 0 < q) {j n : ℕ} (hj : j ≤ n) (α : Fin n → ℂ) (x y : ℝ)
    (hy : y = x - ((n : ℝ) - j)) (v : Fin j → ℤ) (h0 : ∀ i, 0 ≤ v i) (hv : Antitone v) :
    (q : ℝ) ^ GlobalTheory.CellDec.wtS j v * ‖sphW q α (padNat fun i => (v i).toNat)‖ ^ 2 * (q : ℝ) ^ (-y * ∑ i, (v i : ℝ)) =
      ‖schurAt (padNat (n := n) fun i => (v i).toNat) α‖ ^ 2 * (q : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hs : ((∑ i, (v i).toNat : ℕ) : ℝ) = ∑ i, (v i : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    exact_mod_cast (Int.toNat_of_nonneg (h0 i))
  rw [sphW_pad q hq hj α v h0 hv, hs, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hqR.le _)]
  set s : ℝ := ∑ i, (v i : ℝ)
  set A : ℝ := (q : ℝ) ^ (-((GlobalTheory.CellDec.wtS j v : ℝ) + ((n : ℝ) - j) * s) / 2) with hA
  have key : (q : ℝ) ^ GlobalTheory.CellDec.wtS j v * (A * A) * (q : ℝ) ^ (-y * s) = (q : ℝ) ^ (-(s * x)) := by
    rw [hA, ← Real.rpow_intCast, ← Real.rpow_add hqR, ← Real.rpow_add hqR, ← Real.rpow_add hqR, hy]
    congr 1
    ring
  rw [← key]
  ring

theorem ennreal_collect {ι : Type} (s : Finset ι) (a e t : ι → ℝ) (p : ι → ℂ) (ha : ∀ w, 0 ≤ a w) (he : ∀ w, 0 ≤ e w)
    (ht : ∀ w ∈ s, a w * ‖p w‖ ^ 2 * e w = t w) (c W : ℂ) (hc : ‖c‖ = 1) (Z : ℝ≥0∞) (D : ℝ) :
    ENNReal.ofReal (∏ w ∈ s, a w) * (‖c * (∏ w ∈ s, p w) * W‖ₑ ^ 2 * Z * ENNReal.ofReal ((∏ w ∈ s, e w) * D)) =
      (∏ w ∈ s, ENNReal.ofReal (t w)) * (‖W‖ₑ ^ 2 * Z * ENNReal.ofReal D) := by
  have h1 : (∏ w ∈ s, ENNReal.ofReal (t w)) =
      ENNReal.ofReal (∏ w ∈ s, a w) * ‖∏ w ∈ s, p w‖ₑ ^ 2 * ENNReal.ofReal (∏ w ∈ s, e w) := by
    rw [← ENNReal.ofReal_prod_of_nonneg (fun w hw => by rw [← ht w hw]; have := ha w; have := he w; positivity),
      ← Finset.prod_congr rfl ht, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, ← norm_prod,
      ENNReal.ofReal_mul (mul_nonneg (Finset.prod_nonneg fun w _ => ha w) (by positivity)),
      ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => ha w), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have h2 : ‖c‖ₑ = 1 := by rw [← ofReal_norm_eq_enorm, hc, ENNReal.ofReal_one]
  rw [h1, enorm_mul, enorm_mul, h2, ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => he w)]
  ring

end GlobalTheory.CellEvalNM

namespace GlobalTheory.CellEvalNM

open GroundTheory.Automorphic.FourierWhittaker (blockGL blockMat blockMat_apply coe_blockGL)

theorem compV_tl {E : Type} [Field E] [NumberField E] (N : ℕ) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin N → ℤ)) (w : HeightOneSpectrum (𝓞 E)) :
    ((GlobalTheory.CellDec.compV E N w (GlobalTheory.CellDec.tl N ϖ l) : GL (Fin N) (w.adicCompletion E)) :
      Matrix (Fin N) (Fin N) (w.adicCompletion E)) =
      Matrix.diagonal fun a => ((ϖ w ^ l w a : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
  rw [GlobalTheory.CellDec.tl, GlobalTheory.CellDec.compV_finGL]
  refine Matrix.ext fun i j => ?_
  change pLoc E w (((GlobalTheory.SmGL.diagT (Af E) (Fin N) _ : GL (Fin N) (Af E)) : Matrix (Fin N) (Fin N) (Af E)) i j) = _
  rw [GlobalTheory.SmGL.val_diagT]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq]
    change ((ϖ w ^ (Finsupp.mapRange (fun x : Fin N → ℤ => x i) rfl l) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
    simp
  · simp [Matrix.diagonal_apply_ne _ hij]

theorem cell_values (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hψ : ∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w)
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (hϖ : ∀ w, IsUnifV E w (ϖ w : w.adicCompletion E))
    (g : GA E N) (hg : g ∈ GlobalTheory.CellDec.C0 E N S) (l : GlobalTheory.CellDec.abelian₂ E N S) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ V : GA E N → ℂ, (∀ u ∈ GlobalTheory.JSW.NA E N, ∀ g, V (u * g) = GlobalTheory.JSW.psiN u * V g) →
      (∀ k : GL (Fin N) (Af E), (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v N) →
        (∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) → ∀ g, V (g * finGL E N k) = V g) →
      ((∃ w, ¬ Antitone (l.1 w)) → V (GlobalTheory.CellDec.tl N ϖ l.1 * g) = 0) ∧
      ∀ p : HeightOneSpectrum (𝓞 E) → (Fin N → ℕ) → ℂ,
        (∀ l' : HeightOneSpectrum (𝓞 E) →₀ (Fin N → ℕ), (∀ w ∈ l'.support, w ∉ S) → ∀ h ∈ GlobalTheory.JSW.supS E N S,
          V (h * GlobalTheory.JSW.tl ϖ l') = (∏ w ∈ l'.support, p w (l' w)) * V h) →
        (∀ w i, 0 ≤ l.1 w i) →
        V (GlobalTheory.CellDec.tl N ϖ l.1 * g) = c * (∏ w ∈ l.1.support, p w (fun i => (l.1 w i).toNat)) * V g := by
  obtain ⟨u, hu, h, hh, k, hk, hkS, rfl⟩ := GlobalTheory.CellDec.exists_mul_supS_finGL E N S g hg
  set t := GlobalTheory.CellDec.tl N ϖ l.1 with ht
  have hcomm : h * t = t * h := GlobalTheory.CellDec.TlComm.tl_commute_of_one_off E N S ϖ l h hh
  have hu0 : u ∈ GlobalTheory.JSW.NA E N := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
  have hu' : t * u * t⁻¹ ∈ GlobalTheory.JSW.NA E N := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 (GlobalTheory.CellDec.tl_conj_mem ϖ l.1 hu)
  have hσ : t * (u * h * finGL E N k) = (t * u * t⁻¹) * (h * t) * finGL E N k := by
    rw [hcomm]; group
  have hne : GlobalTheory.JSW.psiN u ≠ 0 := norm_ne_zero_iff.1 (by rw [GlobalTheory.RSnmUnfProps.norm_psiN]; exact one_ne_zero)
  refine ⟨GlobalTheory.JSW.psiN (t * u * t⁻¹) * (GlobalTheory.JSW.psiN u)⁻¹, ?_, fun V hN hK => ⟨?_, fun p hp hnn => ?_⟩⟩
  · rw [norm_mul, norm_inv, GlobalTheory.RSnmUnfProps.norm_psiN, GlobalTheory.RSnmUnfProps.norm_psiN, inv_one, mul_one]
  · rintro ⟨w, hw⟩
    have hw0 : l.1 w ≠ 0 := by rintro h0; rw [h0] at hw; exact hw antitone_const
    have hwS : w ∉ S := fun h => hw0 (l.2 w h)
    rw [hσ, hK k hk hkS, hN _ hu', eq_zero_of_comp_diag E N w (hψ w hwS) (ϖ w) (hϖ w) V hN ?_ (l.1 w) hw (h * t) ?_,
      mul_zero]
    · intro k' hk'
      refine hK _ (fun v => ?_) fun v hv => pLoc_locGL_of_ne (fun e : v = w => hwS (e ▸ hv)) k'
      by_cases hvw : v = w
      · subst hvw; rw [pLoc_locGL]; exact hk'
      · rw [pLoc_locGL_of_ne hvw]; exact one_mem _
    · have h1 : GlobalTheory.CellDec.compV E N w h = 1 := hh w hwS
      rw [map_mul, h1, one_mul]
      exact compV_tl N ϖ l.1 w
  · obtain ⟨l', hl'app⟩ : ∃ l' : HeightOneSpectrum (𝓞 E) →₀ (Fin N → ℕ), ∀ w, l' w = fun i => (l.1 w i).toNat :=
      ⟨Finsupp.mapRange (fun v i => (v i).toNat) (funext fun _ => rfl) l.1, fun w => Finsupp.mapRange_apply⟩
    have hl' : ∀ w i, ((l' w i : ℕ) : ℤ) = l.1 w i := fun w i => by
      rw [hl'app]; exact Int.toNat_of_nonneg (hnn w i)
    have hsupp : l'.support = l.1.support := by
      ext w
      simp only [Finsupp.mem_support_iff, ne_eq]
      constructor
      · intro h h0; apply h; rw [hl'app, h0]; rfl
      · intro h h0; apply h; funext i; have := hl' w i; rw [h0] at this; simpa using this.symm
    have htl : t = GlobalTheory.JSW.tl ϖ l' := GlobalTheory.CellDecNat.tl_eq_jsw_tl E N ϖ l.1 l' hl'
    have hsS : ∀ w ∈ l'.support, w ∉ S := fun w hw hS' => by
      rw [hsupp, Finsupp.mem_support_iff] at hw; exact hw (l.2 w hS')
    have e1 : V (h * t) = (∏ w ∈ l.1.support, p w (fun i => (l.1 w i).toNat)) * V h := by
      rw [htl, hp l' hsS h hh, hsupp]
      simp only [hl'app]
    rw [hσ, hK k hk hkS, hN _ hu', e1, hK k hk hkS, hN _ hu0]
    field_simp

theorem lastRow_prim (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (g : GA E (m + 1)) (hg : g ∈ GlobalTheory.CellDec.C0 E (m + 1) S) (w : HeightOneSpectrum (𝓞 E)) (hw : w ∉ S) :
    (∀ j, pLoc E w (pFin E (GlobalTheory.ZEul.lastRow g j)) ∈ w.adicCompletionIntegers E) ∧
      ∃ j, Valued.v (pLoc E w (pFin E (GlobalTheory.ZEul.lastRow g j))) = 1 := by
  obtain ⟨u, hu, k, hk, rfl⟩ := hg
  rw [GlobalTheory.ZEulProps.lastRow_unip hu]
  have hkw : GlobalTheory.CellDec.compV E (m + 1) w k ∈ KGL w (m + 1) := by
    simp only [GlobalTheory.CellDec.US, Subgroup.mem_iInf, Subgroup.mem_comap] at hk
    exact hk w hw
  have he : ∀ j, pLoc E w (pFin E (GlobalTheory.ZEul.lastRow k j)) = ((GlobalTheory.CellDec.compV E (m + 1) w k : GL (Fin (m + 1)) (w.adicCompletion E)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j := fun j => by
    rw [GlobalTheory.CellDec.compV, Matrix.GeneralLinearGroup.map_apply]; rfl
  obtain ⟨j, hj⟩ := exists_val_lastRow_eq_one w hkw
  refine ⟨fun j => ?_, j, ?_⟩
  · rw [he]; exact ((GlobalTheory.HenQ.Basic.mem_KGL_iff w _).1 hkw).1 (Fin.last m) j
  · rw [he]; exact hj

end GlobalTheory.CellEvalNM

open GroundTheory.Automorphic.FourierWhittaker (blockGL) in
open GlobalTheory.CellEvalNM in

theorem GlobalTheory.CellEvalNM.uIntNM_cell_eval : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (α : HeightOneSpectrum (𝓞 E) → Fin (m + r + 1 + 1) → ℂˣ) (β : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ)
      (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (F : (Fin (m + 1) → Ad E) → ℂ),
    (∀ u ∈ GlobalTheory.JSW.NA E (m + r + 1 + 1), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    (∀ k : GL (Fin (m + r + 1 + 1)) (Af E), (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v (m + r + 1 + 1)) →
      (∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) → ∀ g, GlobalTheory.JSW.whit φ (g * finGL E (m + r + 1 + 1) k) = GlobalTheory.JSW.whit φ g) →
    (∀ k : GL (Fin (m + 1)) (Af E), (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v (m + 1)) →
      (∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) → ∀ g, GlobalTheory.JSW.whit φ' (g * finGL E (m + 1) k) = GlobalTheory.JSW.whit φ' g) →
    (∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
      ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S,
        GlobalTheory.JSW.whit φ' (h * GlobalTheory.JSW.tl ϖ l) =
          (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (β w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ' h) →
    (∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
      ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S,
        GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (h * GlobalTheory.JSW.tl ϖ l)) =
          (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (GlobalTheory.RSnmUnf.padNat (l w))) *
            GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)) →
    (∀ a : HeightOneSpectrum (𝓞 E) →₀ ℤ, (∀ v ∈ S, a v = 0) →
      ∀ y : Fin (m + 1) → Ad E,
        (∀ w ∉ S, (∀ j, pLoc E w (pFin E (y j)) ∈ w.adicCompletionIntegers E) ∧
          ∃ j, Valued.v (pLoc E w (pFin E (y j))) = 1) →
        ((∀ w, 0 ≤ a w) → GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (fun j => ((finId E (GlobalTheory.CellDec.adl ϖ a) : (Ad E)ˣ) : Ad E) * y j) = GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y) ∧
        ((∃ w, a w < 0) → GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (fun j => ((finId E (GlobalTheory.CellDec.adl ϖ a) : (Ad E)ˣ) : Ad E) * y j) = 0)) →
    ∀ (x : ℝ), ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) S,
      (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) * GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
        (l.1.prod fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ)) (fun i => (β w i : ℂ)) x v) *
          GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' 0 g * ((GlobalTheory.RSnm.detAbs g ^ x : ℝ) : ℂ) ∧
      ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) * (‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g))‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g))‖ₑ *
          ENNReal.ofReal (GlobalTheory.RSnm.detAbs (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ^ (x - ((r : ℝ) + 1)))) = (l.1.prod fun w v => if (∀ i, 0 ≤ v i) ∧ Antitone v then
          ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (GlobalTheory.RSnmUnf.padNat (n := (m + r + 1 + 1)) fun i => (v i).toNat) (fun i => (α w i : ℂ))‖ ^ 2 *
            (Ideal.absNorm w.asIdeal : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x))) else 0) * (‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (g))‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow (g))‖ₑ *
          ENNReal.ofReal (GlobalTheory.RSnm.detAbs (g) ^ (x - ((r : ℝ) + 1)))) ∧
      ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) * (‖GlobalTheory.JSW.whit φ' (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g)‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g))‖ₑ *
          ENNReal.ofReal (GlobalTheory.RSnm.detAbs (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ^ x)) = (l.1.prod fun w v => if (∀ i, 0 ≤ v i) ∧ Antitone v then
          ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (GlobalTheory.RSnmUnf.padNat (n := (m + 1)) fun i => (v i).toNat) (fun i => (β w i : ℂ))‖ ^ 2 *
            (Ideal.absNorm w.asIdeal : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x))) else 0) * (‖GlobalTheory.JSW.whit φ' (g)‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow (g))‖ₑ *
          ENNReal.ofReal (GlobalTheory.RSnm.detAbs (g) ^ x)) := by
  intro E _ _ _ m r S hψ ϖ hϖ α β φ φ' F hN hN' hK hK' hS' hS hF x g hg l
  have hmn : m + 1 ≤ m + r + 1 + 1 := by omega
  obtain ⟨c, hc, hV⟩ := cell_values E (m + 1) S hψ ϖ hϖ g hg l
  obtain ⟨hz1, hv1⟩ := hV (fun g => GlobalTheory.JSW.whit φ (blockGL hmn g))
    (fun u hu g => by
      rw [map_mul, hN _ (GlobalTheory.RSnmUnfProps.blockGL_mem_NA hmn hu), GlobalTheory.RSnmUnfProps.psiN_blockGL])
    (fun k hk hkS g => by
      rw [map_mul, blockGL_finGL]
      refine hK _ (fun v => ?_) (fun v hv => ?_) _
      · rw [map_blockGL']; exact blockGL_mem_KGL v hmn (hk v)
      · rw [map_blockGL', hkS v hv, map_one])
  obtain ⟨hz2, hv2⟩ := hV (GlobalTheory.JSW.whit φ') hN' hK'
  have hrow : GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) = fun j =>
      ((finId E (GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun x : Fin (m + 1) → ℤ => x (Fin.last m)) rfl l.1)) : (Ad E)ˣ) : Ad E) *
        GlobalTheory.ZEul.lastRow g j := by
    rw [GlobalTheory.CellDec.tl_eq_diagT, lastRow_diag_mul]
  obtain ⟨hF1, hF2⟩ := hF (Finsupp.mapRange (fun x : Fin (m + 1) → ℤ => x (Fin.last m)) rfl l.1)
    (fun v hv => by rw [Finsupp.mapRange_apply, l.2 v hv]; rfl) (GlobalTheory.ZEul.lastRow g) (lastRow_prim E m S g hg)
  rw [← hrow] at hF1 hF2
  simp only [Finsupp.mapRange_apply] at hF1 hF2
  by_cases hgood : ∀ w, (∀ i, 0 ≤ l.1 w i) ∧ Antitone (l.1 w)
  swap
  · obtain ⟨w, hw⟩ := not_forall.1 hgood
    have hws : w ∈ l.1.support := by
      rw [Finsupp.mem_support_iff]; intro h0; rw [h0] at hw; exact hw ⟨fun _ => le_rfl, antitone_const⟩
    rw [Finsupp.prod, Finsupp.prod, Finsupp.prod, Finset.prod_eq_zero hws (by rw [GlobalTheory.RSnmUnf.rsTermNM, if_neg hw]),
      Finset.prod_eq_zero hws (if_neg hw), Finset.prod_eq_zero hws (if_neg hw), GlobalTheory.RSnmUnf.uIntNM]
    by_cases ha : ∀ w, Antitone (l.1 w)
    · have h0 := hF2 ⟨w, not_le.1 fun h => hw ⟨fun i => le_trans h (ha w (Fin.le_last i)), ha w⟩⟩
      simp [h0]
    · have h1 := hz1 (not_forall.1 ha)
      have h2 := hz2 (not_forall.1 ha)
      rw [h1, h2]
      simp
  have hnn : ∀ w i, 0 ≤ l.1 w i := fun w => (hgood w).1
  have e1 := hv1 (fun w v => GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (GlobalTheory.RSnmUnf.padNat v)) hS hnn
  have e2 := hv2 (fun w v => GlobalTheory.JSW.sphW (qV E w) (fun i => (β w i : ℂ)) v) hS' hnn
  have e3 := hF1 fun w => hnn w _
  have hq : ∀ w, 0 < qV E w := fun w => Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hdet : ∀ y : ℝ, GlobalTheory.RSnm.detAbs (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ^ y =
      (∏ w ∈ l.1.support, (qV E w : ℝ) ^ (-y * ∑ i, (l.1 w i : ℝ))) * GlobalTheory.RSnm.detAbs g ^ y := fun y => by
    have := GlobalTheory.CellEvalDet.detPow_tl_mul E (m + 1) ϖ hϖ l.1 y g
    rwa [GlobalTheory.CellEvalDet.detPow_eq_rpow, GlobalTheory.CellEvalDet.detPow_eq_rpow] at this
  refine ⟨?_, ?_, ?_⟩
  · set y : ℝ := x - (((m + r + 1 + 1 : ℕ) : ℝ) - ((m + 1 : ℕ) : ℝ)) / 2 with hy
    have hp : ∀ (z : ℝ) (h : GA E (m + 1)), ((GlobalTheory.RSnm.detAbs h : ℝ) : ℂ) ^ ((z : ℂ) - (((m + r + 1 + 1 : ℕ) : ℂ) - ((m + 1 : ℕ) : ℂ)) / 2) =
        ((GlobalTheory.RSnm.detAbs h ^ (z - (((m + r + 1 + 1 : ℕ) : ℝ) - ((m + 1 : ℕ) : ℝ)) / 2) : ℝ) : ℂ) := fun z h => by
      rw [Complex.ofReal_cpow (GlobalTheory.RSnm.detAbs_pos h).le]
      congr 1
      push_cast
      ring
    have hg2 : GlobalTheory.RSnm.detAbs g ^ y = GlobalTheory.RSnm.detAbs g ^ ((0 : ℝ) - (((m + r + 1 + 1 : ℕ) : ℝ) - ((m + 1 : ℕ) : ℝ)) / 2) *
        GlobalTheory.RSnm.detAbs g ^ x := by
      rw [← Real.rpow_add (GlobalTheory.RSnm.detAbs_pos g), hy]
      congr 1
      ring
    have key : ((GlobalTheory.CellDec.dinv (m + 1) l.1 : ℝ) : ℂ) *
        ((∏ w ∈ l.1.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (GlobalTheory.RSnmUnf.padNat fun i => (l.1 w i).toNat)) *
          conj (∏ w ∈ l.1.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (β w i : ℂ)) (fun i => (l.1 w i).toNat))) *
        (((∏ w ∈ l.1.support, (qV E w : ℝ) ^ (-y * ∑ i, (l.1 w i : ℝ))) : ℝ) : ℂ) =
        l.1.prod fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ))
          (fun i => (β w i : ℂ)) x v := by
      rw [map_prod, ← Finset.prod_mul_distrib, GlobalTheory.CellDec.dinv, Complex.ofReal_prod, Complex.ofReal_prod,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, Finsupp.prod]
      exact Finset.prod_congr rfl fun w _ =>
        localTerm_mixed (qV E w) (hq w) hmn _ _ x y hy (l.1 w) (hgood w).1 (hgood w).2
    have hcc : c * conj c = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
    rw [GlobalTheory.RSnmUnf.uIntNM, GlobalTheory.RSnmUnf.uIntNM, hp, hp, ← hy, hdet, hg2, e1, e2, e3, ← key, map_mul, map_mul,
      Complex.ofReal_mul, Complex.ofReal_mul]
    generalize GlobalTheory.JSW.whit φ (blockGL hmn g) = W₁
    generalize conj (GlobalTheory.JSW.whit φ' g) = W₂
    linear_combination (exp := 1) (((GlobalTheory.CellDec.dinv (m + 1) l.1 : ℝ) : ℂ) *
        ((∏ w ∈ l.1.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (GlobalTheory.RSnmUnf.padNat fun i => (l.1 w i).toNat)) *
          conj (∏ w ∈ l.1.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (β w i : ℂ)) (fun i => (l.1 w i).toNat))) *
        (((∏ w ∈ l.1.support, (qV E w : ℝ) ^ (-y * ∑ i, (l.1 w i : ℝ))) : ℝ) : ℂ) * W₁ * W₂ *
        GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g) *
        ((GlobalTheory.RSnm.detAbs g ^ ((0 : ℝ) - (((m + r + 1 + 1 : ℕ) : ℝ) - ((m + 1 : ℕ) : ℝ)) / 2) : ℝ) : ℂ) *
        ((GlobalTheory.RSnm.detAbs g ^ x : ℝ) : ℂ)) * hcc
  · rw [e1, e3, hdet, GlobalTheory.CellDec.dinv, Finsupp.prod, Finset.prod_congr rfl fun w _ => if_pos (hgood w)]
    refine ennreal_collect _ _ _ _ _ (fun w => zpow_nonneg (Nat.cast_nonneg _) _)
      (fun w => Real.rpow_nonneg (Nat.cast_nonneg _) _) (fun w _ => ?_) c _ hc _ _
    exact localTerm_diag (qV E w) (hq w) hmn _ x _ (by push_cast; ring) (l.1 w) (hgood w).1 (hgood w).2
  · rw [e2, e3, hdet, GlobalTheory.CellDec.dinv, Finsupp.prod, Finset.prod_congr rfl fun w _ => if_pos (hgood w)]
    refine ennreal_collect _ _ _ _ _ (fun w => zpow_nonneg (Nat.cast_nonneg _) _)
      (fun w => Real.rpow_nonneg (Nat.cast_nonneg _) _) (fun w _ => ?_) c _ hc _ _
    have := localTerm_diag (qV E w) (hq w) le_rfl (fun i => (β w i : ℂ)) x x (by ring) (l.1 w) (hgood w).1 (hgood w).2
    rw [padNat_self] at this
    rw [padNat_self]
    exact this
