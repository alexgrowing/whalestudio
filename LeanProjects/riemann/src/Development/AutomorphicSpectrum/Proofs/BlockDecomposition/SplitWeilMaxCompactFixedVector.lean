import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.REALTH
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableIntIndMul

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th ComplexConjugate
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.SphTheta GlobalTheory.CompanionTheory.SphTheta.SplitRW

noncomputable section

namespace GlobalTheory.CompanionTheory.SphTheta.SplitRWK

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {χ : AddChar F Circle}

omit [MeasurableSpace F] [BorelSpace F] in

theorem indicator_eq_phiS :
    Set.indicator {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} 1 = (phiS : F × F → ℂ) := by
  funext z
  by_cases h1 : z.1 ∈ 𝒪[F]
  · by_cases h2 : z.2 ∈ 𝒪[F]
    · rw [Set.indicator_of_mem (show z ∈ {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} from ⟨h1, h2⟩),
        phiS, intInd_of_mem h1, intInd_of_mem h2]
      simp
    · rw [Set.indicator_of_notMem (show z ∉ {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} from fun h => h2 h.2),
        phiS, intInd_of_notMem h2]
      simp
  · rw [Set.indicator_of_notMem (show z ∉ {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} from fun h => h1 h.1),
      phiS, intInd_of_notMem h1]
    simp

omit [MeasurableSpace F] [BorelSpace F] in

theorem chi_of_mem (hχ : IsStd χ) {x : F} (hx : x ∈ 𝒪[F]) : χ x = 1 := by
  have h := isTrivialOn_addCharConductor hχ.1 hχ.2.1
  rw [hχ.2.2] at h
  exact h x (mem_valBall_zero_iff.2 hx)

omit [MeasurableSpace F] [BorelSpace F] in

theorem chi_mul_phiS (hχ : IsStd χ) {t : F} (ht : t ∈ 𝒪[F]) (z : F × F) :
    (χ (t * (z.1 * z.2)) : ℂ) * phiS z = phiS z := by
  by_cases h1 : z.1 ∈ 𝒪[F]
  · by_cases h2 : z.2 ∈ 𝒪[F]
    · rw [chi_of_mem hχ (mul_mem ht (mul_mem h1 h2))]
      simp
    · simp [phiS, intInd_of_notMem h2]
  · simp [phiS, intInd_of_notMem h1]

omit [MeasurableSpace F] [BorelSpace F] in

theorem modulus_unit {u v : F} (hu : u ∈ 𝒪[F]) (hv : v ∈ 𝒪[F]) (huv : u * v = 1) : modulus u = 1 := by
  have h1 := modulus_le_one_iff.2 hu
  have h2 := modulus_le_one_iff.2 hv
  have h3 : modulus u * modulus v = 1 := by rw [← modulus_mul, huv, modulus_one]
  refine le_antisymm h1 ?_
  calc (1 : _) = modulus u * modulus v := h3.symm
    _ ≤ modulus u * 1 := by gcongr
    _ = modulus u := mul_one _

omit [MeasurableSpace F] [BorelSpace F] in

theorem intInd_unit_mul {u v : F} (hu : u ∈ 𝒪[F]) (hv : v ∈ 𝒪[F]) (huv : u * v = 1) (x : F) :
    intInd (u * x) = intInd x := by
  by_cases hx : x ∈ 𝒪[F]
  · rw [intInd_of_mem hx, intInd_of_mem (mul_mem hu hx)]
  · rw [intInd_of_notMem hx, intInd_of_notMem fun h => hx ?_]
    have := mul_mem hv h
    rwa [show v * (u * x) = x by rw [← mul_assoc, mul_comm v u, huv, one_mul]] at this

omit [MeasurableSpace F] [BorelSpace F] in
theorem phiS_unit_mul {u v : F} (hu : u ∈ 𝒪[F]) (hv : v ∈ 𝒪[F]) (huv : u * v = 1) (z : F × F) :
    phiS (algebraMap F (F × F) u * z) = phiS z := by
  simp only [phiS, Prod.algebraMap_apply, Prod.fst_mul, Prod.snd_mul, Algebra.algebraMap_self, RingHom.id_apply]
  rw [intInd_unit_mul hu hv huv, intInd_unit_mul hu hv huv]

theorem rW_gen (hχ : IsStd χ) {a b c d : F} (hc : c ≠ 0) (z : F × F) :
    Ad3.K.GL2LocalData.rW χ Ad3.K.GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1 a b c d phiS z =
      (((modulus c : ℝ)⁻¹ : ℝ) : ℂ) * (χ (a * (z.1 * z.2) / c) : ℂ) * GlobalTheory.CompanionTheory.SphTheta.SplitRW.J χ (d / c) (z.2 / c) (z.1 / c) := by
  rw [Ad3.K.GL2LocalData.rW, if_neg hc, nsg_pair (neg_ne_zero.2 hc), GlobalTheory.CompanionTheory.GJOne.selfDualMeasure_eq_of_isStd hχ]
  set E : F × F → F := fun w => (a * (z.1 * z.2) + d * (w.1 * w.2) - (z.2 * w.1 + z.1 * w.2)) / c with hE
  have hEc : Continuous E := by
    simp only [hE]
    fun_prop
  have hKc : Continuous (fun w => χ (E w)) := hχ.1.comp hEc
  have hint : ∀ w : F × F, (χ ((a * Algebra.norm F z + d * Algebra.norm F w -
      Algebra.trace F (F × F) (Ad3.K.GL2LocalData.swapE z * w)) / c) : ℂ) * phiS w = (χ (E w) : ℂ) * phiS w := by
    intro w
    have : Ad3.K.GL2LocalData.swapE z = (z.2, z.1) := rfl
    rw [this, norm_pair, norm_pair, trace_pair]
    rfl
  simp only [hint]
  have hI : Integrable (fun w : F × F => (χ (E w) : ℂ) * phiS w)
      ((haarIntegers F).prod (haarIntegers F)) := by
    have h := integrable_kernel (D := (1 : F)) one_ne_zero hKc
    have e : ((1 : F), (1 : F)) = (1 : F × F) := rfl
    simpa only [e, mul_one] using h
  rw [integral_prod_symm _ hI]
  have hinner : ∀ q : F, ∫ p, (χ (E (p, q)) : ℂ) * phiS (p, q) ∂(haarIntegers F) =
      (χ (a * (z.1 * z.2) / c) : ℂ) *
        (intInd q * (χ (-(z.1 / c * q)) : ℂ) * intInd (d / c * q - z.2 / c)) := by
    intro q
    have ho := orth hχ ((d * q - z.2) / c)
    have : ∀ p : F, (χ (E (p, q)) : ℂ) * phiS (p, q) =
        ((χ (a * (z.1 * z.2) / c) : ℂ) * (χ (-(z.1 / c * q)) : ℂ) * intInd q) *
          (intInd p * (χ ((d * q - z.2) / c * p) : ℂ)) := by
      intro p
      have e : E (p, q) = a * (z.1 * z.2) / c + -(z.1 / c * q) + (d * q - z.2) / c * p := by
        simp only [hE]
        field_simp
        ring
      rw [e, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, Circle.coe_mul, Circle.coe_mul]
      simp only [phiS]
      ring
    simp only [this]
    rw [integral_const_mul, ho, show (d * q - z.2) / c = d / c * q - z.2 / c by ring]
    ring
  simp only [hinner]
  rw [integral_const_mul, GlobalTheory.CompanionTheory.SphTheta.SplitRW.J]
  simp only [one_mul]
  ring

theorem rW_fix (hχ : IsStd χ) {a b c d : F} (ha : a ∈ 𝒪[F]) (hb : b ∈ 𝒪[F]) (hc : c ∈ 𝒪[F])
    (hd : d ∈ 𝒪[F]) (hdet : a * d - b * c = 1) (z : F × F) :
    Ad3.K.GL2LocalData.rW χ Ad3.K.GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1 a b c d phiS z =
      phiS z := by
  by_cases hc0 : c = 0
  · subst hc0
    have had : a * d = 1 := by simpa using hdet
    have ha0 : a ≠ 0 := left_ne_zero_of_mul_eq_one had
    rw [Ad3.K.GL2LocalData.rW, if_pos rfl, nsg_pair ha0, modulus_unit ha hd had, norm_pair,
      phiS_unit_mul ha hd had]
    have := chi_mul_phiS hχ (mul_mem ha hb) z
    simpa using this
  rw [rW_gen hχ hc0]
  by_cases hδ : d / c ∈ 𝒪[F]
  · set v : F := a * (d / c) - b with hv
    have hvO : v ∈ 𝒪[F] := sub_mem (mul_mem ha hδ) hb
    have hcv : c * v = 1 := by
      rw [hv, ← hdet]
      field_simp
    have hvc : v = c⁻¹ := eq_inv_of_mul_eq_one_right hcv
    have hm : modulus c = 1 := modulus_unit hc hvO hcv
    have hvc' : v * c = 1 := by rw [mul_comm]; exact hcv
    rw [J_of_mem hχ hδ, hm]
    have e1 : z.2 / c = v * z.2 := by rw [hvc]; field_simp
    have e2 : z.1 / c = v * z.1 := by rw [hvc]; field_simp
    have e3 : a * (z.1 * z.2) / c = (a * v) * (z.1 * z.2) := by rw [hvc]; field_simp
    rw [e1, e2, e3, intInd_unit_mul hvO hc hvc', intInd_unit_mul hvO hc hvc']
    have := chi_mul_phiS hχ (mul_mem ha hvO) z
    simp only [phiS] at this ⊢
    simp only [NNReal.coe_one, inv_one, Complex.ofReal_one, one_mul]
    rw [mul_comm (intInd z.2)]
    exact this
  · obtain ⟨hδ0, hδi⟩ := inv_mem_of_notMem hδ
    have hd0 : d ≠ 0 := fun h => hδ0 (by rw [h, zero_div])
    set v : F := a - b * (d / c)⁻¹ with hv
    have hvO : v ∈ 𝒪[F] := sub_mem ha (mul_mem hb hδi)
    have hdv : d * v = 1 := by
      rw [hv, ← hdet]
      field_simp
    have hvd : v = d⁻¹ := eq_inv_of_mul_eq_one_right hdv
    have hm : modulus d = 1 := modulus_unit hd hvO hdv
    have hvd' : v * d = 1 := by rw [mul_comm]; exact hdv
    rw [J_of_notMem hχ hδ]
    have e1 : z.2 / c / (d / c) = v * z.2 := by rw [hvd]; field_simp
    have e2 : z.1 / c / (d / c) = v * z.1 := by rw [hvd]; field_simp
    have e3 : (((modulus c : ℝ)⁻¹ : ℝ) : ℂ) * (((modulus (d / c) : ℝ)⁻¹ : ℝ) : ℂ) = 1 := by
      have hcp : (modulus c : ℝ) ≠ 0 := by exact_mod_cast modulus_ne_zero hc0
      rw [div_eq_mul_inv, modulus_mul, modulus_inv, hm, ← Complex.ofReal_mul]
      push_cast
      field_simp
      simpa using hc0
    have e4 : a * (z.1 * z.2) / c + -(z.2 / c * (z.1 / c) / (d / c)) = (b * v) * (z.1 * z.2) := by
      rw [hvd]
      have hbc : a * d - 1 = b * c := by rw [← hdet]; ring
      have : a * (z.1 * z.2) / c + -(z.2 / c * (z.1 / c) / (d / c)) =
          (a * d - 1) * (z.1 * z.2) / (c * d) := by
        field_simp
        ring
      rw [this, hbc]
      field_simp
    rw [e1, e2, intInd_unit_mul hvO hd hvd', intInd_unit_mul hvO hd hvd']
    have hχ2 := chi_mul_phiS hχ (mul_mem hb hvO) z
    rw [← e4, AddChar.map_add_eq_mul, Circle.coe_mul] at hχ2
    simp only [phiS] at hχ2 ⊢
    calc _ = ((((modulus c : ℝ)⁻¹ : ℝ) : ℂ) * (((modulus (d / c) : ℝ)⁻¹ : ℝ) : ℂ)) *
          ((χ (a * (z.1 * z.2) / c) : ℂ) * (χ (-(z.2 / c * (z.1 / c) / (d / c))) : ℂ) *
            (intInd z.1 * intInd z.2)) := by ring
      _ = _ := by rw [e3, one_mul, hχ2]

theorem rwks : Ad3.K.GL2LocalData.SRep → Ad3.K.QuadraticBaseChangeGL3.Th.RWKS := by
  intro _ F _ _ _ _ _ _ _ χ hc h1 hcond k hdet hk
  have hχ : IsStd χ := ⟨hc, h1, hcond⟩
  rw [indicator_eq_phiS]
  funext z
  have hd : k 0 0 * k 1 1 - k 0 1 * k 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hdet
  exact rW_fix hχ (hk 0 0) (hk 0 1) (hk 1 0) (hk 1 1) hd z

end GlobalTheory.CompanionTheory.SphTheta.SplitRWK
