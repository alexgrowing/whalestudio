import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsMInfNhd
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LocalA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LocalB

noncomputable section

open Finset MeasureTheory Matrix Filter Topology Set
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}

theorem psiM_local (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) (V : Set (Matrix (Fin n) (Fin n) ℂ))
    (hV : IsOpen V) (hpos : posSet n ⊆ V) {g₀ : Matrix (Fin n) (Fin n) ℂ} (hg₀ : inUJ ε g₀) :
    ∃ (W : Set (Matrix (Fin n) (Fin n) ℂ)) (k₀ : KG ε), IsOpen W ∧ g₀ ∈ W ∧
      (∀ g ∈ W, IsUnit g ∧ g⁻¹ * toMK k₀ ∈ V) ∧
      ∀ g ∈ W, inUJ ε g → PsiM T μ g = T.op k₀ * psM T μ (g⁻¹ * toMK k₀) := by
  classical
  have hexp : Continuous (fun X : Matrix (Fin n) (Fin n) ℂ => NormedSpace.exp X) := by
    letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    first
      | (letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
         exact NormedSpace.exp_continuous)
      | (letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
         exact NormedSpace.exp_continuous)
      | (letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
         letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) :=
           { toAlgebra := by infer_instance
             norm_smul_le := fun q A => by
               rw [← Rat.cast_smul_eq_qsmul ℂ q A]
               refine (norm_smul_le _ _).trans (le_of_eq ?_)
               congr 1
               simp
               first
                 | rw [← Rat.norm_cast_real, Real.norm_eq_abs]
                 | rfl }
         first
           | exact @NormedSpace.exp_continuous _ _ _ (FiniteDimensional.complete ℂ _)
           | exact @NormedSpace.exp_continuous _ _ _ _ (FiniteDimensional.complete ℂ _))
  have hnegP : ∀ X : Matrix (Fin n) (Fin n) ℂ, inP ε X → inP ε (-X) := by
    intro X hX
    obtain ⟨h1, h2⟩ := hX
    have h1' : Xᴴ * Jm ε + Jm ε * X = 0 := h1
    show (-X)ᴴ * Jm ε + Jm ε * (-X) = 0 ∧ (-X) * Jm ε = -(Jm ε * -X)
    refine ⟨?_, ?_⟩
    · rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, h1', neg_zero]
    · rw [Matrix.neg_mul, Matrix.mul_neg, h2]
  have hKun : ∀ A : Matrix (Fin n) (Fin n) ℂ, A ∈ Kset ε → Aᴴ * A = 1 ∧ A * Aᴴ = 1 := by
    intro A hA
    have hA' : A ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ A * Jm ε = Jm ε * A := hA
    refine ⟨?_, ?_⟩
    · rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 hA'.1
    · rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.1 hA'.1
  have hKmul : ∀ A B : Matrix (Fin n) (Fin n) ℂ, A ∈ Kset ε → B ∈ Kset ε → Aᴴ * B ∈ Kset ε := by
    intro A B hA hB
    have hA' : A ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ A * Jm ε = Jm ε * A := hA
    have hB' : B ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ B * Jm ε = Jm ε * B := hB
    obtain ⟨hA1, hA2⟩ := hKun A hA
    obtain ⟨_, hB2⟩ := hKun B hB
    have hAJ : Aᴴ * Jm ε = Jm ε * Aᴴ := by
      calc Aᴴ * Jm ε = Aᴴ * Jm ε * (A * Aᴴ) := by rw [hA2, Matrix.mul_one]
        _ = Aᴴ * (Jm ε * A) * Aᴴ := by simp only [Matrix.mul_assoc]
        _ = Aᴴ * (A * Jm ε) * Aᴴ := by rw [hA'.2]
        _ = Jm ε * Aᴴ := by rw [← Matrix.mul_assoc, hA1, Matrix.one_mul]
    show Aᴴ * B ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ Aᴴ * B * Jm ε = Jm ε * (Aᴴ * B)
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc B, hB2,
        Matrix.one_mul, hA1]
    · rw [Matrix.mul_assoc, hB'.2, ← Matrix.mul_assoc, hAJ, Matrix.mul_assoc]
  obtain ⟨K, hK⟩ : ∃ K : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
      ∀ g, K g = g * NormedSpace.exp (-PolarDecomposition.polar_L g) :=
    ⟨fun g => g * NormedSpace.exp (-PolarDecomposition.polar_L g), fun _ => rfl⟩
  have hkmem : ∀ g, inUJ ε g → K g ∈ Kset ε := by
    intro g hg
    rw [hK]
    exact PolarDecomposition.polar_k_mem hg
  have hinv : ∀ g, inUJ ε g →
      g * (NormedSpace.exp (-PolarDecomposition.polar_L g) * (K g)ᴴ) = 1 := by
    intro g hg
    rw [← Matrix.mul_assoc, ← hK]
    exact (hKun _ (hkmem g hg)).2
  obtain ⟨U, hUo, hPU, hdiff, hU⟩ := psM_inf_nhd T μ hμ
  obtain ⟨ℓ, hℓ0, hℓev⟩ := lcA_exists_klog ε
  obtain ⟨k₀, hk₀⟩ := exists_toMK (hkmem g₀ hg₀)
  have hLt := (lcA_polarL_continuousOn ε g₀ hg₀).tendsto
  have hEt : Tendsto (fun g => NormedSpace.exp (-PolarDecomposition.polar_L g)) (𝓝[{g | inUJ ε g}] g₀)
      (𝓝 (NormedSpace.exp (-PolarDecomposition.polar_L g₀))) :=
    (hexp.tendsto _).comp hLt.neg
  have hKt : Tendsto K (𝓝[{g | inUJ ε g}] g₀) (𝓝 (K g₀)) := by
    have h : Tendsto (fun g => g * NormedSpace.exp (-PolarDecomposition.polar_L g)) (𝓝[{g | inUJ ε g}] g₀)
        (𝓝 (g₀ * NormedSpace.exp (-PolarDecomposition.polar_L g₀))) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).mul hEt
    have hKfun : K = fun g => g * NormedSpace.exp (-PolarDecomposition.polar_L g) := funext hK
    rw [hKfun]
    exact h
  have hFt : Tendsto (fun g => (K g)ᴴ * K g₀) (𝓝[{g | inUJ ε g}] g₀) (𝓝 1) := by
    have h : Tendsto (fun g => (K g)ᴴ * K g₀) (𝓝[{g | inUJ ε g}] g₀) (𝓝 ((K g₀)ᴴ * K g₀)) :=
      hKt.star.mul tendsto_const_nhds
    rwa [(hKun _ (hkmem g₀ hg₀)).1] at h
  have hℓt : Tendsto (fun g => ℓ ((K g)ᴴ * K g₀)) (𝓝[{g | inUJ ε g}] g₀) (𝓝 0) := hℓ0.comp hFt
  have hev1 := hFt.eventually hℓev
  have hcpt : ∀ᶠ p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ in
      𝓝 (NormedSpace.exp (-PolarDecomposition.polar_L g₀), (0 : Matrix (Fin n) (Fin n) ℂ)),
      ∀ t ∈ Icc (0 : ℝ) 1, p.1 * NormedSpace.exp ((t : ℂ) • p.2) ∈ U := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually ?_
    intro t _
    have hc : Continuous (fun z : (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) × ℝ =>
        z.1.1 * NormedSpace.exp ((z.2 : ℂ) • z.1.2)) :=
      continuous_fst.fst.matrix_mul
        (hexp.comp ((Complex.continuous_ofReal.comp continuous_snd).smul continuous_fst.snd))
    have hmem : NormedSpace.exp (-PolarDecomposition.polar_L g₀) *
        NormedSpace.exp ((t : ℂ) • (0 : Matrix (Fin n) (Fin n) ℂ)) ∈ U := by
      rw [smul_zero, NormedSpace.exp_zero, Matrix.mul_one]
      exact hPU (exp_noncompactPart_posDef (hnegP _ (PolarDecomposition.polar_L_inP hg₀)))
    exact hc.continuousAt.preimage_mem_nhds (hUo.mem_nhds hmem)
  have hPt : Tendsto (fun g => (NormedSpace.exp (-PolarDecomposition.polar_L g), ℓ ((K g)ᴴ * K g₀)))
      (𝓝[{g | inUJ ε g}] g₀)
      (𝓝 (NormedSpace.exp (-PolarDecomposition.polar_L g₀), (0 : Matrix (Fin n) (Fin n) ℂ))) := by
    first
      | exact hEt.prodMk_nhds hℓt
      | exact hEt.prod_mk_nhds hℓt
  have hev2 := hPt.eventually hcpt
  obtain ⟨O, hOo, hg₀O, hOsub⟩ := mem_nhdsWithin.1 (hev1.and hev2)
  have hdetO : IsOpen {g : Matrix (Fin n) (Fin n) ℂ | g.det ≠ 0} :=
    isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  have hinvc : ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => g⁻¹ * toMK k₀)
      {g : Matrix (Fin n) (Fin n) ℂ | g.det ≠ 0} := by
    intro g hg
    have hg' : g.det ≠ 0 := hg
    have h1 : ContinuousAt Inv.inv g := by
      refine continuousAt_matrix_inv g ?_
      first
        | (rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hg')
        | (simp only [show (Ring.inverse : ℂ → ℂ) = Inv.inv from funext Ring.inverse_eq_inv]
           exact continuousAt_inv₀ hg')
    exact (h1.mul continuousAt_const).continuousWithinAt
  have hO₂ : IsOpen ({g : Matrix (Fin n) (Fin n) ℂ | g.det ≠ 0} ∩
      (fun g : Matrix (Fin n) (Fin n) ℂ => g⁻¹ * toMK k₀) ⁻¹' V) :=
    hinvc.isOpen_inter_preimage hdetO hV
  have hinv0 := hinv g₀ hg₀
  have hdet0 : g₀.det ≠ 0 := (Matrix.isUnit_det_of_right_inverse hinv0).ne_zero
  have hV0 : g₀⁻¹ * toMK k₀ ∈ V := by
    rw [Matrix.inv_eq_right_inv hinv0, hk₀, Matrix.mul_assoc, (hKun _ (hkmem g₀ hg₀)).1,
      Matrix.mul_one]
    exact hpos (exp_noncompactPart_posDef (hnegP _ (PolarDecomposition.polar_L_inP hg₀)))
  refine ⟨O ∩ ({g : Matrix (Fin n) (Fin n) ℂ | g.det ≠ 0} ∩
      (fun g : Matrix (Fin n) (Fin n) ℂ => g⁻¹ * toMK k₀) ⁻¹' V), k₀, hOo.inter hO₂,
      ⟨hg₀O, hdet0, hV0⟩, ?_, ?_⟩
  · intro g hg
    have hgd : g.det ≠ 0 := hg.2.1
    exact ⟨(Matrix.isUnit_iff_isUnit_det g).2 (isUnit_iff_ne_zero.2 hgd), hg.2.2⟩
  · intro g hg hgS
    obtain ⟨hq1, hq2⟩ := hOsub ⟨hg.1, hgS⟩
    obtain ⟨hY, hYe⟩ := hq1 (hKmul _ _ (hkmem g hgS) (hkmem g₀ hg₀))
    obtain ⟨γ, -, hγ, hmul⟩ := exists_oneParam ε hY
    have hid : ∀ z ∈ U, fderiv ℂ (psM T μ) z (z * ℓ ((K g)ᴴ * K g₀)) =
        -(T.dτ (ℓ ((K g)ᴴ * K g₀)) * psM T μ z) :=
      fun z hz => (hU z hz _ ((inK_iff ε _).1 hY).2).1
    have hc := lcB_const T μ hUo hdiff hid hY γ hγ hmul
      (NormedSpace.exp (-PolarDecomposition.polar_L g)) hq2
    have hγ1 : toMK (γ 1) = (K g)ᴴ * K g₀ := by
      rw [hγ 1, Complex.ofReal_one, one_smul]
      exact hYe
    have hkA : toMK (k₀ * (γ 1)⁻¹) = K g := by
      rw [toMK_mul', toMK_inv, hγ1, hk₀, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, (hKun _ (hkmem g₀ hg₀)).2,
        Matrix.one_mul]
    have hg_eq : g = toMK (k₀ * (γ 1)⁻¹) * NormedSpace.exp (PolarDecomposition.polar_L g) := by
      rw [hkA, hK]
      exact PolarDecomposition.eq_mul_exp_neg_polar_L_mul_exp_polar_L
    have hgi : g⁻¹ * toMK k₀ =
        NormedSpace.exp (-PolarDecomposition.polar_L g) * NormedSpace.exp (ℓ ((K g)ᴴ * K g₀)) := by
      rw [Matrix.inv_eq_right_inv (hinv g hgS), hk₀, hYe, Matrix.mul_assoc]
    have hPsi : PsiM T μ g =
        T.op (k₀ * (γ 1)⁻¹) * psM T μ (NormedSpace.exp (PolarDecomposition.polar_L g)) := by
      rw [← psiM_kexp T μ _ (PolarDecomposition.polar_L_inP hgS), ← hg_eq]
    rw [hPsi, hgi, ← psM_exp_neg T μ (PolarDecomposition.polar_L_inP hgS), ← hc, ← mul_assoc,
      ← op_mul' T, inv_mul_cancel_right]

end ReciprocityTheory.ChartRestriction.DS.S7
