import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolume
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualHaarMeasureInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalComponentsNontrivialAdelicCharacterStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem selfDual_matrix_unique_of_equiv {R P ι : Type} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    [Fintype P] [Fintype ι] [DecidableEq ι] (a : R ≃+ (P → ℝ)) (ha : Continuous a)
    (ha' : Continuous a.symm) (χ : R → ℂ) (hc : Continuous χ) (h1 : ∀ x, ‖χ x‖ = 1)
    (hadd : ∀ x y, χ (x + y) = χ x * χ y) (hnd : ∀ x, (∀ y, χ (x * y) = 1) → x = 0)
    (AR : Matrix ι ι R) (hAR : ARᵀ = AR) (hu : IsUnit AR.det) {μ ν : Measure (ι → R)}
    (hμ : SelfDual μ (fun x y => χ (x ⬝ᵥ (AR *ᵥ y))))
    (hν : SelfDual ν (fun x y => χ (x ⬝ᵥ (AR *ᵥ y)))) : μ = ν := by
  obtain ⟨L₀, hL₀c, hL₀a, hL₀⟩ := GlobalTheory.GaugeEx.SdInf.exists_log_char
    (fun u => χ (a.symm u)) (hc.comp ha') (fun u => h1 _) (fun u v => by
      rw [map_add, hadd])
  let L : R → ℝ := fun x => L₀ (a x)
  have hLc : Continuous L := hL₀c.comp ha
  have hLa : ∀ x y, L (x + y) = L x + L y := fun x y => by simp only [L, map_add, hL₀a]
  have hL : ∀ x, χ x = Complex.exp (2 * Real.pi * Complex.I * ((L x : ℝ) : ℂ)) :=
    fun x => by simpa using hL₀ (a x)
  let e : (ι → R) ≃+ (ι → P → ℝ) := AddEquiv.piCongrRight fun _ => a
  have hec : Continuous e := by
    show Continuous fun (x : ι → R) i => a (x i)
    fun_prop
  have hec' : Continuous e.symm := by
    show Continuous fun (x : ι → P → ℝ) i => a.symm (x i)
    fun_prop
  have key := GlobalTheory.GaugeEx.SdInf.existsUnique_of_equiv e hec hec'
    (fun x y => L (x ⬝ᵥ (AR *ᵥ y)))
    (fun x x' y => by rw [add_dotProduct, hLa])
    (fun x y => by
      have : x ⬝ᵥ (AR *ᵥ y) = y ⬝ᵥ (AR *ᵥ x) := by
        rw [Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, hAR]
      rw [this])
    (fun y => hLc.comp (by
      have : Continuous fun x : ι → R => ∑ i, x i * (AR *ᵥ y) i :=
        continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const
      exact this))
    (fun x h => by
      funext i
      refine hnd _ fun t => ?_
      have h0 := h (AR⁻¹ *ᵥ Pi.single i t)
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec,
        dotProduct_single] at h0
      rw [hL, h0]
      simp)
  have hfun : (fun x y : ι → R => χ (x ⬝ᵥ (AR *ᵥ y))) =
      fun x y => Complex.exp (2 * Real.pi * Complex.I * ((L (x ⬝ᵥ (AR *ᵥ y)) : ℝ) : ℂ)) := by
    funext x y
    exact hL _
  rw [hfun] at hμ hν
  exact key.unique hμ hν

theorem selfDual_rationalForm_Ainf_unique : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ k : Measure (Ainf F), SelfDual k (fun s t => psiInf F ψ (s * t)) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.IsSymm → A.det ≠ 0 → ∀ μ ν : Measure (ι → Ainf F), SelfDual μ (fun x y => psiInf F ψ (x ⬝ᵥ (A.map (algebraMap F (Ainf F)) *ᵥ y))) → SelfDual ν (fun x y => psiInf F ψ (x ⬝ᵥ (A.map (algebraMap F (Ainf F)) *ᵥ y))) → μ = ν := by
  intro F _ _ hF ψ hψ _ _ ι _ _ A hA hdet μ ν hμ hν
  haveI : IsTotallyReal F := hF
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hF
  haveI := h1
  haveI := h3
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have hnd : ∀ x : Ainf F, (∀ y, psiInf F ψ (x * y) = 1) → x = 0 := (GlobalTheory.T.localComponents_nontrivial_adelic_character F ψ hψ).2.2
  obtain ⟨a, ha, ha'⟩ := GlobalTheory.GaugeEx.SdInf.exists_equiv_Ainf F
  have hpc : Continuous (psiInf F ψ) := hψ.1.comp (continuous_id.prodMk continuous_const)
  have hadd : ∀ x y, psiInf F ψ (x + y) = psiInf F ψ x * psiInf F ψ y := fun x y => by
    simp only [psiInf, map_add, ← AddChar.map_add_eq_mul]
    congr 1
    exact Prod.ext rfl (add_zero _).symm
  have hAR : (A.map (algebraMap F (Ainf F)))ᵀ = A.map (algebraMap F (Ainf F)) := by
    rw [← Matrix.transpose_map, hA.eq]
  have hu : IsUnit (A.map (algebraMap F (Ainf F))).det := by
    have : (A.map (algebraMap F (Ainf F))).det = algebraMap F (Ainf F) A.det :=
      ((algebraMap F (Ainf F)).map_det A).symm
    rw [this]
    exact (Ne.isUnit hdet).map _
  exact selfDual_matrix_unique_of_equiv a ha ha' (psiInf F ψ) hpc (fun u => hψ.2.1 _) hadd hnd
    _ hAR hu hμ hν

end GlobalTheory.CompanionTheory.SW
