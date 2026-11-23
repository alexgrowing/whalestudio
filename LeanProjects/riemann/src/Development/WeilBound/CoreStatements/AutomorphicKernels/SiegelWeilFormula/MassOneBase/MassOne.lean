import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.Pieces
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.MassOneCounts.DensExact
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.MassOneCounts.CountGood
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EtaleAwayQuotientEqLocalization
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IntegralAlmostAllPlaces

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.BaseOne

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.SW PositivityTheory.SiegelWeilFormula.Densx
  GlobalTheory.CompanionTheory.SW.LGPrim
open scoped TensorProduct ENNReal NNReal Matrix

theorem eR_eq (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    eR E v = 1 ∨ eR E v = -1 := by
  unfold eR PositivityTheory.SiegelWeilFormula.Gen.eSp
  split_ifs <;> simp

theorem massOne : MassOne := by
  intro F E _ _ _ _ _ σ hCM J hJ d b
  classical
  obtain ⟨B, hBs, hBd, hBt⟩ := GlobalTheory.CompanionTheory.SW.trace_form_coords F E σ hCM 1 J hJ d b
  obtain ⟨-, hun⟩ := GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ hCM d b
  have hd : d = 2 := by
    have h1 := Module.finrank_eq_card_basis b
    rw [hCM.2.2.1, Fintype.card_fin] at h1
    exact h1.symm
  have hent : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j, algebraMap F (Fv F v) (B i j) ∈ v.adicCompletionIntegers F := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    by_cases h0 : B i j = 0
    · refine Filter.Eventually.of_forall fun v => ?_
      rw [h0, map_zero]
      exact zero_mem _
    · refine (hun _ h0).mono fun v hv => ?_
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact hv.le
  filter_upwards [hun 2 two_ne_zero, hun _ hBd, hent, PositivityTheory.SiegelWeilFormula.MOne.count_good F E σ hCM J hJ d b B hBt]
    with v hv2 hvd hve hcnt lam hlam m hm s hsu
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hsu
    exact zero_ne_one hsu
  have hv2' : Valued.v (2 : Fv F v) = 1 := by rwa [map_ofNat] at hv2
  have hdet : Valued.v (B.map (algebraMap F (Fv F v))).det = 1 := by
    have h1 := (algebraMap F (Fv F v)).map_det B
    rw [h1] at hvd
    exact hvd
  let BO : Matrix (Fin 1 × Fin d) (Fin 1 × Fin d) (v.adicCompletionIntegers F) :=
    Matrix.of fun i j => ⟨algebraMap F (Fv F v) (B i j), hve i j⟩
  have hBO : BO.map phi = B.map (algebraMap F (Fv F v)) := by
    ext i j
    rfl
  have hs : s ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hsu.le
  let s' : v.adicCompletionIntegers F := ⟨s, hs⟩
  have hN := hcnt BO hBO s' hsu
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = Nat.card {y : Fin 1 × Fin d → IsLocalRing.ResidueField (v.adicCompletionIntegers F) //
      (2 : IsLocalRing.ResidueField (v.adicCompletionIntegers F))⁻¹ *
        (y ⬝ᵥ ((BO.map (IsLocalRing.residue (v.adicCompletionIntegers F))) *ᵥ y)) =
        IsLocalRing.residue (v.adicCompletionIntegers F) s'} := ⟨_, rfl⟩
  rw [← hNdef] at hN
  have hq1 : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0 := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := by omega
    exact_mod_cast this
  have hcardι : Fintype.card (Fin 1 × Fin d) - 1 = 1 := by simp [hd]
  let D : ℝ≥0 := (N : ℝ≥0) * (Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹
  have hD : ∀ A : Set (Fv F v), MeasurableSet A → A ⊆ {z | Valued.v (z - s) < Valued.v s} →
      (Measure.pi fun _ : Fin 1 × Fin d => lam)
        {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
          (2 : Fv F v)⁻¹ * (x ⬝ᵥ ((B.map (algebraMap F (Fv F v))) *ᵥ x)) ∈ A} = (D : ℝ≥0∞) * lam A := by
    intro A hA hAs
    have h := PositivityTheory.SiegelWeilFormula.MOne.dens_exact lam hlam hv2' (Fin 1 × Fin d) BO (by rw [hBO]; exact hBs.map _)
      (by rw [hBO]; exact hdet) s' hsu A hA hAs
    rw [hBO, hcardι, ← hNdef] at h
    rw [h]
    congr 1
    simp only [D, ENNReal.coe_mul, ENNReal.coe_natCast, ENNReal.coe_inv hq0, pow_one]
  have hloc := GlobalTheory.CompanionTheory.SW.LocGood.local_mass σ hCM 1 J hJ d b v (B.map (algebraMap F (Fv F v)))
    (fun x y => hBt (Fv F v) x y) lam hlam m hm s hs0 D hD
  have hq2 : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast hq1
  have hx : 0 < 1 - eR E v / (Ideal.absNorm v.asIdeal : ℝ) := by
    have hqp : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by linarith
    rcases eR_eq F E v with he | he <;> rw [he]
    · rw [sub_pos, div_lt_one hqp]
      linarith
    · have : 0 < 1 / (Ideal.absNorm v.asIdeal : ℝ) := by positivity
      rw [neg_div, sub_neg_eq_add]
      linarith [this, one_div (Ideal.absNorm v.asIdeal : ℝ)]
  have hDr : (D : ℝ) = 1 - eR E v / (Ideal.absNorm v.asIdeal : ℝ) := by
    have hqp : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by positivity
    simp only [D, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_inv]
    rw [hN]
    field_simp
  have hne : m (hermScal (Fv F v) σ s) (latV b v) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hloc
    have : (D : ℝ) = 0 := hloc.symm
    rw [hDr] at this
    linarith
  have hmD : m (hermScal (Fv F v) σ s) (latV b v) = (D : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_toReal hne, hloc, ENNReal.ofReal_coe_nnreal]
  rw [hmD, ← ENNReal.coe_mul, ENNReal.coe_eq_one]
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_one, cfac, Real.coe_toNNReal _ (inv_nonneg.2 hx.le), hDr,
    inv_mul_cancel₀ hx.ne']

end PositivityTheory.SiegelWeilFormula.BaseOne

end
