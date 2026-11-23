import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLeftInvariantOfIsAutForm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAddHaarMeasureUnipMeasure
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.Reduction

namespace PositivityTheory.Rg.Rs.JDict

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem tor_const (N : ℕ) (t : ℝ) : An.tor E (fun _ : Fin N => t) = splitCentre E N t :=
  (GlobalTheory.CuspBoundSiegel.diagUnits_posIdele N (Real.exp_pos t)).trans (by rw [Real.log_exp])

theorem aT_eq (N r : ℕ) (t : ℝ) : aT E N r t = An.aR E N r t := by
  have e : An.aR E N r t = diagUnits N (fun i : Fin N =>
      infId E (expU fun _ : InfinitePlace E => (((if (i : ℕ) < r then t else 0 : ℝ)) : ℂ))) := by
    show diagUnits N (fun i : Fin N => posIdele (K := E) (Real.exp (if (i : ℕ) < r then t else 0)) (Real.exp_pos _)) = _
    congr 1
    funext i
    exact GlobalTheory.CuspBoundSiegel.posIdele_exp _
  rw [e]
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [coe_diagUnits, Matrix.diagonal_apply]
  change (1 : Matrix (Fin N) (Fin N) (Ad E)) i j - sInf E ((1 : Matrix (Fin N) (Fin N) (Cinf E)) i j) +
    sInf E ((aInf E N r t : Matrix (Fin N) (Fin N) (Cinf E)) i j) = _
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, Matrix.one_apply_eq, Matrix.one_apply_eq]
    change _ = 1 - sInf E 1 + sInf E (fun _ => Complex.exp _)
    congr 2
    funext w
    rw [show (aInf E N r t : Matrix (Fin N) (Fin N) (Cinf E)) = Matrix.diagonal (fun (k : Fin N) (_ : InfinitePlace E) =>
      Complex.exp (if (k : ℕ) < r then (t : ℂ) else 0)) from rfl, Matrix.diagonal_apply_eq]
    split_ifs <;> simp
  · rw [if_neg hij, Matrix.one_apply_ne hij, Matrix.one_apply_ne hij]
    rw [show (aInf E N r t : Matrix (Fin N) (Fin N) (Cinf E)) = Matrix.diagonal (fun (k : Fin N) (_ : InfinitePlace E) =>
      Complex.exp (if (k : ℕ) < r then (t : ℂ) else 0)) from rfl, Matrix.diagonal_apply_ne _ hij, map_zero, sub_zero, add_zero]

theorem lat_eq (N : ℕ) : latticeGL E N = An.lat E N := by
  unfold latticeGL An.lat
  rw [tor_const]
  rfl

section CT

variable (E) (N r : ℕ)
omit [IsTotallyComplex E]

theorem pi_eq_borel : (MeasurableSpace.pi : MeasurableSpace (BlockIx N r → Ad E)) = borel _ := by
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  exact BorelSpace.measurable_eq

theorem vol_pos : 0 < (unipMeasure E N r).real (unipFundamentalDomain E N r) := by
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := E) (n := N) (r := r)
  have htop : unipMeasure E N r (unipFundamentalDomain E N r) ≠ ⊤ :=
    ((measure_mono hDC).trans_lt hC.measure_lt_top).ne
  have h0 : unipMeasure E N r (unipFundamentalDomain E N r) ≠ 0 :=
    isAddFundamentalDomain_unipFundamentalDomain.measure_ne_zero (NeZero.ne _)
  exact ENNReal.toReal_pos h0 htop

theorem ct_eq_smul [m : MeasurableSpace (BlockIx N r → Ad E)] [hb : BorelSpace (BlockIx N r → Ad E)]
    (μ : Measure (BlockIx N r → Ad E)) (𝓕 : Set (BlockIx N r → Ad E)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratN E N r) 𝓕 μ) :
    ∃ c : ℝ, 0 < c ∧ ∀ φ : GA E N → ℂ, IsLeftInvariant φ → ∀ g,
      ∫ x in 𝓕, φ (unip x * g) ∂μ = (c : ℂ) * constantTerm r φ g := by
  have h : m = MeasurableSpace.pi := hb.measurable_eq.trans (pi_eq_borel E N r).symm
  subst h
  have e : μ = Measure.addHaarScalarFactor μ (unipMeasure E N r) • unipMeasure E N r :=
    Measure.isAddLeftInvariant_eq_smul μ (unipMeasure E N r)
  have hc : 0 < Measure.addHaarScalarFactor μ (unipMeasure E N r) :=
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ (unipMeasure E N r)
  refine ⟨Measure.addHaarScalarFactor μ (unipMeasure E N r), by exact_mod_cast hc, fun φ hφ g => ?_⟩
  have hac : unipMeasure E N r ≪ μ := by
    rw [e]
    exact Measure.absolutelyContinuous_smul (by exact_mod_cast hc.ne')
  have h𝓕ν : IsAddFundamentalDomain (unipLattice E N r) 𝓕 (unipMeasure E N r) := h𝓕.mono hac
  rw [constantTerm_eq_setIntegral hφ h𝓕ν g]
  conv_lhs => rw [e]
  rw [Measure.restrict_smul, integral_smul_nnreal_measure]
  simp only [GlobalTheory.CompanionTheory.CuspBridge.unipGL_eq_unip]
  rw [NNReal.smul_def, Complex.real_smul]

theorem exists_normed [m : MeasurableSpace (BlockIx N r → Ad E)] [hb : BorelSpace (BlockIx N r → Ad E)] :
    ∃ μ : Measure (BlockIx N r → Ad E), μ.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratN E N r) (unipFundamentalDomain E N r) μ ∧
      ∀ f : (BlockIx N r → Ad E) → ℂ, ∫ x in unipFundamentalDomain E N r, f x ∂μ =
        (((unipMeasure E N r).real (unipFundamentalDomain E N r) : ℝ) : ℂ)⁻¹ *
          ∫ x in unipFundamentalDomain E N r, f x ∂unipMeasure E N r := by
  have h : m = MeasurableSpace.pi := hb.measurable_eq.trans (pi_eq_borel E N r).symm
  subst h
  have hpos := vol_pos E N r
  set a := unipMeasure E N r (unipFundamentalDomain E N r) with ha
  have h0 : a ≠ 0 := fun h => by simp [Measure.real, ← ha, h] at hpos
  have htop : a ≠ ⊤ := fun h => by simp [Measure.real, ← ha, h] at hpos
  refine ⟨a⁻¹ • unipMeasure E N r, Measure.IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 htop) (ENNReal.inv_ne_top.2 h0),
    isAddFundamentalDomain_unipFundamentalDomain.mono Measure.smul_absolutelyContinuous, fun f => ?_⟩
  rw [Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_inv, Complex.real_smul, Complex.ofReal_inv]
  rfl

end CT

end PositivityTheory.Rg.Rs.JDict

namespace PositivityTheory.Rg.Rs

open JDict in
theorem dict_holds : Dict := by
  intro E _ _ _ N
  refine ⟨fun r t => aT_eq N r t, fun t => (tor_const N t).symm, lat_eq N, ?_⟩
  intro φ hφ r _ _
  have hL := GlobalTheory.CompanionTheory.LeftInv.isLeftInvariant_of_isAutForm E N φ hφ
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  have : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨μ, hμ, hD, hint⟩ := exists_normed E N r
    refine ⟨μ, unipFundamentalDomain E N r, hμ, hD, ?_⟩
    funext g
    show An.ctn r φ.1 g = ∫ x in unipFundamentalDomain E N r, φ.1 (unip x * g) ∂μ
    rw [hint]
    simp only [An.ctn, constantTerm, GlobalTheory.CompanionTheory.CuspBridge.unipGL_eq_unip]
  · rintro F ⟨μ, 𝓕, hμ, h𝓕, rfl⟩
    obtain ⟨c, hc, hct⟩ := ct_eq_smul E N r μ 𝓕 hμ h𝓕
    have hv := vol_pos E N r
    refine ⟨(c : ℂ) * (((unipMeasure E N r).real (unipFundamentalDomain E N r) : ℝ) : ℂ), ?_, ?_⟩
    · exact mul_ne_zero (by exact_mod_cast hc.ne') (by exact_mod_cast hv.ne')
    · funext g
      show ∫ x in 𝓕, φ.1 (unip x * g) ∂μ = _
      rw [hct φ.1 hL g]
      simp only [An.ctn]
      have : (((unipMeasure E N r).real (unipFundamentalDomain E N r) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
      field_simp

end PositivityTheory.Rg.Rs

end
