import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLeftInvariantOfIsAutForm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenLevel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchLieDerivativeExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDiff

noncomputable section

open NumberField MeasureTheory Filter Topology Set
open GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

namespace PositivityTheory.Rg.Rs.JNiceAut

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

omit [IsTotallyComplex E] in

theorem diffSum_one (ψ : AdelicGLn.AdelicGL E N → ℂ) (x : AdelicGLn.AdelicGL E N) (Y : ArchMatrix E N) :
    diffSum ψ x (fun _ : Fin 1 => Y) = ψ (x * CuspidalSpectrum.archExp Y) - ψ x := by
  rw [diffSum_eq_altSum, altSum_succ, altSum_zero]
  simp [archExp_zero]

theorem lip_of_autForm (φ : Sm E N) (hφ : IsAutForm φ) (R : ℝ) :
    ∃ (Q₀ : Set (AdelicGLn.AdelicGL E N)) (C : ℝ), IsCompact Q₀ ∧ 0 ≤ C ∧
      ∀ g (Y : ArchMatrix E N) (M : ℝ), Y * Y = 0 → ‖Y‖ ≤ R → (∀ q ∈ Q₀, ‖φ.1 (g * q)‖ ≤ M) →
        ‖φ.1 (g * CuspidalSpectrum.archExp Y) - φ.1 g‖ ≤ C * ‖Y‖ * M := by
  have hs := GlobalTheory.CompanionTheory.ArchSmooth.sm_mem_archSmooth E N φ
  let _ : MeasurableSpace (archGroup E N) := borel _
  have _ : BorelSpace (archGroup E N) := ⟨rfl⟩
  have hD := fun J : Fin 1 → Fin (archDim E N) =>
    GlobalTheory.CompanionTheory.HCRep.uJ_eq_conv E N φ hs hφ Measure.haar 1 J
  choose D hDc hDs hDeq using hD
  obtain ⟨c, hc0, hc⟩ := exists_abs_archBasis_repr_le (K := E) (n := N)
  set T : Set (archGroup E N) := ⋃ J, tsupport (D J) with hTdef
  have hT : IsCompact T := isCompact_iUnion fun J => (hDs J).isCompact
  set S : Set (ArchMatrix E N) := Metric.closedBall 0 (max R 0) with hSdef
  have hS : IsCompact S := isCompact_closedBall _ _
  set f : ArchMatrix E N × archGroup E N → AdelicGLn.AdelicGL E N :=
    fun p => CuspidalSpectrum.archExp p.1 * infEmb E N p.2 with hfdef
  have hf : Continuous f :=
    (continuous_archExp.comp continuous_fst).mul (continuous_infEmb.comp continuous_snd)
  set I : ℝ := ∑ J, ∫ y, ‖D J y‖ ∂(Measure.haar : Measure (archGroup E N)) with hIdef
  have hI0 : 0 ≤ I := Finset.sum_nonneg fun J _ => integral_nonneg fun _ => norm_nonneg _
  refine ⟨insert 1 (f '' (S ×ˢ T)), (archDim E N : ℝ) * c * I, ((hS.prod hT).image hf).insert 1,
    by positivity, fun g Y M hYY hYR hM => ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (by simpa using hM 1 (mem_insert _ _))
  have hB0 : 0 ≤ M * I := mul_nonneg hM0 hI0
  have h := norm_diffSum_le hc0 hc 1 ⟨φ.1, hs⟩ g (fun _ : Fin 1 => Y) (fun _ _ => Commute.refl Y) (M * I) hB0
    (fun J t ht => by
      set Z : ArchMatrix E N := ∑ i, t i • (fun _ : Fin 1 => Y) i with hZdef
      have hZ : Z ∈ S := by
        rw [hSdef, mem_closedBall_zero_iff, hZdef, Fin.sum_univ_one, norm_smul,
          Real.norm_of_nonneg (ht 0).1]
        calc t 0 * ‖Y‖ ≤ 1 * max R 0 :=
              mul_le_mul (ht 0).2 (hYR.trans (le_max_left _ _)) (norm_nonneg _) zero_le_one
          _ = max R 0 := one_mul _
      rw [hDeq J]
      have hb : ∀ y, ‖φ.1 (g * CuspidalSpectrum.archExp Z * infEmb E N y) * D J y‖ ≤ M * ‖D J y‖ := by
        intro y
        rw [norm_mul]
        by_cases hy : y ∈ tsupport (D J)
        · refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          have hq : CuspidalSpectrum.archExp Z * infEmb E N y ∈ insert 1 (f '' (S ×ˢ T)) :=
            mem_insert_of_mem _ ⟨(Z, y), ⟨hZ, mem_iUnion.2 ⟨J, hy⟩⟩, rfl⟩
          simpa only [mul_assoc] using hM _ hq
        · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero, mul_zero, mul_zero]
      have hint : Integrable (fun y => ‖D J y‖) (Measure.haar : Measure (archGroup E N)) :=
        (hDc J).norm.integrable_of_hasCompactSupport (hDs J).norm
      calc ‖∫ y, φ.1 (g * CuspidalSpectrum.archExp Z * infEmb E N y) * D J y ∂(Measure.haar : Measure (archGroup E N))‖
          ≤ ∫ y, M * ‖D J y‖ ∂(Measure.haar : Measure (archGroup E N)) :=
            norm_integral_le_of_norm_le (hint.const_mul M) (Eventually.of_forall hb)
        _ = M * ∫ y, ‖D J y‖ ∂(Measure.haar : Measure (archGroup E N)) := integral_const_mul _ _
        _ ≤ M * I := mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (f := fun J => ∫ y, ‖D J y‖ ∂(Measure.haar : Measure (archGroup E N)))
              (fun J _ => integral_nonneg fun _ => norm_nonneg _) (Finset.mem_univ J)) hM0)
  rw [diffSum_one] at h
  refine h.trans (le_of_eq ?_)
  rw [Fin.prod_univ_one, pow_one]
  ring

end PositivityTheory.Rg.Rs.JNiceAut

namespace PositivityTheory.Rg.Rs

theorem niceAut_holds : NiceAut := by
  intro E _ _ _ N φ hφ hcen
  exact { cont := ContAut.continuous_of_isOpen_stab E N φ hφ.level
          left := GlobalTheory.CompanionTheory.LeftInv.isLeftInvariant_of_isAutForm E N φ hφ
          centre := hcen
          level := GlobalTheory.CompanionTheory.AutLevel.exists_open_level E N φ hφ
          lip := fun R => JNiceAut.lip_of_autForm φ hφ R }

end PositivityTheory.Rg.Rs

end
