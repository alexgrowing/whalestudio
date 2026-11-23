import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.SWMeasCAll
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalQuadraticDensityNearOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IntegralAlmostAllPlaces
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.MassOneCounts.SolCountOneOne
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.MassOneCounts.FormRes
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.QuadAtOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedFiniteIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueRingStructureStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedFieldStructureStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerExistenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceDualAtPlaceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionTwoStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionThreeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionFourStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionFiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardUnimodularHermitianRepsLevelOneStatement

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.MOne

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology GlobalTheory.CompanionTheory.SW.LGPrim
  PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct ENNReal NNReal Matrix

section Helpers

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem alg_mem {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (h1 : (1 : Fv F v ⊗[F] E) ∈ Rv b v) (c : Fv F v) (hc : c ∈ v.adicCompletionIntegers F) :
    algebraMap (Fv F v) (Fv F v ⊗[F] E) c ∈ Rv b v := by
  simp only [Rv, Set.mem_ofPred_eq] at h1 ⊢
  intro k
  rw [Algebra.algebraMap_eq_smul_one, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_mem hc (h1 k)

theorem sigR_alg (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) :
    sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) c) = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := by
  simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, Algebra.algebraMap_self, RingHom.id_apply]

theorem sigR_inclR (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E) :
    sigR (Fv F v) σ (inclR (Fv F v) x) = inclR (Fv F v) (σ x) := by
  simp only [sigR, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

end Helpers

theorem count_good (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (J : Matrix (Fin 1) (Fin 1) E) (hJ : IsHermND σ J) (d : ℕ)
    (b : Module.Basis (Fin d) F E) (B : Matrix (Fin 1 × Fin d) (Fin 1 × Fin d) F)
    (hBt : ∀ (R : Type) [CommRing R] [Algebra F R] (x y : Fin 1 → R ⊗[F] E),
      Algebra.trace R (R ⊗[F] E) (hR R σ J x y) =
        (fun p : Fin 1 × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ
          (B.map (algebraMap F R) *ᵥ fun p : Fin 1 × Fin d => (Algebra.TensorProduct.basis R b).repr (y p.1) p.2)) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ BO : Matrix (Fin 1 × Fin d) (Fin 1 × Fin d) (v.adicCompletionIntegers F),
        BO.map phi = B.map (algebraMap F (Fv F v)) →
      ∀ s : v.adicCompletionIntegers F, Valued.v (s : Fv F v) = 1 →
        (Nat.card {y : Fin 1 × Fin d → IsLocalRing.ResidueField (v.adicCompletionIntegers F) //
            (2 : IsLocalRing.ResidueField (v.adicCompletionIntegers F))⁻¹ *
              (y ⬝ᵥ ((BO.map (IsLocalRing.residue (v.adicCompletionIntegers F))) *ᵥ y)) =
              IsLocalRing.residue (v.adicCompletionIntegers F) s} : ℝ) =
          (Ideal.absNorm v.asIdeal : ℝ) - Densx.eR E v := by
  classical
  have hFI := GlobalTheory.T.unramified_finite_integral F (basisSet σ b)
  obtain ⟨hintE, hun⟩ := GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ hCM d b
  have hj0 : J 0 0 ≠ 0 := by
    have h := hJ.2
    rwa [Matrix.det_unique] at h
  filter_upwards [hFI, hintE (J 0 0), hintE (J 0 0)⁻¹, hun 2 two_ne_zero] with v hInt hjI hjiI hv2 BO hBO s hsu
  have hv2' : Valued.v (2 : Fv F v) = 1 := by rwa [map_ofNat] at hv2
  obtain ⟨ϖ, hϖ0, hϖ1, hϖd, hϖc⟩ := GlobalTheory.T.uniformizer_existence F v
  obtain ⟨S, σS, hS, hsig⟩ := GlobalTheory.T.residue_ring_structure F E σ d b v hInt
  have hfix := GlobalTheory.T.fixed_field_structure F E σ hCM v
  have htr := GlobalTheory.T.trace_dual_at_place F E σ hCM d b v hInt
  have hR1 : (1 : Fv F v ⊗[F] E) ∈ Rv b v := by
    rw [← hS]
    exact S.one_mem
  have hRS : ∀ x, x ∈ Rv b v ↔ x ∈ S := fun x => by rw [← hS]; rfl
  have hRmul : ∀ x ∈ Rv b v, ∀ y ∈ Rv b v, x * y ∈ Rv b v := by
    intro x hx y hy
    rw [hRS] at hx hy ⊢
    exact S.mul_mem hx hy
  have hRsig : ∀ x ∈ Rv b v, sigR (Fv F v) σ x ∈ Rv b v := by
    intro x hx
    rw [hRS] at hx ⊢
    have h := (σS ⟨x, hx⟩).2
    rwa [hsig] at h
  have hϖS : algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ : Fv F v) ∈ S :=
    (hRS _).1 (alg_mem b v hR1 (ϖ : Fv F v) ϖ.2)
  let ε : ℤ := if IsField (Fv F v ⊗[F] E) then -1 else 1
  have hε : (ε : ℂ) = PositivityTheory.SiegelWeilFormula.Gen.eSp E v := by
    simp only [ε, PositivityTheory.SiegelWeilFormula.Gen.eSp]
    split_ifs <;> simp
  have hQ := PositivityTheory.SiegelWeilFormula.Gunr.quadAt_of GlobalTheory.T.unramified_quadratic_condition_one GlobalTheory.T.unramified_quadratic_condition_two GlobalTheory.T.unramified_quadratic_condition_three GlobalTheory.T.unramified_quadratic_condition_four GlobalTheory.T.unramified_quadratic_condition_five
    F E σ hCM d b v hInt S σS hS hsig ϖ hϖ0 hϖ1 hϖd hϖc hϖS ε hε
  let ϖS : S := ⟨_, hϖS⟩
  have hjS : inclR (Fv F v) (J 0 0) ∈ S := (hRS _).1 hjI
  have hjiS : inclR (Fv F v) (J 0 0)⁻¹ ∈ S := (hRS _).1 hjiI
  let jS : S := ⟨_, hjS⟩
  let jiS : S := ⟨_, hjiS⟩
  have hsinv : (s : Fv F v)⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hsu, inv_one]
  have htS : algebraMap (Fv F v) (Fv F v ⊗[F] E) (s : Fv F v) ∈ S := (hRS _).1 (alg_mem b v hR1 _ s.2)
  have htiS : algebraMap (Fv F v) (Fv F v ⊗[F] E) (s : Fv F v)⁻¹ ∈ S := (hRS _).1 (alg_mem b v hR1 _ hsinv)
  let tS : S := ⟨_, htS⟩
  let tiS : S := ⟨_, htiS⟩
  have hs0 : (s : Fv F v) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hsu
    exact zero_ne_one hsu
  have hUj : PositivityTheory.PfSWUS.Loc.IsUnimod σS (Matrix.of fun _ _ => jS : Matrix (Fin 1) (Fin 1) S) := by
    refine ⟨?_, ?_⟩
    · ext i k
      simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
      rw [hsig]
      simp only [jS]
      rw [sigR_inclR, hJ.1 0 0]
    · rw [Matrix.det_unique]
      refine ⟨⟨jS, jiS, ?_, ?_⟩, rfl⟩
      · apply Subtype.ext
        simp only [jS, jiS, MulMemClass.coe_mul, OneMemClass.coe_one]
        rw [← map_mul, mul_inv_cancel₀ hj0, map_one]
      · apply Subtype.ext
        simp only [jS, jiS, MulMemClass.coe_mul, OneMemClass.coe_one]
        rw [← map_mul, inv_mul_cancel₀ hj0, map_one]
  have hUt : PositivityTheory.PfSWUS.Loc.IsUnimod σS (Matrix.of fun _ _ => tS : Matrix (Fin 1) (Fin 1) S) := by
    refine ⟨?_, ?_⟩
    · ext i k
      simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
      rw [hsig]
      simp only [tS]
      rw [sigR_alg]
    · rw [Matrix.det_unique]
      refine ⟨⟨tS, tiS, ?_, ?_⟩, rfl⟩
      · apply Subtype.ext
        simp only [tS, tiS, MulMemClass.coe_mul, OneMemClass.coe_one]
        rw [← map_mul, mul_inv_cancel₀ hs0, map_one]
      · apply Subtype.ext
        simp only [tS, tiS, MulMemClass.coe_mul, OneMemClass.coe_one]
        rw [← map_mul, inv_mul_cancel₀ hs0, map_one]
  have hcount := GlobalTheory.T.card_unimodular_hermitian_reps_level_one S σS ϖS (Ideal.absNorm v.asIdeal) ε hQ 1 1 le_rfl _ _ hUj hUt
  rw [solCount_one_one] at hcount

  have hlev : ∀ x : S, x ∈ PositivityTheory.PfSWUS.Loc.lev ϖS 1 ↔
      ∃ y ∈ Rv b v, (x : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ * y := by
    intro x
    rw [PositivityTheory.PfSWUS.Loc.lev, pow_one, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, (hRS _).2 a.2, ?_⟩
      rw [← ha, MulMemClass.coe_mul, mul_comm]
    · rintro ⟨y, hy, he⟩
      refine ⟨⟨y, (hRS _).1 hy⟩, ?_⟩
      apply Subtype.ext
      rw [MulMemClass.coe_mul, he, mul_comm]
  let φ : (Fin 1 × Fin d → v.adicCompletionIntegers F) → S := fun w => ⟨zOf b v w, (hRS _).1 (zOf_mem b v w)⟩
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨w, hw⟩ := zOf_surj b v x ((hRS _).2 x.2)
    exact ⟨w, Subtype.ext hw⟩
  have ha : Function.Surjective (fun (w : Fin 1 × Fin d → v.adicCompletionIntegers F) p =>
      IsLocalRing.residue (v.adicCompletionIntegers F) (w p)) := by
    intro y
    exact ⟨fun p => lift (y p), funext fun p => res_lift (y p)⟩
  have hker : ∀ w w' : Fin 1 × Fin d → v.adicCompletionIntegers F,
      (fun p => IsLocalRing.residue (v.adicCompletionIntegers F) (w p)) =
        (fun p => IsLocalRing.residue (v.adicCompletionIntegers F) (w' p)) ↔
      φ w - φ w' ∈ PositivityTheory.PfSWUS.Loc.lev ϖS 1 := by
    intro w w'
    rw [hlev, funext_iff]
    simp only [res_eq_iff]
    rw [zOf_ker b v ϖ hϖ0 hϖ1 hϖd w w']
    rfl
  have hhalf : ((2 : Fv F v)⁻¹) ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv2', inv_one]
  let half : v.adicCompletionIntegers F := ⟨(2 : Fv F v)⁻¹, hhalf⟩
  have hhalfr : IsLocalRing.residue (v.adicCompletionIntegers F) half = (2 : IsLocalRing.ResidueField _)⁻¹ := by
    have h2h : half * 2 = 1 := by
      apply Subtype.ext
      show (2 : Fv F v)⁻¹ * 2 = 1
      have h20 : (2 : Fv F v) ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hv2'
        exact zero_ne_one hv2'
      exact inv_mul_cancel₀ h20
    have := congrArg (IsLocalRing.residue (v.adicCompletionIntegers F)) h2h
    rw [map_mul, map_one, map_ofNat] at this
    exact eq_inv_of_mul_eq_one_left this
  have hP : ∀ w : Fin 1 × Fin d → v.adicCompletionIntegers F,
      ((2 : IsLocalRing.ResidueField (v.adicCompletionIntegers F))⁻¹ *
        ((fun p => IsLocalRing.residue (v.adicCompletionIntegers F) (w p)) ⬝ᵥ
          ((BO.map (IsLocalRing.residue (v.adicCompletionIntegers F))) *ᵥ
            (fun p => IsLocalRing.residue (v.adicCompletionIntegers F) (w p)))) =
          IsLocalRing.residue (v.adicCompletionIntegers F) s) ↔
      Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖS 1) (σS (φ w) * jS * φ w) =
        Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖS 1) tS := by
    intro w
    have e1 : (fun p => IsLocalRing.residue (v.adicCompletionIntegers F) (w p)) ⬝ᵥ
        ((BO.map (IsLocalRing.residue (v.adicCompletionIntegers F))) *ᵥ
          (fun p => IsLocalRing.residue (v.adicCompletionIntegers F) (w p))) =
        IsLocalRing.residue (v.adicCompletionIntegers F) (w ⬝ᵥ (BO *ᵥ w)) :=
      (map_quad (IsLocalRing.residue (v.adicCompletionIntegers F)) BO w).symm
    have e2 : (((half * (w ⬝ᵥ (BO *ᵥ w)) : v.adicCompletionIntegers F)) : Fv F v) =
        (2 : Fv F v)⁻¹ * ((fun p => (w p : Fv F v)) ⬝ᵥ
          (B.map (algebraMap F (Fv F v)) *ᵥ fun p => (w p : Fv F v))) := by
      rw [← hBO]
      have h := map_quad (phi (v := v)) BO w
      exact congrArg (fun t => (2 : Fv F v)⁻¹ * t) h
    rw [e1, ← hhalfr, ← map_mul, res_eq_iff, e2, form_res σ hCM J hJ d b B hBt v hfix htr hR1 hRmul hRsig hv2' hjI
      ϖ hϖ0 hϖ1 hϖd w s, Ideal.Quotient.eq, hlev]
    simp only [φ, jS, tS, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, hsig]
  have hbr := card_bridge ϖS _ ha φ hφ hker
    (fun y => (2 : IsLocalRing.ResidueField (v.adicCompletionIntegers F))⁻¹ *
      (y ⬝ᵥ ((BO.map (IsLocalRing.residue (v.adicCompletionIntegers F))) *ᵥ y)) =
        IsLocalRing.residue (v.adicCompletionIntegers F) s)
    (fun x => Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖS 1) (σS x * jS * x) =
      Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖS 1) tS) hP
  rw [hbr, hcount]
  have hq0 : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by
    have : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
    have : Ideal.absNorm v.asIdeal ≠ 0 := by omega
    exact_mod_cast this
  have heR : Densx.eR E v = (ε : ℝ) := by
    simp only [Densx.eR, ← hε, Complex.intCast_re]
  rw [heR, Fin.prod_univ_one]
  norm_num
  field_simp

end PositivityTheory.SiegelWeilFormula.MOne

end
