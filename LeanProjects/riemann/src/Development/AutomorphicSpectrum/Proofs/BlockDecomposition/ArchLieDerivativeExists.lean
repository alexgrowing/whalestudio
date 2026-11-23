import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth
import Development.AutomorphicSpectrum.Proofs.HermitianForms.CasOfCapelliVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOpCommLiB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirMemCenterEnvelopingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOperatorEqCasimirSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOperatorCommutesInfiniteGlStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSpanFiniteDimStableStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LaplacianMonicAnnihilatorMeasureStatement

set_option maxSynthPendingDepth 1

open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep

open AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth

theorem exists_monic_aeval_add {M : Type*} [AddCommGroup M] [Module ℂ M] (Ω T : Module.End ℂ M)
    (hc : Commute Ω T) (W : Submodule ℂ M) [FiniteDimensional ℂ W] (hT : ∀ w ∈ W, T w ∈ W)
    (q : Polynomial ℂ) (hq : q.Monic) (hqW : ∀ w ∈ W, Polynomial.aeval Ω q w = 0) {v : M} (hv : v ∈ W) :
    ∃ P : Polynomial ℂ, P.Monic ∧ 0 < P.natDegree ∧ Polynomial.aeval (Ω + T) P v = 0 := by
  classical
  let V : Submodule ℂ M := ⨆ m : Fin (q.natDegree + 1), W.map (Ω ^ (m : ℕ))
  have hVfd : FiniteDimensional ℂ V := Submodule.finiteDimensional_iSup _
  have hmem : ∀ (i : ℕ), i < q.natDegree + 1 → ∀ w ∈ W, (Ω ^ i) w ∈ V := fun i hi w hw =>
    Submodule.mem_iSup_of_mem (⟨i, hi⟩ : Fin (q.natDegree + 1)) ⟨w, hw, rfl⟩
  have hpow : ∀ (m : ℕ), ∀ w ∈ W, (Ω ^ m) w ∈ V := by
    intro m w hw
    have e : (Ω ^ m) w = Polynomial.aeval Ω (Polynomial.X ^ m %ₘ q) w := by
      have h1 := Polynomial.modByMonic_add_div (Polynomial.X ^ m : Polynomial ℂ) q
      have h2 : Polynomial.aeval Ω (q * (Polynomial.X ^ m /ₘ q)) w = 0 := by
        rw [mul_comm, map_mul, Module.End.mul_apply, hqW w hw, map_zero]
      have h3 := congrArg (fun p => Polynomial.aeval Ω p w) h1
      simp only [map_add, LinearMap.add_apply, h2, add_zero, map_pow, Polynomial.aeval_X] at h3
      exact h3.symm
    rw [e, Polynomial.aeval_eq_sum_range' (n := q.natDegree + 1)
      (Nat.lt_succ_of_le (Polynomial.natDegree_modByMonic_le _ hq)), LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun i hi => by
      rw [LinearMap.smul_apply]
      exact V.smul_mem _ (hmem i (Finset.mem_range.1 hi) w hw)
  have hst : ∀ x ∈ V, (Ω + T) x ∈ V := by
    intro x hx
    have hle : V ≤ V.comap (Ω + T) := by
      refine iSup_le fun m => ?_
      rintro _ ⟨w, hw, rfl⟩
      have e : (Ω + T) ((Ω ^ (m : ℕ)) w) = (Ω ^ ((m : ℕ) + 1)) w + (Ω ^ (m : ℕ)) (T w) := by
        rw [LinearMap.add_apply, pow_succ', Module.End.mul_apply, ← Module.End.mul_apply T,
          ((hc.pow_left (m : ℕ)).eq).symm, Module.End.mul_apply]
      change (Ω + T) ((Ω ^ (m : ℕ)) w) ∈ V
      rw [e]
      exact V.add_mem (hpow _ w hw) (hpow _ _ (hT w hw))
    exact hle hx
  have hv' : v ∈ V := by simpa using hpow 0 v hv
  exact AutomorphicForm.exists_monic_aeval_apply_eq_zero (Ω + T) V hst hv'

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem exists_aeval_lapOp_eq_zero (φ : Sm E a) (hA : IsAutForm φ) {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (horth : ∀ i j, archTraceForm E a (b i) (b j) = if i = j then ε i else 0)
    (hskew : ∀ i, ε i = -1 → b i ∈ archSkew E a) :
    ∃ P : Polynomial ℂ, P.Monic ∧ 0 < P.natDegree ∧ Polynomial.aeval (lapOp (⇑b)) P φ = 0 := by
  classical
  set Ω := omegaOp (E := E) (a := a) (⇑b) ε with hΩ
  set W := Submodule.span ℂ (Set.range fun k => cptRep E a k φ) with hWdef
  haveI : FiniteDimensional ℂ W := hA.kfin
  have hZ : Ω ∈ Zalg E a := by
    rw [hΩ, GlobalTheory.T.omega_operator_eq_casimir_sum  E a d b ε hε horth]
    refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun w _ => Subalgebra.add_mem _ ?_ ?_) _
    · exact GlobalTheory.T.casimir_mem_center_enveloping E a _
    · exact GlobalTheory.T.casimir_mem_center_enveloping E a _
  set Vz := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hVz
  haveI : FiniteDimensional ℂ Vz := hA.zfin
  have hVs : ∀ w ∈ Vz, Ω w ∈ Vz := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => Ω w ∈ Vz) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨z, hz, rfl⟩
      exact Submodule.subset_span ⟨Ω * z, Subalgebra.mul_mem _ hZ hz, rfl⟩
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ c hx
  have hφV : φ ∈ Vz := Submodule.subset_span ⟨1, Subalgebra.one_mem _, rfl⟩
  obtain ⟨q, hqm, -, hq⟩ := AutomorphicForm.exists_monic_aeval_apply_eq_zero Ω Vz hVs hφV
  have hqW : ∀ w ∈ W, Polynomial.aeval Ω q w = 0 := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => Polynomial.aeval Ω q w = 0) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨k, rfl⟩
      have hcomm : ∀ m, cptRep E a k (Ω m) = Ω (cptRep E a k m) := fun m =>
        (congrArg (fun T : Module.End ℂ (Sm E a) => T m)
          (GlobalTheory.T.omega_operator_commutes_infinite_gl E a d b ε hε horth (Unitary.toUnits k))).symm
      have := AutomorphicForm.map_aeval_apply_of_intertwine (cptRep E a k) hcomm q φ
      rw [hq, map_zero] at this
      exact this.symm
    · rw [map_zero]
    · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
    · intro c x _ hx; rw [map_smul, hx, smul_zero]
  have hlap : Commute Ω (lapOp (⇑b)) := by
    simp only [lapOp, Commute, SemiconjBy]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : Ω * liB (b i) = liB (b i) * Ω := omegaOp_comm_liB b ε hε horth (b i)
    rw [← mul_assoc, h1, mul_assoc, h1, mul_assoc]
  have hTW : ∀ w ∈ W, (lapOp (⇑b) - Ω) w ∈ W := by
    intro w hw
    have e : (lapOp (E := E) (a := a) (⇑b) - Ω) w =
        ∑ i, ((1 : ℂ) - (ε i : ℂ)) • liB (b i) (liB (b i) w) := by
      simp only [hΩ, lapOp, omegaOp, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        Module.End.mul_apply]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      module
    rw [e]
    refine Submodule.sum_mem _ fun i _ => ?_
    rcases hε i with h | h
    · simp [h]
    · refine W.smul_mem _ ?_
      have hs := mem_archSkew.1 (hskew i h)
      have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) := hA.kfin
      exact GlobalTheory.T.compact_span_finite_dim_stable E a φ (b i) hs hfd _ (GlobalTheory.T.compact_span_finite_dim_stable E a φ (b i) hs hfd _ hw)
  have hφW : φ ∈ W := by
    refine Submodule.subset_span ⟨1, ?_⟩
    change cptRep E a 1 φ = φ
    rw [map_one]
    rfl
  have hc : Commute Ω (lapOp (⇑b) - Ω) := by
    refine LinearMap.ext fun x => ?_
    have h2 := LinearMap.congr_fun hlap.eq x
    simp only [Module.End.mul_apply] at h2 ⊢
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, h2]
  have hsum : Ω + (lapOp (⇑b) - Ω) = lapOp (⇑b) := LinearMap.ext fun x => by simp
  obtain ⟨P, hP1, hP2, hP3⟩ := exists_monic_aeval_add Ω (lapOp (⇑b) - Ω) hc W hTW q hqm hqW hφW
  refine ⟨P, hP1, hP2, ?_⟩
  rwa [hsum] at hP3

theorem sliceL_aeval_lapOp {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra E a).lieSubalgebra)
    (P : Polynomial ℂ) (ψ : Sm E a) (g : AdelicGLn.AdelicGL E a) :
    sliceL g (smL E a (Polynomial.aeval (lapOp (⇑b)) P ψ)) =
      Polynomial.aeval ((isExpLieAlgebra E a).laplacian (F := ℂ) b) P (sliceL g (smL E a ψ)) := by
  refine AutomorphicForm.map_aeval_apply_of_intertwine ((sliceL g).comp (smL E a)) (fun m => ?_) P ψ
  simp only [LinearMap.comp_apply, smL_lapOp, map_sum, sliceL_uAction,
    IsExpLieAlgebra.laplacian, LinearMap.sum_apply, Module.End.mul_apply,
    IsExpLieAlgebra.rightUAction_ι]

theorem uJ_eq_conv : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (hs : φ.1 ∈ AutomorphicForm.archSmooth E a), IsAutForm φ → (∀ [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)]
    (μ : MeasureTheory.Measure (AutomorphicForm.archGroup E a)) [μ.IsHaarMeasure]
    (k : ℕ) (J : Fin k → Fin (CuspidalSpectrum.archDim E a)),
    ∃ D : AutomorphicForm.archGroup E a → ℂ, Continuous D ∧ HasCompactSupport D ∧ ∀ g : AdelicGLn.AdelicGL E a,
      ((AutomorphicForm.uAction (CuspidalSpectrum.uJ (K := E) (n := a) k J) (⟨φ.1, hs⟩ : ↥(AutomorphicForm.archSmooth E a)) :
        ↥(AutomorphicForm.archSmooth E a)) : AdelicGLn.AdelicGL E a → ℂ) g = ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * D y ∂μ) := by
  intro E _ _ _ a φ hs hA _ _ μ _ k J
  obtain ⟨d, b, ε, hε, horth, hskew⟩ := exists_archCartanBasis (K := E) (n := a)
  obtain ⟨P, hm, hd, hP⟩ := exists_aeval_lapOp_eq_zero φ hA b ε hε horth hskew
  exact GlobalTheory.T.laplacian_monic_annihilator_measure E a (smL E a φ) d b P hm hd
    (fun g => by rw [← sliceL_aeval_lapOp, hP, map_zero, map_zero]) μ k J

end GlobalTheory.CompanionTheory.HCRep

end
