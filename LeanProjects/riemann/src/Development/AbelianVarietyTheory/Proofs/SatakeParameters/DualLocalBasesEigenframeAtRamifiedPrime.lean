import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaInvolutionRealPlacePairsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralEigenCombination
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormLeOneHostBaseModuleAtDStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalBasisUnitScalarsExistStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualFrameHermitianFormTraceRealPlacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualFrameColumnsScaledStandardVectorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualLocalBasesPairDualModRootMinusDStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairEmbeddingsCongrModRootMinusDStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualFramePairedBlocksDiagonalModRootStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

namespace GlobalTheory.Proof.dualLocalBases_eigenframe_at_ramifiedPrime

open GlobalTheory.DFrame

theorem embT_conj (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    TaylorLogMetric.embT D τ (D.host.conj x) = (starRingEnd ℂ) (TaylorLogMetric.embT D τ x) :=
  D.host.conjE_apply (TaylorLogMetric.embT D τ) x

theorem tauEmb_eq_iota : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), Formalism.L2.KerInert.IotaExt lm ι → ∀ (τ : D.what₂.Tau) (y : D.host.E), TaylorLogMetric.tauEmb D lm τ y = ι (TaylorLogMetric.embT D τ y) := by
  intro D p _ lm ι hι τ y
  have halg : TaylorLogMetric.embT D τ y ∈ TaylorLogMetric.Qbar :=
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) y).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)
  unfold TaylorLogMetric.tauEmb TaylorLogMetric.lamC
  rw [dif_pos halg, ← hι]

theorem outer_mem_YYl : ∀ (D : D7) (N N' : ℕ) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (a : D.host.E) (u : Fin N' → D.host.E) (w : Fin N → D.host.E), a ∈ D.host.AA0 → u ∈ L₁' → (∀ x ∈ L₁, ∃ o : 𝓞 D.host.E, (o : D.host.E) = ∑ j, w j * x j) → (Matrix.of fun i k => a * u i * w k : Matrix (Fin N') (Fin N) D.host.E) ∈ TaylorLogMetric.YYl D L₁ L₁' := by
  intro D N N' L₁ L₁' a u w ha hu hw
  refine Submodule.subset_span ⟨a, ha, Matrix.of fun i k => u i * w k, Submodule.subset_span ?_, ?_⟩
  · intro x hx
    obtain ⟨o, ho⟩ := hw x hx
    have : (Matrix.of fun i k => u i * w k).mulVec x = o • u := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply]
      rw [Algebra.smul_def]
      show _ = (o : D.host.E) * u i
      rw [ho, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this]; exact L₁'.smul_mem o hu
  · ext i k; simp [Matrix.smul_apply, mul_assoc]

theorem smul_vecF_mem_laF : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (X : Fields) (s : Seam D X) (N N' : ℕ) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (M : Matrix (Fin N') (Fin N) D.host.E), M ∈ TaylorLogMetric.YYl D L₁ L₁' → ∀ ω ∈ TaylorLogMetric.lamOf D cc δ, ω • GlobalTheory.DFrame.vecF D s M ∈ s.laF (TaylorLogMetric.tor0 D cc δ) L₁ L₁' := by
  intro D cc δ X s N N' L₁ L₁' M hM ω hω
  show (s.flatV N N') (ω • vecF D s M) ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁'
  have : (s.flatV N N') (ω • vecF D s M) = ω • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) M := by
    funext τ i j
    simp [Seam.flatV, vecF, TaylorLogMetric.embV, TaylorLogMetric.tor0]
  rw [this]
  exact AddSubgroup.subset_closure ⟨ω, hω, M, hM, rfl⟩

theorem matH_act_adjoint : ∀ (D : D7) (X : Fields) (s : Seam D X) (N N' : ℕ) (sc : ℝ) (e e' : 𝓞 D.host.E), (e' : D.host.E) = D.host.conj (e : D.host.E) → ∀ x y : DVar X.Tau N N' → ℂ, matH (Formalism.L2.AlgTh.hSc X.Tau N N' sc) (GlobalTheory.DFrame.act D s N N' e x) y = matH (Formalism.L2.AlgTh.hSc X.Tau N N' sc) x (GlobalTheory.DFrame.act D s N N' e' y) := by
  intro D X s N N' sc e e' he x y
  show (∑ i, ∑ j, act D s N N' e x i * Formalism.L2.AlgTh.hSc X.Tau N N' sc i j * (starRingEnd ℂ) (y j)) =
    ∑ i, ∑ j, x i * Formalism.L2.AlgTh.hSc X.Tau N N' sc i j * (starRingEnd ℂ) (act D s N N' e' y j)
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Formalism.L2.AlgTh.hSc, Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    simp only [act, LinearMap.coe_mk, AddHom.coe_mk, he, map_mul, embT_conj, Complex.conj_conj]
    ring
  · simp

theorem act_mem_laF : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (X : Fields) (s : Seam D X) (N N' : ℕ) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (e : 𝓞 D.host.E) (x : DVar X.Tau N N' → ℂ), x ∈ s.laF (TaylorLogMetric.tor0 D cc δ) L₁ L₁' → GlobalTheory.DFrame.act D s N N' e x ∈ s.laF (TaylorLogMetric.tor0 D cc δ) L₁ L₁' := by
  intro D cc δ X s N N' L₁ L₁' e x hx
  show (s.flatV N N') (act D s N N' e x) ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁'
  have hx' : (s.flatV N N') x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁' := hx
  have key : ∀ w ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁',
      (fun τ i j => TaylorLogMetric.embT D τ (e : D.host.E) * w τ i j : TaylorLogMetric.VC D N N') ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁' := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨ω, hω, A, hA, rfl⟩ := hw
      have : (fun τ i j => TaylorLogMetric.embT D τ (e : D.host.E) * (ω • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) A) τ i j : TaylorLogMetric.VC D N N') =
          ω • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (e • A) := by
        funext τ i j
        simp only [TaylorLogMetric.embV, TaylorLogMetric.tor0, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
        rw [Algebra.smul_def, map_mul]
        show _ = ω * (TaylorLogMetric.embT D τ (e : D.host.E) * _)
        ring
      rw [this]
      exact AddSubgroup.subset_closure ⟨ω, hω, e • A, (TaylorLogMetric.YYl D L₁ L₁').smul_mem e hA, rfl⟩
    | zero =>
      have : (fun τ i j => TaylorLogMetric.embT D τ (e : D.host.E) * (0 : TaylorLogMetric.VC D N N') τ i j : TaylorLogMetric.VC D N N') = 0 := by
        funext τ i j; simp
      rw [this]; exact (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁').zero_mem
    | add w₁ w₂ _ _ h₁ h₂ =>
      have := (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁').add_mem h₁ h₂
      convert this using 1
      funext τ i j; simp [mul_add]
    | neg w _ h =>
      have := (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L₁ L₁').neg_mem h
      convert this using 1
      funext τ i j; simp
  have e1 : (s.flatV N N') (act D s N N' e x) = fun τ i j => TaylorLogMetric.embT D τ (e : D.host.E) * (s.flatV N N') x τ i j := by
    funext τ i j
    simp [Seam.flatV, act]
  rw [e1]; exact key _ hx'

end GlobalTheory.Proof.dualLocalBases_eigenframe_at_ramifiedPrime

namespace GlobalTheory.Proof.dualLocalBases_eigenframe_at_ramifiedPrime

open GlobalTheory.DFrame

theorem conj_conj' (D : D7) (y : D.host.E) : D.host.conj (D.host.conj y) = y := by
  apply D.host.φ₀.injective
  show D.host.φ₀ ((D.host.conj) ((D.host.conj) y)) = _
  rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply, Complex.conj_conj]

theorem sum_le_one {p : ℕ} [Fact p.Prime] {ι' : Type} (S : Finset ι') (f : ι' → ℂ_[p]) (h : ∀ i, ‖f i‖ ≤ 1) :
    ‖∑ i ∈ S, f i‖ ≤ 1 :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i _ => h i)

theorem eigenframe_at_d : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (X : Fields) (s : Seam D X), s.Ok → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TaylorLogMetric.admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), p = D.host.d → ∀ ι : ℂ ≃+* ℂ_[p], Formalism.L2.KerInert.IotaExt lm ι → ∀ (cD : D.what₂.Tau → ℂ), IsDgen D cD → ∀ (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (κ : D.what₂.Tau → ℂ_[p]), GlobalTheory.KerStd.StdBases D lm L P → GlobalTheory.KerStd.StdBases D lm L' P' → (∀ τ, ‖κ τ‖ ≤ ‖TaylorLogMetric.lamC lm (cD τ)‖) → ∃ u : HH D → ℂ_[p], (∀ t, ‖u t‖ ≤ 1) ∧ ∀ L₁ L₁', TaylorLogMetric.admitted D N N' L₁ L₁' → TaylorLogMetric.EqAt D p L L₁ → TaylorLogMetric.EqAt D p L' L₁' → ∃ (J : Type) (_ : Fintype J) (v : J → DVar X.Tau N N' → ℂ) (A : J → (Bool × HH D) × Fin N × Fin N' → ℂ_[p]) (cE sE : D.host.E ≃+* D.host.E) (δE : D.host.E) (emb : Bool × HH D → (D.host.E →+* ℂ_[p])) (act : 𝓞 D.host.E → (DVar X.Tau N N' → ℂ) →ₗ[ℂ] (DVar X.Tau N N' → ℂ)), Formalism.L2.Th1.GD.IsEigenFrame ι (cmL a₀ b₀ D.host.d ha hd lam hlam) (ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))) (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF (TaylorLogMetric.tor0 D cc δ) L₁ L₁') D.host.E cE sE δE emb act v A u ∧ ∀ i x, frameM (ι : ℂ →+* ℂ_[p]) v A i x = κ (s.iT i.1) * TaylorLogMetric.chgB D lm P P' (s.iT i.1, i.2) ((0 : ZMod 1), (tauPl D x.1, x.2)) := by
  intro D cc δ hcc hδ X s hs a₀ b₀ c₀ ha hd lam hlam hcm hlat N N' L L' hadm p _ lm hp ι hι cD hcD P P' κ hP hP' hκ
  obtain ⟨cE, sE, δE, hcE, hδ2, hcδ, hsδ, hss, hsc, hinj, hδc, hpair, hkur, hbij, hsg⟩ := GlobalTheory.T.inertiaInvolution_realPlacePairs D p hp ι
  have htau : ∀ (τ : D.what₂.Tau) (y : D.host.E), TaylorLogMetric.tauEmb D lm τ y = ι (TaylorLogMetric.embT D τ y) := tauEmb_eq_iota D p lm ι hι
  have htauR : ∀ z : Bool × HH D, TaylorLogMetric.tauEmb D lm (tauPl D z) = ⇑(rho D ι z) := fun z => funext fun y => htau _ y
  have heig := fun z : Bool × HH D => GlobalTheory.Proof.IntegralEigenCombination.eigGen_integral_comb D cD hcD p lm (tauPl D z)
  choose n r a hr ha hsum using heig
  set c0 : Bool × HH D → ℂ_[p] := fun z => TaylorLogMetric.lamC lm (cD (tauPl D z)) with hc0
  set cκ : Bool × HH D → ℂ_[p] := fun z => κ (tauPl D z) / c0 z with hcκdef
  have hcκ1 : ∀ z, ‖cκ z‖ ≤ 1 := by
    intro z
    simp only [hcκdef, norm_div]
    by_cases h0 : ‖c0 z‖ = 0
    · rw [h0, div_zero]; exact zero_le_one
    · exact div_le_one_of_le₀ (hκ _) (norm_nonneg _)
  have hcκ : ∀ z, cκ z * c0 z = κ (tauPl D z) := by
    intro z
    by_cases h0 : c0 z = 0
    · have h1 := hκ (tauPl D z)
      rw [show TaylorLogMetric.lamC lm (cD (tauPl D z)) = 0 from h0, norm_zero] at h1
      rw [h0, mul_zero]; exact (norm_le_zero_iff.1 h1).symm
    · simp only [hcκdef]; field_simp
  have hA0 : ∀ z (α α' : Σ z : Bool × HH D, Fin (n z)), ‖rho D ι z (a α.1 α.2 * D.host.conj (a α'.1 α'.2))‖ ≤ 1 := by
    intro z α α'
    rw [map_mul, norm_mul]
    refine mul_le_one₀ (GlobalTheory.T.padic_norm_le_one_host_base_module_at_d D p hp _ _ (ha _ _)) (norm_nonneg _) ?_
    exact GlobalTheory.T.padic_norm_le_one_host_base_module_at_d D p hp ((rho D ι z).comp (D.host.conj : D.host.E →+* D.host.E)) _ (ha _ _)
  have hgc : ∀ z α, ‖gc D cκ r z α‖ ≤ 1 := by
    intro z α
    unfold gc
    split_ifs
    · rw [norm_mul]; exact mul_le_one₀ (hcκ1 z) (norm_nonneg _) (hr _ _)
    · simp
  have hu : ∀ t, ‖uu D ι cκ r a t‖ ≤ 1 := by
    intro t
    unfold uu
    refine sum_le_one _ _ fun α => sum_le_one _ _ fun α' => ?_
    rw [norm_mul, norm_mul]
    exact mul_le_one₀ (mul_le_one₀ (hgc _ _) (norm_nonneg _) (hA0 _ _ _)) (norm_nonneg _) (hgc _ _)
  refine ⟨uu D ι cκ r a, hu, fun L₁ L₁' hadm₁ hL hL' => ?_⟩
  · have hPW : ∀ z, TaylorLogMetric.LocBasisW D (rho D ι z) L (P (tauPl D z)) := fun z => by
      have := hP.1 (tauPl D z); rwa [htauR] at this
    have hP'W : ∀ z, TaylorLogMetric.LocBasisW D (rho D ι z) L' (P' (tauPl D z)) := fun z => by
      have := hP'.1 (tauPl D z); rwa [htauR] at this
    have hden := fun z : Bool × HH D => GlobalTheory.T.local_basis_unit_scalars_exist D p (rho D ι z) N N' L L₁ L' L₁' (P (tauPl D z)) (P' (tauPl D z))
      hadm₁.2.2.1.1 hL hL' (hPW z) (hP'W z)
    choose σ σ' hσ hσ' hrow hcol using hden
    obtain ⟨⟨hth1, hth0⟩, hcong⟩ := GlobalTheory.T.pair_embeddings_congr_mod_root_minus_d D p hp ι cE sE δE hcE hδ2 hsδ hss hpair hkur
    have hdualP : ∀ t, ((P (tauPl D (true, t))).map D.host.conj).transpose * P (tauPl D (false, t)) = 1 := fun t => by
      have := hP.2.2 hp (tauPl D (false, t)); rwa [(hsg t).1] at this
    have hdualP' : ∀ t, ((P' (tauPl D (true, t))).map D.host.conj).transpose * P' (tauPl D (false, t)) = 1 := fun t => by
      have := hP'.2.2 hp (tauPl D (false, t)); rwa [(hsg t).1] at this
    have hσ0 : ∀ z, rho D ι z (σ z : D.host.E) ≠ 0 := fun z => norm_ne_zero_iff.1 (by rw [hσ z]; exact one_ne_zero)
    have hσ0' : ∀ z, rho D ι z (σ' z : D.host.E) ≠ 0 := fun z => norm_ne_zero_iff.1 (by rw [hσ' z]; exact one_ne_zero)
    have hframe := GlobalTheory.T.dualFrame_columns_scaled_standard_vectors D p lm ι htau X s n N N' a r cκ c0 P P' σ σ' hσ0 hσ0' (fun z => (hPW z).1) hsum
    have hfr : ∀ (i : DVar X.Tau N N') (x : (Bool × HH D) × Fin N × Fin N'),
        frameM (ι : ℂ →+* ℂ_[p]) (fun j => vecF D s (mat D a P P' σ σ' j)) (coef D ι cκ r σ σ') i x =
          κ (s.iT i.1) * TaylorLogMetric.chgB D lm P P' (s.iT i.1, i.2) ((0 : ZMod 1), (tauPl D x.1, x.2)) := by
      intro i x
      rw [hframe]
      by_cases h : tauPl D x.1 = s.iT i.1
      · rw [hcκ, h]
      · simp [TaylorLogMetric.chgB, h]
    have hmem : ∀ j : JJ D n N N', mat D a P P' σ σ' j ∈ TaylorLogMetric.YYl D L₁ L₁' := by
      intro j
      refine outer_mem_YYl D N N' L₁ L₁' (a j.1.1 j.1.2) (colR D P' σ' j.2.2) (rowL D P σ j.2.1) (ha _ _) (hcol _ _) ?_
      intro x hx
      obtain ⟨o, ho⟩ := hrow j.2.1.1 j.2.1.2 x hx
      refine ⟨o, ?_⟩
      rw [ho, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [rowL]; ring
    have hsep : ∀ τ ρ : Bool × HH D, ρ ≠ τ → ∀ α' : (Σ z : Bool × HH D, Fin (n z)),
        ∑ α, gc D cκ r τ α * rho D ι ρ (a α.1 α.2 * D.host.conj (a α'.1 α'.2)) = 0 := by
      intro τ ρ hne α'
      rw [Fintype.sum_sigma]
      have h1 : ∀ z (k : Fin (n z)), gc D cκ r τ ⟨z, k⟩ * rho D ι ρ (a z k * D.host.conj (a α'.1 α'.2)) =
          if z = τ then cκ τ * rho D ι ρ (D.host.conj (a α'.1 α'.2)) * (r z k * rho D ι ρ (a z k)) else 0 := by
        intro z k
        unfold gc
        split_ifs with hz
        · subst hz; rw [map_mul]; ring
        · rw [zero_mul]
      simp only [h1]
      rw [Finset.sum_eq_single τ]
      · simp only [if_true, ← Finset.mul_sum]
        have := hsum τ (tauPl D ρ)
        rw [htauR] at this
        rw [this, if_neg (fun h => hne (hbij.1 h)), mul_zero]
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ τ) h
    have hd1 := (GlobalTheory.T.dual_local_bases_pair_dual_mod_root_minus_d D p ι _ hth0 hcong P σ hσ hdualP).1
    have hd2 := (GlobalTheory.T.dual_local_bases_pair_dual_mod_root_minus_d D p ι _ hth0 hcong P' σ' hσ' hdualP').2
    refine ⟨JJ D n N N', inferInstance, fun j => vecF D s (mat D a P P' σ σ' j), coef D ι cκ r σ σ', cE, sE, δE,
      rho D ι, act D s N N', ⟨hδ2, hcδ, hsδ, fun y => by rw [hcE (cE y), hcE y, conj_conj'], hss, hsc, ?_,
      fun τ ρ => by simp only [rho, RingHom.coe_comp, Function.comp_apply, hδc (tauPl D τ) (tauPl D ρ)],
      fun t y => by simp only [rho, RingHom.coe_comp, Function.comp_apply, hpair], fun τ y hy => hkur _ y hy,
      fun e e' he x y => matH_act_adjoint D X s N N' _ e e' (by rw [he, hcE]) x y,
      fun e x hx => act_mem_laF D cc δ X s N N' L₁ L₁' e x hx,
      fun j ω hω => smul_vecF_mem_laF D cc δ X s N N' L₁ L₁' _ (hmem j) ω (by rw [← hlat]; exact hω), ?_, ?_,
      GlobalTheory.T.dualFrame_paired_blocks_diagonal_mod_root D p ι X s _ _ n N N' a cκ r P P' σ σ' _ hth1 (fun A B => GlobalTheory.T.dualFrame_hermitian_form_trace_real_places D X s _ _ hlat hbij N N' A B p ι) hsep
        hu hd1 hd2⟩, hfr⟩
    · intro z z' h
      apply hinj
      refine RingHom.ext fun y => ι.injective ?_
      have := congrArg (fun f : D.host.E →+* ℂ_[p] => f y) h
      simpa [rho] using this
    · intro j x
      unfold coef GlobalTheory.DFrame.pc
      rw [norm_mul, norm_mul]
      refine mul_le_one₀ (mul_le_one₀ (hgc _ _) (norm_nonneg _) ?_) (norm_nonneg _) ?_
      · split_ifs
        · rw [norm_inv, hσ]; simp
        · simp
      · split_ifs
        · rw [norm_inv, hσ']; simp
        · simp
    · intro e x i
      have hact : ∀ i' : DVar X.Tau N N', (act D s N N' e) (Pi.single i' 1) i =
          if i = i' then TaylorLogMetric.embT D (s.iT i.1) (e : D.host.E) else 0 := by
        intro i'
        simp only [act, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply, mul_ite, mul_one, mul_zero]
      simp only [hfr, Formalism.L2.Th1.GD.mapVec, hact]
      rw [Finset.sum_eq_single i (fun b _ hb => by rw [if_neg (Ne.symm hb), map_zero, zero_mul])
        (fun h => absurd (Finset.mem_univ i) h), if_pos rfl]
      by_cases h : tauPl D x.1 = s.iT i.1
      · rw [← h]; rfl
      · simp [TaylorLogMetric.chgB, h]

end GlobalTheory.Proof.dualLocalBases_eigenframe_at_ramifiedPrime
