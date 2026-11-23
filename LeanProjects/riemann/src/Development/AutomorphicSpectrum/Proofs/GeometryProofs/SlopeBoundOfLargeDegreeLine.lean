import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolarizedDataFieldExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineOfKeyDegreeStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.ShortVectorOfSubmodule
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.TopSlope

open GroundTheory.Heights₂.Heights.ComplexAt

theorem tmul_eq_smul_one {K : Type} [Field K] (σ : K →+* ℂ) {M : Type} [AddCommGroup M] [Module (𝓞 K) M]
    (z : ComplexAt σ) (m : M) :
    (z ⊗ₜ[𝓞 K] m : Fibre σ M) = ((ofComplex σ).symm z : ℂ) • ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] m) := by
  rw [smul_tmul', complex_smul_def, AlgEquiv.apply_symm_apply, _root_.mul_one]

theorem exists_isometric_ext {K L' : Type} [Field K] [NumberField K] [Field L'] [NumberField L'] [Algebra K L']
    (B : HermitianBundle.{0} K) (B' : HermitianBundle.{0} L')
    (io : B.carrier →ₛₗ[algebraMap (𝓞 K) (𝓞 L')] B'.carrier)
    (hio : ∀ (σ' : L' →+* ℂ) (x y : B.carrier),
      ((B'.metric.form σ').inner ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] io x) ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] io y) : ℂ) =
        ((B.metric.form (σ'.comp (algebraMap K L'))).inner ((1 : ComplexAt _) ⊗ₜ[𝓞 K] x)
          ((1 : ComplexAt _) ⊗ₜ[𝓞 K] y) : ℂ)) :
    ∃ Φ : (B.baseChange L').carrier →+ B'.carrier, ∀ (σ' : L' →+* ℂ) (x y : (B.baseChange L').carrier),
      ((B'.metric.form σ').inner ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] Φ x) ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] Φ y) : ℂ) =
        (((B.baseChange L').metric.form σ').inner ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] x)
          ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] y) : ℂ) := by
  let f : 𝓞 L' →+ B.carrier →+ B'.carrier :=
    { toFun := fun a => (DistribMulAction.toAddMonoidHom B'.carrier a).comp io.toAddMonoidHom
      map_zero' := by ext e; simp
      map_add' := by intro a b; ext e; simp [add_smul] }
  have hf : ∀ (r : 𝓞 K) (a : 𝓞 L') (e : B.carrier), f (r • a) e = f a (r • e) := by
    intro r a e
    simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.coe_comp, Function.comp_apply,
      DistribMulAction.toAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe, LinearMap.map_smulₛₗ,
      Algebra.smul_def, mul_smul, smul_comm a]
  let Φ0 : 𝓞 L' ⊗[𝓞 K] B.carrier →+ B'.carrier := TensorProduct.liftAddHom f hf
  have hΦ : ∀ (a : 𝓞 L') (e : B.carrier), Φ0 (a ⊗ₜ e) = a • io e := fun a e => by
    simp [Φ0, f, TensorProduct.liftAddHom_tmul]
  refine ⟨Φ0, fun σ' => ?_⟩
  have hL : ∀ u v : B'.carrier, ((B'.metric.form σ').inner ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] u)
      ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] v) : ℂ) = inner ℂ (FibreSpace.equiv B'.metric σ' (1 ⊗ₜ u))
      (FibreSpace.equiv B'.metric σ' (1 ⊗ₜ v)) := fun _ _ => rfl
  have hR : ∀ u v : 𝓞 L' ⊗[𝓞 K] B.carrier, (((B.baseChange L').metric.form σ').inner
      ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] u) ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] v) : ℂ) =
      inner ℂ (FibreSpace.equiv B.metric _ (baseChangeCoord σ' ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] u)))
        (FibreSpace.equiv B.metric _ (baseChangeCoord σ' ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] v))) := fun _ _ => rfl
  have hB : ∀ u v : B.carrier, inner ℂ (FibreSpace.equiv B.metric (σ'.comp (algebraMap K L')) (1 ⊗ₜ u))
      (FibreSpace.equiv B.metric _ (1 ⊗ₜ v)) = inner ℂ (FibreSpace.equiv B'.metric σ' (1 ⊗ₜ io u))
      (FibreSpace.equiv B'.metric σ' (1 ⊗ₜ io v)) := fun u v => (hio σ' u v).symm
  have h1 : ∀ (a : 𝓞 L') (e : B.carrier), ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] Φ0 (a ⊗ₜ e)) =
      (σ' (a : L')) • ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] io e) := by
    intro a e
    rw [hΦ, ← smul_tmul, tmul_eq_smul_one]
    congr 1
    rw [smul_def, _root_.mul_one, AlgEquiv.symm_apply_apply]
  have h2 : ∀ (a : 𝓞 L') (e : B.carrier), baseChangeCoord σ' ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] (a ⊗ₜ e)) =
      (σ' (a : L')) • ((1 : ComplexAt (σ'.comp (algebraMap K L'))) ⊗ₜ[𝓞 K] e) := by
    intro a e
    rw [baseChangeCoord_tmul, tmul_eq_smul_one]
    congr 1
    show σ' (a : L') * 1 = σ' (a : L')
    rw [_root_.mul_one]
  have key : ∀ x y : 𝓞 L' ⊗[𝓞 K] B.carrier,
      inner ℂ (FibreSpace.equiv B'.metric σ' (1 ⊗ₜ Φ0 x)) (FibreSpace.equiv B'.metric σ' (1 ⊗ₜ Φ0 y)) =
      inner ℂ (FibreSpace.equiv B.metric _ (baseChangeCoord σ' ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] x)))
        (FibreSpace.equiv B.metric _ (baseChangeCoord σ' ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] y))) := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, tmul_zero, inner_zero_left]
    | add x x' hx hx' => simp only [map_add, tmul_add, inner_add_left, hx, hx']
    | tmul a e =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero, tmul_zero, inner_zero_right]
      | add y y' hy hy' => simp only [map_add, tmul_add, inner_add_right, hy, hy']
      | tmul b e' =>
        rw [h1, h1, h2, h2, map_smul, map_smul, map_smul, map_smul, inner_smul_left, inner_smul_left,
          inner_smul_right, inner_smul_right, hB]
  intro x y
  exact (hL _ _).trans ((key x y).trans (hR x y).symm)

end GlobalTheory.CompanionTheory.Ar.Sl.TopSlope

namespace GlobalTheory.CompanionTheory.Ar.Sl.TopSlope

theorem slopeBound (hS7 : LineOfLargeDegree.Statement) (hKey : KeyDegSt) : SlopeBoundSt ∧ Prov.LemmaS := by
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.line_of_key_degree hKey
  have hS : SlopeBoundSt := by
    refine ⟨C + 2, by linarith, ?_⟩
    intro E _ _ _ H L _ _ t tK m princ B MB fib
    let D : PPData H L := ⟨t, tK, m, princ, B, MB, fib⟩
    set ℓ := Real.log (2 + (Module.finrank (𝓞 L) B.carrier : ℝ) + max (-B.normDegree ⊤) 0) with hℓ
    have hpos : 0 ≤ max (-B.normDegree ⊤) 0 := le_max_right _ _
    have hℓ2 : Real.log 2 ≤ ℓ := by
      apply Real.log_le_log (by norm_num)
      have : (0 : ℝ) ≤ (Module.finrank (𝓞 L) B.carrier : ℝ) := Nat.cast_nonneg _
      linarith
    have hℓ0 : 2 / 3 ≤ ℓ := by
      have := Real.log_two_gt_d9
      linarith
    have hg : Real.log (Module.finrank (𝓞 L) B.carrier : ℝ) ≤ ℓ := by
      rcases Nat.eq_zero_or_pos (Module.finrank (𝓞 L) B.carrier) with h | h
      · rw [h, Nat.cast_zero, Real.log_zero]; linarith
      · apply Real.log_le_log (by exact_mod_cast h)
        linarith
    simp only [HermitianBundle.slopeMax]
    refine iSup₂_le fun F hF => ?_
    rw [EReal.coe_le_coe_iff]
    obtain ⟨L', iF, iN, iA, x, -, hx⟩ := GlobalTheory.CompanionTheory.Ar.Lines.short_vector_of_submodule hS7 L B F hF
    obtain ⟨⟨D', e⟩⟩ := (GlobalTheory.T.polarized_data_field_extension E H L D L').1
    obtain ⟨hg', hh', io, -, -, hio⟩ := (GlobalTheory.T.polarized_data_field_extension E H L D L').2 D' e
    obtain ⟨Φ, hΦ⟩ := exists_isometric_ext D.B D'.B io hio
    have hlen : ∀ σ : L' →+* ℂ, D'.len σ (Φ x) = Real.sqrt ((((B.baseChange L').metric.form σ).inner
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 L'] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L'] x) : ℂ).re) := by
      intro σ
      simp only [PPData.len]
      rw [hΦ]
    have hline : -mean L' (fun σ => Real.log (D'.len σ (Φ x))) ≤ C * ℓ := by
      by_cases h0 : Φ x = 0
      · have hz : ∀ σ : L' →+* ℂ, D'.len σ (Φ x) = 0 := by
          intro σ
          simp only [PPData.len, h0, tmul_zero]
          have : ((D'.B.metric.form σ).inner (0 : Fibre σ D'.B.carrier) 0 : ℂ) = 0 :=
            inner_zero_left (𝕜 := ℂ) (x := (0 : FibreSpace D'.B.metric σ))
          rw [this, Complex.zero_re, Real.sqrt_zero]
        simp only [hz, Real.log_zero, mean, Finset.sum_const_zero, zero_div, neg_zero]
        exact mul_nonneg hC0 (by linarith)
      · have := hC E H L' D' (Φ x) h0
        rw [hg', hh'] at this
        exact this
    simp only [hlen] at hline
    have hexp : (C + 2) * ℓ = C * ℓ + 2 * ℓ := by ring
    rw [hexp]
    linarith
  exact ⟨hS, hS⟩

end GlobalTheory.CompanionTheory.Ar.Sl.TopSlope
