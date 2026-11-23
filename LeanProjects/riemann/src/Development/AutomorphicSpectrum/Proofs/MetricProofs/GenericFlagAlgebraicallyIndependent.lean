import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem IsGenericFlag.indep_twist_mul_genUp : ∀ (Ω Φ : Type) [Field Ω] [Field Φ] [Algebra Ω Φ] (Ψ : Type) (N j : ℕ) (g : Ψ → Matrix (Fin N) (Fin N) Φ) (T : Ψ → Matrix (Fin N) (Fin N) Ω), (∀ τ, IsBlockDiag j (g τ)) → IsGenericFlag Ω j g → (∀ τ, IsBlockDiag j (T τ) ∧ (T τ).det ≠ 0) → AlgebraicIndependent Ω (fun q : inertBlockIndex Ψ N j => (((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (UpIdx Ψ N j) Φ))) * ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1)) q.1.2.1 q.1.2.2) := by
  intro Ω Φ _ _ _ Ψ N j g T hg hgen hT
  have hTu : ∀ τ, IsUnit (T τ).det := fun τ => isUnit_iff_ne_zero.mpr (hT τ).2
  have hM : ∀ τ, IsBlockDiag j ((g τ).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j τ) :=
    fun τ => IsBlockDiag.mul (IsBlockDiag.map (hg τ) (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ))
      (genUp_blockDiag (R := Φ) τ)
  have key : ∀ (R : Type) [CommRing R] [Algebra Ω R] (f : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] R)
      (Z : Ψ → Matrix (Fin N) (Fin N) R), (∀ τ, IsBlockDiag j (Z τ)) →
      (∀ q : inertBlockIndex Ψ N j, f (X q) = Z q.1.1 q.1.2.1 q.1.2.2) →
      ∀ τ c b, f (genericBlockMatrix Ω N j τ c b) = Z τ c b := by
    intro R _ _ f Z hZ hf τ c b
    exact congrFun (congrFun (generic_block_matrix_map f.toRingHom hZ hf τ) c) b
  have hlin : ∀ (R : Type) [CommRing R] [Algebra Ω R] (f : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] R)
      (U : Matrix (Fin N) (Fin N) Ω) (G : Matrix (Fin N) (Fin N) (MvPolynomial (inertBlockIndex Ψ N j) Ω)) (a b : Fin N),
      f ((U.map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)) * G) a b)
        = (U.map (algebraMap Ω R) * G.map f) a b := by
    intro R _ _ f U G a b
    simp only [Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply, AlgHom.commutes]
  obtain ⟨φ, hφ⟩ : ∃ φ : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] MvPolynomial (inertBlockIndex Ψ N j) Ω,
      ∀ q : inertBlockIndex Ψ N j, φ (X q) = ((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))
        * genericBlockMatrix Ω N j q.1.1) q.1.2.1 q.1.2.2 :=
    ⟨MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j => ((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))
        * genericBlockMatrix Ω N j q.1.1) q.1.2.1 q.1.2.2), fun q => MvPolynomial.aeval_X _ q⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MvPolynomial (inertBlockIndex Ψ N j) Ω →ₐ[Ω] MvPolynomial (inertBlockIndex Ψ N j) Ω,
      ∀ q : inertBlockIndex Ψ N j, ψ (X q) = ((T q.1.1).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))
        * genericBlockMatrix Ω N j q.1.1) q.1.2.1 q.1.2.2 :=
    ⟨MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j => ((T q.1.1).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))
        * genericBlockMatrix Ω N j q.1.1) q.1.2.1 q.1.2.2), fun q => MvPolynomial.aeval_X _ q⟩
  have hZ : ∀ τ, IsBlockDiag j ((T τ).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)) * genericBlockMatrix Ω N j τ) :=
    fun τ => IsBlockDiag.mul (IsBlockDiag.map (hT τ).1 (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)))
      (generic_block_matrix_isBlockDiag (R := Ω) τ)
  have hψg := key _ ψ _ hZ hψ
  have hGψ : ∀ τ, (genericBlockMatrix Ω N j τ).map ψ
      = (T τ).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)) * genericBlockMatrix Ω N j τ :=
    fun τ => Matrix.ext fun c b => by rw [Matrix.map_apply]; exact hψg τ c b
  have hcomp : ∀ p, ψ (φ p) = p := by
    have hc : ψ.comp φ = AlgHom.id Ω _ := by
      apply MvPolynomial.algHom_ext
      intro q
      rw [AlgHom.comp_apply, AlgHom.id_apply, hφ, hlin _ ψ, hGψ, ← Matrix.mul_assoc, ← Matrix.map_mul,
        Matrix.nonsing_inv_mul _ (hTu _),
        show ((1 : Matrix (Fin N) (Fin N) Ω).map (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω))) = 1 from
          (algebraMap Ω (MvPolynomial (inertBlockIndex Ψ N j) Ω)).mapMatrix.map_one,
        Matrix.one_mul, generic_block_matrix_apply]
    intro p
    exact DFunLike.congr_fun hc p
  have hx := IsGenericFlag.indep_mul_genUp hg hgen
  have hxg := key _ (MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j =>
      ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1) q.1.2.1 q.1.2.2)) _ hM
    (fun q => MvPolynomial.aeval_X _ q)
  have hGx : ∀ τ, (genericBlockMatrix Ω N j τ).map (MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j =>
      ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1) q.1.2.1 q.1.2.2))
      = (g τ).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j τ :=
    fun τ => Matrix.ext fun c b => by rw [Matrix.map_apply]; exact hxg τ c b
  have h1 : ∀ r, MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j => (((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (UpIdx Ψ N j) Φ)))
        * ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1)) q.1.2.1 q.1.2.2) r
      = MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j =>
        ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1) q.1.2.1 q.1.2.2) (φ r) := by
    have hc : (MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j => (((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (UpIdx Ψ N j) Φ)))
        * ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1)) q.1.2.1 q.1.2.2))
      = (MvPolynomial.aeval (fun q : inertBlockIndex Ψ N j =>
        ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1) q.1.2.1 q.1.2.2)).comp φ := by
      apply MvPolynomial.algHom_ext
      intro q
      rw [AlgHom.comp_apply, MvPolynomial.aeval_X, hφ, hlin, hGx]
    intro r
    exact DFunLike.congr_fun hc r
  rw [algebraicIndependent_iff_injective_aeval] at hx ⊢
  intro p p' hpp
  have h2 : φ p = φ p' := hx (by rw [← h1, ← h1]; exact hpp)
  calc p = ψ (φ p) := (hcomp p).symm
    _ = ψ (φ p') := by rw [h2]
    _ = p' := hcomp p'

end GlobalTheory.CompanionTheory.Ar.PB
