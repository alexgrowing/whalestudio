import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyHermitianIntegrallyCongruentCmExtStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoordEquivApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceFormGramPowerBasisHermitianNondegenerateStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowerBasisCoordsIsTorusHermitianIsometryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyLocalIntegersIffPowerBasisCoordsAllStatement
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrUnitLat
theorem alpha_mem_stab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (r : ℕ) (P : PPol σ r), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, diagH (star' P) (one₁ P) (Fv F v) (alphaRat P) ∈ stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v := by
  intro F E _ _ _ _ _ σ r P
  filter_upwards [eventually_one_tmul_mem_intLoc (F := F) (alpha P),
    eventually_one_tmul_mem_intLoc (F := F) (alpha P)⁻¹] with v h1 h2
  have e0 : ∀ Y : Fin 1 → Fv F v ⊗[F] Fld P,
      (matHom _ (star' P) (one₁ P) (diagH (star' P) (one₁ P) (Fv F v) (alphaRat P))).1 *ᵥ Y ∈
        latLoc F (stdLattice (Fld P) 1) v ↔ (1 : Fv F v) ⊗ₜ[F] alpha P * Y 0 ∈ intLoc F (Fld P) v := fun Y => by
    have e : (matHom _ (star' P) (one₁ P) (diagH (star' P) (one₁ P) (Fv F v) (alphaRat P))).1 0 0 =
        (1 : Fv F v) ⊗ₜ[F] alpha P := rfl
    rw [mem_latLoc_stdLattice, Fin.forall_fin_one, ← e]
    simp [Matrix.mulVec, dotProduct]
  have hinv : (1 : Fv F v) ⊗ₜ[F] (alpha P)⁻¹ * (1 : Fv F v) ⊗ₜ[F] alpha P = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ (alpha_ne_zero P), Algebra.TensorProduct.one_def]
  refine mem_stabLoc.2 fun Y => ?_
  rw [e0, mem_latLoc_stdLattice, Fin.forall_fin_one]
  refine ⟨mul_mem h1, fun hY => ?_⟩
  have := mul_mem h2 hY
  rwa [← mul_assoc, hinv, one_mul] at this

theorem stab_torEmb_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (r n : ℕ) (P : PPol σ r) (v : HeightOneSpectrum (𝓞 F)) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (x : Fv F v ⊗[F] Fld P) (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)) (h : IsIsom P (Fv F v) J x φ), (∀ y, y ∈ intLoc F (Fld P) v ↔ φ y ∈ latLoc F L v) → ∀ t, torEmb h t ∈ stabLoc σ J L v ↔ t ∈ stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v := by
  intro F E _ _ _ _ σ r n P v J L x φ h hφ t
  have e1 : (matHom _ σ J (torEmb h t)).1 = mulMat φ (torUnit t).1 := rfl
  have e0 : (torUnit t).1 = t.1.1 0 0 := Matrix.det_fin_one _
  have e2 : ∀ Y : Fin 1 → Fv F v ⊗[F] Fld P,
      (matHom _ (star' P) (one₁ P) t).1 *ᵥ Y ∈ latLoc F (stdLattice (Fld P) 1) v ↔
        (torUnit t).1 * Y 0 ∈ intLoc F (Fld P) v := fun Y => by
    rw [mem_latLoc_stdLattice, Fin.forall_fin_one, e0]
    simp [Matrix.mulVec, dotProduct, matHom]
    exact Iff.rfl
  rw [mem_stabLoc, mem_stabLoc]
  constructor
  · intro H Y
    rw [e2, mem_latLoc_stdLattice, Fin.forall_fin_one]
    have := H (φ (Y 0))
    rwa [e1, mulMat_mulVec, ← hφ, ← hφ] at this
  · intro H Y
    obtain ⟨y, rfl⟩ := φ.surjective Y
    rw [e1, mulMat_mulVec, ← hφ, ← hφ]
    have := H (fun _ => y)
    rwa [e2, mem_latLoc_stdLattice, Fin.forall_fin_one] at this

end GlobalTheory.TrUnitLat

namespace GlobalTheory.TrUnitLat

theorem hform_mulVec' {A : Type} [CommRing A] (s : A →+* A) {n : ℕ} (J k : Matrix (Fin n) (Fin n) A) (a b : Fin n → A) :
    Formalism.UG.hform s J (k *ᵥ a) (k *ᵥ b) = Formalism.UG.hform s (Formalism.UG.cT s k * J * k) a b := by
  have e2 : ∀ (J : Matrix (Fin n) (Fin n) A) a b, Formalism.UG.hform s J a b = (s ∘ a) ⬝ᵥ J *ᵥ b := by
    intro J a b
    simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, Function.comp_apply, mul_assoc]
  have e3 : s ∘ (k *ᵥ a) = (s ∘ a) ᵥ* Formalism.UG.cT s k := by
    funext i
    rw [Formalism.UG.cT, Matrix.vecMul_transpose, Function.comp_apply, RingHom.map_mulVec]
  rw [e2, e2, e3, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem eventually_unitClass_isom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsLattice E L], ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∃ (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin r → Fv F v ⊗[F] E)) (h : IsIsom P (Fv F v) J (1 : plusUnits P (Fv F v)).1.1 φ), gam h ∈ stabLoc σ J L v ∧ ∀ t, torEmb h t ∈ stabLoc σ J L v ↔ t ∈ stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v := by
  intro F E _ _ _ _ _ σ hcm r P J hJ L _
  haveI := isLattice_stdLattice (E := E) (n := r)
  filter_upwards [GlobalTheory.T.traceFormGramPowerBasis_hermitian_nondegenerate F E σ hcm r P |> fun hH => GlobalTheory.T.eventually_hermitian_integrally_congruent_cmExt F E σ hcm r J (gramOne P) hJ hH,
    eventually_latLoc_eq F L (stdLattice E r), GlobalTheory.T.eventually_localIntegers_iff_powerBasisCoords_all F E σ r P, GlobalTheory.TrUnitLat.alpha_mem_stab F E σ r P] with v hu hL h3 h4
  obtain ⟨u, hu, hul⟩ := hu
  let φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin r → Fv F v ⊗[F] E) :=
    (coordEquiv P (Fv F v)).trans (Matrix.toLinearEquiv' u.1 (Units.invertible u))
  have eφ : ∀ y, φ y = u.1 *ᵥ coordEquiv P (Fv F v) y := fun y => rfl
  have hφ : IsIsom P (Fv F v) J (1 : plusUnits P (Fv F v)).1.1 φ := fun y y' => by
    rw [eφ, eφ, hform_mulVec', hu]
    exact GlobalTheory.T.powerBasisCoords_isTorusHermitianIsometry F E σ r P (Fv F v) y y'
  have h5 : ∀ y, y ∈ intLoc F (Fld P) v ↔ φ y ∈ latLoc F L v := fun y => by
    rw [eφ, hL, hul, h3]
  exact ⟨φ, hφ, (GlobalTheory.TrUnitLat.stab_torEmb_iff F E σ r r P v J L _ φ hφ h5 _).2 h4, GlobalTheory.TrUnitLat.stab_torEmb_iff F E σ r r P v J L _ φ hφ h5⟩

end GlobalTheory.TrUnitLat
