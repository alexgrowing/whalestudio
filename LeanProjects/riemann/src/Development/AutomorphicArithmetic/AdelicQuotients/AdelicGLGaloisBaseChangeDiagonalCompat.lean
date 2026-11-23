import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem galAd_alg (σ : E ≃ₐ[F] E) (x : E) :
    galAd σ (algebraMap E 𝔸[E] x) = algebraMap E 𝔸[E] (σ x) := by
  have h : (adeleTensorEquiv F E).symm (algebraMap E 𝔸[E] x) = x ⊗ₜ[F] 1 := by
    rw [AlgEquiv.symm_apply_eq, adeleTensorEquiv_tmul, map_one, mul_one]
  change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
    ((adeleTensorEquiv F E).symm (algebraMap E 𝔸[E] x))) = _
  rw [h, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul, map_one, map_one, mul_one]
  rfl

private theorem rat_of_map (a : 𝔸[F]) (x : E) (h : adeleMap F E a = algebraMap E 𝔸[E] x) :
    ∃ y : F, algebraMap F 𝔸[F] y = a := by
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F E)
    (LinearMap.ker_eq_bot.2 (algebraMap F E).injective)
  have h1 : φ 1 = 1 := by simpa using LinearMap.congr_fun hφ 1
  have h2 : (1 : E) ⊗ₜ[F] a = x ⊗ₜ[F] (1 : 𝔸[F]) := by
    apply (adeleTensorEquiv F E).injective
    rw [adeleTensorEquiv_tmul, adeleTensorEquiv_tmul, map_one, map_one, one_mul, mul_one, h]
  have h3 := congrArg (fun z => TensorProduct.lid F 𝔸[F] (LinearMap.rTensor 𝔸[F] φ z)) h2
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, h1, one_smul] at h3
  exact ⟨φ x, by rw [h3, Algebra.algebraMap_eq_smul_one]⟩

private theorem mat_rat {n : ℕ} (t : AdelicGLn.AdelicGL F n) (h : GL (Fin n) E)
    (e : mapGL n (adeleMap F E) t = AdelicGLn.diagonal E n h) :
    ∃ M : Matrix (Fin n) (Fin n) F, (algebraMap F 𝔸[F]).mapMatrix M = (t : Matrix (Fin n) (Fin n) 𝔸[F]) := by
  have : ∀ i j, ∃ y : F, algebraMap F 𝔸[F] y = (t : Matrix (Fin n) (Fin n) 𝔸[F]) i j := fun i j =>
    rat_of_map _ ((h : Matrix (Fin n) (Fin n) E) i j)
      (congrArg (fun u : AdelicGLn.AdelicGL E n => (u : Matrix (Fin n) (Fin n) 𝔸[E]) i j) e)
  choose M hM using this
  exact ⟨Matrix.of M, Matrix.ext hM⟩
end

theorem UpperTheory.adelicGL_galois_baseChange_diagonal_compat :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ),
        (∀ h : GL (Fin n) E, mapGL n (galAd σ) (AdelicGLn.diagonal E n h) = AdelicGLn.diagonal E n (sigmaGL σ h)) ∧
        (∀ g : GL (Fin n) F, mapGL n (adeleMap F E) (AdelicGLn.diagonal F n g) = AdelicGLn.diagonal E n (incl g)) ∧
        ∀ (t : AdelicGLn.AdelicGL F n) (h : GL (Fin n) E), mapGL n (adeleMap F E) t = AdelicGLn.diagonal E n h →
          ∃ g : GL (Fin n) F, t = AdelicGLn.diagonal F n g := by
  intro F E _ _ _ _ _ σ n
  refine ⟨fun h => ?_, fun g => ?_, fun t h e => ?_⟩
  · refine Units.ext (Matrix.ext fun i j => ?_)
    exact galAd_alg σ (h.1 i j)
  · refine Units.ext (Matrix.ext fun i j => ?_)
    exact adeleMap_algebraMap (K := F) (L := E) (g.1 i j)
  · obtain ⟨M, hM⟩ := mat_rat t h e
    obtain ⟨N, hN⟩ := mat_rat t⁻¹ h⁻¹ (by rw [map_inv, map_inv, e])
    have hinj : Function.Injective ((algebraMap F 𝔸[F]).mapMatrix : Matrix (Fin n) (Fin n) F →+* _) :=
      Matrix.map_injective (AdeleRing.algebraMap_injective (𝓞 F) F)
    refine ⟨⟨M, N, hinj ?_, hinj ?_⟩, Units.ext hM.symm⟩
    · rw [map_mul, hM, hN, map_one, Units.mul_inv]
    · rw [map_mul, hM, hN, map_one, Units.inv_mul]
