import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing TensorProduct

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem galAd_apply (σ : E ≃ₐ[F] E) (y : 𝔸[E]) : galAd σ y = σ • y := by
  have h : galAd σ = MulSemiringAction.toRingHom (E ≃ₐ[F] E) 𝔸[E] σ := by
    refine adeleRingHom_ext (K := F) (fun l => ?_) (fun a => ?_)
    · change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
        ((adeleTensorEquiv F E).symm (algebraMap E 𝔸[E] l))) = σ • algebraMap E 𝔸[E] l
      rw [adeleTensorEquiv_symm_algebraMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul,
        AdeleBaseChange.smul_algebraMap, map_one, map_one, mul_one]
      rfl
    · change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
        ((adeleTensorEquiv F E).symm (adeleMap F E a))) = σ • adeleMap F E a
      rw [adeleTensorEquiv_symm_adeleMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul,
        smul_adeleMap, map_one, map_one, one_mul]
      rfl
  rw [h]
  rfl

private theorem gal_diag (σ : E ≃ₐ[F] E) (n : ℕ) (h : GL (Fin n) E) :
    mapGL n (galAd σ) (AdelicGLn.diagonal E n h) = AdelicGLn.diagonal E n (sigmaGL σ h) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change galAd σ (algebraMap E 𝔸[E] (h.1 i j)) = algebraMap E 𝔸[E] (σ (h.1 i j))
  rw [galAd_apply, AdeleBaseChange.smul_algebraMap]

private noncomputable def thetaE (σ : E ≃ₐ[F] E) (n : ℕ) : Monoid.End (AdelicGLn.AdelicGL E n) :=
  mapGL n (galAd σ)

private theorem theta_pow_val (σ : E ≃ₐ[F] E) (n m : ℕ) (g : AdelicGLn.AdelicGL E n) (i j : Fin n) :
    ((((thetaE σ n ^ m) g :
        AdelicGLn.AdelicGL E n) : Matrix (Fin n) (Fin n) 𝔸[E]) i j) =
      (σ ^ m) • ((g : Matrix (Fin n) (Fin n) 𝔸[E]) i j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ_apply', pow_succ', mul_smul, ← ih, ← galAd_apply]
    rfl

private theorem theta_pow_eq_one [IsGalois F E] (σ : E ≃ₐ[F] E) (n : ℕ) :
    thetaE σ n ^ Module.finrank F E = 1 := by
  have hσ : σ ^ Module.finrank F E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank F E]
    exact pow_card_eq_one'
  have key : ∀ g : AdelicGLn.AdelicGL E n, (thetaE σ n ^ Module.finrank F E) g = g :=
    fun g => Units.ext (Matrix.ext fun i j => by rw [theta_pow_val, hσ, one_smul])
  exact MonoidHom.ext key

private theorem theta_pow_diag (σ : E ≃ₐ[F] E) (n m : ℕ) (h : GL (Fin n) E) :
    (thetaE σ n ^ m) (AdelicGLn.diagonal E n h) =
      AdelicGLn.diagonal E n (((sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ m) h) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ_apply', pow_succ_apply', ih]
    exact gal_diag σ n _

private theorem twNorm_diag (σ : E ≃ₐ[F] E) (n m : ℕ) (h : GL (Fin n) E) :
    twNorm (thetaE σ n) m (AdelicGLn.diagonal E n h) =
      AdelicGLn.diagonal E n (twNorm (sigmaGL σ) m h) := by
  induction m with
  | zero => rw [twNorm_zero, twNorm_zero, map_one]
  | succ m ih => rw [twNorm_succ, twNorm_succ, ih, theta_pow_diag, map_mul]

end

theorem UpperTheory.twNorm_conj_diagonal_eq_conj_normGL :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E) (n : ℕ) (δ : GL (Fin n) E) (x : AdelicGLn.AdelicGL E n),
        twNorm (G := AdelicGLn.AdelicGL E n) (mapGL n (galAd σ)) (Module.finrank F E) (x⁻¹ * AdelicGLn.diagonal E n δ * mapGL n (galAd σ) x) =
          x⁻¹ * AdelicGLn.diagonal E n (normGL σ δ) * x := by
  intro F E _ _ _ _ _ _ σ n δ x
  have h := twNorm_twConj_of_pow_eq_one (thetaE σ n) (theta_pow_eq_one σ n) x
    (AdelicGLn.diagonal E n δ)
  rw [twNorm_diag] at h
  exact h
