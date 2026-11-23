import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.OneSubEvTInvInt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryApproxFin

open NumberField PI.UJClassFin PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Apx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem Psi_sigR (v : HeightOneSpectrum (𝓞 F)) (x : Af F ⊗[F] E) :
    Psi v (PI.UJClassFin.sigR (Af F) σ x) = PI.UnitaryApproxDefs.sigR σ (Fv F v) (Psi v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have e1 : PI.UJClassFin.sigR (Af F) σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by simp [PI.UJClassFin.sigR]
    rw [e1, Psi_tmul, Psi_tmul]
    simp [PI.UnitaryApproxDefs.sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem Psi_inclR (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    Psi v (inclR (F := F) (Af F) e) = PI.UnitaryApproxDefs.inclE (F := F) (Fv F v) e := by
  show Psi v ((1 : Af F) ⊗ₜ[F] e) = e ⊗ₜ[F] (1 : Fv F v)
  rw [Psi_tmul]; rfl

def finU (g : HA (AF F) σ J) : GL (Fin M) (Af F ⊗[F] E) :=
  ⟨finMat σ J g, finMat σ J g⁻¹, by rw [← finMat_mul, mul_inv_cancel, finMat_one],
    by rw [← finMat_mul, inv_mul_cancel, finMat_one]⟩

def gLoc (g : HA (AF F) σ J) (v : HeightOneSpectrum (𝓞 F)) : GL (Fin M) (E ⊗[F] Fv F v) :=
  Units.map ((Psi (E := E) v).toRingHom.mapMatrix : Matrix (Fin M) (Fin M) (Af F ⊗[F] E) →+*
    Matrix (Fin M) (Fin M) (E ⊗[F] Fv F v)).toMonoidHom (finU σ J g)

theorem gLoc_val (g : HA (AF F) σ J) (v : HeightOneSpectrum (𝓞 F)) :
    ((gLoc σ J g v : GL (Fin M) (E ⊗[F] Fv F v)) : Matrix (Fin M) (Fin M) (E ⊗[F] Fv F v)) =
      (finMat σ J g).map (Psi v) := rfl

theorem gLoc_mem (g : HA (AF F) σ J) (v : HeightOneSpectrum (𝓞 F)) :
    gLoc σ J g v ∈ PI.UnitaryApproxDefs.UPts σ J (Fv F v) := by
  show PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (Fv F v)) ((gLoc σ J g v : GL (Fin M) (E ⊗[F] Fv F v)) : Matrix (Fin M) (Fin M) _) *
      J.map (PI.UnitaryApproxDefs.inclE (F := F) (Fv F v)) * ((gLoc σ J g v : GL (Fin M) (E ⊗[F] Fv F v)) : Matrix (Fin M) (Fin M) _) =
    J.map (PI.UnitaryApproxDefs.inclE (F := F) (Fv F v))
  rw [gLoc_val]
  have hU := congrArg (fun X => X.map (Psi (E := E) v)) (finMat_unitary σ J g)
  beta_reduce at hU
  rw [mapAlg_mul, mapAlg_mul] at hU
  have hcT : ∀ X : Matrix (Fin M) (Fin M) (Af F ⊗[F] E),
      (PI.UJClassFin.cT (PI.UJClassFin.sigR (Af F) σ) X).map (Psi v) = PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (Fv F v)) (X.map (Psi v)) := by
    intro X; ext i j; simp [PI.UJClassFin.cT, PI.UnitaryApproxDefs.cT, Psi_sigR]
  have hJ : (JR (Af F) J).map (Psi (E := E) v) = J.map (PI.UnitaryApproxDefs.inclE (F := F) (Fv F v)) := by
    ext i j; simp [JR, Psi_inclR]
  rw [hcT, hJ] at hU
  exact hU

theorem approxT (hσσ : ∀ e, σ (σ e) = e) (hθ : ∃ θ, σ θ ≠ θ) (hH : PI.UnitaryApproxDefs.IsHerm (σ : E →+* E) J)
    (hdet : IsUnit J.det) (g : HA (AF F) σ J) (T : Finset (HeightOneSpectrum (𝓞 F))) (N0 : ℕ)
    (hN0 : 0 < N0) :
    ∃ γ : PI.UJClassFin.UJ (σ : E →+* E) J, ∀ i j, ∃ o ∈ Oh F E,
      (evT (T : Set (HeightOneSpectrum (𝓞 F))) ⊗ₜ[F] (1 : E)) *
        (finMat σ J g i j - inclR (F := F) (Af F) (((γ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) i j)) =
        N0 • o := by
  classical
  have hD : ((N0 : 𝓞 F)) ≠ 0 := by exact_mod_cast hN0.ne'
  obtain ⟨γ, hγ, hc⟩ := unitary_approximation_finite F E (Fin M) σ J hσσ hθ hH hdet T
    (fun w => gLoc σ J g w) (fun w _ => gLoc_mem σ J g w) (N0 : 𝓞 F) hD
  refine ⟨⟨γ, hγ⟩, fun i j => ?_⟩
  show ∃ o ∈ Oh F E, (evT (T : Set (HeightOneSpectrum (𝓞 F))) ⊗ₜ[F] (1 : E)) *
        (finMat σ J g i j - inclR (F := F) (Af F) ((γ : Matrix (Fin M) (Fin M) E) i j)) = N0 • o
  have hc' : ∀ w : T, ∃ s ∈ PI.UnitaryApproxDefs.tensInt (F := F) (Fv F w.1) (PI.UnitaryApproxDefs.intOE E) (w.1.adicCompletionIntegers F).toSubring,
      Psi w.1 (finMat σ J g i j) - PI.UnitaryApproxDefs.inclE (F := F) (Fv F w.1) ((γ : Matrix (Fin M) (Fin M) E) i j) =
        PI.UnitaryApproxDefs.inclE (F := F) (Fv F w.1) (algebraMap F E ((N0 : 𝓞 F) : F)) * s := fun w => hc w.1 w.2 i j
  choose s hs hse using hc'
  refine ⟨∑ w : T, (sgl w.1 1 ⊗ₜ[F] (1 : E)) * Phi w.1 (s w),
    AddSubgroup.sum_mem _ fun w _ => Oh_mul (tmul_mem_Oh (sgl_int _ (one_mem _)) isIntegral_one) (Phi_int _ (hs w)), ?_⟩
  rw [evT_eq_sum, TensorProduct.sum_tmul, Finset.sum_mul, ← Finset.sum_coe_sort T, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Phi_Psi, map_sub, Psi_inclR, hse w, Phi_mul, Phi_inclE]
  have e0 : ((N0 : 𝓞 F) : F) = (N0 : F) := by simp
  have e1 : sgl w.1 1 ⊗ₜ[F] (algebraMap F E ((N0 : 𝓞 F) : F)) = N0 • (sgl w.1 1 ⊗ₜ[F] (1 : E)) := by
    rw [e0, show algebraMap F E (N0 : F) = (N0 : F) • (1 : E) by rw [Algebra.smul_def, mul_one],
      TensorProduct.tmul_smul, Nat.cast_smul_eq_nsmul]
  rw [e1, smul_mul_assoc]

end Apx

end PI.UnitaryGroupMassFormula.UJClassMass
