import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaFamilyNormalisedAtStandardPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationTransportIsometryStatement
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWAPlaces
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntEasy
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.FinalEq
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.ThLoc.AllPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem tPull_comp (γ₁ γ₂ : Matrix (Fin N) (Fin N) D.host.E) (γ₁' γ₂' : Matrix (Fin N') (Fin N') D.host.E)
    (z : TaylorLogMetric.VC D N N') :
    Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) γ₂ γ₂' (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) γ₁ γ₁' z) =
      Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (γ₁ * γ₂) (γ₁' * γ₂') z := by
  funext τ
  show (Matrix.conjTranspose (γ₂'.map (TaylorLogMetric.embT D τ)) *
      (Matrix.conjTranspose (γ₁'.map (TaylorLogMetric.embT D τ)) * Matrix.of (z τ) * γ₁.map (TaylorLogMetric.embT D τ)) *
      γ₂.map (TaylorLogMetric.embT D τ) : Matrix _ _ ℂ) =
    (Matrix.conjTranspose ((γ₁' * γ₂').map (TaylorLogMetric.embT D τ)) * Matrix.of (z τ) * (γ₁ * γ₂).map (TaylorLogMetric.embT D τ) : Matrix _ _ ℂ)
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem tPull_one (z : TaylorLogMetric.VC D N N') :
    Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (1 : Matrix (Fin N) (Fin N) D.host.E)
      (1 : Matrix (Fin N') (Fin N') D.host.E) z = z := by
  funext τ
  show (Matrix.conjTranspose ((1 : Matrix (Fin N') (Fin N') D.host.E).map (TaylorLogMetric.embT D τ)) * Matrix.of (z τ) *
      (1 : Matrix (Fin N) (Fin N) D.host.E).map (TaylorLogMetric.embT D τ) : Matrix _ _ ℂ) = z τ
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one]
  rfl

theorem smulLat_star_smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (hγ : star γ * γ = 1)
    (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) :
    SDLat.smulLat (star γ) (SDLat.smulLat γ M) = M := by
  unfold SDLat.smulLat
  rw [← Submodule.map_comp]
  have h : ((Matrix.toLin' (star γ)).restrictScalars (𝓞 D.host.E)).comp ((Matrix.toLin' γ).restrictScalars (𝓞 D.host.E)) =
      LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    show Matrix.toLin' (star γ) (Matrix.toLin' γ x) = x
    rw [← Matrix.toLin'_mul_apply, hγ, Matrix.toLin'_one, LinearMap.id_apply]
  rw [h, Submodule.map_id]

theorem mem_La_smulLat_iff (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E)
    (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (x : TaylorLogMetric.VC D N N') :
    x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M') ↔
      Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
        (γ' : Matrix (Fin N') (Fin N') D.host.E) x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) M M' := by
  have h1 : star (γ : Matrix (Fin N) (Fin N) D.host.E) * γ = 1 := Matrix.mem_unitaryGroup_iff'.mp γ.2
  have h1' : star (γ' : Matrix (Fin N') (Fin N') D.host.E) * γ' = 1 := Matrix.mem_unitaryGroup_iff'.mp γ'.2
  have h2 : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ.2
  have h2' : (γ' : Matrix (Fin N') (Fin N') D.host.E) * star (γ' : Matrix (Fin N') (Fin N') D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ'.2
  constructor
  · intro hx
    exact Formalism.L2.KerInert.ie_La_pull cc δ _ _ h1' M M' hx
  · intro hx
    have h3 : star (star (γ' : Matrix (Fin N') (Fin N') D.host.E)) * star (γ' : Matrix (Fin N') (Fin N') D.host.E) = 1 := by
      rw [star_star]; exact h2'
    have h := Formalism.L2.KerInert.ie_La_pull cc δ (star (γ : Matrix (Fin N) (Fin N) D.host.E))
      (star (γ' : Matrix (Fin N') (Fin N') D.host.E)) h3 (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
      (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M')
    rw [smulLat_star_smulLat _ h1, smulLat_star_smulLat _ h1'] at h
    have h4 := h hx
    rw [AddSubgroup.mem_comap] at h4
    have e : Formalism.L2.KerInert.ieTPullHom cc δ (star (γ : Matrix (Fin N) (Fin N) D.host.E))
        (star (γ' : Matrix (Fin N') (Fin N') D.host.E))
        (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
          (γ' : Matrix (Fin N') (Fin N') D.host.E) x) = x := by
      show Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ x) = x
      rw [tPull_comp, h2, h2', tPull_one]
    rw [e] at h4
    exact h4

end GlobalTheory.ThLoc.AllPlaces

namespace GlobalTheory.ThLoc.AllPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem formV_eq_Hf (u v : TaylorLogMetric.VC D N N') :
    formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N' u v = TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) u v := rfl

def tPullLin (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N' where
  toFun := Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) γ γ'
  map_add' := Formalism.L2.KerInert.ie_tPull_add cc δ γ γ'
  map_smul' := Formalism.L2.KerInert.ie_tPull_smul cc δ γ γ'

def tPullEquiv (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix.unitaryGroup (Fin N) D.host.E)
    (γ' : Matrix.unitaryGroup (Fin N') D.host.E) : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N' :=
  LinearEquiv.ofLinearMap (tPullLin cc δ (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E))
    (tPullLin cc δ (star (γ : Matrix (Fin N) (Fin N) D.host.E)) (star (γ' : Matrix (Fin N') (Fin N') D.host.E)))
    (LinearMap.ext fun z => by
      show Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ z) = z
      rw [tPull_comp, Matrix.mem_unitaryGroup_iff'.mp γ.2, Matrix.mem_unitaryGroup_iff'.mp γ'.2, tPull_one])
    (LinearMap.ext fun z => by
      show Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ z) = z
      rw [tPull_comp, Matrix.mem_unitaryGroup_iff.mp γ.2, Matrix.mem_unitaryGroup_iff.mp γ'.2, tPull_one])

end GlobalTheory.ThLoc.AllPlaces

open GlobalTheory.ThLoc.AllPlaces in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem GlobalTheory.ThLoc.latAt_all : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (X : Fields) (s : Seam D X), s.Ok → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TaylorLogMetric.admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ D.host.d ha hd lam hlam (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF B.tor L L') (fun z => B.eNat χ N N' L L' (s.flatV N N' z)) p ι := by
  intro D cc δ hcc hδ B χ hχ X s hs a₀ b₀ c₀ ha hd lam hlam hcm hlat N N' L L' hA p _ ι
  have hp : p.Prime := Fact.out
  have hCM : PI.UG.IsCMUnram D.host.E := D.sp.cm.cmUnram
  obtain ⟨hN, hN', hL, hL'⟩ := hA
  obtain ⟨γ, M, hM, hEq, hLM⟩ := Formalism.L2.KerInert.wa_main Formalism.L2.KerInert.weak_approximation_places hCM p hp N L hL
  obtain ⟨γ', M', hM', hEq', hLM'⟩ := Formalism.L2.KerInert.wa_main Formalism.L2.KerInert.weak_approximation_places hCM p hp N' L' hL'
  have hAM : TaylorLogMetric.admitted D N N' M M' := ⟨hN, hN', hM, hM'⟩
  have hAL : TaylorLogMetric.admitted D N N' L L' := ⟨hN, hN', hL, hL'⟩
  have hStd := GlobalTheory.T.normalisedThetaFamily_normalised_at_standardPrime D cc δ hcc hδ B χ hχ X s hs a₀ b₀ c₀ ha hd lam hlam hcm hlat N N' M M' hAM p ι hEq hEq'

  let φ : (DVar X.Tau N N' → ℂ) ≃ₗ[ℂ] (DVar X.Tau N N' → ℂ) :=
    (s.flatV N N').trans ((tPullEquiv cc δ γ γ').trans (s.flatV N N').symm)
  have hφ : ∀ z, s.flatV N N' (φ z) = Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
      (γ' : Matrix (Fin N') (Fin N') D.host.E) (s.flatV N N' z) := fun z => by
    show s.flatV N N' ((s.flatV N N').symm (tPullEquiv cc δ γ γ' (s.flatV N N' z))) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hI : IsIsom (matH (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹))
      (matH (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹)) (φ : (DVar X.Tau N N' → ℂ) →ₗ[ℂ] _) := by
    intro x y
    show matH _ (φ x) (φ y) = _
    rw [KS.Lat.form_flat s, KS.Lat.form_flat s, hφ, hφ, formV_eq_Hf, formV_eq_Hf,
      Formalism.L2.KerInert.PullbackComparison.Hf_tPull cc δ _ _ (Matrix.mem_unitaryGroup_iff.mp γ.2) (Matrix.mem_unitaryGroup_iff.mp γ'.2)]
  have hloc := GlobalTheory.T.localNormalisation_transport_isometry a₀ b₀ D.host.d ha hd lam hlam (DVar X.Tau N N') _ (s.laF B.tor M M')
    (fun z => B.eNat χ N N' M M' (s.flatV N N' z)) p ι φ hI hStd.locNorm
  have hΛ : (s.laF B.tor M M').comap (φ : (DVar X.Tau N N' → ℂ) →ₗ[ℂ] _).toAddMonoidHom = s.laF B.tor L L' := by
    ext x
    show s.flatV N N' (φ x) ∈ TaylorLogMetric.La D B.tor M M' ↔ s.flatV N N' x ∈ TaylorLogMetric.La D B.tor L L'
    rw [hφ, hLM, hLM']
    exact (mem_La_smulLat_iff γ γ' M M' _).symm
  have hθ : (fun z => B.eNat χ N N' M M' (s.flatV N N' (φ z))) = fun z => B.eNat χ N N' L L' (s.flatV N N' z) := by
    funext z
    rw [hφ, hLM, hLM']
    have h := (Formalism.L2.PairingIndexBounds.Eq.SqG.eulerProduct_eq_of_curve_ideal B hcc hδ χ hχ).1 N N' ⟨M, hM⟩ ⟨M', hM'⟩ hN hN' γ γ'
    exact congrFun h (s.flatV N N' z)
  rw [hΛ] at hloc
  simp only [hθ] at hloc
  exact ⟨hcm, KS.Lat.selfDual_laF s B hcc hδ hAL, fun x hx => KS.Lat.theta_laF s B (KS.Lat.odd_of_cmOK hcm) hx,
    KS.Lat.eNat_laF s B hcc hδ χ hAL, hloc⟩
