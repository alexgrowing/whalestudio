import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.WeilM

noncomputable section

namespace GlobalTheory.ThK.SqIntCont

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem polData_le_schA {B : Base F E} {M : Model σ X W} (hM : M.IsGood B.ψ) :
    PolData B M ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, -, φ, hSB, hev, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hM.std).mono fun v hv => hv.1.trans hv.2)

theorem theta_add (om : Rep σ X W) (hpres : ∀ p, ∀ Φ ∈ schA F (Fin n × Fin d), om p Φ ∈ schA F (Fin n × Fin d))
    {Φ Ψ : (Fin n × Fin d → AF F) → ℂ} (hΦ : Φ ∈ schA F _) (hΨ : Ψ ∈ schA F _) (g : UA σ X.J) (h : UA σ W.J) :
    theta om (Φ + Ψ) g h = theta om Φ g h + theta om Ψ g h := by
  simp only [theta, thetaSum, map_add, Pi.add_apply]
  exact (summable_of_mem_schA F (hpres _ _ hΦ)).tsum_add (summable_of_mem_schA F (hpres _ _ hΨ))

theorem theta_smul (om : Rep σ X W) (z : ℂ) (Φ : (Fin n × Fin d → AF F) → ℂ) (g : UA σ X.J) (h : UA σ W.J) :
    theta om (z • Φ) g h = z * theta om Φ g h := by
  simp only [theta, thetaSum, map_smul, Pi.smul_apply, smul_eq_mul]
  exact tsum_mul_left

theorem continuous_I (M : Model σ X W) (om : Rep σ X W) (hcont : IsContOn (adeleClass F) om)
    (hpres : ∀ p, ∀ Φ ∈ schA F (Fin n × Fin d), om p Φ ∈ schA F (Fin n × Fin d))
    (hconv : ∀ Φ ∈ schA F (Fin n × Fin d), M.Conv om Φ)
    (hreal : ∀ φ ∈ SB (Fin n × Fin d → Af F), ∀ h, Continuous fun f : SInf F (Fin n × Fin d) => M.I om (pureA F f φ) h)
    {Φ : (Fin n × Fin d → AF F) → ℂ} (hΦ : Φ ∈ schA F _) : Continuous (M.I om Φ) := by
  rw [continuous_iff_continuousAt]
  intro h0
  let L0 : schA F (Fin n × Fin d) →ₗ[ℂ] ℂ :=
    { toFun := fun Ψ => M.I om Ψ.1 h0
      map_add' := fun Ψ Ψ' => by
        simp only [Submodule.coe_add, Model.I]
        rw [← integral_add (hconv _ Ψ.2 h0) (hconv _ Ψ'.2 h0)]
        exact integral_congr_ae (Filter.Eventually.of_forall fun g => theta_add om hpres Ψ.2 Ψ'.2 g h0)
      map_smul' := fun z Ψ => by
        simp only [Submodule.coe_smul, Model.I, RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun g => theta_smul om z _ g h0) }
  obtain ⟨L, hL⟩ := LinearMap.exists_extend L0
  have hLe : ∀ Ψ (hΨ : Ψ ∈ schA F (Fin n × Fin d)), L Ψ = M.I om Ψ h0 := fun Ψ hΨ => by
    have := congrArg (fun T => T ⟨Ψ, hΨ⟩) hL
    simpa [L0] using this
  have hadm : L ∈ (adeleClass F).adm (Fin n × Fin d) := by
    intro φ hφ
    have hm : ∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ schA F (Fin n × Fin d) :=
      fun f => Submodule.subset_span ⟨f, φ, hφ, rfl⟩
    refine ⟨{ toFun := fun f => L (pureA F f φ), map_add' := ?_, map_smul' := ?_, cont := ?_ }, fun f => rfl⟩
    · intro f f'
      rw [← map_add]
      congr 1
      funext x
      simp [pureA, add_mul]
    · intro z f
      rw [RingHom.id_apply, ← map_smul]
      congr 1
      funext x
      simp [pureA, mul_assoc]
    · exact (hreal φ hφ h0).congr fun f => (hLe _ (hm f)).symm
  have key : ∀ h, M.I om Φ h = L (om (1, h0⁻¹ * h) Φ) := fun h => by
    rw [hLe _ (hpres _ _ hΦ)]
    simp only [Model.I, theta]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have e : om (g, h) = om (g, h0) * om (1, h0⁻¹ * h) := by
      rw [← map_mul]
      simp
    simp only [e, Module.End.mul_apply]
  have hc : Continuous fun h : UA σ W.J => L (om (1, h0⁻¹ * h) Φ) :=
    (hcont L hadm Φ hΦ).comp (continuous_const.prodMk (continuous_const.mul continuous_id))
  exact (hc.congr fun h => (key h).symm).continuousAt

end GlobalTheory.ThK.SqIntCont

namespace GlobalTheory.ThK.SquareIntegrability

open GlobalTheory.ThK.SqIntCont

theorem continuous_I_toGAd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
      Continuous (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc _ Φ hΦ
  have hP := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1
  have hW := GlobalTheory.T.weil_convergence_of_kernel hKP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hP
    (Or.inl (GlobalTheory.ThK.Check.conv_range hT.geo))
  have hS : Φ ∈ schA F (Fin a × Fin (a + a')) := polData_le_schA hT.geo.hM hΦ
  have hcI : Continuous (G.M.I om Φ) :=
    continuous_I G.M om hT.weil.2.2 (IsUWeilPair.isUSplitting hT.weil).pres (fun Ψ hΨ => (hW.1 Ψ hΨ).1) hW.2 hS
  refine hcI.comp ?_
  exact continuous_subtype_val.subtype_mk _

end GlobalTheory.ThK.SquareIntegrability
