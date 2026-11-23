import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.WeilBound.ThetaLifts.FrameEstimates.CuspRapid
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.TendstoIndMul
import Development.WeilBound.ThetaLifts.LatticeBasics.PolFin
import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
import Development.WeilBound.ThetaLifts.LatticeBasics.PairsL

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions

open UpperTheory.TP

theorem UpperTheory.theta_lift_equivariant :
    Tools → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), IsPair B M χX χW om n 0 d 0 → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ φ : UA σ X.J → ℂ, IsFn φ → ∀ (a : UA σ X.J) (b h : UA σ W.J), lift M om (om (a, b) Φ) (fun y => φ (y * a)) h = lift M om Φ φ (h * b) := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om hp Φ hΦ φ hφ a b h
  have c : Cpt σ X.J := T.cpt F E σ B n X n 0 hp.base (Or.inl hp.herm) (by simp)
  have hTB := T.basic F E σ B n d X W M χX χW om n 0 d 0 hp
  let G : UA σ X.J → ℂ := fun x => theta om Φ x (h * b) * star (φ x)
  have hinv : ∀ γ ∈ ratU σ X.J, ∀ x, G (γ * x) = G x := by
    intro γ hγ x
    have h1 := (hTB.1 Φ hΦ).2.1 γ hγ 1 (one_mem _) x (h * b)
    rw [one_mul] at h1
    simp only [G]
    rw [h1, hφ.2 γ hγ x]
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := hp.good.haar
  haveI : M.μ.IsMulRightInvariant := c.right _ hp.good.haar
  haveI := c.cnt
  haveI : MeasurableConstSMul (ratU σ X.J) (UA σ X.J) := ⟨fun c => measurable_const_mul (c : UA σ X.J)⟩
  haveI : SMulInvariantMeasure (ratU σ X.J) (UA σ X.J) M.μ :=
    ⟨fun c s _ => measure_preimage_mul M.μ (c : UA σ X.J) s⟩
  have hL : lift M om (om (a, b) Φ) (fun y => φ (y * a)) h = ∫ x in M.dom, G (x * a) ∂M.μ := by
    unfold lift
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [G, theta]
    rw [← Module.End.mul_apply, ← map_mul]
    rfl
  have hmp := measurePreserving_mul_right M.μ a
  have h1 := hmp.setIntegral_preimage_emb (measurableEmbedding_mulRight a) G
    ((fun x : UA σ X.J => x * a⁻¹) ⁻¹' M.dom)
  have hpre : (fun x : UA σ X.J => x * a) ⁻¹' ((fun x : UA σ X.J => x * a⁻¹) ⁻¹' M.dom) = M.dom := by
    ext x; simp
  rw [hpre] at h1
  have hfd : IsFundamentalDomain (ratU σ X.J) ((fun x : UA σ X.J => x * a⁻¹) ⁻¹' M.dom) M.μ :=
    hp.good.dom.preimage_of_equiv (measurePreserving_mul_right M.μ a⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id (fun γ x => by
        show (γ.1 * x) * a⁻¹ = γ.1 * (x * a⁻¹)
        exact mul_assoc _ _ _)
  have h2 := hfd.setIntegral_eq hp.good.dom (f := G) (fun γ x => hinv γ.1 γ.2 x)
  rw [hL, h1, h2]
  rfl
