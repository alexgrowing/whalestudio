import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleIntegralInterchangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerHaarAdelicStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
open scoped Classical
namespace GlobalTheory.ConeWeilComm

theorem eval_mem_adm (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • (BoundedContinuousFunction.evalCLM ℂ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  rw [mul_comm]

theorem weil_cone_comm : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h h₁,
        ∀ g y, om₁' (g, h₁) (cone B G.M' om' e' K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (om' (1, h) Φ')) y =
          ∫ k, ∫ l, om₁' (g, h₁) (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))) y * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1) ∂μ ∂μK := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h h₁ g y
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  have hKc : IsCompact (K : Set (UA σ G.V'.J)) :=
    GlobalTheory.StabCpt.isCompact_of_isStab hKP F E σ B (b + 2) G.V' G.q (b + 2 - G.q) K hT.base hT.geo.hV' hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  haveI : IsFiniteMeasure μK := inferInstance
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : SecondCountableTopology (AE F E) := eh.secondCountableTopology
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (AE F E)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology (Matrix (Fin (b + 2)) (Fin (b + 2)) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin (b + 2) → Fin (b + 2) → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin (b + 2)) (Fin (b + 2)) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin (b + 2)) (AE F E)) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology K := inferInstance
  obtain ⟨r, gg, f, hg, hdec, hcont, hdom⟩ :=
    GlobalTheory.T.config_b_stabilizer_haar_adelic hKP F E σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h
  have hW : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G₁.V'.J) (incM F G₁.W.J) G₁.M'.co X.α (X.α / X.β) om₁' :=
    hT₁.weil'
  set L : Fn F b (a + b) →ₗ[ℂ] ℂ := (LinearMap.proj y : Fn F b (a + b) →ₗ[ℂ] ℂ) ∘ₗ om₁' (g, h₁) with hLdef
  have hL : L ∈ (adeleClass F).adm (Fin b × Fin (a + b)) :=
    hW.isUSplitting.adm (g, h₁) _ (eval_mem_adm F _ y)
  have hmul : ∀ k : K, om' (k.1, 1) (om' (1, h) Φ') = om' (k.1, h) Φ' := by
    intro k
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  have hfun : cone B G.M' om' e' K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (om' (1, h) Φ') =
      fun y => ∫ k, ∫ l, ∑ j, pureA F (f j k l) (gg j) y ∂μ ∂μK := by
    funext y'
    simp only [cone, hmul, hdec]
  have hsum : ∀ (k : K) (l : (AE F E)ˣ), (∑ j, pureA F (f j k l) (gg j)) =
      ((X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) •
        e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ')) := by
    intro k l
    funext y'
    rw [Finset.sum_apply, ← hdec, Pi.smul_apply, smul_eq_mul]
    ring
  show L (cone B G.M' om' e' K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (om' (1, h) Φ')) = _
  rw [hfun, GlobalTheory.T.admissible_integral_interchange F _ K (AE F E)ˣ μK μ r gg f hg hcont hdom L hL]
  congr 1
  funext k
  congr 1
  funext l
  rw [hsum, map_smul, smul_eq_mul, hLdef, LinearMap.comp_apply, LinearMap.proj_apply]
  ring

end GlobalTheory.ConeWeilComm
