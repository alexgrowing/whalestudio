import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOpInfMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionMapsSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryLocallyCompactHausdorff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeaklyConvergentSchwartzBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakBoundedSchwartzTendstoStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.ThK.WeilCont

theorem continuousOn_of_weak {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {X : Type} [TopologicalSpace X] [FirstCountableTopology X] {φ : X → SchwartzMap V ℂ} {s : Set X}
    (h : ∀ T : SchwartzMap V ℂ →L[ℂ] ℂ, ContinuousOn (fun x => T (φ x)) s) : ContinuousOn φ s := by
  intro x hx
  refine tendsto_of_seq_tendsto fun u hu => ?_
  have hw : ∀ T : SchwartzMap V ℂ →L[ℂ] ℂ, Tendsto (fun j => T ((φ ∘ u) j)) atTop (𝓝 (T (φ x))) :=
    fun T => (h T x hx).tendsto.comp hu
  exact GlobalTheory.T.weak_bounded_schwartz_tendsto _ _ hw (GlobalTheory.T.weakly_convergent_schwartz_bounded _ _ hw)

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def archPt (y : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => GlobalTheory.HeisSchA.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) 0

theorem at_archPt (y : κ → mixedEmbedding.mixedSpace F) : At (evI F) (archPt y) :=
  fun u hu => funext fun i => GlobalTheory.HeisSchA.at_mk _ u hu

theorem evI_archPt (y : κ → mixedEmbedding.mixedSpace F) : (fun i => evI F (archPt y i)) = y :=
  funext fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

def coeLin : SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) where
  toFun f := ⇑f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ker_coeLin : LinearMap.ker (coeLin (F := F) (κ := κ)) = ⊥ :=
  LinearMap.ker_eq_bot.2 fun _ _ h => DFunLike.coe_injective h

theorem exists_adm (T : SInf F κ →L[ℂ] ℂ) : ∃ l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm κ ∧
    ∀ (f : SInf F κ) (r : (κ → AF F) → ℂ), (∀ x z, At (evI F) z → r (x + z) = r x) →
      l (tens (evI F) (⇑f) r) = r 0 * T f := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ (ker_coeLin (F := F) (κ := κ))
  have hgf : ∀ f : SInf F κ, g ⇑f = f := fun f => LinearMap.congr_fun hg f
  let l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ := (T : SInf F κ →ₗ[ℂ] ℂ) ∘ₗ g ∘ₗ LinearMap.funLeft ℂ ℂ (archPt (F := F))
  have key : ∀ (f : SInf F κ) (c : ℂ) (Φ : (κ → AF F) → ℂ), (∀ y, Φ (archPt y) = c * f y) → l Φ = c * T f := by
    intro f c Φ hΦ
    have e : LinearMap.funLeft ℂ ℂ (archPt (F := F)) Φ = ⇑(c • f) := funext fun y => by
      rw [LinearMap.funLeft_apply, hΦ, SchwartzMap.smul_apply, smul_eq_mul]
    simp only [l, LinearMap.comp_apply, e, hgf, ContinuousLinearMap.coe_coe, map_smul, smul_eq_mul]
  refine ⟨l, fun φ hφ => ⟨φ 0 • T, fun f => ?_⟩, fun f r hr => ?_⟩
  · rw [key f (φ 0) _ fun y => ?_]
    · rfl
    · simp only [pureA]
      rw [mul_comm]
      congr 1
      exact congrArg f (evI_archPt y)
  · refine key f (r 0) _ fun y => ?_
    have hrz : r (archPt y) = r 0 := by simpa using hr 0 _ (at_archPt y)
    simp only [tens]
    rw [evI_archPt, hrz, mul_comm]

end GlobalTheory.ThK.WeilCont

namespace GlobalTheory.ThK.WeilCont

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem weak_cont (B : Base F E) {a a' : ℕ} (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (hT : IsTriple B G X om om')
    (hacts : ∀ g ∈ UAt σ G.V' (evI F), ∀ f : SInf F (Fin a' × Fin (a + a')), ∃ f₁ : SInf F (Fin a' × Fin (a + a')),
      Acts (evI F) (om' (g, 1)) f f₁)
    (f : SInf F (Fin a' × Fin (a + a'))) (T : SInf F (Fin a' × Fin (a + a')) →L[ℂ] ℂ) :
    ContinuousOn (fun g => T (locOpInf (om' (g, 1)) f)) (UAt σ G.V' (evI F)) := by
  obtain ⟨r, h0, hr⟩ := exists_rest_inf F (Fin a' × Fin (a + a'))
  obtain ⟨l, hl, hlT⟩ := exists_adm T
  have hc : Continuous fun g : UA σ G.V'.J => l (om' (g, 1) (tens (evI F) (⇑f) r)) :=
    (hT.weil'.2.2 l hl _ (hr f).2).comp (continuous_id.prodMk continuous_const)
  refine (hc.continuousOn.const_smul (r 0)⁻¹).congr fun g hg => ?_
  change T (locOpInf (om' (g, 1)) f) = (r 0)⁻¹ • l (om' (g, 1) (tens (evI F) (⇑f) r))
  rw [acts_locOpInf (hacts g hg f) r (hr f), hlT (locOpInf (om' (g, 1)) f) r (hr f).1, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]

theorem weilcont : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ f : SInf F (Fin a' × Fin (a + a')), ContinuousOn (fun g => locOpInf (om' (g, 1)) f) (UAt σ G.V' (evI F)) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT f
  haveI : SecondCountableTopology (UA σ G.V'.J) := (GlobalTheory.AdelicUnitaryTop.lcsc_UA F E σ a' G.V'.J).2.1
  haveI : FirstCountableTopology (UA σ G.V'.J) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  exact continuousOn_of_weak fun T => weak_cont B G X om om' hT
    (GlobalTheory.T.weil_action_maps_schwartz hP F E σ a' (a + a') G.V' G.W G.M' B.ψ X.α (X.α / X.β) om' hT.base.cm hT.base.std hT.weil') f T

end GlobalTheory.ThK.WeilCont
