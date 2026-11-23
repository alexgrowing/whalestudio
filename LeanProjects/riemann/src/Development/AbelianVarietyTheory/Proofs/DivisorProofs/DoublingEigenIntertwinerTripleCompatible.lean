import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistribution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeTermCont

open scoped Classical

section Heis

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def schrLin [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ((κ → AdeleRing (𝓞 F) F) → ℂ) where
  toFun := schr ψ w
  map_add' := fun φ φ' => funext fun x => by simp only [schr, Pi.add_apply]; ring
  map_smul' := fun a φ => funext fun x => by
    simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem schrLin_comp_mem_adm [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsStd ψ)
    (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) (l : ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ℂ)
    (hl : l ∈ (adeleClass F).adm κ) : l ∘ₗ schrLin ψ w ∈ (adeleClass F).adm κ := by
  intro g hg
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F := e.toRingHom.comp p1
  let h : AdeleRing (𝓞 F) F := ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)
  let c : κ → mixedEmbedding.mixedSpace F := fun i => q (w.2 i)
  let t : κ → mixedEmbedding.mixedSpace F := fun i => q (w.1 i)
  let k : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (q h)
  let d : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (w.2 i)
  let s : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (w.1 i)
  obtain ⟨T, hT⟩ := hl _ (finS_mem ψ hψ.1 hg d s (p2 h))
  refine ⟨T.comp ((SchwartzMap.smulLeftCLM ℂ (fun y : κ → mixedEmbedding.mixedSpace F => eChar ((-trL c) y + -k))).comp
    (SchwartzMap.compSubConstCLM ℂ (-t) : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] _)), fun f => ?_⟩
  have key : schr ψ w (pureA F f g) = pureA F (archS f c t k) (finS ψ g d s (p2 h)) := by
    funext x
    let y : κ → mixedEmbedding.mixedSpace F := fun i => q (x i)
    let z : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (x i)
    have h1 : (fun i => q ((x + w.1) i)) = y + t := funext fun i => map_add q (x i) (w.1 i)
    have h2 : (fun i => p2 ((x + w.1) i)) = z + s := funext fun i => map_add p2 (x i) (w.1 i)
    have h3 : ψ (x ⬝ᵥ w.2 + h) = eChar ((-trL c) y + -k) * finChar ψ (z ⬝ᵥ d + p2 h) := by
      rw [map_eq_mul ψ, hψ.2.2 _ (at_mk _)]
      congr 1
      · have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (mk (p1 (x ⬝ᵥ w.2 + h)) 0) = y ⬝ᵥ c + q h := by
          change q (x ⬝ᵥ w.2 + h) = _
          rw [map_add, RingHom.map_dotProduct]
          rfl
        rw [e1, map_add, eChar_apply, ContinuousLinearMap.neg_apply, trL_apply]
        congr 1
        push_cast
        ring
      · rw [map_add, RingHom.map_dotProduct]
        rfl
    change ψ (x ⬝ᵥ w.2 + h) * (f (fun i => q ((x + w.1) i)) * g (fun i => p2 ((x + w.1) i))) =
      archS f c t k y * (finChar ψ (z ⬝ᵥ d + p2 h) * g (z + s))
    rw [h1, h2, h3, archS_apply]
    ring
  rw [LinearMap.comp_apply]
  change l (schr ψ w (pureA F f g)) = _
  rw [key, hT]
  rfl

end Heis

theorem polData_le {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ X W) (hM : M.IsGood B.ψ) :
    PolData B M ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, -, φ, hφ, hvac, rfl⟩
  exact GlobalTheory.BigNZ.Fam.mem hM ⟨hφ, hvac⟩ f

theorem continuous_shift_term : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ ∈ PolData B G.M, ∀ h, Continuous fun g => thetaSum F (e (G.M.co.rho B.ψ (shiftA H H' 1) (om (g, h) Φ))) := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' _ e he X om om' om₁ om₁' hT hT₁ Φ hΦ h
  obtain ⟨l₀, hl₀, hl₀eq⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin b × Fin (b + a'))
  have hl₁ := GlobalTheory.T.eigen_intertwiner_good_models F E σ B _ _ _ _ G.V G.W G₁.V G₁.W G.M G₁.M H.ι H'.ι _ e hT.geo.hM hT₁.geo.hM he l₀ hl₀
  have hl₂ := schrLin_comp_mem_adm B.ψ hT.base.std (G.M.co.e (shiftA H H' 1)) _ hl₁
  have hw : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hT.weil
  have hΦA : Φ ∈ schA F _ := polData_le B G.M hT.geo.hM hΦ
  have hc := (hw.2.2 _ hl₂ Φ hΦA).comp
    (continuous_id.prodMk continuous_const : Continuous fun g : UA σ G.V.J => (g, h))
  refine hc.congr fun g => ?_
  have h1 := hw.isUSplitting.pres (g, h) Φ hΦA
  have h2 := GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hT.base.std (shiftA H H' 1) _ h1
  rw [← hl₀eq _ (he.maps _ h2)]
  rfl

end GlobalTheory.ConeTermCont
