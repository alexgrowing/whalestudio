import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerIntegralBound

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.OuterMeas

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic GlobalTheory.ConeMeasV GlobalTheory.ConeMeasSmall

theorem integrand_aestronglyMeasurable : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h h₁,
        AEStronglyMeasurable (fun p : UA σ G₁.V'.J × K × (AE F E)ˣ => theta om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' p.2.2) (om' (p.2.1.1, h) Φ'))) p.1 h₁ * (X.ν p.2.2 : ℂ) * ((absE F E p.2.2 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) ((G₁.M'.μ.restrict G₁.M'.dom).prod (μK.prod μ)) := by
  intro _ F E _ _ _ _ _ σ B a b G G₁ H H' _ e' hE K μK μ _ _ _ X om om' om₁ om₁' hT hT₁ Φ' hΦ h h₁
  have hM := hT.geo.hM'
  have hM₁ := hT₁.geo.hM'
  have hψ := hT.base.std
  have hS := IsUWeilPair.isUSplitting hT.weil'
  have hS₁ := IsUWeilPair.isUSplitting hT₁.weil'
  obtain ⟨l₀, hl₀, hl₀eq⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin b × Fin (a + b))
  have hΦA := polData_le_schA hM hΦ.1
  obtain ⟨t1, t2, t3, t4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ _ G.V'.J
  obtain ⟨u1, u2, u3, u4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ _ G₁.V'.J
  obtain ⟨v1, v2⟩ := idele_top (F := F) (E := E)
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ G₁.V'.J) := ⟨rfl⟩
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI : TopologicalSpace.MetrizableSpace (UA σ G.V'.J) := metrizable_group _ t1 t4 t3
  haveI : TopologicalSpace.MetrizableSpace (UA σ G₁.V'.J) := metrizable_group _ u1 u4 u3
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsModuleTopology (AF F) (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin (b + 2) → Fin (a + (b + 2)) → AE F E))
  have hco : Continuous G.M'.co.e := IsModuleTopology.continuous_of_linearMap G.M'.co.e.toLinearMap
  have hcA : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hsh : Continuous (shiftB σ H H') := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (hcA.comp Units.continuous_val).mul continuous_const

  let u : UA σ G₁.V'.J → UA σ G.V'.J → (AE F E)ˣ → ℂ := fun g k l =>
    l₀ (om₁' (g, h₁) (e' (schr B.ψ (G.M'.co.e (shiftB σ H H' l)) (om' (k, h) Φ'))))
  have hmem : ∀ k l, e' (schr B.ψ (G.M'.co.e (shiftB σ H H' l)) (om' (k, h) Φ')) ∈ schA F _ := fun k l =>
    hE.maps _ (GlobalTheory.ConeMeasV.schr_mem_schA hψ _ (hS.pres _ _ hΦA))
  have hadm : ∀ g, (l₀ ∘ₗ om₁' (g, h₁)) ∘ₗ e' ∈ (adeleClass F).adm _ := fun g =>
    comp_ev_mem_adm hM hM₁ hE (hS₁.adm _ _ hl₀)
  have cg : ∀ k l, Continuous fun g => u g k l := fun k l =>
    (hS₁.cont _ hl₀ _ (hmem k l)).comp (continuous_id.prodMk continuous_const)
  have ck : ∀ g l, Continuous fun k => u g k l := fun g l =>
    (hS.cont _ (comp_schr_mem_adm hψ (G.M'.co.e (shiftB σ H H' l)) (hadm g)) _ hΦA).comp
      (continuous_id.prodMk continuous_const)
  have cl : ∀ g k, Continuous (u g k) := fun g k =>
    (continuous_schr hψ (hadm g) (hS.pres (k, h) _ hΦA)).comp (hco.comp hsh)
  have m1 : ∀ g, Measurable (Function.uncurry (u g)) := fun g =>
    measurable_uncurry_of_continuous_of_measurable (ck g) fun k => (cl g k).measurable
  have m2 : Measurable (Function.uncurry fun g (p : UA σ G.V'.J × (AE F E)ˣ) => u g p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable (fun p => cg p.1 p.2) m1
  have m3 : Measurable fun x : UA σ G₁.V'.J × K × (AE F E)ˣ => u x.1 x.2.1.1 x.2.2 :=
    m2.comp (measurable_fst.prodMk ((measurable_subtype_coe.comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)))
  have cν : Continuous fun l : (AE F E)ˣ => (X.ν l : ℂ) :=
    continuous_subtype_val.comp (hT.chars.heckeα.1.div' hT.chars.heckeβ.1)
  have cN : Continuous fun l : (AE F E)ˣ => ((absE F E l : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1) :=
    (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE)).pow _
  have m22 : Measurable fun x : UA σ G₁.V'.J × K × (AE F E)ˣ => x.2.2 := measurable_snd.comp measurable_snd
  have m4 := (m3.mul (cν.measurable.comp m22)).mul (cN.measurable.comp m22)
  refine StronglyMeasurable.aestronglyMeasurable ?_
  refine cast (congrArg StronglyMeasurable (funext fun p => ?_)) m4.stronglyMeasurable
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (hl₀eq _ (hS₁.pres _ _ (hmem _ _))) rfl) rfl

end GlobalTheory.OuterMeas
