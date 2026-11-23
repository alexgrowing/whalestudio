import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerIntegralBound
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

noncomputable section

namespace GlobalTheory.ConeUnipMeas

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic GlobalTheory.ConeMeasV GlobalTheory.ConeMeasSmall

theorem integrand_aestronglyMeasurable : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ (V : Spc F E a) (V' : Spc F E b) (W₁' : Spc F E (a + b)), IsTriple B (reG G₁ V V' W₁') X om₁ om₁' →
    ∀ (e : ℕ) (W₂ : Spc F E e) (H₂ : Plane E (a + b) e) (i₀ i₁ : ℕ), H₂.IsAdapted σ B (reG G₁ V V' W₁').W W₂ i₀ i₁ →
    ∀ (s : ℂ) (g : UA σ G.W.J) (h : UA σ G₁.W.J) (μ' : Measure (unip σ G₁.W H₂)) (𝓕 : Set (unip σ G₁.W H₂)), μ'.IsHaarMeasure →
      AEStronglyMeasurable (fun p : unip σ G₁.W H₂ × (K × (AE F E)ˣ) => G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' p.2.2) (om' (p.2.1.1, g) Φ'))) (p.1.1 * h) * (X.ν p.2.2 : ℂ) * ((absE F E p.2.2 : ℝ) : ℂ) ^ (s + ((a : ℂ) + 1) / 2)) ((μ'.restrict 𝓕).prod (μK.prod μ)) := by
  intro _ F E _ _ _ _ _ σ B a b G G₁ H H' _ e' hE K μK μ _ _ _ X om om' om₁ om₁' hT hT₁ Φ' hΦ V V' W₁' _ e W₂ H₂ i₀ i₁ _
    s g h μ' 𝓕 _
  have hM := hT.geo.hM'
  have hM₁ := hT₁.geo.hM'
  have hψ := hT.base.std
  have hS := IsUWeilPair.isUSplitting hT.weil'
  have hS₁ := IsUWeilPair.isUSplitting hT₁.weil'
  obtain ⟨l₀, hl₀, hl₀eq⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin b × Fin (a + b))
  have hΦA := polData_le_schA hM hΦ.1
  obtain ⟨t1, t2, t3, t4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ _ G.V'.J
  obtain ⟨u1, u2, u3, u4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ _ G₁.V'.J
  obtain ⟨w1, w2, w3, w4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ _ G₁.W.J
  obtain ⟨v1, v2⟩ := idele_top (F := F) (E := E)
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ G₁.V'.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ G₁.W.J) := ⟨rfl⟩
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI : TopologicalSpace.MetrizableSpace (UA σ G.V'.J) := metrizable_group _ t1 t4 t3
  haveI : TopologicalSpace.MetrizableSpace (UA σ G₁.V'.J) := metrizable_group _ u1 u4 u3
  haveI : TopologicalSpace.MetrizableSpace (UA σ G₁.W.J) := metrizable_group _ w1 w4 w3
  haveI := hM₁.haar
  haveI : SigmaCompactSpace (UA σ G₁.V'.J) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SFinite (G₁.M'.μ.restrict G₁.M'.dom) := sfinite_restrict _ (Measure.IsHaarMeasure.sigmaFinite _) _
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsModuleTopology (AF F) (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin (b + 2) → Fin (a + (b + 2)) → AE F E))
  have hco : Continuous G.M'.co.e := IsModuleTopology.continuous_of_linearMap G.M'.co.e.toLinearMap
  have hcA : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hsh : Continuous (shiftB σ H H') := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (hcA.comp Units.continuous_val).mul continuous_const

  let u : UA σ G₁.W.J → UA σ G₁.V'.J → UA σ G.V'.J → (AE F E)ˣ → ℂ := fun x y k l =>
    l₀ (om₁' (y, x) (e' (schr B.ψ (G.M'.co.e (shiftB σ H H' l)) (om' (k, g) Φ'))))
  have hmem : ∀ k l, e' (schr B.ψ (G.M'.co.e (shiftB σ H H' l)) (om' (k, g) Φ')) ∈ schA F _ := fun k l =>
    hE.maps _ (GlobalTheory.ConeMeasV.schr_mem_schA hψ _ (hS.pres _ _ hΦA))
  have hadm : ∀ x y, (l₀ ∘ₗ om₁' (y, x)) ∘ₗ e' ∈ (adeleClass F).adm _ := fun x y =>
    comp_ev_mem_adm hM hM₁ hE (hS₁.adm _ _ hl₀)
  have cx : ∀ y k l, Continuous fun x => u x y k l := fun y k l =>
    (hS₁.cont _ hl₀ _ (hmem k l)).comp (continuous_const.prodMk continuous_id)
  have cy : ∀ x k l, Continuous fun y => u x y k l := fun x k l =>
    (hS₁.cont _ hl₀ _ (hmem k l)).comp (continuous_id.prodMk continuous_const)
  have ck : ∀ x y l, Continuous fun k => u x y k l := fun x y l =>
    (hS.cont _ (comp_schr_mem_adm hψ (G.M'.co.e (shiftB σ H H' l)) (hadm x y)) _ hΦA).comp
      (continuous_id.prodMk continuous_const)
  have cl : ∀ x y k, Continuous (u x y k) := fun x y k =>
    (continuous_schr hψ (hadm x y) (hS.pres (k, g) _ hΦA)).comp (hco.comp hsh)
  have m1 : ∀ x y, Measurable (Function.uncurry (u x y)) := fun x y =>
    measurable_uncurry_of_continuous_of_measurable (ck x y) fun k => (cl x y k).measurable
  have m2 : ∀ x, Measurable (Function.uncurry fun y (p : UA σ G.V'.J × (AE F E)ˣ) => u x y p.1 p.2) := fun x =>
    measurable_uncurry_of_continuous_of_measurable (fun p => cy x p.1 p.2) (m1 x)
  have m2' : Measurable (Function.uncurry fun x (p : UA σ G₁.V'.J × (UA σ G.V'.J × (AE F E)ˣ)) => u x p.1 p.2.1 p.2.2) :=
    measurable_uncurry_of_continuous_of_measurable (fun p => cx p.1 p.2.1 p.2.2) m2
  have mh : Measurable fun x : UA σ G₁.W.J => x * h := (continuous_id.mul continuous_const).measurable
  have mu : Measurable fun x : unip σ G₁.W H₂ => x.1 * h := mh.comp measurable_subtype_coe
  have m3 : Measurable fun x : (unip σ G₁.W H₂ × (K × (AE F E)ˣ)) × UA σ G₁.V'.J =>
      u (x.1.1.1 * h) x.2 x.1.2.1.1 x.1.2.2 :=
    m2'.comp ((mu.comp (measurable_fst.comp measurable_fst)).prodMk (measurable_snd.prodMk
      ((measurable_subtype_coe.comp (measurable_fst.comp (measurable_snd.comp measurable_fst))).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_fst)))))
  have m4 := m3.stronglyMeasurable.integral_prod_right' (ν := G₁.M'.μ.restrict G₁.M'.dom)
  have cν : Continuous fun l : (AE F E)ˣ => (X.ν l : ℂ) :=
    continuous_subtype_val.comp (hT.chars.heckeα.1.div' hT.chars.heckeβ.1)
  have cN : Measurable fun l : (AE F E)ˣ => ((absE F E l : ℝ) : ℂ) ^ (s + ((a : ℂ) + 1) / 2) :=
    (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE)).measurable.pow_const _
  have m22 : Measurable fun x : unip σ G₁.W H₂ × (K × (AE F E)ˣ) => x.2.2 := measurable_snd.comp measurable_snd
  have m5 := (m4.mul (cν.measurable.comp m22).stronglyMeasurable).mul (cN.comp m22).stronglyMeasurable
  refine StronglyMeasurable.aestronglyMeasurable ?_
  refine cast (congrArg StronglyMeasurable (funext fun p => ?_)) m5
  refine congrArg₂ (fun x y : ℂ => x * y) (congrArg₂ (fun x y : ℂ => x * y) ?_ rfl) rfl
  refine congrArg (integral (G₁.M'.μ.restrict G₁.M'.dom)) (funext fun y => ?_)
  exact (hl₀eq _ (hS₁.pres _ _ (hmem _ _)))

end GlobalTheory.ConeUnipMeas

end
