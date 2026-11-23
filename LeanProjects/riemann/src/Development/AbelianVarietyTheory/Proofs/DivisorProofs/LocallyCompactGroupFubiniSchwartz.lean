import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainClosure

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory

theorem heisenberg_preimage_haar : ∀ {G V Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
  [AddCommGroup Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z] [LocallyCompactSpace Z] [SecondCountableTopology Z] [T2Space Z] [MeasurableSpace Z] [BorelSpace Z]
  (νV : Measure V) (νZ : Measure Z), νV.IsAddHaarMeasure → νZ.IsAddHaarMeasure →
  ∀ (Φ : G ≃ₜ V × Z) (β : V → V → Z), Continuous (Function.uncurry β) →
  (∀ u v, Φ (u * v) = ((Φ u).1 + (Φ v).1, (Φ u).2 + (Φ v).2 + β (Φ u).1 (Φ v).1)) →
  ∀ (f : G → G) (A : V ≃ₜ V) (C : Z ≃ₜ Z) (a c : ENNReal), a ≠ ⊤ → c ≠ ⊤ → νV.map A = a • νV → νZ.map C = c • νZ →
  (∀ u, Φ (f u) = (A (Φ u).1, C (Φ u).2)) →
  ∀ μ : Measure G, μ.IsHaarMeasure → ∀ S : Set G, μ (f ⁻¹' S) = a * c * μ S := by
  intro G V Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ νV νZ hV hZ Φ β hβ hΦ f A C a c ha hc hA hC hf μ hμ S

  set P : Measure (V × Z) := νV.prod νZ with hPdef
  haveI : LocallyCompactSpace G := Φ.isOpenEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology G := Φ.isEmbedding.secondCountableTopology
  let e : G ≃ᵐ V × Z := Φ.toMeasurableEquiv
  set ρ : Measure G := P.map e.symm with hρdef
  have hρapp : ∀ T : Set G, ρ T = P (e.symm ⁻¹' T) := fun T => e.symm.map_apply T

  have hinv : ρ.IsMulLeftInvariant := by
    constructor
    intro g
    set a0 := (Φ g).1
    set b0 := (Φ g).2
    have hskew : MeasurePreserving (fun p : V × Z => (a0 + p.1, b0 + p.2 + β a0 p.1)) P P := by
      have h1 : MeasurePreserving (fun v : V => a0 + v) νV νV := measurePreserving_add_left νV a0
      have hm : Measurable (Function.uncurry fun (v : V) (z : Z) => b0 + z + β a0 v) := by
        apply Continuous.measurable
        exact (continuous_const.add continuous_snd).add (hβ.comp (continuous_const.prodMk continuous_fst))
      have := h1.skew_product (μc := νZ) (μd := νZ) hm (Filter.Eventually.of_forall fun v => by
        have : (fun z : Z => b0 + z + β a0 v) = fun z => (b0 + β a0 v) + z := by
          funext z; abel
        rw [this]; exact (measurePreserving_add_left νZ _).map_eq)
      exact this
    have hconj : (fun x : G => g * x) ∘ e.symm = e.symm ∘ (fun p : V × Z => (a0 + p.1, b0 + p.2 + β a0 p.1)) := by
      funext p
      apply Φ.injective
      simp only [Function.comp_apply]
      change Φ (g * Φ.symm p) = Φ (Φ.symm _)
      rw [hΦ, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
    rw [hρdef, Measure.map_map (measurable_const_mul g) e.symm.measurable, hconj,
      ← Measure.map_map e.symm.measurable hskew.measurable, hskew.map_eq]
  haveI : IsFiniteMeasureOnCompacts ρ := Measure.IsFiniteMeasureOnCompacts.map P Φ.symm
  haveI : ρ.IsOpenPosMeasure := Φ.symm.continuous.isOpenPosMeasure_map Φ.symm.surjective
  haveI : ρ.IsHaarMeasure := { }
  have hμρ := Measure.isMulLeftInvariant_eq_smul μ ρ

  let D : V × Z ≃ᵐ V × Z := (A.prodCongr C).toMeasurableEquiv
  have hD : P.map D = (a * c) • P := by
    change P.map (Prod.map A C) = _
    rw [hPdef, ← Measure.map_prod_map νV νZ A.measurable C.measurable, hA, hC,
      Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  have hpre : e.symm ⁻¹' (f ⁻¹' S) = D ⁻¹' (e.symm ⁻¹' S) := by
    ext p
    simp only [Set.mem_preimage]
    have : f (e.symm p) = e.symm (D p) := by
      apply Φ.injective
      change Φ (f (Φ.symm p)) = Φ (Φ.symm (A p.1, C p.2))
      rw [hf, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
    rw [this]
  rw [hμρ, Measure.smul_apply, Measure.smul_apply, hρapp, hρapp, hpre, ← D.map_apply, hD,
    Measure.smul_apply]
  simp only [ENNReal.smul_def, smul_eq_mul]
  ring

end GlobalTheory
