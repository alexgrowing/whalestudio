import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHaarMapProdEq

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CommProd

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def mulEquiv (A B : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G)
    (he : ∀ p, e p = p.1 * p.2) : (B × A) ≃ₜ* G where
  toFun p := (p.1 : G) * p.2
  invFun g := ((e.symm g).2, (e.symm g).1)
  left_inv p := by
    have : e.symm ((p.1 : G) * p.2) = (p.2, p.1) := by
      rw [Homeomorph.symm_apply_eq, he, hc _ p.2.2 _ p.1.2]
    simp [this]
  right_inv g := by
    change ((e.symm g).2 : G) * (e.symm g).1 = g
    rw [← hc _ (e.symm g).1.2 _ (e.symm g).2.2, ← he, e.apply_symm_apply]
  map_mul' p q := by
    change ((p.1 * q.1 : B) : G) * ((p.2 * q.2 : A) : G) = ((p.1 : G) * p.2) * ((q.1 : G) * q.2)
    simp only [Subgroup.coe_mul, mul_assoc]
    rw [← mul_assoc (p.2 : G), hc _ p.2.2 _ q.1.2]
    simp only [mul_assoc]
  continuous_toFun := (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := (e.symm.continuous.snd).prodMk (e.symm.continuous.fst)

@[simp] theorem mulEquiv_apply (A B : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G)
    (he : ∀ p, e p = p.1 * p.2) (p : B × A) : mulEquiv A B hc e he p = (p.1 : G) * p.2 := rfl

def mulEquivSub (A B R : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G)
    (he : ∀ p, e p = p.1 * p.2) (hR : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ R → a ∈ R ∧ b ∈ R) :
    (R.subgroupOf B × R.subgroupOf A) ≃ₜ* R where
  toFun p := ⟨((p.1 : B) : G) * ((p.2 : A) : G), R.mul_mem (Subgroup.mem_subgroupOf.1 p.1.2) (Subgroup.mem_subgroupOf.1 p.2.2)⟩
  invFun r :=
    have h := hR _ (e.symm r).1.2 _ (e.symm r).2.2 (by rw [← he, e.apply_symm_apply]; exact r.2)
    (⟨(e.symm r).2, Subgroup.mem_subgroupOf.2 h.2⟩, ⟨(e.symm r).1, Subgroup.mem_subgroupOf.2 h.1⟩)
  left_inv p := by
    have : e.symm (((p.1 : B) : G) * ((p.2 : A) : G)) = ((p.2 : A), (p.1 : B)) := by
      rw [Homeomorph.symm_apply_eq, he, hc _ (p.2 : A).2 _ (p.1 : B).2]
    ext <;> simp [this]
  right_inv r := by
    apply Subtype.ext
    change ((e.symm r).2 : G) * (e.symm r).1 = r
    rw [← hc _ (e.symm r).1.2 _ (e.symm r).2.2, ← he, e.apply_symm_apply]
  map_mul' p q := by
    apply Subtype.ext
    change (((p.1 * q.1 : R.subgroupOf B) : B) : G) * (((p.2 * q.2 : R.subgroupOf A) : A) : G) =
      (((p.1 : B) : G) * ((p.2 : A) : G)) * (((q.1 : B) : G) * ((q.2 : A) : G))
    simp only [Subgroup.coe_mul, mul_assoc]
    rw [← mul_assoc ((p.2 : A) : G), hc _ (p.2 : A).2 _ (q.1 : B).2]
    simp only [mul_assoc]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
  continuous_invFun := by
    have hs : Continuous fun r : R => e.symm r := e.symm.continuous.comp continuous_subtype_val
    exact ((hs.snd).subtype_mk _).prodMk ((hs.fst).subtype_mk _)

@[simp] theorem mulEquivSub_apply (A B R : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G)
    (he : ∀ p, e p = p.1 * p.2) (hR : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ R → a ∈ R ∧ b ∈ R) (p : R.subgroupOf B × R.subgroupOf A) :
    (mulEquivSub A B R hc e he hR p : G) = ((p.1 : B) : G) * ((p.2 : A) : G) := rfl

end GlobalTheory.CommProd

namespace GlobalTheory.CommProd

theorem invInv : ∀ {X Y H : Type} [Group X] [Group Y] [Group H] [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace H] [IsTopologicalGroup X] [IsTopologicalGroup Y] [IsTopologicalGroup H] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace H] [BorelSpace X] [BorelSpace Y] [BorelSpace H] [LocallyCompactSpace X]
    [LocallyCompactSpace Y] [LocallyCompactSpace H] [SecondCountableTopology X] [SecondCountableTopology Y]
    [SecondCountableTopology H] (e : (Y × X) ≃ₜ* H) (ρ : Measure Y) (ν : Measure X) (μH : Measure H),
    ρ.IsHaarMeasure → ρ.IsInvInvariant → ν.IsHaarMeasure → μH.IsInvInvariant → (ρ.prod ν).map e = μH →
    ν.IsInvInvariant := by
  intro X Y H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e ρ ν μH _ _ _ _ h
  have he : Measurable e := e.continuous.measurable
  have h1 : (ρ.prod ν.inv).map e = μH := by
    have hp : ρ.prod ν.inv = (ρ.prod ν).map (fun p => p⁻¹) := by
      rw [show (fun p : Y × X => p⁻¹) = Prod.map (·⁻¹) (·⁻¹) from rfl,
        ← Measure.map_prod_map _ _ measurable_inv measurable_inv]
      change ρ.prod ν.inv = ρ.inv.prod ν.inv
      rw [Measure.inv_eq_self ρ]
    have hc : (e ∘ fun p : Y × X => p⁻¹) = (fun q : H => q⁻¹) ∘ e := funext fun p => map_inv e p
    rw [hp, Measure.map_map he measurable_inv, hc, ← Measure.map_map measurable_inv he, h]
    exact Measure.inv_eq_self μH
  have h2 : ρ.prod ν.inv = ρ.prod ν := by
    let E := e.toHomeomorph.toMeasurableEquiv
    have hE : (E : Y × X → H) = e := rfl
    rw [← E.map_symm_map (μ := ρ.prod ν.inv), ← E.map_symm_map (μ := ρ.prod ν), hE, h1, h]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : Y)
  have hK0 : ρ K ≠ 0 := (Measure.measure_pos_of_mem_nhds (μ := ρ) hK1).ne'
  have hKt : ρ K ≠ ⊤ := hK.measure_lt_top.ne
  refine ⟨Measure.ext fun S hS => ?_⟩
  have := congrArg (fun m : Measure (Y × X) => m (K ×ˢ S)) h2
  simp only [Measure.prod_prod] at this
  exact (ENNReal.mul_right_inj hK0 hKt).1 this

theorem cutProd : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (A B R : Subgroup G)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (e : (A × B) ≃ₜ G) (he : ∀ p, e p = p.1 * p.2)
    (hR : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ R → a ∈ R ∧ b ∈ R) (μR : Measure R) (ρ : Measure (R.subgroupOf B))
    (ν : Measure (R.subgroupOf A)) (βB : B → NNReal) (βA : A → NNReal), SFinite ρ → SFinite ν →
    (ρ.prod ν).map (mulEquivSub A B R hc e he hR) = μR →
    GlobalTheory.Tw.IsCosetCutoff (R.subgroupOf B) ρ βB → GlobalTheory.Tw.IsCosetCutoff (R.subgroupOf A) ν βA →
    GlobalTheory.Tw.IsCosetCutoff R μR (fun g => βB (e.symm g).2 * βA (e.symm g).1) := by
  intro G _ _ _ _ _ _ _ _ A B R hc e he hR μR ρ ν βB βA _ _ hm hB hA
  have hs : Measurable fun g : G => e.symm g := e.symm.continuous.measurable
  have hmeas : Measurable fun g : G => βB (e.symm g).2 * βA (e.symm g).1 :=
    (hB.1.comp (measurable_snd.comp hs)).mul (hA.1.comp (measurable_fst.comp hs))
  refine ⟨hmeas, fun x => ?_⟩
  set ψ := mulEquivSub A B R hc e he hR
  have hψ : Measurable ψ := ψ.continuous.measurable
  have hmx : Measurable fun r : R => ((βB (e.symm ((r : G) * x)).2 * βA (e.symm ((r : G) * x)).1 : NNReal) : ℝ≥0∞) :=
    (hmeas.comp (measurable_subtype_coe.mul_const x)).coe_nnreal_ennreal
  rw [← hm, lintegral_map hmx hψ]
  have key : ∀ p : R.subgroupOf B × R.subgroupOf A, e.symm ((ψ p : G) * x) = ((p.2 : A) * (e.symm x).1, (p.1 : B) * (e.symm x).2) := by
    intro p
    rw [Homeomorph.symm_apply_eq, he, mulEquivSub_apply]
    have hx : x = ((e.symm x).1 : G) * (e.symm x).2 := by rw [← he, e.apply_symm_apply]
    have h1 : ((p.1 : B) : G) * ((p.2 : A) : G) = ((p.2 : A) : G) * ((p.1 : B) : G) :=
      (hc _ (p.2 : A).2 _ (p.1 : B).2).symm
    have h2 : ((p.1 : B) : G) * ((e.symm x).1 : G) = ((e.symm x).1 : G) * ((p.1 : B) : G) :=
      (hc _ (e.symm x).1.2 _ (p.1 : B).2).symm
    calc ((p.1 : B) : G) * ((p.2 : A) : G) * x
        = ((p.2 : A) : G) * (((p.1 : B) : G) * ((e.symm x).1 : G)) * (e.symm x).2 := by
          rw [h1]; conv_lhs => rw [hx]
          simp only [mul_assoc]
      _ = _ := by rw [h2]; simp only [Subgroup.coe_mul, mul_assoc]
  simp only [key, ENNReal.coe_mul]
  refine (lintegral_prod _ ((hB.1.coe_nnreal_ennreal.comp ((measurable_subtype_coe.comp measurable_fst).mul_const _)).mul
    (hA.1.coe_nnreal_ennreal.comp ((measurable_subtype_coe.comp measurable_snd).mul_const _))).aemeasurable).trans ?_
  simp only [Pi.mul_apply, Function.comp_apply, lintegral_const_mul' _ _ ENNReal.coe_ne_top, hA.2, mul_one, hB.2]

end GlobalTheory.CommProd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.CommProd in

theorem GlobalTheory.CommProd.quot_vanish_of_prod : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (A B R : Subgroup G), IsClosed (A : Set G) → IsClosed (B : Set G) → IsClosed (R : Set G) → (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) → (∃ e : (A × B) ≃ₜ G, ∀ p, e p = p.1 * p.2) → (∀ a ∈ A, ∀ b ∈ B, a * b ∈ R → a ∈ R ∧ b ∈ R) → ∀ (μR : Measure R) (μG : Measure G) (ρ : Measure (R.subgroupOf B)) (μ : Measure B), μR.IsHaarMeasure → μR.IsInvInvariant → μG.IsHaarMeasure → ρ.IsHaarMeasure → ρ.IsInvInvariant → μ.IsHaarMeasure → ∀ (f : G → ℂ) (z : ℂ), IsQuotIntL1 μR μG f z → (∀ a ∈ A, IsQuotIntL1 ρ μ (fun b => f (a * b.1)) 0) → z = 0 := by
  intro G _ _ _ _ _ _ _ _ A B R hA hB hR hc ⟨e, he⟩ hdec μR μG ρ μ _ _ _ _ _ _ f z hf hz
  have : LocallyCompactSpace A := hA.locallyCompactSpace
  have : LocallyCompactSpace B := hB.locallyCompactSpace
  have hRA : IsClosed ((R.subgroupOf A : Subgroup A) : Set A) := hR.preimage continuous_subtype_val
  have hRB : IsClosed ((R.subgroupOf B : Subgroup B) : Set B) := hR.preimage continuous_subtype_val
  have : LocallyCompactSpace (R.subgroupOf A) := hRA.locallyCompactSpace
  have : LocallyCompactSpace (R.subgroupOf B) := hRB.locallyCompactSpace
  have : LocallyCompactSpace R := hR.locallyCompactSpace
  let φ := mulEquiv A B hc e he
  let ψ := mulEquivSub A B R hc e he hdec
  obtain ⟨μA, hμA, hG⟩ := GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq φ μ μG
  obtain ⟨ν, hν, hRm⟩ := GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq ψ ρ μR
  have : ν.IsInvInvariant := invInv ψ ρ ν μR inferInstance inferInstance hν inferInstance hRm
  obtain ⟨βB, -, hβB⟩ := GlobalTheory.Tw.exists_isCosetCutoff (μT := ρ) hRB
  obtain ⟨βA, -, hβA⟩ := GlobalTheory.Tw.exists_isCosetCutoff (μT := ν) hRA
  have hβ := cutProd G A B R hc e he hdec μR ρ ν βB βA inferInstance inferInstance hRm hβB hβA
  obtain ⟨hi, rfl⟩ := hf.cutoff hβ
  have hφs : ∀ p : B × A, e.symm (φ p) = (p.2, p.1) := fun p => by
    rw [Homeomorph.symm_apply_eq, he, mulEquiv_apply, hc _ p.2.2 _ p.1.2]
  have hme : MeasurableEmbedding φ := φ.toHomeomorph.measurableEmbedding
  rw [← hG] at hi ⊢
  rw [hme.integral_map]
  rw [hme.integrable_map_iff] at hi
  refine (integral_prod_symm _ hi).trans ?_
  have hin : ∀ a : A, ∫ b : B, ((fun g => ((βB (e.symm g).2 * βA (e.symm g).1 : NNReal) : ℝ) • f g) ∘ φ) (b, a) ∂μ = 0 := by
    intro a
    obtain ⟨-, h0⟩ := (hz a a.2).cutoff hβB
    have e1 : ∀ b : B, ((fun g => ((βB (e.symm g).2 * βA (e.symm g).1 : NNReal) : ℝ) • f g) ∘ φ) (b, a) =
        (βA a : ℝ) • ((βB b : ℝ) • f (a * b)) := fun b => by
      simp only [Function.comp_apply, hφs, mulEquiv_apply, NNReal.coe_mul, smul_smul]
      rw [show φ (b, a) = (b : G) * a from rfl, hc _ a.2 _ b.2, mul_comm (βB b : ℝ)]
    simp only [e1, integral_smul, ← h0, smul_zero]
  exact (integral_congr_ae (Filter.Eventually.of_forall hin)).trans (integral_zero _ _)
