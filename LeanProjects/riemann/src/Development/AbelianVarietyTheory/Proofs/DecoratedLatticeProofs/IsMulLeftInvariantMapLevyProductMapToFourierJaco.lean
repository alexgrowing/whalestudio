import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdRFJCoe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjByColumnUnipotentPreservesUnipotentHaarStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

noncomputable section
namespace GlobalTheory.HaarR.LeftFJ

open GlobalTheory.RootEx

section Alg
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def conjN (p : ℕ) (g : GL n k) (u' : N k n c p) : N k n c p :=
  ⟨embX c g⁻¹ * (u' : GL (n ⊕ Fin c) k) * (embX c g⁻¹)⁻¹,
    ((Radical.unipotent_radical_basic k n c p).2.2.2.1 g⁻¹ u' u'.2).1⟩

theorem mul_prodRFJ_embX (ρ : ℕ) (g' : GL n k) (q : (GL n k × N k n c (ρ + 1)) × (n → k)) :
    embX c g' * (prodRFJ ρ q : GL (n ⊕ Fin c) k) = prodRFJ ρ ((g' * q.1.1, q.1.2), q.2) := by
  simp only [prodRFJ_coe, map_mul, mul_assoc]

theorem mul_prodRFJ_N (ρ : ℕ) (u' : N k n c (ρ + 1)) (q : (GL n k × N k n c (ρ + 1)) × (n → k)) :
    (u' : GL (n ⊕ Fin c) k) * (prodRFJ ρ q : GL (n ⊕ Fin c) k) =
      prodRFJ ρ ((q.1.1, conjN (ρ + 1) q.1.1 u' * q.1.2), q.2) := by
  simp only [prodRFJ_coe, conjN, Subgroup.coe_mul, map_inv, inv_inv]
  group

theorem mul_prodRFJ_colE (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (β' : n → k)
    (q : (GL n k × N k n c (ρ + 1)) × (n → k)) :
    colE c (ρ + 1) β' * (prodRFJ ρ q : GL (n ⊕ Fin c) k) =
      prodRFJ ρ ((q.1.1, cjE ρ h1 h2 (((q.1.1)⁻¹ : GL n k).val *ᵥ β') q.1.2),
        ((q.1.1)⁻¹ : GL n k).val *ᵥ β' + q.2) := by
  obtain ⟨⟨g, u⟩, β⟩ := q
  set γ := ((g)⁻¹ : GL n k).val *ᵥ β'
  have hc : colE c (ρ + 1) β' = embX c g * colE c (ρ + 1) γ * (embX c g)⁻¹ := by
    rw [QuotStep.conj_colE]
    congr 1
    simp only [γ, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rw [prodRFJ_coe, prodRFJ_coe, cjE_coe, hc, ← FourierJacobiGroup.colE_add]
  group

end Alg

section Meas
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem continuous_conjN (p : ℕ) (u' : N k n c p) : Continuous fun g : GL n k => conjN p g u' := by
  have he := QuotStep.continuous_embX (k := k) (n := n) (c := c)
  refine Continuous.subtype_mk ?_ _
  exact ((he.comp continuous_inv).mul continuous_const).mul (he.comp continuous_inv).inv

theorem continuous_cjE (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) :
    Continuous fun x : (n → k) × N k n c (ρ + 1) => cjE ρ h1 h2 x.1 x.2 := by
  have hc := QuotStep.continuous_colE (k := k) (n := n) (c := c) (ρ + 1)
  refine Continuous.subtype_mk ?_ _
  exact ((hc.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).mul
    (hc.comp continuous_fst).inv

theorem continuous_prodRFJ (ρ : ℕ) : Continuous (prodRFJ (k := k) (n := n) (c := c) ρ) := by
  have he := QuotStep.continuous_embX (k := k) (n := n) (c := c)
  have hc := QuotStep.continuous_colE (k := k) (n := n) (c := c) (ρ + 1)
  refine Continuous.subtype_mk ?_ _
  exact ((he.comp (continuous_fst.comp continuous_fst)).mul
    (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))).mul (hc.comp continuous_snd)

theorem continuous_invMulVec (β' : n → k) : Continuous fun g : GL n k => ((g⁻¹ : GL n k)).val *ᵥ β' :=
  (Units.continuous_val.comp continuous_inv).matrix_mulVec continuous_const

end Meas

theorem map_mul_left_of_conj {Q G : Type} [MeasurableSpace Q] [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure Q) (f : Q → G) (hf : Measurable f) (h : G) (T : Q → Q) (hT : MeasurePreserving T μ μ)
    (he : ∀ q, h * f q = f (T q)) : (μ.map f).map (h * ·) = μ.map f := by
  rw [Measure.map_map (measurable_const_mul h) hf]
  have : (fun x => h * x) ∘ f = f ∘ T := funext he
  rw [this, ← Measure.map_map hf hT.measurable, hT.map_eq]

theorem map_mul_left_mul {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (κ : Measure G)
    (a b : G) (ha : κ.map (a * ·) = κ) (hb : κ.map (b * ·) = κ) : κ.map ((a * b) * ·) = κ := by
  have : (fun x => a * b * x) = (fun x => a * x) ∘ (fun x => b * x) := funext fun x => mul_assoc a b x
  rw [this, ← Measure.map_map (measurable_const_mul a) (measurable_const_mul b), hb, ha]

section Kinds
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  [SecondCountableTopology k] [BorelSpace (GL n k)] [SecondCountableTopology (GL n k)]
  [BorelSpace (GL (n ⊕ Fin c) k)] [SecondCountableTopology (GL (n ⊕ Fin c) k)]

def fibFJ (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (β' : n → k) (g : GL n k) (x : N k n c (ρ + 1) × (n → k)) :
    N k n c (ρ + 1) × (n → k) :=
  (cjE ρ h1 h2 (((g⁻¹ : GL n k)).val *ᵥ β') x.1, ((g⁻¹ : GL n k)).val *ᵥ β' + x.2)

theorem measurable_fibFJ (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (β' : n → k) :
    Measurable (Function.uncurry (fibFJ ρ h1 h2 β')) := by
  have hγ : Continuous fun p : GL n k × (N k n c (ρ + 1) × (n → k)) => ((p.1⁻¹ : GL n k)).val *ᵥ β' :=
    (continuous_invMulVec β').comp continuous_fst
  have hc : Continuous fun p : GL n k × (N k n c (ρ + 1) × (n → k)) =>
      (cjE ρ h1 h2 (((p.1⁻¹ : GL n k)).val *ᵥ β') p.2.1, ((p.1⁻¹ : GL n k)).val *ᵥ β' + p.2.2) :=
    ((continuous_cjE ρ h1 h2).comp (hγ.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (hγ.add (continuous_snd.comp continuous_snd))
  exact hc.measurable

theorem map_fibFJ (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure]
    [SFinite (volN ν n c (ρ + 1))] (β' : n → k) (g : GL n k) :
    ((volN ν n c (ρ + 1)).prod (Measure.pi fun _ : n => ν)).map (fibFJ ρ h1 h2 β' g) =
      (volN ν n c (ρ + 1)).prod (Measure.pi fun _ : n => ν) := by
  have e : fibFJ ρ h1 h2 β' g = Prod.map (cjE ρ h1 h2 (((g⁻¹ : GL n k)).val *ᵥ β'))
      (fun β => ((g⁻¹ : GL n k)).val *ᵥ β' + β) := rfl
  have hcm : Measurable (cjE ρ h1 h2 (((g⁻¹ : GL n k)).val *ᵥ β')) :=
    ((continuous_cjE ρ h1 h2).comp (continuous_const.prodMk continuous_id)).measurable
  rw [e, ← Measure.map_prod_map _ _ hcm (measurable_const_add _), GlobalTheory.T.conjByColumnUnipotent_preserves_unipotentHaar k n c ρ h1 h2 ν inferInstance,
    map_add_left_eq_self]

theorem mp_colE (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure]
    [SFinite (volN ν n c (ρ + 1))] (m : Measure (GL n k)) [SFinite m] (β' : n → k) :
    MeasurePreserving (fun q : (GL n k × N k n c (ρ + 1)) × (n → k) =>
      ((q.1.1, cjE ρ h1 h2 (((q.1.1)⁻¹ : GL n k).val *ᵥ β') q.1.2), ((q.1.1)⁻¹ : GL n k).val *ᵥ β' + q.2))
      ((m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν))
      ((m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν)) := by
  have hA := measurePreserving_prodAssoc m (volN ν n c (ρ + 1)) (Measure.pi fun _ : n => ν)
  have hs := (MeasurePreserving.id m).skew_product (measurable_fibFJ ρ h1 h2 β')
    (Filter.Eventually.of_forall (map_fibFJ ρ h1 h2 ν β'))
  exact (MeasurePreserving.symm _ hA).comp (hs.comp hA)

theorem mp_N (ρ : ℕ) (ν : Measure k) [ν.IsAddHaarMeasure] (V : Measure (N k n c (ρ + 1)))
    [V.IsMulLeftInvariant] [SFinite V] (m : Measure (GL n k)) [SFinite m] (u' : N k n c (ρ + 1)) :
    MeasurePreserving (fun q : (GL n k × N k n c (ρ + 1)) × (n → k) =>
      ((q.1.1, conjN (ρ + 1) q.1.1 u' * q.1.2), q.2))
      ((m.prod V).prod (Measure.pi fun _ : n => ν)) ((m.prod V).prod (Measure.pi fun _ : n => ν)) := by
  have hm2 : Measurable (Function.uncurry fun (g : GL n k) (u : N k n c (ρ + 1)) => conjN (ρ + 1) g u' * u) :=
    (((continuous_conjN (ρ + 1) u').comp continuous_fst).mul continuous_snd).measurable
  have hs := (MeasurePreserving.id m).skew_product hm2 (Filter.Eventually.of_forall fun g => map_mul_left_eq_self V _)
  exact hs.prod (MeasurePreserving.id _)

theorem mp_embX (ρ : ℕ) (ν : Measure k) [ν.IsAddHaarMeasure] (V : Measure (N k n c (ρ + 1))) [SFinite V]
    (m : Measure (GL n k)) [m.IsMulLeftInvariant] [SFinite m] (g' : GL n k) :
    MeasurePreserving (fun q : (GL n k × N k n c (ρ + 1)) × (n → k) => ((g' * q.1.1, q.1.2), q.2))
      ((m.prod V).prod (Measure.pi fun _ : n => ν)) ((m.prod V).prod (Measure.pi fun _ : n => ν)) :=
  ((measurePreserving_mul_left m g').prod (MeasurePreserving.id V)).prod (MeasurePreserving.id _)

end Kinds

theorem isMulLeftInvariant_map_prodRFJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), 1 ≤ ρ → ρ < c → ∀ (ν : Measure k), ν.IsAddHaarMeasure → ∀ m : Measure (GL n k), m.IsHaarMeasure → (((m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν)).map (prodRFJ ρ)).IsMulLeftInvariant := by
  intro k _ _ _ _ _ _ n _ _ c ρ h1 h2 ν hν m hm
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : BorelSpace (GL n k) := GlobalTheory.SplitFlip.borel_GL
  haveI : BorelSpace (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.borel_GL
  haveI : SecondCountableTopology (GL n k) := GlobalTheory.SplitFlip.secondCountable_GL
  haveI : SecondCountableTopology (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.secondCountable_GL
  haveI : LocallyCompactSpace (GL n k) := GlobalTheory.SplitFlip.locallyCompact_GL
  haveI hVH : (volN ν n c (ρ + 1)).IsHaarMeasure :=
    (GlobalTheory.RootEx.VolN.volN_haar_and_modulus k n c (ρ + 1) (by omega) (by omega) ν).2.2.1
  haveI : SFinite (volN ν n c (ρ + 1)) := by rw [GlobalTheory.RootEx.VolN.volN_eq]; infer_instance
  have hf : Measurable (prodRFJ (k := k) (n := n) (c := c) ρ) := (continuous_prodRFJ ρ).measurable
  refine ⟨fun h => ?_⟩
  obtain ⟨r, hr, β', he⟩ := ((FourierJacobiGroup.mem_RFJ_iff k n c ρ h1 h2).1 h.1).1 h.2
  obtain ⟨g', u', hu', rfl⟩ := Radical.exists_of_mem_R hr
  have hg : embX c g' ∈ RFJ k n c ρ := Subgroup.mem_sup_right (Subgroup.mem_sup_left ⟨g', rfl⟩)
  have hu : u' ∈ RFJ k n c ρ := Subgroup.mem_sup_right (Subgroup.mem_sup_right hu')
  have hb : colE c (ρ + 1) β' ∈ RFJ k n c ρ := Subgroup.mem_sup_left (Subgroup.mem_sup_right
    ((GlobalTheory.RootEx.Radical.unipotent_radical_basic k n c ρ).2.2.2.2.2.2.2 (ρ + 1) β' (Nat.lt_succ_self ρ)).1)
  have hh : h = (⟨embX c g', hg⟩ : RFJ k n c ρ) * ⟨u', hu⟩ * ⟨colE c (ρ + 1) β', hb⟩ := Subtype.ext he
  rw [hh]
  refine map_mul_left_mul _ _ _ (map_mul_left_mul _ _ _ ?_ ?_) ?_
  · exact map_mul_left_of_conj _ _ hf _ _ (mp_embX ρ ν _ m g') fun q => Subtype.ext (mul_prodRFJ_embX ρ g' q)
  · exact map_mul_left_of_conj _ _ hf _ _ (mp_N ρ ν _ m ⟨u', hu'⟩) fun q => Subtype.ext (mul_prodRFJ_N ρ ⟨u', hu'⟩ q)
  · exact map_mul_left_of_conj _ _ hf _ _ (mp_colE ρ h1 h2 ν m β') fun q => Subtype.ext (mul_prodRFJ_colE ρ h1 h2 β' q)

end GlobalTheory.HaarR.LeftFJ
