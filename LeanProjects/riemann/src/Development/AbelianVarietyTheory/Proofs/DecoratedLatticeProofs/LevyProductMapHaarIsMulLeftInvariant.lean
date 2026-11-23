import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdRFJCoe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

theorem GlobalTheory.HaarR.map_prodR_isMulLeftInvariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (ν : Measure k), ν.IsAddHaarMeasure → ∀ m : Measure (GL n k), m.IsHaarMeasure → ((m.prod (volN ν n c p)).map (prodR p)).IsMulLeftInvariant := by
  intro k _ _ _ _ _ _ n _ _ c p h1 hp ν hν m hm
  haveI := hν
  haveI := hm
  haveI : BorelSpace (GL n k) := GlobalTheory.SplitFlip.borel_GL
  haveI : BorelSpace (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.borel_GL
  obtain ⟨hNc, -, hH, -, -⟩ := GlobalTheory.RootEx.VolN.volN_haar_and_modulus k n c p h1 hp ν
  haveI := hH
  haveI : LocallyCompactSpace (N k n c p) := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (N k n c p) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaFinite m := inferInstance
  haveI : SigmaFinite (volN ν n c p) := inferInstance
  have hE : Continuous (embX c : GL n k → GL (n ⊕ Fin c) k) := GlobalTheory.RootEx.QuotStep.continuous_embX
  have hφ : Measurable (prodR (k := k) (n := n) (c := c) p) :=
    (Continuous.subtype_mk ((hE.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)) _).measurable
  have hmulJ : ∀ g : R k n c p, Measurable (fun y : R k n c p => g * y) :=
    fun g => (continuous_mul_left g).measurable
  have hmulH : ∀ g : GL n k, Measurable (fun y : GL n k => g * y) := fun g => (continuous_mul_left g).measurable
  let μR : Measure (R k n c p) := (m.prod (volN ν n c p)).map (prodR p)
  let K : Subgroup (GL (n ⊕ Fin c) k) :=
    { carrier := {x | ∃ hx : x ∈ R k n c p,
        μR.map (fun y => (⟨x, hx⟩ : R k n c p) * y) = μR}
      one_mem' := ⟨one_mem _, by
        simp only [show (⟨1, one_mem _⟩ : R k n c p) = 1 from rfl, one_mul]
        exact Measure.map_id'⟩
      mul_mem' := by
        rintro a b ⟨ha, Ha⟩ ⟨hb, Hb⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have : (fun y : R k n c p => (⟨a * b, mul_mem ha hb⟩ : R k n c p) * y)
            = (fun y => (⟨a, ha⟩ : R k n c p) * y) ∘ (fun y => (⟨b, hb⟩ : R k n c p) * y) :=
          funext fun y => mul_assoc (⟨a, ha⟩ : R k n c p) ⟨b, hb⟩ y
        rw [this, ← Measure.map_map (hmulJ _) (hmulJ _), Hb, Ha]
      inv_mem' := by
        rintro a ⟨ha, Ha⟩
        refine ⟨inv_mem ha, ?_⟩
        conv_lhs => rw [← Ha]
        rw [Measure.map_map (hmulJ _) (hmulJ _)]
        have : (fun y : R k n c p => (⟨a⁻¹, inv_mem ha⟩ : R k n c p) * y) ∘
            (fun y => (⟨a, ha⟩ : R k n c p) * y) = id :=
          funext fun y => inv_mul_cancel_left (⟨a, ha⟩ : R k n c p) y
        rw [this, Measure.map_id] }
  have hXK : (embX c : GL n k →* GL (n ⊕ Fin c) k).range ≤ K := by
    rintro _ ⟨g₀, rfl⟩
    refine ⟨Subgroup.mem_sup_left ⟨g₀, rfl⟩, ?_⟩
    show Measure.map _ (Measure.map _ _) = _
    rw [Measure.map_map (hmulJ _) hφ]
    have : (fun y : R k n c p => (⟨embX c g₀, Subgroup.mem_sup_left ⟨g₀, rfl⟩⟩ : R k n c p) * y) ∘ prodR p
        = prodR p ∘ Prod.map (fun y : GL n k => g₀ * y) id := by
      funext q; apply Subtype.ext; simp [mul_assoc]
    rw [this, ← Measure.map_map hφ ((hmulH _).prodMap measurable_id),
      ← Measure.map_prod_map m (volN ν n c p) (hmulH _) measurable_id, map_mul_left_eq_self, Measure.map_id]
  have hNK : N k n c p ≤ K := by
    intro u₀ hu₀
    refine ⟨Subgroup.mem_sup_right hu₀, ?_⟩
    show Measure.map _ (Measure.map _ _) = _
    rw [Measure.map_map (hmulJ _) hφ]
    let cg : GL n k → N k n c p := fun g => ⟨(embX c g)⁻¹ * u₀ * embX c g, GlobalTheory.RootEx.Model.conj_mem hu₀ g⟩
    have hcg : Continuous cg :=
      Continuous.subtype_mk (((hE.inv).mul continuous_const).mul hE) _
    let F : GL n k → N k n c p → N k n c p := fun g u => cg g * u
    have hF : Measurable (Function.uncurry F) :=
      (((hcg.comp continuous_fst).mul continuous_snd)).measurable
    have hFm : ∀ g, Measure.map (F g) (volN ν n c p) = volN ν n c p := fun g => map_mul_left_eq_self _ _
    have hmp := (MeasurePreserving.id m).skew_product hF (Filter.Eventually.of_forall hFm)
    have : (fun y : R k n c p => (⟨u₀, Subgroup.mem_sup_right hu₀⟩ : R k n c p) * y) ∘ prodR p
        = prodR p ∘ (fun q : GL n k × N k n c p => (id q.1, F q.1 q.2)) := by
      funext q; apply Subtype.ext; simp [F, cg, mul_assoc]
    rw [this, ← Measure.map_map hφ hmp.measurable, hmp.map_eq]
  refine ⟨fun g => ?_⟩
  obtain ⟨hx, H⟩ := (sup_le hXK hNK) g.2
  exact H
