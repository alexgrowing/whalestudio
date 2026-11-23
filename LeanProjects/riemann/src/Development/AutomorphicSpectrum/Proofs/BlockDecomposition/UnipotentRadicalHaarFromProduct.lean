import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMulRightInvariantMapWittFlagCoordinatesHaar

noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg.RadHaar

theorem isMulLeftInvariant_map_of {X G : Type*} [MeasurableSpace X] [MeasurableSpace G] [Mul G] (P : Measure X)
    (e : X ≃ᵐ G) (h : ∀ q, ∃ T : X → X, MeasurePreserving T P P ∧ ∀ p, e (T p) = e q * e p) :
    (P.map e).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  obtain ⟨T, hT, hTe⟩ := h (e.symm g)
  have h1 : (fun x => g * x) = e ∘ T ∘ e.symm := by
    funext x
    simp [hTe]
  have hm : Measurable (fun x => g * x) := by
    rw [h1]
    exact e.measurable.comp (hT.measurable.comp e.symm.measurable)
  rw [Measure.map_map hm e.measurable]
  have h2 : (fun x => g * x) ∘ e = e ∘ T := by
    funext p
    simp [hTe]
  rw [h2, ← Measure.map_map e.measurable hT.measurable, hT.map_eq]

theorem measurePreserving_shear {A C : Type*} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A]
    [AddCommGroup C] [MeasurableSpace C] [MeasurableAdd₂ C] (κ : Measure A) (β : Measure C) [SFinite κ] [SFinite β]
    [κ.IsAddLeftInvariant] [β.IsAddLeftInvariant] {f : C → A} (hf : Measurable f) (b₀ : C) :
    MeasurePreserving (fun p : A × C => (p.1 + f p.2, p.2 + b₀)) (κ.prod β) (κ.prod β) := by
  have h1 : MeasurePreserving (fun p : C × A => (b₀ + p.1, f p.1 + p.2)) (β.prod κ) (β.prod κ) :=
    (measurePreserving_add_left β b₀).skew_product (g := fun c a => f c + a)
      (by exact (hf.comp measurable_fst).add measurable_snd)
      (Filter.Eventually.of_forall fun c => map_add_left_eq_self κ (f c))
  have h2 := (Measure.measurePreserving_swap (μ := β) (ν := κ)).comp
    (h1.comp (Measure.measurePreserving_swap (μ := κ) (ν := β)))
  have hfun : (fun p : A × C => (p.1 + f p.2, p.2 + b₀)) =
      Prod.swap ∘ (fun p : C × A => (b₀ + p.1, f p.1 + p.2)) ∘ Prod.swap := by
    funext p
    exact Prod.ext (add_comm _ _) (add_comm _ _)
  rw [hfun]
  exact h2

private theorem isMulRightInvariant_map_of_exists_measurePreserving {X G : Type*} [MeasurableSpace X] [MeasurableSpace G] [Mul G] (P : Measure X)
    (e : X ≃ᵐ G) (h : ∀ q, ∃ T : X → X, MeasurePreserving T P P ∧ ∀ p, e (T p) = e p * e q) :
    (P.map e).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  obtain ⟨T, hT, hTe⟩ := h (e.symm g)
  have h1 : (fun x => x * g) = e ∘ T ∘ e.symm := by
    funext x
    simp [hTe]
  have hm : Measurable (fun x => x * g) := by
    rw [h1]
    exact e.measurable.comp (hT.measurable.comp e.symm.measurable)
  rw [Measure.map_map hm e.measurable]
  have h2 : (fun x => x * g) ∘ e = e ∘ T := by
    funext p
    simp [hTe]
  rw [h2, ← Measure.map_map e.measurable hT.measurable, hT.map_eq]

theorem haar_of_shear {A C G : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A] [LocallyCompactSpace A]
    [AddCommGroup C] [TopologicalSpace C] [IsTopologicalAddGroup C]
    [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C] [LocallyCompactSpace C]
    [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (e : A × C ≃ₜ G) (f : C → C → A) (hf : Continuous fun x : C × C => f x.1 x.2)
    (hmul : ∀ c b c' b', e (c, b) * e (c', b') = e (c + (c' + f b b'), b + b'))
    (κ : Measure A) (β : Measure C) [κ.IsAddHaarMeasure] [β.IsAddHaarMeasure] :
    ((κ.prod β).map e).IsHaarMeasure ∧ ((κ.prod β).map e).IsMulRightInvariant := by
  have hfc : IsFiniteMeasureOnCompacts ((κ.prod β).map e) := by
    refine ⟨fun K hK => ?_⟩
    change (κ.prod β).map e.toMeasurableEquiv K < ⊤
    rw [MeasurableEquiv.map_apply]
    exact (e.isCompact_preimage.2 hK).measure_lt_top
  have hop : Measure.IsOpenPosMeasure ((κ.prod β).map e) := by
    refine ⟨fun U hU hne => ?_⟩
    change (κ.prod β).map e.toMeasurableEquiv U ≠ 0
    rw [MeasurableEquiv.map_apply]
    exact (hU.preimage e.continuous).measure_ne_zero _ (hne.preimage e.surjective)
  have hl : ((κ.prod β).map e).IsMulLeftInvariant := by
    refine isMulLeftInvariant_map_of (κ.prod β) e.toMeasurableEquiv ?_
    rintro ⟨c, b⟩
    refine ⟨fun p => (p.1 + (c + f b p.2), p.2 + b),
      measurePreserving_shear κ β ((hf.comp (continuous_const.prodMk continuous_id)).measurable.const_add c) b, ?_⟩
    rintro ⟨c', b'⟩
    change e _ = e (c, b) * e (c', b')
    rw [hmul]
    congr 1
    exact Prod.ext (add_left_comm _ _ _) (add_comm _ _)
  have hr : ((κ.prod β).map e).IsMulRightInvariant := by
    refine isMulRightInvariant_map_of_exists_measurePreserving (κ.prod β) e.toMeasurableEquiv ?_
    rintro ⟨c, b⟩
    refine ⟨fun p => (p.1 + (c + f p.2 b), p.2 + b),
      measurePreserving_shear κ β ((hf.comp (continuous_id.prodMk continuous_const)).measurable.const_add c) b, ?_⟩
    rintro ⟨c', b'⟩
    change e _ = e (c', b') * e (c, b)
    rw [hmul]
  exact ⟨{ toIsFiniteMeasureOnCompacts := hfc, toIsMulLeftInvariant := hl, toIsOpenPosMeasure := hop }, hr⟩

variable {D : D7} {B W : HSp D} {t : ℕ} (d : HypDec B W t)

def coordB (q : GA D B) : Mx D t W.rank := d.pX ⬝ mt B q ⬝ d.j0

def coordC (q : GA D B) : Mx D t t :=
  d.pX ⬝ mt B q ⬝ d.jY + half D • (coordB d q ⬝ plus W (coordB d q))

theorem pX_nn (c : skewA D t) (b : Mx D t W.rank) : d.pX ⬝ mt B (d.nC c * d.nB b) =
    d.pX + b ⬝ d.p0 - (half D • (b ⬝ plus W b)) ⬝ d.pY + c.1 ⬝ d.pY := by
  rw [GlobalTheory.MixModel.mt_mul, ← Matrix.mul_assoc, GlobalTheory.MixModel.HypDec.pX_nC, Matrix.add_mul, Matrix.mul_assoc, GlobalTheory.MixModel.HypDec.pY_nB, GlobalTheory.MixModel.HypDec.pX_nB]

theorem coordB_nn (c : skewA D t) (b : Mx D t W.rank) : coordB d (d.nC c * d.nB b) = b := by
  rw [coordB, pX_nn]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, GlobalTheory.MixModel.HypDec.pX_j0, GlobalTheory.MixModel.HypDec.p0_j0, GlobalTheory.MixModel.HypDec.pY_j0, Matrix.mul_one,
    Matrix.mul_zero, zero_add, sub_zero, add_zero]

theorem coordC_nn (c : skewA D t) (b : Mx D t W.rank) : coordC d (d.nC c * d.nB b) = c.1 := by
  rw [coordC, coordB_nn, pX_nn]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, GlobalTheory.MixModel.HypDec.pX_jY, GlobalTheory.MixModel.HypDec.p0_jY, GlobalTheory.MixModel.HypDec.pY_jY, Matrix.mul_one,
    Matrix.mul_zero]
  abel

section Top

local instance topRingAE : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1

local instance topGrpGA (S : HSp D) : IsTopologicalGroup (GA D S) := (Formalism.IndefR.Eqv.ga_facts D S).1

theorem continuous_coordB : Continuous (coordB d) := by
  show Continuous fun q : GA D B => d.pX * mt B q * d.j0
  exact (continuous_const.matrix_mul (GlobalTheory.MixModel.continuous_mt B)).matrix_mul continuous_const

theorem continuous_coordC : Continuous (coordC d) := by
  have hB := continuous_coordB d
  have hP : Continuous fun q : GA D B => GlobalTheory.MixModel.giA W * GlobalTheory.MixModel.adj (coordB d q) :=
    continuous_const.matrix_mul (GlobalTheory.MixModel.continuous_adj.comp hB)
  have hS : Continuous fun q : GA D B =>
      GlobalTheory.MixModel.half D • (coordB d q * (GlobalTheory.MixModel.giA W * GlobalTheory.MixModel.adj (coordB d q))) :=
    (hB.matrix_mul hP).const_smul (GlobalTheory.MixModel.half D)
  have hA : Continuous fun q : GA D B => d.pX * mt B q * d.jY :=
    (continuous_const.matrix_mul (GlobalTheory.MixModel.continuous_mt B)).matrix_mul continuous_const
  exact hA.add hS

theorem coordC_mem (n : radN d) : coordC d n.1.1 ∈ skewA D t := by
  obtain ⟨c, b, h⟩ := n.2
  rw [h, coordC_nn]
  exact c.2

def coordHomeo : (skewA D t × Mx D t W.rank) ≃ₜ radN d where
  toFun p := ⟨⟨d.nC p.1 * d.nB p.2, mul_mem (GlobalTheory.GodementSectionReduction.nC_mem d _) (GlobalTheory.GodementSectionReduction.nB_mem d _)⟩, p.1, p.2, rfl⟩
  invFun n := (⟨coordC d n.1.1, coordC_mem d n⟩, coordB d n.1.1)
  left_inv p := by
    apply Prod.ext
    · exact Subtype.ext (coordC_nn d p.1 p.2)
    · exact coordB_nn d p.1 p.2
  right_inv n := by
    obtain ⟨c, b, h⟩ := n.2
    apply Subtype.ext
    apply Subtype.ext
    change d.nC ⟨coordC d n.1.1, coordC_mem d n⟩ * d.nB (coordB d n.1.1) = n.1.1
    have e1 : (⟨coordC d n.1.1, coordC_mem d n⟩ : skewA D t) = c :=
      Subtype.ext (by change coordC d n.1.1 = c.1; rw [h, coordC_nn])
    rw [e1, h, coordB_nn]
  continuous_toFun :=
    Continuous.subtype_mk (Continuous.subtype_mk
      ((d.continuous_nC.comp continuous_fst).mul (d.continuous_nB.comp continuous_snd)) _) _
  continuous_invFun :=
    (Continuous.subtype_mk ((continuous_coordC d).comp (continuous_subtype_val.comp continuous_subtype_val)) _).prodMk
      ((continuous_coordB d).comp (continuous_subtype_val.comp continuous_subtype_val))

theorem coordHomeo_coe (p : skewA D t × Mx D t W.rank) :
    (((coordHomeo d p : radN d) : GlobalTheory.RegSW.stab d) : GA D B) = d.nC p.1 * d.nB p.2 := rfl

end Top

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in

theorem exists_coord : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (radN d)] (κ : Measure (skewA D t)) (β : Measure (Mx D t W.rank)), κ.IsAddHaarMeasure → β.IsAddHaarMeasure → ∃ Ψ : (skewA D t × Mx D t W.rank) ≃ₜ radN d, (∀ p, (((Ψ p : GlobalTheory.RegSW.stab d) : GA D B)) = d.nC p.1 * d.nB p.2) ∧ ((κ.prod β).map Ψ).IsHaarMeasure ∧ ((κ.prod β).map Ψ).IsMulRightInvariant := by
  intro D B W t d _ κ β hκ hβ
  have hc := coordHomeo_coe d
  obtain ⟨i1, i2, i3, i4, i5⟩ := Formalism.IndefR.Eqv.ae_facts D
  obtain ⟨j1, j2, j3, j4, j5⟩ := Formalism.IndefR.Eqv.ga_facts D B
  have : T2Space (Mx D t t) := inferInstanceAs (T2Space (Fin t → Fin t → AE D))
  have : BorelSpace (Mx D t t) := ⟨rfl⟩
  have : SecondCountableTopology (Mx D t t) := inferInstanceAs (SecondCountableTopology (Fin t → Fin t → AE D))
  have : LocallyCompactSpace (Mx D t t) := inferInstanceAs (LocallyCompactSpace (Fin t → Fin t → AE D))
  have : T2Space (Mx D t W.rank) := inferInstanceAs (T2Space (Fin t → Fin W.rank → AE D))
  have : BorelSpace (Mx D t W.rank) := ⟨rfl⟩
  have : SecondCountableTopology (Mx D t W.rank) := inferInstanceAs (SecondCountableTopology (Fin t → Fin W.rank → AE D))
  have : LocallyCompactSpace (Mx D t W.rank) := inferInstanceAs (LocallyCompactSpace (Fin t → Fin W.rank → AE D))
  have q3 : SecondCountableTopology (skewA D t) :=
    inferInstanceAs (SecondCountableTopology ((skewA D t : Set (Mx D t t))))
  have hcl : IsClosed ((skewA D t : Set (Mx D t t))) := by
    show IsClosed {c : Mx D t t | GlobalTheory.MixModel.adj c = -c}
    exact isClosed_eq GlobalTheory.MixModel.continuous_adj continuous_neg
  have : LocallyCompactSpace (skewA D t) := hcl.locallyCompactSpace
  refine ⟨coordHomeo d, hc, ?_⟩
  refine haar_of_shear (coordHomeo d) (fun b b' => cComm W b b') (GlobalTheory.Unf.HaarCoord.continuous_cComm W t) ?_ κ β
  intro c b c' b'
  apply Subtype.ext
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hc, hc, hc]
  dsimp only
  rw [GlobalTheory.MixModel.HypDec.nC_add, GlobalTheory.MixModel.HypDec.nC_add]
  simp only [mul_assoc]
  rw [← mul_assoc (d.nB b) (d.nC c'), ← GlobalTheory.MixModel.HypDec.nC_mul_nB d b c', mul_assoc (d.nC c'), GlobalTheory.MixModel.HypDec.nB_mul_nB,
    ← GlobalTheory.MixModel.HypDec.nC_mul_nB d (b + b') (cComm W b b')]

end GlobalTheory.CompanionTheory.QKAvg.RadHaar
