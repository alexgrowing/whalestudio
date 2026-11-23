import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentCoordinatesStatement
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountStA

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.BlockMeas

abbrev Yf (k r : ℕ) : Type := (NEntry.Idx k r → ℂ) × (UTr r → ℂ) × (Fin r → ℝ)

abbrev Ys (k r : ℕ) : Type :=
  ((UTr r → ℂ) × (Fin r → Fin (k + 1) → ℂ)) × ((UTr r → ℂ) × (Fin r → ℝ))

abbrev Zb (ι : Type) (k r : ℕ) : Type :=
  (UTr r → ι → ℂ) × (Fin r → ι → Fin (k + 1) → ℂ) × (UTr r → ι → ℂ) × (Fin r → ι → ℝ)

def sp (ι : Type) (k r : ℕ) (y : ι → Yf k r) : Zb ι k r :=
  (fun p w => (y w).1 (NEntry.idx k r (.inl p)), fun a w j => (y w).1 (NEntry.idx k r (.inr (a, j))),
    fun p w => (y w).2.1 p, fun a w => (y w).2.2 a)

def sq (ι : Type) (k r : ℕ) (y : ι → Ys k r) : Zb ι k r :=
  (fun p w => (y w).1.1 p, fun a w => (y w).1.2 a, fun p w => (y w).2.1 p, fun a w => (y w).2.2 a)

theorem sq_mp (ι : Type) [Fintype ι] (k r : ℕ) : MeasurePreserving (sq ι k r) volume volume := by
  have h1 := volume_measurePreserving_arrowProdEquivProdArrow ((UTr r → ℂ) × (Fin r → Fin (k + 1) → ℂ))
    ((UTr r → ℂ) × (Fin r → ℝ)) ι
  have h2 := volume_measurePreserving_arrowProdEquivProdArrow (UTr r → ℂ) (Fin r → Fin (k + 1) → ℂ) ι
  have h3 := volume_measurePreserving_arrowProdEquivProdArrow (UTr r → ℂ) (Fin r → ℝ) ι
  have s1 : MeasurePreserving (fun (f : ι → UTr r → ℂ) (p : UTr r) (i : ι) => f i p) volume volume :=
    ReciprocityTheory.GeometryOfNumbersTheory.measurePreserving_swapPi (volume : Measure ℂ)
  have s2 : MeasurePreserving (fun (f : ι → Fin r → Fin (k + 1) → ℂ) (p : Fin r) (i : ι) => f i p) volume volume :=
    ReciprocityTheory.GeometryOfNumbersTheory.measurePreserving_swapPi (volume : Measure (Fin (k + 1) → ℂ))
  have s3 : MeasurePreserving (fun (f : ι → Fin r → ℝ) (p : Fin r) (i : ι) => f i p) volume volume :=
    ReciprocityTheory.GeometryOfNumbersTheory.measurePreserving_swapPi (volume : Measure ℝ)
  haveI u0 : SigmaFinite (volume : Measure (Fin (k + 1) → ℂ)) := inferInstance
  haveI u1 : SigmaFinite (volume : Measure (Fin r → Fin (k + 1) → ℂ)) := inferInstance
  haveI u2 : SigmaFinite (volume : Measure (ι → Fin (k + 1) → ℂ)) := inferInstance
  haveI t1 : SigmaFinite (volume : Measure (ι → UTr r → ℂ)) := inferInstance
  haveI t2 : SigmaFinite (volume : Measure (ι → Fin r → Fin (k + 1) → ℂ)) := inferInstance
  haveI t3 : SigmaFinite (volume : Measure (UTr r → ι → ℂ)) := inferInstance
  haveI t4 : SigmaFinite (volume : Measure (Fin r → ι → Fin (k + 1) → ℂ)) := inferInstance
  have a := s1.prod s2
  have b := s1.prod s3
  have c := (a.prod b).comp ((h2.prod h3).comp h1)
  exact (volume_preserving_prodAssoc).comp c

theorem pi_smul (ι : Type) [Fintype ι] {X : Type} [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν] (c : NNReal) :
    Measure.pi (fun _ : ι => (c : ℝ≥0∞) • ν) = ((c : ℝ≥0∞) ^ Fintype.card ι) • Measure.pi (fun _ : ι => ν) := by
  haveI : SigmaFinite ((c : ℝ≥0∞) • ν) := by
    have e : (c : ℝ≥0∞) • ν = c • ν := by
      ext s _
      simp [Measure.smul_apply]
    rw [e]
    infer_instance
  refine Measure.pi_eq fun s hs => ?_
  simp [Measure.smul_apply, Measure.pi_pi, Finset.prod_mul_distrib, smul_eq_mul]

theorem mem_iff (ι : Type) (k r : ℕ) (DU : UTr r → Set (ι → ℂ)) (DH : Fin r → Set (ι → Fin (k + 1) → ℂ))
    (DC : UTr r → Set (ι → ℂ)) (DG : Fin r → Set (ι → ℝ)) (x : ι → Mt k r) :
    (∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet ι k r DU DH DC DG β) ↔
      sp ι k r (fun w => nCoords k r (x w)) ∈
        Set.univ.pi DU ×ˢ Set.univ.pi DH ×ˢ Set.univ.pi DC ×ˢ Set.univ.pi DG := by
  simp only [Sum.forall, Set.mem_prod, Set.mem_univ_pi]
  exact Iff.rfl

theorem measure_blocks : ∀ (ι : Type) [Fintype ι] (k r : ℕ) (DU : UTr r → Set (ι → ℂ)) (DH : Fin r → Set (ι → Fin (k + 1) → ℂ)) (DC : UTr r → Set (ι → ℂ)) (DG : Fin r → Set (ι → ℝ)), (∀ p, MeasurableSet (DU p)) → (∀ a, MeasurableSet (DH a)) → (∀ p, MeasurableSet (DC p)) → (∀ a, MeasurableSet (DG a)) → MeasurableSet {x : ι → Mt k r | (∀ w, Matrix.of (x w) ∈ Nset k r) ∧ ∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet ι k r DU DH DC DG β} ∧ (Measure.pi fun _ : ι => haarLie (Nset k r) 1) {x : ι → Mt k r | (∀ w, Matrix.of (x w) ∈ Nset k r) ∧ ∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet ι k r DU DH DC DG β} = (2 : ℝ≥0∞) ^ (Fintype.card ι * (r * (r - 1) + r * (k + 1))) * ((∏ p, volume (DU p)) * (∏ a, volume (DH a)) * (∏ p, volume (DC p)) * ∏ a, volume (DG a)) := by
  intro ι _ k r DU DH DC DG hU hH hC hG
  obtain ⟨⟨hσ, -, hnull, -⟩, -, -, hmap⟩ := GlobalTheory.T.haar_lie_nilpotent_coordinates k r
  set μ := haarLie (Nset k r) 1 with hμ
  set e := r * (r - 1) + r * (k + 1) with he
  set F : (ι → Mt k r) → (ι → Yf k r) := fun x w => nCoords k r (x w) with hFdef
  set R : Set (Zb ι k r) := Set.univ.pi DU ×ˢ Set.univ.pi DH ×ˢ Set.univ.pi DC ×ˢ Set.univ.pi DG with hRdef
  have hF : Measurable F :=
    measurable_pi_lambda _ fun w => NEntry.cont_nCoords.measurable.comp (measurable_pi_apply w)
  have hsp : Measurable (sp ι k r) := by
    unfold sp
    fun_prop
  have hR : MeasurableSet R :=
    (MeasurableSet.univ_pi hU).prod ((MeasurableSet.univ_pi hH).prod
      ((MeasurableSet.univ_pi hC).prod (MeasurableSet.univ_pi hG)))
  have hNm : MeasurableSet {x : Mt k r | Matrix.of x ∈ Nset k r} := by
    have : IsClosed {x : Mt k r | Matrix.of x ∈ Nset k r} := GlobalTheory.Amp.NLie.closed_N
    exact this.measurableSet
  have hNi : MeasurableSet {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} := by
    have : {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} =
        Set.univ.pi fun _ => {x : Mt k r | Matrix.of x ∈ Nset k r} := by
      ext x
      simp
    rw [this]
    exact MeasurableSet.univ_pi fun _ => hNm
  have hS : {x : ι → Mt k r | (∀ w, Matrix.of (x w) ∈ Nset k r) ∧
      ∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet ι k r DU DH DC DG β} =
      (sp ι k r ∘ F) ⁻¹' R ∩ {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Function.comp_apply]
    rw [mem_iff]
    exact and_comm
  rw [hS]
  refine ⟨((hsp.comp hF) hR).inter hNi, ?_⟩
  have hconull : (Measure.pi fun _ : ι => μ) {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r}ᶜ = 0 := by
    have : {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r}ᶜ ⊆
        ⋃ w, Function.eval w ⁻¹' {x : Mt k r | Matrix.of x ∉ Nset k r} := by
      intro x hx
      simpa using hx
    refine measure_mono_null this (measure_iUnion_null fun w => ?_)
    exact Measure.pi_eval_preimage_null _ hnull
  rw [measure_inter_conull hconull]
  have hc : ((2 : ℝ≥0∞) ^ e) = ((2 ^ e : NNReal) : ℝ≥0∞) := by
    push_cast
    rfl
  haveI : SigmaFinite (μ.map (nCoords k r)) := by
    rw [hmap, hc]
    have e' : ((2 ^ e : NNReal) : ℝ≥0∞) • (volume : Measure (Yf k r)) = (2 ^ e : NNReal) • volume := by
      ext s _
      simp [Measure.smul_apply]
    rw [e']
    infer_instance
  have hpi : (Measure.pi fun _ : ι => μ).map F = Measure.pi fun _ : ι => μ.map (nCoords k r) :=
    Measure.pi_map_pi (fun _ => NEntry.cont_nCoords.measurable.aemeasurable)
  have hpre : (sp ι k r ∘ F) ⁻¹' R = F ⁻¹' (sp ι k r ⁻¹' R) := rfl
  rw [hpre, ← Measure.map_apply hF (hsp hR), hpi, hmap, hc, pi_smul, Measure.smul_apply, smul_eq_mul]

  have hΦ : MeasurePreserving (fun (y : ι → Ys k r) w => ((NEntry.glue (y w).1, (y w).2) : Yf k r)) volume volume :=
    volume_preserving_pi (f := fun _ : ι => Prod.map (NEntry.glue (k := k) (r := r)) id)
      fun _ => (NEntry.glue_mp (k := k) (r := r)).1.prod (MeasurePreserving.id _)
  have hcomp : (fun (y : ι → Ys k r) w => ((NEntry.glue (y w).1, (y w).2) : Yf k r)) ⁻¹' (sp ι k r ⁻¹' R) =
      sq ι k r ⁻¹' R := by
    ext y
    have : sp ι k r (fun w => ((NEntry.glue (y w).1, (y w).2) : Yf k r)) = sq ι k r y := by
      simp [sp, sq, NEntry.glue]
    simp only [Set.mem_preimage, this]
  have hvol : (Measure.pi fun _ : ι => (volume : Measure (Yf k r))) (sp ι k r ⁻¹' R) = volume R := by
    have h1 := hΦ.measure_preimage (hsp hR).nullMeasurableSet
    rw [hcomp, (sq_mp ι k r).measure_preimage hR.nullMeasurableSet] at h1
    exact h1.symm
  haveI u0 : SigmaFinite (volume : Measure (Fin (k + 1) → ℂ)) := inferInstance
  haveI u2 : SigmaFinite (volume : Measure (ι → Fin (k + 1) → ℂ)) := inferInstance
  haveI t3 : SigmaFinite (volume : Measure (UTr r → ι → ℂ)) := inferInstance
  haveI t4 : SigmaFinite (volume : Measure (Fin r → ι → Fin (k + 1) → ℂ)) := inferInstance
  haveI t5 : SigmaFinite (volume : Measure (Fin r → ι → ℝ)) := inferInstance
  have hpow : ((2 ^ e : NNReal) : ℝ≥0∞) ^ Fintype.card ι = (2 : ℝ≥0∞) ^ (Fintype.card ι * e) := by
    rw [← hc, ← pow_mul, mul_comm]
  rw [hvol, hRdef, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
    Measure.volume_eq_prod, Measure.prod_prod, volume_pi_pi, volume_pi_pi, volume_pi_pi, volume_pi_pi, hpow]
  simp only [mul_assoc]

end GlobalTheory.SnMass.VolN.BlockMeas
