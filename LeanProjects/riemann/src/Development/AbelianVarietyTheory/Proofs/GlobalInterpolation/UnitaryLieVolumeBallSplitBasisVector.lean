import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.OmegaSplit

theorem mp_interchange {A B C D : Type} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [MeasurableSpace D] (a : Measure A) (b : Measure B) (c : Measure C) (d : Measure D)
    [SFinite a] [SFinite b] [SFinite c] [SFinite d] :
    MeasurePreserving (fun x : (A × B) × (C × D) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
      ((a.prod b).prod (c.prod d)) ((a.prod c).prod (b.prod d)) := by
  have e1 := measurePreserving_prodAssoc a b (c.prod d)
  have e2 := (measurePreserving_prodAssoc b c d).symm
  have e3 := (Measure.measurePreserving_swap (μ := b) (ν := c)).prod (MeasurePreserving.id d)
  have e4 := measurePreserving_prodAssoc c b d
  have e5 := (measurePreserving_prodAssoc a c (b.prod d)).symm
  exact e5.comp (((MeasurePreserving.id a).prod (e4.comp (e3.comp e2))).comp e1)

theorem mp_diag : MeasurePreserving
    (fun t : ℝ × ℝ => ((t.1 : ℂ) * Complex.I + Complex.I * ((t.2 : ℂ) * Complex.I)))
    ((volume : Measure ℝ).prod volume) volume := by
  have h2 := (rotation (Circle.exp (Real.pi / 2))).measurePreserving
  have h3 := Complex.volume_preserving_equiv_real_prod.symm
  have h4 := h2.comp h3
  have h5 : (fun t : ℝ × ℝ => ((t.1 : ℂ) * Complex.I + Complex.I * ((t.2 : ℂ) * Complex.I))) =
      rotation (Circle.exp (Real.pi / 2)) ∘ Complex.measurableEquivRealProd.symm := by
    funext ab
    simp [rotation_apply, Complex.measurableEquivRealProd, Complex.ext_iff]
  rw [h5]
  exact h4

theorem mp_unit (s : ℂ) (hs : ‖s‖ = 1) : MeasurePreserving (fun z : ℂ => s * z) volume volume := by
  have h := (rotation ⟨s, by simpa [Submonoid.unitSphere] using hs⟩).measurePreserving
  exact h

theorem mp_colrow {ι : Type} [Fintype ι] (s : ι → ℂ) (hs : ∀ i, ‖s i‖ = 1) :
    MeasurePreserving (fun z : (ι → ℂ) × (ι → ℂ) =>
      ((fun i => z.1 i + Complex.I * z.2 i : ι → ℂ),
        (fun i => s i * (starRingEnd ℂ) (z.1 i) + Complex.I * (s i * (starRingEnd ℂ) (z.2 i)) : ι → ℂ)))
      (((2 : ℝ≥0∞) ^ Fintype.card ι • volume : Measure (ι → ℂ)).prod
        ((2 : ℝ≥0∞) ^ Fintype.card ι • volume : Measure (ι → ℂ)))
      ((volume : Measure (ι → ℂ)).prod volume) := by
  set n := Fintype.card ι with hn
  have hI : MeasurePreserving (fun (z : ι → ℂ) i => Complex.I * z i) volume volume :=
    volume_preserving_pi fun _ => mp_unit _ Complex.norm_I
  have hS : MeasurePreserving (fun (z : ι → ℂ) i => s i * (starRingEnd ℂ) (z i)) volume volume :=
    volume_preserving_pi (f := fun i z => s i * (starRingEnd ℂ) z) fun i =>
      (mp_unit _ (hs i)).comp Complex.conjLIE.measurePreserving
  have hsc : MeasurePreserving (fun z : ι → ℂ => (-2 : ℝ) • z)
      (((2 : ℝ≥0∞) ^ n * 2 ^ n) • volume) volume := by
    refine ⟨measurable_const_smul _, ?_⟩
    rw [Measure.map_smul, Measure.map_addHaar_smul _ (by norm_num), smul_smul]
    have hf : Module.finrank ℝ (ι → ℂ) = n * 2 := by
      simp [Module.finrank_pi_fintype, hn]
    have h1 : ENNReal.ofReal |((-2 : ℝ) ^ Module.finrank ℝ (ι → ℂ))⁻¹| = ((2 : ℝ≥0∞) ^ n * 2 ^ n)⁻¹ := by
      rw [hf, abs_inv, abs_pow, abs_neg, abs_two, ENNReal.ofReal_inv_of_pos (by positivity),
        ENNReal.ofReal_pow (by norm_num), mul_two, pow_add]
      simp
    rw [h1, ENNReal.mul_inv_cancel (by simp) (by finiteness), one_smul]
  have hsh1 := measurePreserving_add_prod (volume : Measure (ι → ℂ)) (volume : Measure (ι → ℂ))
  have hsh2 := measurePreserving_prod_add (volume : Measure (ι → ℂ)) (volume : Measure (ι → ℂ))
  have hA := (hsh1.comp ((MeasurePreserving.id volume).prod hI)).smul_measure ((2 : ℝ≥0∞) ^ n * 2 ^ n)
  have hB := ((MeasurePreserving.id volume).prod hS).comp
    (hsh2.comp ((MeasurePreserving.id (volume : Measure (ι → ℂ))).prod hsc))
  haveI : SFinite (((2 : ℝ≥0∞) ^ n • volume : Measure (ι → ℂ))) := inferInstance
  rw [Measure.prod_smul_right] at hB
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  convert hB.comp hA using 1
  funext z
  ext i
  · simp
  · simp [map_ofNat]
    ring

def idxEquiv (ι : Type) : (Unit ⊕ (ι ⊕ ι)) ⊕ (ι × ι) ≃ Option ι × Option ι where
  toFun x := match x with
    | .inl (.inl _) => (none, none)
    | .inl (.inr (.inl a)) => (some a, none)
    | .inl (.inr (.inr b)) => (none, some b)
    | .inr (a, b) => (some a, some b)
  invFun y := match y with
    | (none, none) => .inl (.inl ())
    | (some a, none) => .inl (.inr (.inl a))
    | (none, some b) => .inl (.inr (.inr b))
    | (some a, some b) => .inr (a, b)
  left_inv := by rintro ((_ | _ | _) | ⟨_, _⟩) <;> rfl
  right_inv := by rintro ⟨_ | _, _ | _⟩ <;> rfl

theorem exists_assemble {ι κ : Type} [Fintype ι] [Fintype κ] (e : Option ι ≃ κ) :
    ∃ f : (ℂ × ((ι → ℂ) × (ι → ℂ))) × (ι × ι → ℂ) → (κ × κ → ℂ),
      MeasurePreserving f (((volume : Measure ℂ).prod
        ((volume : Measure (ι → ℂ)).prod volume)).prod volume) volume ∧
      ∀ x, f x (e none, e none) = x.1.1 ∧ (∀ a, f x (e (some a), e none) = x.1.2.1 a) ∧
        (∀ b, f x (e none, e (some b)) = x.1.2.2 b) ∧
        ∀ a b, f x (e (some a), e (some b)) = x.2 (a, b) := by
  have h1 := (volume_preserving_funUnique Unit ℂ).symm
  have h2 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : ι ⊕ ι => ℂ)
  have h3 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Unit ⊕ (ι ⊕ ι) => ℂ)
  have h4 := volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : (Unit ⊕ (ι ⊕ ι)) ⊕ (ι × ι) => ℂ)
  have h5 := volume_measurePreserving_piCongrLeft (fun _ : κ × κ => ℂ)
    ((idxEquiv ι).trans (e.prodCongr e))
  refine ⟨_, h5.comp (h4.comp ((h3.comp (h1.prod h2)).prod (MeasurePreserving.id volume))), ?_⟩
  intro x
  have key := fun y i => MeasurableEquiv.piCongrLeft_apply_apply
    ((idxEquiv ι).trans (e.prodCongr e)) (β := fun _ : κ × κ => ℂ) y i
  exact ⟨key _ (.inl (.inl ())), fun a => key _ (.inl (.inr (.inl a))),
    fun b => key _ (.inl (.inr (.inr b))), fun a b => key _ (.inr (a, b))⟩

variable {P Q P' Q' : ℕ}

theorem Jpq_eq (P Q : ℕ) : Formalism.UG.Jpq P Q = Matrix.diagonal fun i => (sg i : ℂ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Formalism.UG.Jpq, sg, Matrix.one_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem sg_mul_self (i : Fin P ⊕ Fin Q) : (sg i : ℂ) * sg i = 1 := by
  rcases sg_eq i with h | h <;> rw [h] <;> simp

theorem norm_sg (i : Fin P ⊕ Fin Q) : ‖(sg i : ℂ)‖ = 1 := by
  rcases sg_eq i with h | h <;> rw [h] <;> simp

theorem mem_lieU_iff (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    X ∈ lieU P Q ↔ ∀ a b, X a b = -((sg a : ℂ) * sg b) * (starRingEnd ℂ) (X b a) := by
  change Xᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X = 0 ↔ _
  rw [Jpq_eq, ← Matrix.ext_iff]
  refine forall_congr' fun a => forall_congr' fun b => ?_
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, conjTranspose_apply,
    Matrix.zero_apply, Complex.star_def]
  have ha := sg_mul_self a
  constructor
  · intro h
    linear_combination (sg a : ℂ) * h - X a b * ha
  · intro h
    linear_combination (sg a : ℂ) * h - (sg b : ℂ) * (starRingEnd ℂ) (X b a) * ha

def coord (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (he : SignCompat e) :
    lieU P Q →ₗ[ℝ] (ℝ × Sp P' Q') × lieU P' Q' where
  toFun X := (((X.val (e none) (e none)).im, fun a => X.val (e (some a)) (e none)),
    ⟨Matrix.of fun a b => X.val (e (some a)) (e (some b)), by
      rw [mem_lieU_iff]
      intro a b
      have := (mem_lieU_iff _).1 X.2 (e (some a)) (e (some b))
      rw [he, he] at this
      exact this⟩)
  map_add' X Y := by
    refine Prod.ext (Prod.ext ?_ rfl) rfl
    simp
  map_smul' c X := by
    refine Prod.ext (Prod.ext ?_ rfl) rfl
    simp

theorem diag_eq (X : lieU P Q) (k : Fin P ⊕ Fin Q) :
    X.val k k = ((X.val k k).im : ℂ) * Complex.I := by
  have h := (mem_lieU_iff _).1 X.2 k k
  rw [sg_mul_self] at h
  have h2 := congrArg Complex.re h
  simp at h2
  apply Complex.ext <;> simp
  linarith

theorem row_eq (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (X : lieU P Q) (b) :
    X.val (e none) (e (some b)) = -((sg (e none) : ℂ) * sg (e (some b))) *
      (starRingEnd ℂ) (X.val (e (some b)) (e none)) :=
  (mem_lieU_iff _).1 X.2 _ _

theorem coord_injective (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (he : SignCompat e) :
    Function.Injective (coord e he) := by
  rw [injective_iff_map_eq_zero]
  intro X h
  have h1 : (X.val (e none) (e none)).im = 0 := congrArg (fun t => t.1.1) h
  have h2 : ∀ a, X.val (e (some a)) (e none) = 0 := fun a => congrArg (fun t => t.1.2 a) h
  have h3 : ∀ a b, X.val (e (some a)) (e (some b)) = 0 := fun a b =>
    congrArg (fun t => t.2.val a b) h
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  rcases i with _ | i <;> rcases j with _ | j
  · rw [diag_eq, h1]; simp
  · rw [row_eq, h2]; simp
  · exact h2 i
  · exact h3 i j

theorem coord_surjective (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (he : SignCompat e) :
    Function.Surjective (coord e he) := by
  rintro ⟨⟨θ, z⟩, Y⟩
  let g : Option (Fin P' ⊕ Fin Q') → Option (Fin P' ⊕ Fin Q') → ℂ := fun i j =>
    match i, j with
    | none, none => (θ : ℂ) * Complex.I
    | some a, none => z a
    | none, some b => -((sg (e none) : ℂ) * sg (e (some b))) * (starRingEnd ℂ) (z b)
    | some a, some b => Y.val a b
  refine ⟨⟨Matrix.of fun i j => g (e.symm i) (e.symm j), ?_⟩, ?_⟩
  · rw [mem_lieU_iff]
    intro i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    simp only [Matrix.of_apply, Equiv.symm_apply_apply]
    rcases i with _ | i <;> rcases j with _ | j
    · rw [sg_mul_self]; simp [g]
    · rfl
    · have h1 := sg_mul_self (e none)
      have h2 := sg_mul_self (e (some i))
      simp only [g, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_conj]
      linear_combination (-z i) * h1 - z i * (sg (e none) : ℂ) * (sg (e none) : ℂ) * h2
    · rw [he, he]
      exact (mem_lieU_iff _).1 Y.2 i j
  · refine Prod.ext (Prod.ext ?_ ?_) ?_
    · simp [coord, g]
    · funext a; simp [coord, g]
    · ext a b; simp [coord, g]

theorem matrixEntryAbsSum_unitaryLie_coordinates_split (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (he : SignCompat e) (X : lieU P Q) :
    l1 X.val = tanGauge (coord e he X).1 + l1 (coord e he X).2.val := by
  have h1 : ‖X.val (e none) (e none)‖ = |(X.val (e none) (e none)).im| := by
    conv_lhs => rw [diag_eq]
    simp
  have h2 : ∀ b, ‖X.val (e none) (e (some b))‖ = ‖X.val (e (some b)) (e none)‖ := by
    intro b
    rw [row_eq, norm_mul, norm_neg, norm_mul, norm_sg, norm_sg]; simp
  change ∑ i, ∑ j, ‖X.val i j‖ = |(X.val (e none) (e none)).im| +
    2 * ∑ a, ‖X.val (e (some a)) (e none)‖ + ∑ a, ∑ b, ‖X.val (e (some a)) (e (some b))‖
  have h3 : ∀ i, ∑ j, ‖X.val i j‖ = ‖X.val i (e none)‖ + ∑ b, ‖X.val i (e (some b))‖ := by
    intro i
    rw [← e.sum_comp, Fintype.sum_option]
  simp only [h3]
  rw [← e.sum_comp, Fintype.sum_option, Finset.sum_add_distrib, h1]
  simp only [h2]
  ring

theorem omega_split : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)), SignCompat e → ∀ (lam : Measure (lieU P Q)) (lam' : Measure (lieU P' Q')), IsOmegaLeb lam → IsOmegaLeb lam' → ∀ r : ℝ, lam (ballU P Q r) = (2 : ℝ≥0∞) ^ (P' + Q') * ((volume : Measure (ℝ × Sp P' Q')).prod lam') {p | tanGauge p.1 + l1 (p.2 : Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) < r} := by
  intro P Q P' Q' e he lam lam' hl hl' r
  have : BorelSpace (lieU P Q) := ⟨rfl⟩
  have : BorelSpace (lieU P' Q') := ⟨rfl⟩
  have : SecondCountableTopology (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  have : SecondCountableTopology (Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P' ⊕ Fin Q') → (Fin P' ⊕ Fin Q') → ℂ))
  have : SecondCountableTopology (lieU P Q) := TopologicalSpace.Subtype.secondCountableTopology _
  have : SecondCountableTopology (lieU P' Q') := TopologicalSpace.Subtype.secondCountableTopology _
  have : LocallyCompactSpace (lieU P Q) := LocallyCompactSpace.of_finiteDimensional_of_complete ℝ _
  have : LocallyCompactSpace (lieU P' Q') := LocallyCompactSpace.of_finiteDimensional_of_complete ℝ _
  obtain ⟨h1, h2⟩ := hl'
  let D : lieU P Q ≃L[ℝ] (ℝ × Sp P' Q') × lieU P' Q' :=
    (LinearEquiv.ofBijective (coord e he)
      ⟨coord_injective e he, coord_surjective e he⟩).toContinuousLinearEquiv
  have hD : ∀ X, D X = coord e he X := fun _ => rfl
  have hn : Fintype.card (Fin P' ⊕ Fin Q') = P' + Q' := by simp
  let μ : Measure (Sp P' Q') := (2 : ℝ≥0∞) ^ Fintype.card (Fin P' ⊕ Fin Q') • volume
  have : μ.IsAddHaarMeasure := Measure.IsAddHaarMeasure.smul _ (by simp) (by finiteness)
  let ν : Measure ((ℝ × Sp P' Q') × lieU P' Q') := ((volume : Measure ℝ).prod μ).prod lam'
  have : ((volume : Measure ℝ).prod μ).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have : ν.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have hc : ∀ A B : ℕ, Continuous (fun ab : lieU A B × lieU A B =>
      entries ((ab.1 : Matrix (Fin A ⊕ Fin B) (Fin A ⊕ Fin B) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin A ⊕ Fin B) (Fin A ⊕ Fin B) ℂ))) := by
    intro A B
    refine continuous_pi fun ij => ?_
    exact ((continuous_subtype_val.comp continuous_fst).add
      ((continuous_subtype_val.comp continuous_snd).const_smul Complex.I)).matrix_elem ij.1 ij.2
  have hm : Measurable D.symm := D.symm.continuous.measurable
  have hω : IsOmegaLeb (ν.map D.symm) := by
    refine ⟨D.symm.isAddHaarMeasure_map ν, ?_⟩
    obtain ⟨f, hf, hf'⟩ := exists_assemble e
    have m1 := mp_interchange ((volume : Measure ℝ).prod μ) lam' ((volume : Measure ℝ).prod μ) lam'
    have m2 := mp_interchange (volume : Measure ℝ) μ (volume : Measure ℝ) μ
    have m3 := mp_colrow (fun b => -((sg (e none) : ℂ) * sg (e (some b))))
      (fun b => by rw [norm_neg, norm_mul, norm_sg, norm_sg, mul_one])
    have m4 : MeasurePreserving _ (lam'.prod lam') volume := ⟨(hc P' Q').measurable, h2⟩
    have m5 := hf.comp ((((mp_diag.prod m3).comp m2).prod m4).comp m1)
    rw [Measure.map_prod_map _ _ hm hm, Measure.map_map (hc P Q).measurable (hm.prodMap hm),
      ← m5.map_eq]
    congr 1
    funext ⟨x, y⟩ ⟨i, j⟩
    obtain ⟨X, rfl⟩ := D.surjective x
    obtain ⟨Y, rfl⟩ := D.surjective y
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    simp only [Function.comp_apply, Prod.map_apply, ContinuousLinearEquiv.symm_apply_apply]
    change X.val (e i) (e j) + Complex.I * Y.val (e i) (e j) = _
    rcases i with _ | i <;> rcases j with _ | j
    · rw [(hf' _).1, diag_eq X, diag_eq Y]; rfl
    · rw [(hf' _).2.2.1, row_eq e X, row_eq e Y]; rfl
    · rw [(hf' _).2.1]; rfl
    · rw [(hf' _).2.2.2]; rfl
  have hopen : IsOpen (ballU P Q r) :=
    isOpen_lt (continuous_matrixEntryAbsSum.comp continuous_subtype_val) continuous_const
  rw [GlobalTheory.CompactDualUnique.isOmegaLeb_unique hl hω, Measure.map_apply hm hopen.measurableSet]
  have hset : D.symm ⁻¹' ballU P Q r = {p | tanGauge p.1 +
      l1 (p.2 : Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) < r} := by
    ext p
    obtain ⟨X, rfl⟩ := D.surjective p
    rw [Set.mem_preimage, D.symm_apply_apply]
    change l1 X.val < r ↔ _
    rw [matrixEntryAbsSum_unitaryLie_coordinates_split e he]
    rfl
  rw [hset]
  simp only [ν, μ, hn]
  rw [Measure.prod_smul_right, Measure.prod_smul_left, Measure.smul_apply, smul_eq_mul]
  rfl

end GlobalTheory.OmegaSplit
