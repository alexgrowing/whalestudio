import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory NumberField GlobalTheory.Mem.Vol Matrix Topology

namespace GlobalTheory.Mem.Vol.Scale

variable {n P Q : ℕ} {ε : Fin n → Bool}

def Sorts (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n) : Prop :=
  (∀ i, ε (e (Sum.inl i)) = true) ∧ ∀ j, ε (e (Sum.inr j)) = false

theorem Sorts.reindex_Jpq {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) :
    Matrix.reindex e e (Formalism.UG.Jpq P Q) = Formalism.REAL.Jm ε := by
  ext i j
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Formalism.REAL.Jm,
    Matrix.diagonal_apply, EmbeddingLike.apply_eq_iff_eq, Formalism.UG.Jpq]
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply, h.1, h.2]
  split_ifs <;> simp

theorem Sorts.card_true {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) : Nat.card {a // ε a = true} = P := by
  have : Function.Bijective fun i : Fin P => (⟨e (Sum.inl i), h.1 i⟩ : {a // ε a = true}) := by
    refine ⟨fun i j hij => Sum.inl_injective (e.injective (congrArg Subtype.val hij)), ?_⟩
    rintro ⟨a, ha⟩
    obtain ⟨b | b, rfl⟩ := e.surjective a
    · exact ⟨b, rfl⟩
    · rw [h.2] at ha; cases ha
  rw [← Nat.card_eq_of_bijective _ this]; simp

theorem Sorts.add_eq (e : Fin P ⊕ Fin Q ≃ Fin n) : P + Q = n := by
  simpa using Fintype.card_congr e

theorem exists_sorts (ε : Fin n → Bool) : ∃ (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n), Sorts ε e := by
  refine ⟨_, _, (Equiv.sumCongr (Fintype.equivFin {a // ε a = true}).symm
    (Fintype.equivFin {a // ¬ ε a = true}).symm).trans (Equiv.sumCompl fun a => ε a = true), fun i => ?_, fun j => ?_⟩
  · exact ((Fintype.equivFin {a // ε a = true}).symm i).2
  · exact Bool.eq_false_iff.2 ((Fintype.equivFin {a // ¬ ε a = true}).symm j).2

def reindexUnits (e : Fin P ⊕ Fin Q ≃ Fin n) :
    GL (Fin P ⊕ Fin Q) ℂ ≃ₜ* (Matrix (Fin n) (Fin n) ℂ)ˣ where
  toMulEquiv := Units.mapEquiv (Matrix.reindexAlgEquiv ℂ ℂ e).toMulEquiv
  continuous_toFun := Units.continuous_map
    (f := ((Matrix.reindexAlgEquiv ℂ ℂ e).toMulEquiv.toMonoidHom))
    (continuous_id.matrix_reindex _ _)
  continuous_invFun := Units.continuous_map
    (f := ((Matrix.reindexAlgEquiv ℂ ℂ e).toMulEquiv.symm.toMonoidHom))
    ((continuous_id.matrix_reindex e.symm e.symm).congr fun _ => rfl)

theorem reindexUnits_val (e : Fin P ⊕ Fin Q ≃ Fin n) (g : GL (Fin P ⊕ Fin Q) ℂ) :
    (reindexUnits e g : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.reindex e e (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := rfl

theorem Sorts.mem_iff {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) (g : GL (Fin P ⊕ Fin Q) ℂ) :
    reindexUnits e g ∈ Formalism.REAL.UJ ε ↔ g ∈ Formalism.UG.Upq P Q := by
  change Formalism.REAL.inUJ ε (reindexUnits e g : Matrix (Fin n) (Fin n) ℂ) ↔
    (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ).conjTranspose * Formalism.UG.Jpq P Q *
      (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) = Formalism.UG.Jpq P Q
  rw [Formalism.REAL.inUJ, reindexUnits_val, ← h.reindex_Jpq, Matrix.conjTranspose_reindex]
  rw [← (Matrix.reindex (α := ℂ) e e).injective.eq_iff]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

def Sorts.equiv {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) : UpqT P Q ≃ₜ* Formalism.REAL.UJ ε where
  toFun g := ⟨reindexUnits e (g : Formalism.UG.Upq P Q).1, (h.mem_iff _).2 (g : Formalism.UG.Upq P Q).2⟩
  invFun k := (⟨(reindexUnits e).symm k.1, (h.mem_iff _).1 (by simpa using k.2)⟩ : Formalism.UG.Upq P Q)
  left_inv g := Subtype.ext ((reindexUnits e).symm_apply_apply _)
  right_inv k := Subtype.ext ((reindexUnits e).apply_symm_apply _)
  map_mul' g k := Subtype.ext (map_mul (reindexUnits e) _ _)
  continuous_toFun := ((reindexUnits e).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((reindexUnits e).symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem Sorts.umat_equiv {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) (g : UpqT P Q) :
    umat (h.equiv g) = Matrix.reindex e e (UpqT.mat g) := rfl

theorem umat_injective : Function.Injective (umat : Formalism.REAL.UJ ε → _) :=
  fun _ _ h => Subtype.ext (Units.ext h)

theorem Sorts.set_eq {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) (A : Set (Formalism.REAL.UJ ε)) :
    {g | ∃ a ∈ A, umat a = Matrix.reindex e e (UpqT.mat g)} = h.equiv ⁻¹' A := by
  ext g
  constructor
  · rintro ⟨a, ha, hg⟩
    rw [← h.umat_equiv] at hg
    rw [Set.mem_preimage, ← umat_injective hg]
    exact ha
  · intro hg
    exact ⟨_, hg, rfl⟩

theorem Sorts.exists_conj {e e' : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) (h' : Sorts ε e') :
    ∃ u : UpqT P Q, ∀ g, h'.equiv g = h.equiv (u * g * u⁻¹) := by
  set σ : Fin P ⊕ Fin Q ≃ Fin P ⊕ Fin Q := e.trans e'.symm with hσ
  have hJ : (Formalism.UG.Jpq P Q).submatrix σ σ = Formalism.UG.Jpq P Q := by
    apply (Matrix.reindex (α := ℂ) e e).injective
    rw [h.reindex_Jpq, ← h'.reindex_Jpq]
    ext i j
    simp [hσ]
  have hmem : (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ).submatrix σ id ∈
      Set.range (UpqT.mat (P := P) (Q := Q)) := by
    rw [GlobalTheory.UpqTopology.range_mat]
    change _ = _
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
    conv_lhs => rw [← hJ]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    simp
  obtain ⟨u, hu⟩ := hmem
  refine ⟨u, fun g => ?_⟩
  rw [← h.equiv.symm_apply_eq, eq_mul_inv_iff_mul_eq]
  apply GlobalTheory.UpqTopology.isClosedEmbedding_mat.injective
  have h1 : UpqT.mat (h.equiv.symm (h'.equiv g)) = (UpqT.mat g).submatrix σ σ := by
    apply (Matrix.reindex (α := ℂ) e e).injective
    rw [← h.umat_equiv, h.equiv.apply_symm_apply, h'.umat_equiv]
    ext i j
    simp [hσ]
  change UpqT.mat (h.equiv.symm (h'.equiv g)) * UpqT.mat u = UpqT.mat u * UpqT.mat g
  rw [h1, hu, Matrix.submatrix_mul_equiv, Matrix.mul_one]
  have := Matrix.submatrix_mul_equiv (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (UpqT.mat g) σ
    (Equiv.refl _) id
  simpa using this.symm

theorem Sorts.measurable_equiv {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) : Measurable h.equiv := by
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  exact h.equiv.continuous.measurable

theorem Sorts.map_eq (cd : CDHaar) {P' Q' : ℕ} {e : Fin P ⊕ Fin Q ≃ Fin n} {e' : Fin P' ⊕ Fin Q' ≃ Fin n}
    (h : Sorts ε e) (h' : Sorts ε e') : (cd.cd P' Q').map h'.equiv = (cd.cd P Q).map h.equiv := by
  obtain rfl : P = P' := h.card_true.symm.trans h'.card_true
  obtain rfl : Q = Q' := by
    have h1 := Sorts.add_eq e
    have h2 := Sorts.add_eq e'
    omega
  haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  haveI := cd.haar P Q
  haveI := GlobalTheory.UpqHaarRight.isMulRightInvariant P Q _ (cd.haar P Q)
  obtain ⟨u, hu⟩ := h.exists_conj h'
  have : (h'.equiv : UpqT P Q → Formalism.REAL.UJ ε) = h.equiv ∘ (fun g => g * u⁻¹) ∘ fun g => u * g := funext hu
  rw [this, ← Measure.map_map h.measurable_equiv ((measurable_mul_const _).comp (measurable_const_mul _)),
    ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _), map_mul_left_eq_self,
    map_mul_right_eq_self]

theorem Sorts.exists_scale (cd : CDHaar) {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) :
    ∃ c : NNReal, 0 < c ∧ (cd.cd P Q).map h.equiv = (c : ENNReal) • Formalism.REAL.muG ε := by
  haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  haveI := cd.haar P Q
  haveI : ((cd.cd P Q).map h.equiv).IsHaarMeasure := h.equiv.isHaarMeasure_map _
  exact ⟨_, Measure.haarScalarFactor_pos_of_isHaarMeasure _ _,
    Measure.isMulLeftInvariant_eq_smul ((cd.cd P Q).map h.equiv) (Formalism.REAL.muG ε)⟩

theorem exists_cdScaleIs (cd : CDHaar) :
    ∃ sc : ∀ n : ℕ, (Fin n → Bool) → NNReal, (∀ n ε, 0 < sc n ε) ∧ CdScaleIs cd sc := by
  choose P Q e he using fun (n : ℕ) (ε : Fin n → Bool) => exists_sorts ε
  choose sc hpos hsc using fun (n : ℕ) (ε : Fin n → Bool) => (he n ε).exists_scale cd
  refine ⟨sc, hpos, fun n ε P' Q' e' h1 h2 A hA => ?_⟩
  have h' : Sorts ε e' := ⟨h1, h2⟩
  rw [h'.set_eq, ← Measure.map_apply h'.measurable_equiv hA, (he n ε).map_eq cd h', hsc]

theorem cdScaleIs_trueScale : ∀ cd : CDHaar, CdScaleIs cd (trueScale cd) := by
  intro cd
  unfold trueScale
  rw [dif_pos (exists_cdScaleIs cd)]
  exact (Classical.choose_spec (exists_cdScaleIs cd)).2

theorem cdScaleIs_unique (cd : CDHaar) {sc sc' : ∀ n : ℕ, (Fin n → Bool) → NNReal}
    (h : CdScaleIs cd sc) (h' : CdScaleIs cd sc') : sc = sc' := by
  funext n ε
  obtain ⟨P, Q, e, he⟩ := exists_sorts ε
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (Formalism.REAL.UJ ε)) := inferInstance
  have hm : MeasurableSet (K : Set (Formalism.REAL.UJ ε)) := K.isCompact.measurableSet
  have h0 : Formalism.REAL.muG ε K ≠ 0 := (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have ht : Formalism.REAL.muG ε K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have := (h n ε P Q e he.1 he.2 K hm).trans (h' n ε P Q e he.1 he.2 K hm).symm
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul] at this
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj h0 ht).1 this)

end GlobalTheory.Mem.Vol.Scale
