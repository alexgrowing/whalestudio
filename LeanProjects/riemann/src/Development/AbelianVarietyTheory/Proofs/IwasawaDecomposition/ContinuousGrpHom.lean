import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDensityUpqUniqueAndSmulStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

noncomputable section

namespace GlobalTheory.CompactDualSwap

variable {P Q P' Q' : ℕ}

def AntiIso (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') : Prop :=
  (Formalism.UG.Jpq P Q).submatrix e.symm e.symm = -Formalism.UG.Jpq P' Q'

theorem AntiIso.symm {e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q'} (h : AntiIso e) : AntiIso e.symm := by
  unfold AntiIso at *
  ext i j
  have := congrFun (congrFun h (e i)) (e j)
  simp only [submatrix_apply, Equiv.symm_apply_apply, Matrix.neg_apply, Equiv.symm_symm] at *
  rw [this, neg_neg]

def grpHom (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) : UpqT P Q →* UpqT P' Q' :=
  let f : Formalism.UG.Upq P Q →* GL (Fin P' ⊕ Fin Q') ℂ :=
    (Units.map (Matrix.reindexAlgEquiv ℂ ℂ e).toMonoidHom).comp (Formalism.UG.Upq P Q).subtype
  let f' : Formalism.UG.Upq P Q →* Formalism.UG.Upq P' Q' := f.codRestrict _ (by
    rintro ⟨g, hg⟩
    change Formalism.UG.cT _ g.val * _ * g.val = _ at hg
    change Formalism.UG.cT _ (g.val.submatrix e.symm e.symm) * _ *
      (g.val.submatrix e.symm e.symm) = _
    have h2 : Formalism.UG.Jpq P' Q' = -(Formalism.UG.Jpq P Q).submatrix e.symm e.symm := by
      rw [h, neg_neg]
    have h3 : Formalism.UG.cT (starRingEnd ℂ) (g.val.submatrix e.symm e.symm) =
      (Formalism.UG.cT (starRingEnd ℂ) g.val).submatrix e.symm e.symm := rfl
    rw [h2, h3, Matrix.mul_neg, Matrix.neg_mul, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, hg])
  f'

theorem mat_grpHom (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) (g : UpqT P Q) :
    (grpHom e h g).mat = g.mat.submatrix e.symm e.symm := rfl

theorem mat_injective : Function.Injective (UpqT.mat : UpqT P Q → _) :=
  (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.2.injective

theorem continuous_grpHom (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) :
    Continuous (grpHom e h) := by
  rw [(GlobalTheory.UpqTopology.upq_lcsc P' Q').2.2.2.2.2.isInducing.continuous_iff]
  exact ((GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.2.continuous).matrix_submatrix e.symm e.symm

def grpEquiv (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) : UpqT P Q ≃ₜ* UpqT P' Q' where
  toFun := grpHom e h
  invFun := grpHom e.symm h.symm
  left_inv g := mat_injective (by ext i j; simp [mat_grpHom])
  right_inv g := mat_injective (by ext i j; simp [mat_grpHom])
  map_mul' := map_mul _
  continuous_toFun := continuous_grpHom e h
  continuous_invFun := continuous_grpHom e.symm h.symm

theorem lie_mem (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) (X : lieU P Q) :
    X.val.submatrix e.symm e.symm ∈ lieU P' Q' := by
  have hX : X.valᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X.val = 0 := X.2
  change (X.val.submatrix e.symm e.symm)ᴴ * Formalism.UG.Jpq P' Q' +
    Formalism.UG.Jpq P' Q' * X.val.submatrix e.symm e.symm = 0
  have h2 : Formalism.UG.Jpq P' Q' = -(Formalism.UG.Jpq P Q).submatrix e.symm e.symm := by
    rw [h, neg_neg]
  rw [h2, Matrix.conjTranspose_submatrix, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, ← neg_add, neg_eq_zero]
  have := congrArg (fun M => Matrix.submatrix M e.symm e.symm) hX
  exact this

def lieEquiv (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) : lieU P Q ≃L[ℝ] lieU P' Q' where
  toFun X := ⟨_, lie_mem e h X⟩
  invFun X := ⟨_, lie_mem e.symm h.symm X⟩
  left_inv X := by ext i j; simp
  right_inv X := by ext i j; simp
  map_add' X Y := rfl
  map_smul' c X := rfl
  continuous_toFun := (continuous_subtype_val.matrix_submatrix e.symm e.symm).subtype_mk _
  continuous_invFun := (continuous_subtype_val.matrix_submatrix e e).subtype_mk _

theorem coe_lieEquiv (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) (X : lieU P Q) :
    ((lieEquiv e h X : lieU P' Q') : Matrix _ _ ℂ) = X.val.submatrix e.symm e.symm := rfl

theorem mem_ball (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) (X : lieU P Q) (r : ℝ) :
    lieEquiv e h X ∈ ballU P' Q' r ↔ X ∈ ballU P Q r := by
  simp only [ballU, Set.mem_ofPred_eq, coe_lieEquiv, submatrix_apply]
  have : ∑ i, ∑ j, ‖X.val (e.symm i) (e.symm j)‖ = ∑ i, ∑ j, ‖X.val i j‖ := by
    rw [← e.symm.sum_comp (fun i => ∑ j, ‖X.val i j‖)]
    exact Finset.sum_congr rfl fun i _ => e.symm.sum_comp (fun j => ‖X.val (e.symm i) j‖)
  rw [this]

open scoped Matrix.Norms.Operator in
theorem exp_submatrix {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (X : Matrix m m ℂ) :
    NormedSpace.exp (X.submatrix e.symm e.symm) = (NormedSpace.exp X).submatrix e.symm e.symm :=
  (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e)
    (continuous_id.matrix_submatrix e.symm e.symm) X).symm

theorem isOmegaLeb_map (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e)
    (lam : Measure (lieU P Q)) (hl : IsOmegaLeb lam) : IsOmegaLeb (lam.map (lieEquiv e h)) := by
  have : BorelSpace (lieU P Q) := ⟨rfl⟩
  have : BorelSpace (lieU P' Q') := ⟨rfl⟩
  have : SecondCountableTopology (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  have : SecondCountableTopology (Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P' ⊕ Fin Q') → (Fin P' ⊕ Fin Q') → ℂ))
  have : SecondCountableTopology (lieU P Q) := TopologicalSpace.Subtype.secondCountableTopology _
  have : SecondCountableTopology (lieU P' Q') := TopologicalSpace.Subtype.secondCountableTopology _
  have : LocallyCompactSpace (lieU P Q) := LocallyCompactSpace.of_finiteDimensional_of_complete ℝ _
  obtain ⟨h1, h2⟩ := hl
  refine ⟨(lieEquiv e h).isAddHaarMeasure_map lam, ?_⟩
  have hm : Measurable (lieEquiv e h) := (lieEquiv e h).continuous.measurable
  have hc : ∀ A B : ℕ, Continuous (fun ab : lieU A B × lieU A B =>
      entries ((ab.1 : Matrix (Fin A ⊕ Fin B) (Fin A ⊕ Fin B) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin A ⊕ Fin B) (Fin A ⊕ Fin B) ℂ))) := by
    intro A B
    refine continuous_pi fun ij => ?_
    exact ((continuous_subtype_val.comp continuous_fst).add
      ((continuous_subtype_val.comp continuous_snd).const_smul Complex.I)).matrix_elem ij.1 ij.2
  have hv := volume_measurePreserving_piCongrLeft
    (fun _ : (Fin P' ⊕ Fin Q') × (Fin P' ⊕ Fin Q') => ℂ) (e.prodCongr e)
  rw [Measure.map_prod_map _ _ hm hm, Measure.map_map (hc P' Q').measurable (hm.prodMap hm),
    ← hv.map_eq, ← h2, Measure.map_map hv.measurable (hc P Q).measurable]
  congr 1
  funext ab ij
  obtain ⟨ij, rfl⟩ := (e.prodCongr e).surjective ij
  simp only [Function.comp_apply, MeasurableEquiv.piCongrLeft_apply_apply]
  simp [entries, coe_lieEquiv]

theorem omegaDensity_map (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e)
    (μ : Measure (UpqT P Q)) (c : ENNReal) (hμ : OmegaDensity μ c) :
    OmegaDensity (μ.map (grpEquiv e h)) c := by
  have : BorelSpace (lieU P Q) := ⟨rfl⟩
  have : BorelSpace (lieU P' Q') := ⟨rfl⟩
  have : BorelSpace (UpqT P Q) := ⟨rfl⟩
  have : BorelSpace (UpqT P' Q') := ⟨rfl⟩
  obtain ⟨lam, hl, ht⟩ := hμ
  refine ⟨_, isOmegaLeb_map e h lam hl, ?_⟩
  refine ht.congr fun r => ?_
  have e1 := (grpEquiv e h).toHomeomorph.toMeasurableEquiv.map_apply (μ := μ)
  have e2 := (lieEquiv e h).toHomeomorph.toMeasurableEquiv.map_apply (μ := lam)
  congr 1
  · refine Eq.trans ?_ (e1 _).symm
    congr 1
    ext g
    change (∃ X ∈ ballU P Q r, _) ↔ ∃ X ∈ ballU P' Q' r, g.mat.submatrix e.symm e.symm = _
    rw [(lieEquiv e h).surjective.exists]
    refine exists_congr fun X => ?_
    rw [mem_ball, coe_lieEquiv, exp_submatrix]
    refine and_congr_right fun _ => ⟨fun hh => by rw [hh], fun hh => ?_⟩
    ext i j
    simpa using congrFun (congrFun hh (e i)) (e j)
  · refine Eq.trans ?_ (e2 _).symm
    congr 1
    ext X
    exact (mem_ball e h X r).symm

def swapIdx (N : ℕ) : Fin 0 ⊕ Fin N ≃ Fin (0 + N) ⊕ Fin 0 :=
  (Equiv.sumComm _ _).trans (Equiv.sumCongr (finCongr (Nat.zero_add N).symm) (Equiv.refl _))

theorem antiIso_swapIdx (N : ℕ) : AntiIso (swapIdx N) := by
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [swapIdx, Formalism.UG.Jpq, Matrix.one_apply, Fin.ext_iff]
    · exact j.elim0
  · exact i.elim0

theorem cd_zero_univ : ∀ (c : CDHaar) (N : ℕ), c.cd 0 N Set.univ = 1 := by
  intro c N
  obtain ⟨d, hd0, hdt, h1, h2⟩ := c.trick 0 N
  obtain ⟨_, _, _, _, _, -⟩ := GlobalTheory.UpqTopology.upq_lcsc 0 N
  obtain ⟨_, _, _, _, _, -⟩ := GlobalTheory.UpqTopology.upq_lcsc (0 + N) 0
  have := c.haar 0 N
  have := c.haar (0 + N) 0
  have := c.prob (0 + N)
  let G := grpEquiv (swapIdx N) (antiIso_swapIdx N)
  have : ((c.cd 0 N).map G).IsHaarMeasure := G.isHaarMeasure_map _
  have h3 := omegaDensity_map _ (antiIso_swapIdx N) _ _ h1
  have h4 := Measure.isMulLeftInvariant_eq_smul ((c.cd 0 N).map G) (c.cd (0 + N) 0)
  set a := Measure.haarScalarFactor ((c.cd 0 N).map G) (c.cd (0 + N) 0)
  have h5 : OmegaDensity ((c.cd 0 N).map G) (a * d) := by
    rw [h4]; exact (GlobalTheory.T.omegaDensity_upq_unique_and_smul _ _ _ _ h2).2 a
  have h6 : (a : ENNReal) * d = 1 * d := by
    rw [one_mul]; exact (GlobalTheory.T.omegaDensity_upq_unique_and_smul _ _ _ _ h3).1 _ h5
  have h7 : (a : ENNReal) = 1 := (ENNReal.mul_left_inj hd0 hdt).1 h6
  have h8 : ((c.cd 0 N).map G) Set.univ = 1 := by
    rw [h4, Measure.smul_apply, measure_univ, ENNReal.smul_def, h7, one_smul]
  have hG : Measurable G := G.continuous.measurable
  rwa [Measure.map_apply hG MeasurableSet.univ, Set.preimage_univ] at h8

end GlobalTheory.CompactDualSwap
