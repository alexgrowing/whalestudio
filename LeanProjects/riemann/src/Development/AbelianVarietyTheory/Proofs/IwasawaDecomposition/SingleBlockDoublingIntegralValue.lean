import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Formalism.DoubleCosetMeasures.LatticeCoset
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.IsClosedLowUni
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoAF
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsNrm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocalAtCompletionIntegersChosenUniformiserStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardResidueRingCompletionChosenUniformiserStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHaarGLCompletionIntegersVolOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddHaarCompletionIntegralMatricesVolOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardGLFiniteFieldEqPowMulProdStatement

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.Mem.SingleQ

section Gen

variable {F : Type} [Field F]

theorem unitCharExtendedByZero_det_eq_char_det (δ : Fˣ →* ℂˣ) {n : ℕ} (k : GL (Fin n) F) :
    chi0 δ (k : Matrix (Fin n) (Fin n) F).det = ((δ (GeneralLinearGroup.det k) : ℂˣ) : ℂ) := by
  have h : (k : Matrix (Fin n) (Fin n) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
  have e : Units.mk0 _ h = GeneralLinearGroup.det k :=
    Units.ext (by simp [Matrix.GeneralLinearGroup.val_det_apply])
  rw [chi0, dif_neg h, e]

def rowEq (r t : ℕ) : Matrix (Fin r ⊕ Fin t) (Fin r) F ≃ Matrix (Fin (r + t)) (Fin r) F :=
  Matrix.reindex finSumFinEquiv (Equiv.refl _)

omit [Field F] in
theorem rowEq_apply {r t : ℕ} (x : Matrix (Fin r ⊕ Fin t) (Fin r) F) (i : Fin (r + t)) (j : Fin r) :
    rowEq r t x i j = x (finSumFinEquiv.symm i) j := rfl

theorem rowEq_mul {r t : ℕ} (x : Matrix (Fin r ⊕ Fin t) (Fin r) F) (g : Matrix (Fin r) (Fin r) F) :
    rowEq r t (x * g) = rowEq r t x * g := by
  ext i j
  simp only [rowEq_apply, Matrix.mul_apply]

theorem phiQ_rowEq (O : Subring F) (ϖ : F) (δ : Fˣ →* ℂˣ) (r t : ℕ) (x : Matrix (Fin r ⊕ Fin t) (Fin r) F) :
    phiQ O ϖ δ r t 0 (rowEq r t x) =
      phiU O ϖ (GLint O r) (δ.comp (GeneralLinearGroup.det.comp (GLint O r).subtype))⁻¹ x := by
  have hA : bAA (d := t) (c := 0) (rowEq r t x) = Matrix.toRows₁ x := by
    ext i j; simp only [bAA, Matrix.submatrix_apply, rowEq_apply, finSumFinEquiv_symm_apply_castAdd]; rfl
  have hD : bDA (d := t) (c := 0) (rowEq r t x) = Matrix.toRows₂ x := by
    ext i j; simp only [bDA, Matrix.submatrix_apply, rowEq_apply, finSumFinEquiv_symm_apply_natAdd]; rfl
  have hB : bAD (d := t) (c := 0) (rowEq r t x) ∈ intMat O r 0 := fun _ j => j.elim0
  have hC : bDD (d := t) (c := 0) (rowEq r t x) ∈ intMat O t 0 := fun _ j => j.elim0
  unfold phiQ phiU
  by_cases h : (∃ k : GLint O r, ((k : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = Matrix.toRows₁ x) ∧
      Matrix.toRows₂ x ∈ IIset O ϖ
  · rw [dif_pos h]
    have hc : bAA (d := t) (c := 0) (rowEq r t x) ∈ Jset (GLint O r) ∧
        bDA (d := t) (c := 0) (rowEq r t x) ∈ IIset O ϖ ∧
        bAD (d := t) (c := 0) (rowEq r t x) ∈ intMat O r 0 ∧
        bDD (d := t) (c := 0) (rowEq r t x) ∈ intMat O t 0 := by
      rw [hA, hD]
      obtain ⟨k, hk⟩ := h.1
      exact ⟨⟨k, k.2, hk⟩, h.2, hB, hC⟩
    rw [if_pos hc, hA]
    have hk := Classical.choose_spec h.1
    have e : chi0 δ (Matrix.toRows₁ x).det =
        ((δ (GeneralLinearGroup.det ((Classical.choose h.1 : GLint O r) : GL (Fin r) F)) : ℂˣ) : ℂ) := by
      rw [← unitCharExtendedByZero_det_eq_char_det, hk]
    rw [e]
    simp [Units.val_inv_eq_inv_val]
  · rw [dif_neg h, if_neg]
    rintro ⟨h1, h2, -, -⟩
    rw [hA] at h1
    rw [hD] at h2
    obtain ⟨k, hk, e⟩ := h1
    exact h ⟨⟨⟨k, hk⟩, e⟩, h2⟩

end Gen

end GlobalTheory.Mem.SingleQ

namespace GlobalTheory.Mem.SingleQ

section Triv

variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

omit [IsTopologicalRing F] in
theorem isUnrM_one (O : Subring F) (nrm : AbsoluteValue F ℝ) (r : ℕ) (χ : Fin 0 → F → ℂ) :
    IsUnrM O nrm r 0 χ (1 : GL (Fin r) F × GL (Fin 0) F →* (ℂ ≃ₗᵢ[ℂ] ℂ)) where
  smooth x := by
    convert isOpen_univ using 1
    ext m
    simp
  irred W _ := Ideal.eq_bot_or_top W
  sph := by
    haveI : Subsingleton (GL (Fin 0) F) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    refine ⟨1, by simp, fun _ _ _ _ => rfl, fun _ => 1, Measure.dirac 1, ?_, ?_, ?_, ?_⟩
    · intro b _ k _
      simp
    · exact ⟨fun g => by
        rw [show (fun x : GL (Fin 0) F => g * x) = id from funext fun _ => Subsingleton.elim _ _,
          Measure.map_id]⟩
    · exact Measure.dirac_apply_of_mem (GLint O 0).one_mem
    · intro g
      rw [setIntegral_const, Measure.real, Measure.dirac_apply_of_mem (GLint O 0).one_mem]
      simp

omit [TopologicalSpace F] [IsTopologicalRing F] in
theorem one_mem_typeSp (O : Subring F) (ϖ : F) (nrm : AbsoluteValue F ℝ) (δ : Fˣ →* ℂˣ) (r : ℕ) :
    (fun _ => (1 : ℂ)) ∈ typeSp O ϖ nrm δ r 0 (1 : GL (Fin r) F × GL (Fin 0) F →* (ℂ ≃ₗᵢ[ℂ] ℂ)) := by
  refine ⟨fun p m₁ m₂ _ _ _ g => ?_, fun k _ g => ?_⟩
  · obtain rfl : m₂ = 1 := Subsingleton.elim _ _
    simp
  · simp [lamJ, chi0]

end Triv

end GlobalTheory.Mem.SingleQ

namespace GlobalTheory.Mem.SingleQ

section Tr

variable {F : Type} [Field F] [MeasurableSpace F]

def rowEqM (r t : ℕ) : Matrix (Fin r ⊕ Fin t) (Fin r) F ≃ᵐ Matrix (Fin (r + t)) (Fin r) F where
  toEquiv := rowEq r t
  measurable_toFun := by
    change Measurable fun (x : Fin r ⊕ Fin t → Fin r → F) (i : Fin (r + t)) => x (finSumFinEquiv.symm i)
    exact measurable_pi_lambda _ fun i => measurable_pi_apply _
  measurable_invFun := by
    change Measurable fun (x : Fin (r + t) → Fin r → F) (i : Fin r ⊕ Fin t) => x (finSumFinEquiv i)
    refine measurable_pi_lambda _ fun i => ?_
    exact measurable_pi_apply _

omit [Field F] in
theorem rowEqM_apply {r t : ℕ} (x : Matrix (Fin r ⊕ Fin t) (Fin r) F) : rowEqM r t x = rowEq r t x := rfl

variable [TopologicalSpace F] [IsTopologicalRing F]

omit [IsTopologicalRing F] in
theorem localZ_map {r t : ℕ} (μ : Measure (GL (Fin r) F)) (m : Measure (Matrix (Fin r ⊕ Fin t) (Fin r) F))
    (χ : Fˣ →* ℂˣ) (nrm : AbsoluteValue F ℝ) (Φ : Matrix (Fin (r + t)) (Fin r) F → ℂ) (c : GL (Fin r) F → ℂ) :
    localZ μ (m.map (rowEqM r t)) χ nrm Φ Φ c = localZ μ m χ nrm (Φ ∘ rowEq r t) (Φ ∘ rowEq r t) c := by
  unfold localZ
  congr 1 with g
  congr 1
  unfold weilIP
  rw [integral_map_equiv]
  congr 1 with x
  simp only [omegaS, rowEqM_apply, Function.comp_apply, rowEq_mul, Fintype.card_sum, Fintype.card_fin]

end Tr

end GlobalTheory.Mem.SingleQ

namespace GlobalTheory.Mem.SingleQ

section Loc

theorem isMaximal_span {F : Type} [Field F] {O : Subring F} {ϖ : F} (hϖ : ϖ ∈ O) (h : IsLocalAt O ϖ) :
    (Ideal.span {(⟨ϖ, hϖ⟩ : O)}).IsMaximal := by
  obtain ⟨h1, h2⟩ := h
  rw [Ideal.isMaximal_iff]
  refine ⟨fun hm => ?_, fun J x _ hx hxJ => ?_⟩
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hm
    have hc' : (c : F) * ϖ = 1 := by simpa using congrArg Subtype.val hc
    exact h1 ((eq_inv_of_mul_eq_one_left hc') ▸ c.2)
  · have hx' : ∀ o ∈ O, (x : F) ≠ ϖ * o := by
      rintro o ho he
      exact hx (Ideal.mem_span_singleton'.mpr ⟨⟨o, ho⟩, Subtype.ext (by simp [he, mul_comm])⟩)
    have hx0 : (x : F) ≠ 0 := fun h0 => hx' 0 O.zero_mem (by simp [h0])
    have hinv := h2 x x.2 hx'
    have e : (1 : O) = x * ⟨(x : F)⁻¹, hinv⟩ := Subtype.ext (by simp [hx0])
    rw [e]
    exact J.mul_mem_right _ hxJ

variable {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))

theorem isOpen_OP : IsOpen ((OP P : Subring (P.adicCompletion L)) : Set (P.adicCompletion L)) := by
  have hc : Continuous fun x : P.adicCompletion L => (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => x) :=
    continuous_pi fun _ => continuous_pi fun _ => continuous_id
  convert (GlobalTheory.HaarMat.isOpen_intMat P 1 1).preimage hc using 1
  ext x
  simp [intMat]

theorem mem_adicCompletionIntegers_iff₂ (x : P.adicCompletion L) : x ∈ OP P ↔ Valued.v x ≤ 1 := by
  first
  | exact Iff.rfl
  | exact HeightOneSpectrum.mem_adicCompletionIntegers _ _ _

theorem piP_mem : ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) ∈ OP P := by
  rw [mem_adicCompletionIntegers_iff₂]
  have h := unif_spec P
  unfold IsUnifAt at h
  rw [piP, h, ← WithZero.exp_zero, WithZero.exp_le_exp]
  norm_num

theorem isCompact_GLint (r : ℕ) :
    IsCompact ((GLint (OP P) r : Subgroup (GL (Fin r) (P.adicCompletion L))) : Set (GL (Fin r) (P.adicCompletion L))) := by
  have hK : IsCompact (intMat (OP P) r r ×ˢ (MulOpposite.unop ⁻¹' intMat (OP P) r r)) :=
    (GlobalTheory.HaarMat.isCompact_intMat P r r).prod
      ((MulOpposite.opHomeomorph.symm.isCompact_preimage).2 (GlobalTheory.HaarMat.isCompact_intMat P r r))
  convert Units.isClosedEmbedding_embedProduct.isCompact_preimage hK using 1
  ext g
  exact Iff.rfl

theorem isUnitAt_det {r : ℕ} {k : GL (Fin r) (P.adicCompletion L)} (hk : k ∈ GLint (OP P) r) :
    IsUnitAt P (GeneralLinearGroup.det k) := by
  obtain ⟨h1, h2⟩ := hk
  have hdet : ∀ M : Matrix (Fin r) (Fin r) (P.adicCompletion L), IsInt (OP P) M → M.det ∈ OP P := by
    intro M hM
    have e : M = (OP P).subtype.mapMatrix (Matrix.of fun i j => (⟨M i j, hM i j⟩ : OP P)) := by
      ext i j; rfl
    rw [e, ← RingHom.map_det]
    exact Subtype.property _
  have a := (mem_adicCompletionIntegers_iff₂ P _).1 (hdet _ h1)
  have b := (mem_adicCompletionIntegers_iff₂ P _).1 (hdet _ h2)
  have hmul : (k : Matrix (Fin r) (Fin r) (P.adicCompletion L)).det * ((k⁻¹ : GL (Fin r) (P.adicCompletion L)) : Matrix (Fin r) (Fin r) (P.adicCompletion L)).det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  unfold IsUnitAt
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  apply le_antisymm a
  calc (1 : _) = Valued.v (k : Matrix (Fin r) (Fin r) (P.adicCompletion L)).det *
        Valued.v ((k⁻¹ : GL (Fin r) (P.adicCompletion L)) : Matrix (Fin r) (Fin r) (P.adicCompletion L)).det := by rw [← map_mul, hmul, map_one]
    _ ≤ Valued.v (k : Matrix (Fin r) (Fin r) (P.adicCompletion L)).det * 1 := by
      first
      | exact mul_le_mul_left' b _
      | exact mul_le_mul_of_nonneg_left b (zero_le _)
      | gcongr
    _ = _ := mul_one _

end Loc

end GlobalTheory.Mem.SingleQ

namespace GlobalTheory.Mem.SingleQ

section Dx

variable {F : Type} [Field F] [MeasurableSpace F]

omit [Field F] in
theorem measurable_fromRows' (r t : ℕ) :
    Measurable (fun p : Matrix (Fin r) (Fin r) F × Matrix (Fin t) (Fin r) F => Matrix.fromRows p.1 p.2) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  rcases i with i | i
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst)
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd)

def rowsH (r t : ℕ) : (Matrix (Fin r) (Fin r) F × Matrix (Fin t) (Fin r) F) →ₙ+ Matrix (Fin (r + t)) (Fin r) F where
  toFun p := rowEq r t (Matrix.fromRows p.1 p.2)
  map_add' p q := by
    ext i j
    simp only [rowEq_apply, Prod.fst_add, Prod.snd_add, Matrix.add_apply]
    rcases finSumFinEquiv.symm i with k | k <;> simp

theorem measurable_rowsH (r t : ℕ) : Measurable (rowsH (F := F) r t) := (rowEqM r t).measurable.comp (measurable_fromRows' r t)

omit [MeasurableSpace F] in
theorem rowsH_surj (r t : ℕ) : Function.Surjective (rowsH (F := F) r t) := fun y => ⟨(((rowEq r t).symm y).toRows₁, ((rowEq r t).symm y).toRows₂), by
  show rowEq r t (Matrix.fromRows _ _) = y
  rw [Matrix.fromRows_toRows, Equiv.apply_symm_apply]⟩

theorem map_rowsH (r t : ℕ) (m : Measure (Matrix (Fin r) (Fin r) F × Matrix (Fin t) (Fin r) F)) :
    (m.map (fun p => Matrix.fromRows p.1 p.2)).map (rowEqM r t) = m.map (rowsH r t) := by
  rw [Measure.map_map (rowEqM r t).measurable (measurable_fromRows' r t)]
  rfl

theorem measurableSet_intMat [TopologicalSpace F] [OpensMeasurableSpace F] {O : Subring F} (hO : IsOpen (O : Set F)) (n m : ℕ) :
    MeasurableSet (intMat O n m) := by
  have e : intMat O n m = ⋂ i, ⋂ j, (fun y : Matrix (Fin n) (Fin m) F => y i j) ⁻¹' (O : Set F) := by
    ext y; simp [intMat]
  rw [e]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    ((measurable_pi_apply j).comp (measurable_pi_apply i)) hO.measurableSet

omit [MeasurableSpace F] in
theorem preimage_rowsH (O : Subring F) (r t : ℕ) :
    (rowsH (F := F) r t) ⁻¹' intMat O (r + t) r = intMat O r r ×ˢ intMat O t r := by
  ext ⟨A, B⟩
  simp only [Set.mem_preimage, Set.mem_prod]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i j
      have hij := h (finSumFinEquiv (Sum.inl i)) j
      change rowEq r t (Matrix.fromRows A B) _ j ∈ O at hij
      rw [rowEq_apply, Equiv.symm_apply_apply] at hij
      exact hij
    · intro i j
      have hij := h (finSumFinEquiv (Sum.inr i)) j
      change rowEq r t (Matrix.fromRows A B) _ j ∈ O at hij
      rw [rowEq_apply, Equiv.symm_apply_apply] at hij
      exact hij
  · rintro ⟨h1, h2⟩ i j
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
    change rowEq r t (Matrix.fromRows A B) _ j ∈ O
    rw [rowEq_apply, Equiv.symm_apply_apply]
    rcases s with k | k
    · exact h1 k j
    · exact h2 k j

end Dx

end GlobalTheory.Mem.SingleQ

namespace GlobalTheory.Mem.SingleQ

section Main

variable {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))

theorem absNorm_ne_zero₂ : qP P ≠ 0 := by
  unfold qP
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact P.ne_bot

theorem finite_kF : Finite (kF (OP P) ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) (piP_mem P)) := Nat.finite_of_card_ne_zero (by rw [GlobalTheory.T.card_residueRing_completion_chosenUniformiser L P (piP_mem P)]; exact absNorm_ne_zero₂ P)

theorem vol_Jset (r : ℕ) [MeasurableSpace (P.adicCompletion L)] [BorelSpace (P.adicCompletion L)]
    (ν₁ : Measure (Matrix (Fin r) (Fin r) (P.adicCompletion L))) [ν₁.IsAddLeftInvariant]
    (h1 : ν₁ (intMat (OP P) r r) = 1) :
    (ν₁ (Jset (GLint (OP P) r))).toReal = Formalism.MainNotions.ZetaProductPairs.qE (qP P : ℝ) 1 r := by
  haveI := isMaximal_span (piP_mem P) (GlobalTheory.T.isLocalAt_completionIntegers_chosenUniformiser L P)
  letI : Field (kF (OP P) _ (piP_mem P)) := Ideal.Quotient.field _
  letI : Fintype (kF (OP P) _ (piP_mem P)) := @Fintype.ofFinite _ (finite_kF P)
  have hc : Nat.card (kF (OP P) _ (piP_mem P)) = qP P := GlobalTheory.T.card_residueRing_completion_chosenUniformiser L P (piP_mem P)
  have h := Formalism.DoubleCosetMeasures.Final.volJadd (P.adicCompletion L) (OP P) (isOpen_OP P) _ (piP_mem P) (Units.ne_zero _)
    (GlobalTheory.T.isLocalAt_completionIntegers_chosenUniformiser L P) (finite_kF P) r ν₁ (GLint (OP P) r) (fun g hg => hg.1) le_rfl
  rw [Formalism.DoubleCosetMeasures.Final.glRed (P.adicCompletion L) (OP P) _ (piP_mem P) (Units.ne_zero _) (GlobalTheory.T.isLocalAt_completionIntegers_chosenUniformiser L P)
    (finite_kF P) r, h1, mul_one, hc] at h
  have hG := GlobalTheory.T.card_GL_finiteField_eq_pow_mul_prod (kF (OP P) _ (piP_mem P)) r
  rw [Fintype.card_eq_nat_card, hc] at hG
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_natCast, hG] at h'
  have hq : (qP P : ℝ) ^ (r * r) ≠ 0 := pow_ne_zero _ (by exact_mod_cast absNorm_ne_zero₂ P)
  exact mul_right_cancel₀ hq (by rw [h', mul_comm])

theorem vol_II (r t : ℕ) [MeasurableSpace (P.adicCompletion L)] [BorelSpace (P.adicCompletion L)]
    (ν₂ : Measure (Matrix (Fin t) (Fin r) (P.adicCompletion L))) [ν₂.IsAddLeftInvariant]
    (h2 : ν₂ (intMat (OP P) t r) = 1) :
    (ν₂ (IIset (OP P) ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L))).toReal =
      (qP P : ℝ) ^ (-((t * r : ℕ) : ℤ)) := by
  have hq : (Nat.card (kF (OP P) _ (piP_mem P)) : ENNReal) = (qP P : ENNReal) := by
    rw [GlobalTheory.T.card_residueRing_completion_chosenUniformiser L P (piP_mem P)]
  have h := Formalism.DoubleCosetMeasures.Final.volII (P.adicCompletion L) (OP P) (isOpen_OP P) _ (piP_mem P) (Units.ne_zero _)
    (finite_kF P) t r ν₂
  rw [h2, hq] at h
  have e : ν₂ (IIset (OP P) ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L)) = ((qP P : ENNReal) ^ (t * r))⁻¹ :=
    ENNReal.eq_inv_of_mul_eq_one_left h
  rw [e, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast, _root_.zpow_neg, zpow_natCast]

end Main

end GlobalTheory.Mem.SingleQ

namespace GlobalTheory.Mem.SingleQ

theorem parJ_zero {F : Type} [Field F] (O : Subring F) (ϖ : F) (r : ℕ) :
    parJ O ϖ r 0 = ((GLint O r : Subgroup (GL (Fin r) F)) : Set (GL (Fin r) F)) := by
  ext k
  simp only [parJ, Set.mem_setOf_eq, SetLike.mem_coe]
  exact ⟨fun h => h.1, fun h => ⟨h, fun i => i.elim0⟩⟩

theorem stepAt_one : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)), Deg1 P →
    ∀ (δ ν : (P.adicCompletion L)ˣ →* ℂˣ), IsDel P δ → IsNu P ν → ∀ r t : ℕ, 1 ≤ t →
    StepAt P δ (fun _ => ν) r t 0 (zVal1 (qP P) r t : ℂ) := by
  intro L _ _ P _ δ ν hδ hν r t _
  obtain ⟨nrm, hnrm⟩ := GlobalTheory.Mem.NrmCompl.exists_isNrm L P
  letI : MeasurableSpace (P.adicCompletion L) := borel _
  haveI : BorelSpace (P.adicCompletion L) := ⟨rfl⟩
  refine ⟨nrm, hnrm, ?_⟩
  have hchar : ∀ k : GLint (OP P) r,
      (((ν * δ) (GeneralLinearGroup.det (k : GL (Fin r) (P.adicCompletion L))) : ℂˣ) : ℂ) *
        (((nrm (((GeneralLinearGroup.det (k : GL (Fin r) (P.adicCompletion L))) : (P.adicCompletion L)ˣ) :
          P.adicCompletion L)) ^ (((r + t : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
        (((δ.comp (GeneralLinearGroup.det.comp (GLint (OP P) r).subtype))⁻¹ k : ℂˣ) : ℂ) *
        (starRingEnd ℂ) (((1 : GLint (OP P) r →* ℂˣ) k : ℂˣ) : ℂ) = 1 := by
    intro k
    have hu := isUnitAt_det P k.2
    have hd : (((δ (GeneralLinearGroup.det (k : GL (Fin r) (P.adicCompletion L)))) : ℂˣ) : ℂ) ≠ 0 :=
      Units.ne_zero _
    rw [MonoidHom.mul_apply, Units.val_mul, hν.unr _ hu, (hnrm _).1 hu, Real.one_rpow]
    simp [Units.val_inv_eq_inv_val, hd]
  obtain ⟨μ, hμ, hμ1⟩ := GlobalTheory.T.exists_haar_GL_completion_integers_vol_one L P r
  obtain ⟨ν₁, hν₁, hs₁, hν₁1⟩ := GlobalTheory.T.exists_addHaar_completionIntegralMatrices_vol_one L P r r
  obtain ⟨ν₂, hν₂, hs₂, hν₂1⟩ := GlobalTheory.T.exists_addHaar_completionIntegralMatrices_vol_one L P t r
  haveI := hν₁
  haveI := hν₂
  haveI := hs₁
  haveI := hs₂
  haveI hA1 : MeasurableAdd (Matrix (Fin r) (Fin r) (P.adicCompletion L)) :=
    inferInstanceAs (MeasurableAdd (Fin r → Fin r → P.adicCompletion L))
  haveI hA2 : MeasurableAdd (Matrix (Fin t) (Fin r) (P.adicCompletion L)) :=
    inferInstanceAs (MeasurableAdd (Fin t → Fin r → P.adicCompletion L))
  haveI hA3 : MeasurableAdd (Matrix (Fin (r + t)) (Fin r) (P.adicCompletion L)) :=
    inferInstanceAs (MeasurableAdd (Fin (r + t) → Fin r → P.adicCompletion L))
  haveI hA4 : MeasurableAdd (Matrix (Fin r) (Fin r) (P.adicCompletion L) × Matrix (Fin t) (Fin r) (P.adicCompletion L)) :=
    ⟨fun c => by
      first
      | exact ((measurable_const_add c.1).comp measurable_fst).prodMk ((measurable_const_add c.2).comp measurable_snd)
      | exact ((measurable_const_add c.1).comp measurable_fst).prod_mk ((measurable_const_add c.2).comp measurable_snd),
     fun c => by
      first
      | exact ((measurable_add_const c.1).comp measurable_fst).prodMk ((measurable_add_const c.2).comp measurable_snd)
      | exact ((measurable_add_const c.1).comp measurable_fst).prod_mk ((measurable_add_const c.2).comp measurable_snd)⟩
  have hc : ∀ g, mcoef (OP P) μ (fun _ : GL (Fin r) (P.adicCompletion L) => (1 : ℂ)) g = 1 := by
    intro g
    simp [mcoef, setIntegral_const, Measure.real, hμ1]
  show IsStep (OP P) _ nrm δ (fun _ => ν) r t 0 _
  unfold IsStep
  rw [Nat.zero_mul, Nat.zero_add, Nat.one_mul]
  refine ⟨ℂ, inferInstance, inferInstance, 1, isUnrM_one (OP P) nrm r _, fun _ => 1,
    one_mem_typeSp (OP P) _ nrm δ r, μ, (ν₁.prod ν₂).map (rowsH r t), hμ, ?_, hc 1, ?_, ?_, ?_⟩
  · rw [parJ_zero]; exact hμ1
  · exact isAddLeftInvariant_map (rowsH r t) (measurable_rowsH r t) (rowsH_surj r t)
  · show Measure.map (rowsH r t) (ν₁.prod ν₂) (intMat (OP P) (r + t) r) = 1
    rw [Measure.map_apply (measurable_rowsH r t) (measurableSet_intMat (isOpen_OP P) _ _), preimage_rowsH,
      Measure.prod_prod, hν₁1, hν₂1, one_mul]
  · have hlam : ∀ (g : GL (Fin r) (P.adicCompletion L)) (k : GLint (OP P) r),
        mcoef (OP P) μ (fun _ => (1 : ℂ)) (g * k) =
          (((1 : GLint (OP P) r →* ℂˣ) k : ℂˣ) : ℂ) * mcoef (OP P) μ (fun _ => (1 : ℂ)) g := by
      intro g k; rw [hc, hc]; simp
    have hρ : ∀ k, ‖(((δ.comp (GeneralLinearGroup.det.comp (GLint (OP P) r).subtype))⁻¹ k : ℂˣ) : ℂ)‖ = 1 := by
      intro k; simp [hδ.unitary]
    have key := Formalism.DoubleCosetMeasures.Final.lemmaUSplit (P.adicCompletion L) r t (OP P) (isOpen_OP P) _ (Units.ne_zero (piP P))
      (GLint (OP P) r) (isCompact_GLint P r) (fun k hk => hk.1)
      ((δ.comp (GeneralLinearGroup.det.comp (GLint (OP P) r).subtype))⁻¹) hρ (ν * δ) nrm 1
      hchar
      (mcoef (OP P) μ fun _ => (1 : ℂ)) hlam μ ν₁ ν₂
    have hΦ : (phiQ (OP P) ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) δ r t 0 ∘ rowEq r t) =
        phiU (OP P) _ (GLint (OP P) r) ((δ.comp (GeneralLinearGroup.det.comp (GLint (OP P) r).subtype))⁻¹) :=
      funext (phiQ_rowEq (OP P) _ δ r t)
    rw [← hΦ, ← localZ_map, map_rowsH] at key
    refine Eq.trans ?_ key.symm
    rw [hμ1, vol_Jset P r ν₁ hν₁1, vol_II P r t ν₂ hν₂1, hc 1]
    simp [zVal1]

end GlobalTheory.Mem.SingleQ
