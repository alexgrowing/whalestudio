import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

noncomputable section

namespace GlobalTheory.GLCongrCptOpen

def congrSubgroup {R : Type} [CommRing R] (n : ℕ) (O : Subring R) (I : AddSubgroup R)
    (hI : ∀ a ∈ O, ∀ x ∈ I, a * x ∈ I) : Subgroup (GL (Fin n) R) where
  carrier := {g | (∀ i j, (g : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
    (∀ i j, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
    ∀ i j, (g : Matrix (Fin n) (Fin n) R) i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I}
  one_mem' := by
    have h : ∀ i j, (1 : Matrix (Fin n) (Fin n) R) i j ∈ O := fun i j => by
      rw [Matrix.one_apply]
      split_ifs
      exacts [O.one_mem, O.zero_mem]
    refine ⟨h, by simpa using h, fun i j => by simp⟩
  mul_mem' := by
    rintro g h ⟨g1, g2, g3⟩ ⟨h1, h2, h3⟩
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · rw [Units.val_mul, Matrix.mul_apply]
      exact O.sum_mem fun k _ => O.mul_mem (g1 _ _) (h1 _ _)
    · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
      exact O.sum_mem fun k _ => O.mul_mem (h2 _ _) (g2 _ _)
    · have e : ((g * h : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) - 1 =
          (g : Matrix (Fin n) (Fin n) R) * ((h : Matrix (Fin n) (Fin n) R) - 1) +
            ((g : Matrix (Fin n) (Fin n) R) - 1) := by
        rw [Units.val_mul]; noncomm_ring
      rw [← Matrix.sub_apply, e, Matrix.add_apply, Matrix.mul_apply]
      exact I.add_mem (I.sum_mem fun k _ => hI _ (g1 _ _) _ (h3 _ _)) (g3 _ _)
  inv_mem' := by
    rintro g ⟨g1, g2, g3⟩
    refine ⟨g2, by simpa only [inv_inv] using g1, fun i j => ?_⟩
    have e : ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) - 1 =
        -(((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * ((g : Matrix (Fin n) (Fin n) R) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [← Matrix.sub_apply, e, Matrix.neg_apply, Matrix.mul_apply]
    exact I.neg_mem (I.sum_mem fun k _ => hI _ (g2 _ _) _ (g3 _ _))

theorem isOpen_congrSubgroup {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (n : ℕ)
    (O : Subring R) (I : AddSubgroup R) (hI : ∀ a ∈ O, ∀ x ∈ I, a * x ∈ I)
    (hO : IsOpen (O : Set R)) (hIo : IsOpen (I : Set R)) :
    IsOpen (congrSubgroup n O I hI : Set (GL (Fin n) R)) := by
  have c1 : ∀ i j, Continuous fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R) i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  have c2 : ∀ i j, Continuous fun g : GL (Fin n) R => ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j :=
    fun i j => Units.continuous_coe_inv.matrix_elem i j
  change IsOpen {g : GL (Fin n) R | (∀ i j, (g : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
    (∀ i j, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
    ∀ i j, (g : Matrix (Fin n) (Fin n) R) i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I}
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hO.preimage (c1 i j)).inter
    ((isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hO.preimage (c2 i j)).inter
      (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        hIo.preimage ((c1 i j).sub continuous_const)))

theorem isCompact_congrSubgroup {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (n : ℕ) (O : Subring R) (I : AddSubgroup R) (hI : ∀ a ∈ O, ∀ x ∈ I, a * x ∈ I)
    (hO : IsOpen (O : Set R)) (hIo : IsOpen (I : Set R)) (hOc : IsCompact (O : Set R)) :
    IsCompact (congrSubgroup n O I hI : Set (GL (Fin n) R)) := by
  have hM : IsCompact {A : Matrix (Fin n) (Fin n) R | ∀ i j, A i j ∈ O} := by
    have := isCompact_univ_pi (fun _ : Fin n => isCompact_univ_pi (fun _ : Fin n => hOc))
    have e : {A : Matrix (Fin n) (Fin n) R | ∀ i j, A i j ∈ O} =
        (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => (O : Set R)) :=
      Set.ext fun A => ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    rw [e]
    exact this
  have hP := hM.prod (hM.image MulOpposite.continuous_op)
  have hE := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) R)).isCompact_preimage hP
  refine hE.of_isClosed_subset
    ((congrSubgroup n O I hI).isClosed_of_isOpen (isOpen_congrSubgroup n O I hI hO hIo)) ?_
  rintro g ⟨g1, g2, -⟩
  exact ⟨g1, _, g2, rfl⟩

theorem exists_compactOpen_congr :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (c : v.adicCompletion F), c ≠ 0 →
    ∃ K : Subgroup (GL (Fin n) (v.adicCompletion F)), IsOpen (K : Set (GL (Fin n) (v.adicCompletion F))) ∧
      IsCompact (K : Set (GL (Fin n) (v.adicCompletion F))) ∧ ∀ g ∈ K, ∀ i j,
        Valued.v ((g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤
          Valued.v c := by
  intro F _ _ v n c hc
  let O : Subring (v.adicCompletion F) := (v.adicCompletionIntegers F).toSubring
  have hO : IsOpen (O : Set (v.adicCompletion F)) := Valued.isOpen_valuationSubring _
  have hOc : IsCompact (O : Set (v.adicCompletion F)) :=
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  let I : AddSubgroup (v.adicCompletion F) := Valued.v.leAddSubgroup (Valued.v c)
  have hI : ∀ a ∈ O, ∀ x ∈ I, a * x ∈ I := fun a ha x hx => by
    change Valued.v (a * x) ≤ Valued.v c
    rw [map_mul]
    have ha' : Valued.v a ≤ 1 := ha
    have hx' : Valued.v x ≤ Valued.v c := hx
    simpa using mul_le_mul' ha' hx'
  have hIo : IsOpen (I : Set (v.adicCompletion F)) := by
    have e : (I : Set (v.adicCompletion F)) = (fun x => x / c) ⁻¹' (O : Set (v.adicCompletion F)) := by
      ext x
      change Valued.v x ≤ Valued.v c ↔ Valued.v (x / c) ≤ 1
      rw [map_div₀, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hc))]
    rw [e]
    exact hO.preimage (continuous_id.div_const c)
  exact ⟨congrSubgroup n O I hI, isOpen_congrSubgroup n O I hI hO hIo,
    isCompact_congrSubgroup n O I hI hO hIo hOc, fun g hg => hg.2.2⟩

end GlobalTheory.GLCongrCptOpen
