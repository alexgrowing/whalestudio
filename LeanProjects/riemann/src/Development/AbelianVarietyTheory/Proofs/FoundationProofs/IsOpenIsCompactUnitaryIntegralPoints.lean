import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.LFun.IntPtsUnitary

section General
variable {L : Type} [Field L] [TopologicalSpace L] [IsTopologicalRing L] {n : Type} [Fintype n] [DecidableEq n]

omit [TopologicalSpace L] [IsTopologicalRing L] in
theorem coe_GLint (O : Subring L) : (GLint n O : Set (GL n L)) =
    {g : GL n L | ∀ i j, (g : Matrix n n L) i j ∈ O} ∩ {g : GL n L | ∀ i j, ((g⁻¹ : GL n L) : Matrix n n L) i j ∈ O} :=
  Set.ext fun g => ⟨fun h => ⟨P.cartan_entries_of_mem O g h, P.cartan_entries_of_mem O _ (inv_mem h)⟩,
    fun h => P.cartan_mem_of_entries O g h.1 h.2⟩

theorem isOpen_GLint (O : Subring L) (hO : IsOpen (O : Set L)) : IsOpen (GLint n O : Set (GL n L)) := by
  rw [coe_GLint]
  simp only [Set.ofPred_forall]
  refine IsOpen.inter ?_ ?_
  · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hO.preimage (Units.continuous_val.matrix_elem i j)
  · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hO.preimage (Units.continuous_coe_inv.matrix_elem i j)

theorem isCompact_GLint [T2Space L] (O : Subring L) (hO : IsCompact (O : Set L)) :
    IsCompact (GLint n O : Set (GL n L)) := by
  have hM : IsCompact {A : Matrix n n L | ∀ i j, A i j ∈ O} := by
    have := isCompact_univ_pi fun _ : n => isCompact_univ_pi fun _ : n => hO
    have e : {A : Matrix n n L | ∀ i j, A i j ∈ O} =
        Set.univ.pi fun _ : n => Set.univ.pi fun _ : n => (O : Set L) :=
      Set.ext fun A => ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    exact e ▸ this
  have := (Units.isClosedEmbedding_embedProduct (α := Matrix n n L)).isCompact_preimage
    (hM.prod (hM.image MulOpposite.continuous_op))
  convert this using 1
  rw [coe_GLint]
  ext g
  exact ⟨fun h => ⟨h.1, _, h.2, rfl⟩, fun ⟨h1, A, hA, e⟩ => ⟨h1, fun i j => by
    have : A = ((g⁻¹ : GL n L) : Matrix n n L) := MulOpposite.op_injective e
    exact this ▸ hA i j⟩⟩

end General

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem isCompact_intL [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) :
    IsCompact (intL L : Set L) := by
  obtain ⟨-, -, -, hϖ, -, hq, hcard⟩ := h
  haveI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨ϖ, by rw [hϖ]; exact WithZero.coe_ne_zero, by rw [hϖ, ← WithZero.coe_one, ne_eq, WithZero.coe_inj]; decide⟩
  letI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)
  have hp := (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := L)).2 ⟨(Valued.isClosed_integer L).completeSpace_coe,
      (Valued.v : Valuation L _).valuationSubring_isDiscreteValuationRing,
      Nat.finite_of_card_ne_zero (ne_of_eq_of_ne hcard (pow_ne_zero _ (by omega)))⟩
  exact isCompact_iff_compactSpace.2 hp

theorem coe_KU (σ : L →+* L) (n : ℕ) :
    (KU σ n : Set (GU σ n)) = Subtype.val ⁻¹' (GLint (Fin n) (intL L) : Set (GL (Fin n) L)) := by
  ext g
  exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩

theorem isOpen_isCompact_KU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q →
      IsOpen (KU σ n : Set (GU σ n)) ∧ IsCompact (KU σ n : Set (GU σ n)) := by
  intro L _ _ _ ϖ σ q n h
  rw [coe_KU]
  refine ⟨(isOpen_GLint _ (Valued.isOpen_integer L)).preimage continuous_subtype_val, ?_⟩
  have hc : IsClosed (GU σ n : Set (GL (Fin n) L)) :=
    isClosed_eq (((Units.continuous_val.matrix_map (GlobalTheory.LGrp.continuous_of_unramInv h)).matrix_transpose.matrix_mul
      continuous_const).matrix_mul Units.continuous_val) continuous_const
  exact hc.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_GLint _ (isCompact_intL h))

end GlobalTheory.LFun.IntPtsUnitary
