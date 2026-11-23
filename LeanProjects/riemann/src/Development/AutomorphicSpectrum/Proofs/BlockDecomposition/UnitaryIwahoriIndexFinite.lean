import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwUIff
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem isOpen_iwU {σ : L →+* L} {n : ℕ} (hσv : ∀ x, Valued.v (σ x) = Valued.v x) :
    IsOpen (IwU σ n : Set (GU σ n)) := by
  have hc : ∀ i j : Fin n, Continuous fun g : GU σ n =>
      ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j := fun i j =>
    (Units.continuous_val.comp continuous_subtype_val).matrix_elem i j
  have hle : IsOpen {x : L | Valued.v x ≤ 1} := by
    convert Valued.isOpen_integer (Γ₀ := WithZero (Multiplicative ℤ)) L using 1
    ext x
    exact (Valuation.mem_integer_iff (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) x).symm
  have hlt : IsOpen {x : L | Valued.v x < 1} := by
    convert Valued.isOpen_ball L 1 using 2 with x
    simp only [Valuation.restrict_lt_one_iff]
  have hset : (IwU σ n : Set (GU σ n)) =
      ⋂ i : Fin n, ⋂ j : Fin n,
        ({g : GU σ n | Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1} ∩
         {g : GU σ n | j < i → Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) < 1}) := by
    ext g
    simp only [SetLike.mem_coe, mem_iwU_iff hσv g, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩ i j
      exact ⟨h1 i j, h2 i j⟩
    · intro h
      exact ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  refine (hle.preimage (hc i j)).inter ?_
  by_cases hij : j < i
  · have e : {g : GU σ n | j < i → Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) < 1} =
        (fun g : GU σ n => ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ⁻¹'
          {x : L | Valued.v x < 1} := by
      ext g
      simp [hij]
    rw [e]
    exact hlt.preimage (hc i j)
  · have e : {g : GU σ n | j < i → Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) < 1} =
        Set.univ := by
      ext g
      simp [hij]
    rw [e]
    exact isOpen_univ

theorem isOpen_map_conj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Subgroup G} (hH : IsOpen (H : Set G)) (t : G) :
    IsOpen ((H.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map]
  have e : ⇑(MulAut.conj t).toMonoidHom = fun x => t * x * t⁻¹ := by
    funext x
    simp [MulAut.conj_apply]
  rw [e]
  have h1 : IsOpenMap fun x : G => t * x * t⁻¹ :=
    (isOpenMap_mul_right t⁻¹).comp (isOpenMap_mul_left t)
  exact h1 _ hH

theorem finite_index_iwU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q →
      Finite (KU σ n ⧸ (IwU σ n).subgroupOf (KU σ n)) ∧
      ∀ t : GU σ n, Finite (IwU σ n ⧸
        (IwU σ n ⊓ (IwU σ n).map (MulAut.conj t).toMonoidHom).subgroupOf (IwU σ n)) := by
  intro L _ _ _ ϖ σ q n h
  obtain ⟨-, hKc, hle, -⟩ := GlobalTheory.CompanionTheory.KUFactsU.kuFacts L ϖ σ q n h
  have hIo : IsOpen (IwU σ n : Set (GU σ n)) := isOpen_iwU h.2.1
  haveI : CompactSpace (KU σ n) := isCompact_iff_compactSpace.mp hKc
  refine ⟨Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen _ _ hIo), fun t => ?_⟩
  have hIc : IsCompact (IwU σ n : Set (GU σ n)) :=
    hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hIo) fun x hx => hle hx
  haveI : CompactSpace (IwU σ n) := isCompact_iff_compactSpace.mp hIc
  have hOpen : IsOpen ((IwU σ n ⊓ (IwU σ n).map (MulAut.conj t).toMonoidHom : Subgroup (GU σ n)) :
      Set (GU σ n)) := by
    rw [Subgroup.coe_inf]
    exact hIo.inter (isOpen_map_conj hIo t)
  exact Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen _ _ hOpen)

end GlobalTheory.CompanionTheory.SatPow

end
