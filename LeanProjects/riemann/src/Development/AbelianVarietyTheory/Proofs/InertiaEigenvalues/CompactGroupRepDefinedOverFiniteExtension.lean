import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicAutomorphismUnique

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CompactRepField

open Polynomial IntermediateField

theorem exists_mem_adjoin_simple (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (j : Ω →+* PadicAlgCl l) (x : PadicAlgCl l) : ∃ y : Ω, x ∈ ℚ_[l]⟮j y⟯ := by
  have hint : ∀ z : PadicAlgCl l, IsIntegral ℚ_[l] z := fun z =>
    (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  have hfin : ({x' | IsConjRoot ℚ_[l] x x' ∧ x ≠ x'} : Set (PadicAlgCl l)).Finite := by
    refine ((minpoly ℚ_[l] x).rootSet_finite (PadicAlgCl l)).subset fun x' hx' => ?_
    exact (isConjRoot_iff_mem_minpoly_rootSet (hint x)).1 hx'.1
  have hop : IsOpen (⋂ x' ∈ ({x' | IsConjRoot ℚ_[l] x x' ∧ x ≠ x'} : Set (PadicAlgCl l)),
      {y : PadicAlgCl l | ‖x - y‖ < ‖x - x'‖}) :=
    hfin.isOpen_biInter fun x' _ => isOpen_lt (by fun_prop) continuous_const
  obtain ⟨y, hy⟩ := (GlobalTheory.denseRange_of_isAlgClosed_padicAlgCl l Ω j).exists_mem_open hop
    ⟨x, by
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, sub_self, norm_zero, norm_pos_iff, sub_ne_zero]
      exact fun x' h => h.2⟩
  refine ⟨y, IsKrasner.krasner (minpoly.irreducible (hint x)).separable (IsAlgClosed.splits _)
    (hint _) fun x' h1 h2 => ?_⟩
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hy
  exact hy x' ⟨h1, h2⟩

theorem exists_countable_family (l : ℕ) [Fact l.Prime] :
    ∃ (ι : Type) (_ : Countable ι) (K : ι → IntermediateField ℚ_[l] (PadicAlgCl l)),
      (∀ i, FiniteDimensional ℚ_[l] (K i)) ∧
      ∀ s : Set (PadicAlgCl l), s.Finite → ∃ i, s ⊆ K i := by
  classical
  haveI halg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Countable (AlgebraicClosure ℚ) := by
    have h : {x : AlgebraicClosure ℚ | IsAlgebraic ℚ x}.Countable := Algebraic.countable ℚ _
    exact Set.countable_univ_iff.1 (h.mono fun x _ => halg.isAlgebraic x)
  let j : AlgebraicClosure ℚ →+* PadicAlgCl l :=
    (IsAlgClosed.lift (R := ℚ) (S := AlgebraicClosure ℚ) (M := PadicAlgCl l)).toRingHom
  refine ⟨Finset (AlgebraicClosure ℚ), inferInstance,
    fun S => IntermediateField.adjoin ℚ_[l] (j '' (S : Set _)), fun S => ?_, fun s hs => ?_⟩
  · haveI : Finite (j '' (S : Set (AlgebraicClosure ℚ))) := (S.finite_toSet.image j).to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  · choose y hy using exists_mem_adjoin_simple l (AlgebraicClosure ℚ) j
    refine ⟨(hs.image y).toFinset, fun x hx => ?_⟩
    refine IntermediateField.adjoin.mono _ _ _ ?_ (hy x)
    rw [Set.singleton_subset_iff]
    exact ⟨y x, by simpa using ⟨x, hx, rfl⟩, rfl⟩

def entrySubgroup {F E G : Type} [Field F] [Field E] [Algebra F E] [Group G] {a : ℕ}
    (r : G →* Matrix.GeneralLinearGroup (Fin a) E) (K : IntermediateField F E) : Subgroup G where
  carrier := {g | ∀ i j, (r g : Matrix (Fin a) (Fin a) E) i j ∈ K ∧
    (r g⁻¹ : Matrix (Fin a) (Fin a) E) i j ∈ K}
  one_mem' := fun i j => by
    have : (r 1 : Matrix (Fin a) (Fin a) E) i j ∈ K := by
      rw [map_one, Units.val_one, Matrix.one_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    exact ⟨this, by rwa [inv_one]⟩
  mul_mem' := fun {g h} hg hh i j => by
    rw [mul_inv_rev, map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_apply,
      Matrix.mul_apply]
    exact ⟨sum_mem fun k _ => mul_mem (hg i k).1 (hh k j).1,
      sum_mem fun k _ => mul_mem (hh i k).2 (hg k j).2⟩
  inv_mem' := fun {g} hg i j => ⟨(hg i j).2, by rw [inv_inv]; exact (hg i j).1⟩

theorem exists_finiteDimensional_entries_mem (l : ℕ) [Fact l.Prime] (G : Type) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] (n : ℕ)
    (r : G →* Matrix.GeneralLinearGroup (Fin n) (PadicAlgCl l))
    (hr : ∀ i j, Continuous fun g => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j) :
    ∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧
      ∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ K := by
  obtain ⟨ι, _, K, hK, hcov⟩ := exists_countable_family l
  have hKcl : ∀ m, IsClosed (K m : Set (PadicAlgCl l)) := fun m =>
    haveI : FiniteDimensional ℚ_[l] (K m).toSubalgebra.toSubmodule := hK m
    Submodule.closed_of_finiteDimensional (K m).toSubalgebra.toSubmodule
  have hcl : ∀ m, IsClosed (entrySubgroup r (K m) : Set G) := fun m => by
    have : (entrySubgroup r (K m) : Set G) = ⋂ i, ⋂ j,
        ((fun g => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j) ⁻¹' (K m) ∩
         (fun g => (r g⁻¹ : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j) ⁻¹' (K m)) := by
      ext g
      simp only [Set.mem_iInter]
      rfl
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      ((hKcl m).preimage (hr i j)).inter ((hKcl m).preimage ((hr i j).comp continuous_inv))
  have hun : ⋃ m, (entrySubgroup r (K m) : Set G) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨m, hm⟩ := hcov
      (Set.range (fun p : Fin n × Fin n => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) p.1 p.2) ∪
       Set.range (fun p : Fin n × Fin n => (r g⁻¹ : Matrix (Fin n) (Fin n) (PadicAlgCl l)) p.1 p.2))
      ((Set.finite_range _).union (Set.finite_range _))
    exact Set.mem_iUnion.2 ⟨m, fun i j =>
      ⟨hm (Or.inl ⟨(i, j), rfl⟩), hm (Or.inr ⟨(i, j), rfl⟩)⟩⟩
  obtain ⟨m, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hcl hun
  have hop : IsOpen (entrySubgroup r (K m) : Set G) :=
    Subgroup.isOpen_of_mem_nhds _ (mem_interior_iff_mem_nhds.1 hx)
  haveI : Finite (G ⧸ entrySubgroup r (K m)) := Subgroup.quotient_finite_of_isOpen _ hop
  let s : Set (PadicAlgCl l) := Set.range fun p : (G ⧸ entrySubgroup r (K m)) × Fin n × Fin n =>
    (r p.1.out : Matrix (Fin n) (Fin n) (PadicAlgCl l)) p.2.1 p.2.2
  haveI : Finite s := (Set.finite_range _).to_subtype
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] s) :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  haveI := hK m
  refine ⟨IntermediateField.adjoin ℚ_[l] s ⊔ K m, inferInstance, fun g i j => ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (entrySubgroup r (K m)) g
  have hg : g = (g : G ⧸ entrySubgroup r (K m)).out * (h : G)⁻¹ := by
    rw [hh, mul_inv_cancel_right]
  rw [hg, map_mul, Units.val_mul, Matrix.mul_apply]
  refine sum_mem fun k _ => mul_mem ?_ ?_
  · exact (le_sup_left : IntermediateField.adjoin ℚ_[l] s ≤ _)
      (IntermediateField.subset_adjoin _ _ ⟨(g, i, k), rfl⟩)
  · exact (le_sup_right : K m ≤ _) (h.2 k j).2

theorem exists_finExt_entries_mem :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] (a : ℕ) (r : G →* Matrix.GeneralLinearGroup (Fin a) (Om l)), Continuous (fun g => ((r g : Matrix.GeneralLinearGroup (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → ∀ L₀ : FinExt l, ∃ L : FinExt l, L₀.1 ≤ L.1 ∧ ∀ g i j, ((r g : Matrix.GeneralLinearGroup (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1 := by
  intro l _ G _ _ _ _ _ a r hr L₀
  obtain ⟨K, hK, h⟩ := exists_finiteDimensional_entries_mem l G a r
    fun i j => hr.matrix_elem i j
  haveI := L₀.2
  exact ⟨⟨L₀.1 ⊔ K, inferInstance⟩, le_sup_left, fun g i j =>
    (le_sup_right : K ≤ L₀.1 ⊔ K) (h g i j)⟩

end GlobalTheory.CompactRepField
