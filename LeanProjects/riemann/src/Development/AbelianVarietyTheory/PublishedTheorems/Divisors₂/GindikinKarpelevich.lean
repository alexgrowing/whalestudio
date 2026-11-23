import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBorelSphericalFunction
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
import Formalism.SatakeDualWeyl.StatementF
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

noncomputable section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound Formalism.UG

namespace GlobalTheory

namespace WeylCell

section Ring

variable {R : Type} [CommRing R] {n : ℕ}

def IsWeylRep (w : Equiv.Perm (Fin n)) (x : GL (Fin n) R) : Prop :=
  ∀ i j, i ≠ w j → (x : Matrix (Fin n) (Fin n) R) i j = 0

def cell (x : GL (Fin n) R) : Subgroup (GL (Fin n) R) :=
  unipB R (Fin n) ⊓ (unipBLower R (Fin n)).comap (MulAut.conj x⁻¹).toMonoidHom

theorem mem_unipBLower {g : GL (Fin n) R} :
    g ∈ unipBLower R (Fin n) ↔ (∀ i j, i < j → (g : Matrix (Fin n) (Fin n) R) i j = 0) ∧
      ∀ i, (g : Matrix (Fin n) (Fin n) R) i i = 1 := by
  refine (mem_unipRad (e := opp (points (Fin n)))).trans (and_congr Iff.rfl ⟨fun h i => ?_, fun h i _ _ => ?_⟩)
  · exact (h i () ()).trans (by simp)
  · exact (h i).trans (by simp)

theorem mem_cell {x u : GL (Fin n) R} :
    u ∈ cell x ↔ u ∈ unipB R (Fin n) ∧ x⁻¹ * u * x ∈ unipBLower R (Fin n) := by
  simp [cell, Subgroup.mem_inf, Subgroup.mem_comap]

theorem isClosed_cell [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] (x : GL (Fin n) R) :
    IsClosed (cell x : Set (GL (Fin n) R)) := by
  have key : ∀ (f : GL (Fin n) R → GL (Fin n) R), Continuous f → ∀ i j (c : R),
      IsClosed {u | (f u : Matrix (Fin n) (Fin n) R) i j = c} := fun f hf i j c =>
    isClosed_eq ((Units.continuous_val.comp hf).matrix_elem i j) continuous_const
  have hc : Continuous fun u : GL (Fin n) R => x⁻¹ * u * x := by fun_prop
  have e : (cell x : Set (GL (Fin n) R)) =
      ((⋂ i, ⋂ j, ⋂ _ : j < i, {u : GL (Fin n) R | (u : Matrix (Fin n) (Fin n) R) i j = 0}) ∩
        ⋂ i, {u : GL (Fin n) R | (u : Matrix (Fin n) (Fin n) R) i i = 1}) ∩
      ((⋂ i, ⋂ j, ⋂ _ : i < j, {u : GL (Fin n) R | ((x⁻¹ * u * x : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j = 0}) ∩
        ⋂ i, {u : GL (Fin n) R | ((x⁻¹ * u * x : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i i = 1}) := by
    ext u
    simp only [SetLike.mem_coe, mem_cell, mem_unipB, mem_unipBLower, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_setOf_eq]
  rw [e]
  refine ((isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => key _ continuous_id i j 0).inter
    (isClosed_iInter fun i => key _ continuous_id i i 1)).inter
    ((isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => key _ hc i j 0).inter
    (isClosed_iInter fun i => key _ hc i i 1))

variable (R) in

abbrev permRep (w : Equiv.Perm (Fin n)) : GL (Fin n) R := (Matrix.permMatrixHom (R := R)).toHomUnits w

theorem permRep_apply (w : Equiv.Perm (Fin n)) (i j : Fin n) :
    (permRep R w : Matrix (Fin n) (Fin n) R) i j = if i = w j then 1 else 0 := by
  simp [Matrix.permMatrixHom, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.Perm.inv_def, Equiv.symm_apply_eq]

theorem isWeylRep_permRep (w : Equiv.Perm (Fin n)) : IsWeylRep w (permRep R w) := fun _ _ h => by
  rw [permRep_apply, if_neg h]

end Ring

def cSL (Q z : ℂ) : ℂ := (1 - Q⁻¹ * z) / (1 - z)

def cSU (q z : ℂ) : ℂ := (1 - (q ^ 2)⁻¹ * z) * (1 + q⁻¹ * z) / (1 - z ^ 2)

abbrev lo {n : ℕ} (i : Fin (n / 2)) : Fin n := Fin.castLE (Nat.div_le_self n 2) i

def FormulaGL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ (n : ℕ) (α : Fin n → ℂˣ) (φ : GL (Fin n) k → ℂ),
    IsBorelSph k (fun i => (α i : ℂ) * (resCard k : ℂ) ^ (-(((n : ℂ) - 1 - 2 * (i.val : ℂ)) / 2))) φ →
  ∀ (w : Equiv.Perm (Fin n)) (x : GL (Fin n) k), x ∈ KO k (Fin n) → IsWeylRep w x →
    (∀ i j, i < j → w j < w i → ‖(α i : ℂ) / α j‖ < 1) →
  ∀ [MeasurableSpace (cell x)] [BorelSpace (cell x)] (μ : Measure (cell x)) [μ.IsHaarMeasure],
    μ ((KO k (Fin n)).subgroupOf (cell x)) = 1 →
    Integrable (fun u : cell x => φ (x⁻¹ * u)) μ ∧
      ∫ u : cell x, φ (x⁻¹ * u) ∂μ =
        ∏ i, ∏ j with i < j ∧ w j < w i, cSL (resCard k) ((α i : ℂ) / α j)

section Unitary

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def cellU {σ : L →+* L} {n : ℕ} (x : GU σ n) : Subgroup (GU σ n) :=
  (cell (x : GL (Fin n) L)).subgroupOf (GU σ n)

def FormulaU (σ : L →+* L) (q : ℕ) : Prop :=
  ∀ (n : ℕ) (α : Fin (n / 2) → ℂˣ) (φ : GU σ n → ℂ), IsSphericalU q (fun i => (α i : ℂ)) φ → φ 1 = 1 →
  ∀ (w : Equiv.Perm (Fin n)) (x : GU σ n), x ∈ KU σ n → IsWeylRep w (x : GL (Fin n) L) →
    (∀ i j, i < j → w (lo j) < w (lo i) → ‖(α i : ℂ) / α j‖ < 1) →
    (∀ i j, i < j → w (lo j).rev < w (lo i) → ‖(α i : ℂ) * α j‖ < 1) →
    (∀ i, w (lo i).rev < w (lo i) → ‖(α i : ℂ)‖ < 1) →
  ∀ [MeasurableSpace (cellU x)] [BorelSpace (cellU x)] (μ : Measure (cellU x)) [μ.IsHaarMeasure],
    μ ((KU σ n).subgroupOf (cellU x)) = 1 →
    Integrable (fun u : cellU x => φ (x⁻¹ * u)) μ ∧
      ∫ u : cellU x, φ (x⁻¹ * u) ∂μ =
        (∏ i, ∏ j with i < j ∧ w (lo j) < w (lo i), cSL ((q : ℂ) ^ 2) ((α i : ℂ) / α j)) *
        (∏ i, ∏ j with i < j ∧ w (lo j).rev < w (lo i), cSL ((q : ℂ) ^ 2) ((α i : ℂ) * α j)) *
        ∏ i with w (lo i).rev < w (lo i), if Even n then cSL q (α i) else cSU q (α i)

end Unitary

end WeylCell

namespace Published

open WeylCell

def GindikinKarpelevich : Prop :=
  (∀ (k : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    FormulaGL k) ∧
  ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L)
    (q : ℕ), IsUnramInv ϖ σ q → FormulaU σ q

end Published

namespace WeylCell

theorem exists_haar {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K N : Subgroup G}
    (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) (hN : IsClosed (N : Set G))
    [MeasurableSpace N] [BorelSpace N] : ∃ μ : Measure N, μ.IsHaarMeasure ∧ μ (K.subgroupOf N) = 1 := by
  have h1 : IsOpen (K.subgroupOf N : Set N) := ho.preimage continuous_subtype_val
  have h2 : IsCompact (K.subgroupOf N : Set N) := hN.isClosedEmbedding_subtypeVal.isCompact_preimage hc
  let P : TopologicalSpace.PositiveCompacts N := ⟨⟨_, h2⟩, by
    rw [show interior ((⟨_, h2⟩ : TopologicalSpace.Compacts N).carrier) = (K.subgroupOf N : Set N) from h1.interior_eq]
    exact ⟨1, one_mem _⟩⟩
  haveI : LocallyCompactSpace N := h2.locallyCompactSpace_of_mem_nhds_of_group (h1.mem_nhds (one_mem _))
  exact ⟨Measure.haarMeasure P, inferInstance, Measure.haarMeasure_self⟩

theorem exists_data_U {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L}
    {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (n : ℕ) (α : Fin (n / 2) → ℂˣ) (w : Equiv.Perm (Fin n))
    (hw : ∀ i, w i.rev = (w i).rev) :
    (∃ φ : GU σ n → ℂ, IsSphericalU q (fun i => (α i : ℂ)) φ ∧ φ 1 = 1) ∧
      (∃ x : GU σ n, x ∈ KU σ n ∧ IsWeylRep w (x : GL (Fin n) L)) ∧
      ∀ (x : GU σ n) [MeasurableSpace (cellU x)] [BorelSpace (cellU x)],
        ∃ μ : Measure (cellU x), μ.IsHaarMeasure ∧ μ ((KU σ n).subgroupOf (cellU x)) = 1 := by
  obtain ⟨ho, hc⟩ := LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n h
  obtain ⟨φ, hφ, h1, -⟩ := Final.SphericalExistsU L ϖ σ q n (n / 2) h (by omega) (by omega) (fun i => (α i : ℂ))
    fun i => (α i).ne_zero
  have hx : permRep L w ∈ GU σ n := by
    rw [LGrp.mem_GU_iff]
    intro i j
    rw [← map_inv, permRep_apply, permRep_apply, hw, apply_ite σ, map_one, map_zero]
    simp only [Fin.rev_inj, Equiv.Perm.eq_inv_iff_eq, eq_comm (a := j)]
  refine ⟨⟨φ, hφ, h1⟩, ⟨⟨_, hx⟩, ⟨hx, permRep _ w, ?_⟩, isWeylRep_permRep w⟩,
    fun x _ _ => exists_haar ho hc ((isClosed_cell _).preimage continuous_subtype_val)⟩
  ext i j
  show (intL L).subtype ((permRep _ w).val i j) = (permRep L w).val i j
  simp only [permRep_apply, apply_ite (intL L).subtype, map_one, map_zero]

end WeylCell

end GlobalTheory

end
