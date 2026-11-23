import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemClosureOfMemChartRing
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPositive
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.IntNumRelabel
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver chartRingOver secOver secMOver)

noncomputable section

section OneBlock

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

def unitSigmaEquiv (κ : Type) : (Σ _ : Unit, κ) ≃ κ where
  toFun v := v.2
  invFun i := ⟨(), i⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {κ : Type} [Fintype κ]

omit [Fintype κ] in

theorem chartRingOver_oneBlock_eq (x : κ → Ω) (c : Unit → κ) :
    chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) c = Algebra.adjoin F (Set.range fun i => x i / x (c ())) := by
  unfold chartRingOver
  congr 1
  ext z
  constructor
  · rintro ⟨⟨⟨⟩, a⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨(), a⟩, rfl⟩

omit [Fintype κ] in

theorem mem_secOver_oneBlock (x : κ → Ω) (n : ℤ) (t : Ω) :
    t ∈ secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => n) ↔
      ∀ j, x j ≠ 0 → t * x j ^ (-n) ∈ Algebra.adjoin F (Set.range fun i => x i / x j) := by
  unfold secOver
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply, Finset.univ_unique,
    Finset.prod_singleton, Subalgebra.mem_toSubmodule, chartRingOver_oneBlock_eq]
  constructor
  · intro h j hj
    exact h (fun _ => j) (fun _ => hj)
  · intro h c hc
    exact h (c ()) (hc ())

omit [Fintype κ] in

theorem secOver_oneBlock_comp {κ' : Type} (σ : κ' ≃ κ) (x : κ → Ω) (n : ℤ) :
    secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (x ∘ σ)) (fun _ => n) = secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => n) := by
  ext t
  rw [mem_secOver_oneBlock, mem_secOver_oneBlock]
  have hr : ∀ j', Set.range (fun i' => x (σ i') / x (σ j')) = Set.range (fun i => x i / x (σ j')) :=
    fun j' => σ.surjective.range_comp (fun i => x i / x (σ j'))
  simp only [Function.comp_apply]
  constructor
  · intro h j hj
    obtain ⟨j', rfl⟩ := σ.surjective j
    have := h j' hj
    rwa [hr] at this
  · intro h j' hj'
    rw [hr]
    exact h (σ j') hj'

omit [Fintype κ] in

theorem relDim_oneBlock_eq_iff (P : Ideal (MvPolynomial (Σ _ : Unit, κ) F)) (e : ℕ) :
    FieldNumbers.relDim P = ((e : ℕ) : WithBot (WithTop ℤ)) ↔
      ringKrullDim (MvPolynomial (Σ _ : Unit, κ) F ⧸ P) = ((e + 1 : ℕ) : WithBot ℕ∞) := by
  rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, Fintype.card_unit]

end OneBlock

section FirstTyping

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {N : ℕ}

theorem twistSys_secs_eq_secOver (x : Fin (N + 1) → Ω) (n : ℤ) :
    (Kleiman.twistSys F x n).secs = secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ => n) := by
  ext t
  rw [mem_secs_iff, mem_secOver_oneBlock]
  refine forall_congr' fun j => forall_congr' fun hj => ?_
  change t ∈ Kleiman.twistMod F x n (Kleiman.singleChart hj) ↔ _
  rw [Kleiman.twistMod_eq_span n _ (Finset.mem_singleton_self j), Submodule.mem_span_singleton]
  have hA : Kleiman.chartRing F x (Kleiman.singleChart hj) =
      Algebra.adjoin F (Set.range fun i => x i / x j) :=
    (chartRingOver_oneBlock x (fun _ => j) hj).symm.trans (chartRingOver_oneBlock_eq x (fun _ => j))
  rw [← hA]
  have hxn : x j ^ n ≠ 0 := zpow_ne_zero n hj
  constructor
  · rintro ⟨a, rfl⟩
    rw [Kleiman.chartRing_smul_def, zpow_neg, mul_assoc, mul_inv_cancel₀ hxn, mul_one]
    exact a.2
  · intro h
    refine ⟨⟨_, h⟩, ?_⟩
    rw [Kleiman.chartRing_smul_def]
    show t * x j ^ (-n) * x j ^ n = t
    rw [zpow_neg]
    exact inv_mul_cancel_right₀ hxn t

theorem mIdealOver_oneBlock (x : Fin (N + 1) → Ω) :
    mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) = Kleiman.primeOfOne (S := F) x := by
  have hc : ((MvPolynomial.uniqueAlgEquiv Ω Unit).toAlgHom.restrictScalars F).comp
      (mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)) = (Kleiman.cone (S := F) x).comp (Kleiman.oneBlock (S := F) (N := N)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, Kleiman.cone, Kleiman.oneBlock, ReciprocityTheory.ChartRestriction.G.Geo.coneMap]
  ext f
  rw [mIdealOver, RingHom.mem_ker, Kleiman.primeOfOne, Ideal.mem_comap, Kleiman.primeOf_eq, RingHom.mem_ker]
  have h := congrArg (fun φ => φ f) hc
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h
  rw [← h]
  exact (map_eq_zero_iff _ (MvPolynomial.uniqueAlgEquiv Ω Unit).injective).symm

theorem isSubvar_primeOf_iff (x : Fin (N + 1) → Ω) (e : ℕ) :
    Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) e ↔
      (∃ i, x i ≠ 0) ∧ ringKrullDim (Kleiman.Poly F N ⧸ Kleiman.primeOf (S := F) x) = ((e + 1 : ℕ) : WithBot ℕ∞) := by
  have hX : ∀ i, (X i : Kleiman.Poly F N) ∈ Kleiman.primeOf (S := F) x ↔ x i = 0 := fun i => by
    rw [Kleiman.mem_primeOf_of_isHomogeneous x (isHomogeneous_X F i), aeval_X]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := h.relevant
    exact ⟨⟨i, fun hx => hi ((hX i).mpr hx)⟩, h.dim⟩
  · rintro ⟨⟨i, hi⟩, hdim⟩
    exact ⟨inferInstance, fun p hp d => Kleiman.homogeneousComponent_mem_primeOf x hp d, le_rfl,
      ⟨i, fun h => hi ((hX i).mp h)⟩, hdim⟩

theorem isSubvar_iff_relDim (x : Fin (N + 1) → Ω) (e : ℕ) :
    Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) e ↔
      (∃ i, x i ≠ 0) ∧ FieldNumbers.relDim (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)) = ((e : ℕ) : WithBot (WithTop ℤ)) := by
  rw [isSubvar_primeOf_iff, relDim_oneBlock_eq_iff, mIdealOver_oneBlock, HilbertPositive.ringKrullDim_primeOfOne]

end FirstTyping

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
