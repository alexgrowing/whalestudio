import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgClosedResidueField
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ClosedBallValuationSubringToSubring
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section

open Matrix

namespace GlobalTheory.ValRing

section Lat

variable {K : Type} [Field K] (O : ValuationSubring K) {Γ : Type} [Group Γ] {n : ℕ}

def actL (M : Matrix (Fin n) (Fin n) K) : (Fin n → K) →ₗ[O] (Fin n → K) :=
  (Matrix.mulVecLin M).restrictScalars O

theorem actL_apply (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : actL O M v = M *ᵥ v := rfl

def lat (ρ : Γ →* GL (Fin n) K) (S : Finset Γ) : Submodule O (Fin n → K) :=
  Submodule.span O (Set.range fun p : S × Fin n =>
    ((ρ p.1.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (Pi.single p.2 1 : Fin n → K))

theorem gen_mem (ρ : Γ →* GL (Fin n) K) (S : Finset Γ)
    (hS : ∀ g, ∃ s ∈ S, ∀ i j, ((ρ (s⁻¹ * g) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ O)
    (g t : Γ) (i : Fin n) :
    ((ρ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (((ρ t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (Pi.single i 1 : Fin n → K)) ∈ lat O ρ S := by
  obtain ⟨s, hs, hh⟩ := hS (g * t)
  set h := ((ρ (s⁻¹ * (g * t)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hhdef
  have e1 : ((ρ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (((ρ t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (Pi.single i 1 : Fin n → K)) =
      ((ρ s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (h *ᵥ (Pi.single i 1 : Fin n → K)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hhdef, ← Units.val_mul, ← Units.val_mul, ← map_mul,
      ← map_mul, mul_inv_cancel_left]
  have e2 : h *ᵥ (Pi.single i 1 : Fin n → K) = ∑ k, h k i • (Pi.single k 1 : Fin n → K) := by
    funext m
    simp [Finset.sum_apply, Pi.single_apply]
  rw [e1, e2, Matrix.mulVec_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [Matrix.mulVec_smul]
  exact (lat O ρ S).smul_mem (⟨h k i, hh k i⟩ : O) (Submodule.subset_span ⟨(⟨s, hs⟩, k), rfl⟩)

theorem lat_stable (ρ : Γ →* GL (Fin n) K) (S : Finset Γ)
    (hS : ∀ g, ∃ s ∈ S, ∀ i j, ((ρ (s⁻¹ * g) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ O) (g : Γ) :
    ∀ x ∈ lat O ρ S, actL O ((ρ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x ∈ lat O ρ S := by
  have h : lat O ρ S ≤ (lat O ρ S).comap (actL O ((ρ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨t, i⟩, rfl⟩
    exact gen_mem O ρ S hS g t.1 i
  exact fun x hx => h hx

theorem single_mem (ρ : Γ →* GL (Fin n) K) (S : Finset Γ) (h1 : (1 : Γ) ∈ S) (i : Fin n) :
    (Pi.single i 1 : Fin n → K) ∈ lat O ρ S :=
  Submodule.subset_span ⟨(⟨1, h1⟩, i), by
    show ((ρ 1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (Pi.single i 1 : Fin n → K) = _
    rw [map_one, Units.val_one, Matrix.one_mulVec]⟩

def act (ρ : Γ →* GL (Fin n) K) (S : Finset Γ)
    (hS : ∀ g, ∃ s ∈ S, ∀ i j, ((ρ (s⁻¹ * g) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ O) :
    Γ →* Module.End O (lat O ρ S) where
  toFun δ := (actL O ((ρ δ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).restrict (lat_stable O ρ S hS δ)
  map_one' := by
    ext x : 1
    apply Subtype.ext
    simp [actL_apply]
  map_mul' := by
    intro a b
    ext x : 1
    apply Subtype.ext
    simp [actL_apply, Matrix.mulVec_mulVec]

theorem act_apply (ρ : Γ →* GL (Fin n) K) (S : Finset Γ)
    (hS : ∀ g, ∃ s ∈ S, ∀ i j, ((ρ (s⁻¹ * g) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ O)
    (δ : Γ) (x : lat O ρ S) :
    ((act O ρ S hS δ x : lat O ρ S) : Fin n → K) =
      ((ρ δ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (x : Fin n → K) := rfl

theorem lat_finite (ρ : Γ →* GL (Fin n) K) (S : Finset Γ) : Module.Finite O (lat O ρ S) :=
  Module.Finite.iff_fg.mpr (Submodule.fg_span (Set.finite_range _))

theorem lat_torsion (ρ : Γ →* GL (Fin n) K) (S : Finset Γ) : Submodule.torsion O (lat O ρ S) = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  rw [Submodule.mem_bot]
  obtain ⟨a, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
  have ha : ((a : O) : K) ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero a (Subtype.ext h)
  have h2 : ((a : O) : K) • (x : Fin n → K) = 0 := congrArg Subtype.val hax
  exact Subtype.ext ((smul_eq_zero.mp h2).resolve_left ha)

theorem exists_basis (ρ : Γ →* GL (Fin n) K) (S : Finset Γ) (h1 : (1 : Γ) ∈ S) :
    Nonempty (Module.Basis (Fin n) O (lat O ρ S)) := by
  have := lat_finite O ρ S
  have : Module.Flat O (lat O ρ S) :=
    (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).mpr (lat_torsion O ρ S)
  have : Module.Free O (lat O ρ S) := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis O (lat O ρ S)
  have hle : Fintype.card (Module.Free.ChooseBasisIndex O (lat O ρ S)) ≤ n := by
    have li := b.linearIndependent.map' (lat O ρ S).subtype (Submodule.ker_subtype _)
    have liK := (LinearIndependent.iff_fractionRing O K).mp li
    simpa using liK.fintype_card_le_finrank
  have hge : n ≤ Fintype.card (Module.Free.ChooseBasisIndex O (lat O ρ S)) := by
    have li : LinearIndependent O fun i : Fin n =>
        (⟨Pi.single i 1, single_mem O ρ S h1 i⟩ : lat O ρ S) := by
      apply LinearIndependent.of_comp (lat O ρ S).subtype
      refine (LinearIndependent.iff_fractionRing O K).mpr ?_
      have e : ((lat O ρ S).subtype ∘ fun i : Fin n =>
          (⟨Pi.single i 1, single_mem O ρ S h1 i⟩ : lat O ρ S)) = fun i => Pi.basisFun K (Fin n) i := by
        funext i
        simp
      rw [e]
      exact (Pi.basisFun K (Fin n)).linearIndependent
    have := li.fintype_card_le_finrank
    rwa [Module.finrank_eq_card_basis b, Fintype.card_fin] at this
  exact ⟨b.reindex (Fintype.equivFinOfCardEq (le_antisymm hle hge))⟩

theorem coe_repr_sum (ρ : Γ →* GL (Fin n) K) (S : Finset Γ) (b : Module.Basis (Fin n) O (lat O ρ S))
    (x : lat O ρ S) (l : Fin n) :
    ∑ i, algebraMap O K (b.repr x i) * ((b i : lat O ρ S) : Fin n → K) l = (x : Fin n → K) l := by
  have h := congrArg (fun y : lat O ρ S => (y : Fin n → K) l) (b.sum_repr x)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Algebra.smul_def] at h
  exact h

theorem conj (ρ : Γ →* GL (Fin n) K) (S : Finset Γ)
    (hS : ∀ g, ∃ s ∈ S, ∀ i j, ((ρ (s⁻¹ * g) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ O)
    (h1 : (1 : Γ) ∈ S) :
    ∃ (ρ0 : Γ →* GL (Fin n) O) (P : GL (Fin n) K), ∀ g,
      ((ρ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (P : Matrix (Fin n) (Fin n) K) * ((ρ0 g : GL (Fin n) O) : Matrix (Fin n) (Fin n) O).map (algebraMap O K) *
          ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨b⟩ := exists_basis O ρ S h1
  let G : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => ((b j : lat O ρ S) : Fin n → K) i
  let D : Matrix (Fin n) (Fin n) K :=
    Matrix.of fun i j => algebraMap O K (b.repr ⟨Pi.single j 1, single_mem O ρ S h1 j⟩ i)
  have hGD : G * D = 1 := by
    refine Matrix.ext fun l j => ?_
    rw [Matrix.mul_apply]
    have := coe_repr_sum O ρ S b ⟨Pi.single j 1, single_mem O ρ S h1 j⟩ l
    simp only [G, D, Matrix.of_apply]
    rw [Matrix.one_apply]
    convert this using 1
    · exact Finset.sum_congr rfl fun i _ => mul_comm (((b i : lat O ρ S) : Fin n → K) l) _
    · simp [Pi.single_apply]
  have hDG : D * G = 1 := mul_eq_one_comm.mp hGD
  let P : GL (Fin n) K := ⟨G, D, hGD, hDG⟩
  let ρ₀ : Γ →* GL (Fin n) O :=
    (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp (act O ρ S hS).toHomUnits
  refine ⟨ρ₀, P, fun γ => ?_⟩
  set C := LinearMap.toMatrixAlgEquiv b (act O ρ S hS γ) with hC
  have hρ0 : ((ρ₀ γ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = C := rfl
  have key : ((ρ γ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * G = G * C.map (algebraMap O K) := by
    refine Matrix.ext fun l j => ?_
    rw [Matrix.mul_apply, Matrix.mul_apply]
    have h1' := act_apply O ρ S hS γ (b j)
    have h2 := coe_repr_sum O ρ S b (act O ρ S hS γ (b j)) l
    rw [h1'] at h2
    simp only [G, Matrix.of_apply, Matrix.map_apply, hC, LinearMap.toMatrixAlgEquiv_apply]
    simp only [Matrix.mulVec, dotProduct] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hρ0]
  show ((ρ γ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = G * C.map (algebraMap O K) * D
  rw [← key, Matrix.mul_assoc, hGD, Matrix.mul_one]

end Lat

section Top

variable {K : Type} [Field K] (O : ValuationSubring K)

theorem exists_cover [TopologicalSpace K] (hO : IsOpen (O : Set K)) {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] {n : ℕ} (ρ : Γ →* GL (Fin n) K)
    (hρ : Continuous fun g => ((ρ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ∃ S : Finset Γ, (1 : Γ) ∈ S ∧
      ∀ g, ∃ s ∈ S, ∀ i j, ((ρ (s⁻¹ * g) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ O := by
  let U : Γ → Set Γ := fun s => {x | ∀ i j, ((ρ (s⁻¹ * x) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ O}
  have hU : ∀ s, IsOpen (U s) := by
    intro s
    have e : U s = ⋂ i, ⋂ j,
        (fun x => ((ρ (s⁻¹ * x) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) ⁻¹' (O : Set K) := by
      ext x
      simp [U]
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hO.preimage ((hρ.comp (continuous_const.mul continuous_id)).matrix_elem i j)
  have hcov : Set.univ ⊆ ⋃ s, U s := by
    intro x _
    refine Set.mem_iUnion.2 ⟨x, ?_⟩
    show ∀ i j, ((ρ (x⁻¹ * x) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ O
    intro i j
    rw [inv_mul_cancel, map_one, Units.val_one, Matrix.one_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU hcov
  classical
  refine ⟨insert 1 t, Finset.mem_insert_self _ _, fun g => ?_⟩
  have hg := ht (Set.mem_univ g)
  rw [Set.mem_iUnion₂] at hg
  obtain ⟨s, hs, hgs⟩ := hg
  exact ⟨s, Finset.mem_insert_of_mem hs, hgs⟩

theorem res_algClosed [IsAlgClosed K] : IsAlgClosed (IsLocalRing.ResidueField O) := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.AlgClosedResidueField.isAlgClosed_residueField
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.AlgClosedResidueField.isAlgClosed_residueField
  | exact @_root_.GlobalTheory.AlgClosedResidueField.isAlgClosed_residueField
  | exact _root_.GlobalTheory.AlgClosedResidueField.isAlgClosed_residueField
  | (apply _root_.GlobalTheory.AlgClosedResidueField.isAlgClosed_residueField <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlgClosedResidueField.isAlgClosed_residueField <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlgClosedResidueField.isAlgClosed_residueField <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlgClosedResidueField.isAlgClosed_residueField ..)

end Top

section Ball

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def unitBall : ValuationSubring K := GlobalTheory.ClosedBallValuationSubring.closedBallValuationSubring K

theorem mem_unitBall (x : K) : x ∈ (unitBall : ValuationSubring K) ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem mem_maximalIdeal_unitBall (x : (unitBall : ValuationSubring K)) :
    x ∈ IsLocalRing.maximalIdeal (unitBall : ValuationSubring K) ↔ ‖(x : K)‖ < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hx
    refine lt_of_le_of_ne x.2 fun h1 => hx ?_
    have hx0 : (x : K) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h1; exact zero_ne_one h1
    refine isUnit_iff_exists_inv.2 ⟨⟨(x : K)⁻¹, ?_⟩, Subtype.ext ?_⟩
    · show ‖(x : K)⁻¹‖ ≤ 1
      rw [norm_inv, h1, inv_one]
    · show (x : K) * (x : K)⁻¹ = 1
      exact mul_inv_cancel₀ hx0
  · rintro hx ⟨u, hu⟩
    have h0 : ((u : (unitBall : ValuationSubring K)) : K) *
        (((u⁻¹ : (unitBall : ValuationSubring K)ˣ) : (unitBall : ValuationSubring K)) : K) = 1 :=
      congrArg Subtype.val u.mul_inv
    have h := congrArg norm h0
    rw [norm_mul, norm_one] at h
    have h2 : ‖((u⁻¹ : (unitBall : ValuationSubring K)ˣ) : K)‖ ≤ 1 := (u⁻¹ : (unitBall : ValuationSubring K)ˣ).1.2
    rw [hu] at h
    nlinarith [norm_nonneg ((u⁻¹ : (unitBall : ValuationSubring K)ˣ) : K), norm_nonneg (x : K)]

theorem isOpen_unitBall : IsOpen ((unitBall : ValuationSubring K) : Set K) := by
  have : ((unitBall : ValuationSubring K) : Set K) = Metric.closedBall 0 1 := by
    ext x
    simp [mem_unitBall]
  rw [this]
  exact IsUltrametricDist.isOpen_closedBall 0 one_ne_zero

end Ball

theorem valRingModel : ValRingModel := by
  intro l _
  let O : ValuationSubring (Qbar l) := unitBall
  refine ⟨O, inferInstance, inferInstance, res_algClosed O, algebraMap O (Qbar l), fun a b h => Subtype.ext h,
    ?_, fun x => mem_maximalIdeal_unitBall x, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  · intro Γ _ _ _ _ n ρ hρ
    obtain ⟨S, h1, hS⟩ := exists_cover O isOpen_unitBall ρ hρ
    exact conj O ρ S hS h1

end GlobalTheory.ValRing
