import Mathlib
import Formalism.PeriodIntegrals.LocJacTyp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.BoxMulAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitAbs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitSplit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.BoxMul

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim

section Gen

variable {W : Type} [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [LocallyCompactSpace W] [SecondCountableTopology W] [T2Space W] [MeasurableSpace W] [BorelSpace W]

theorem haar_shear (μ : Measure W) [μ.IsAddHaarMeasure] (Φ : W ≃ₜ+ W) (K : Set W)
    (hK : IsCompact K) (hKo : IsOpen K) (hK0 : K.Nonempty) (hΦ : Φ ⁻¹' K = K) (S : Set W) :
    μ (Φ ⁻¹' S) = μ S := by
  have hmap : ∀ T, (μ.map Φ) T = μ (Φ ⁻¹' T) := fun T =>
    (Φ.toHomeomorph.toMeasurableEquiv).map_apply (μ := μ) T
  have e := Measure.isAddLeftInvariant_eq_smul (μ.map Φ) μ
  have hpos : μ K ≠ 0 := hKo.measure_ne_zero μ hK0
  have hfin : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have h1 := congrArg (fun ν : Measure W => ν K) e
  simp only [hmap, hΦ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
  have hc : ((Measure.addHaarScalarFactor (μ.map Φ) μ : NNReal) : ENNReal) = 1 := by
    have h2 : (1 : ENNReal) * μ K = (Measure.addHaarScalarFactor (μ.map Φ) μ : ENNReal) * μ K := by
      rw [one_mul]; exact h1
    exact ((ENNReal.mul_left_inj hpos hfin).1 h2).symm
  rw [← hmap, e, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hc, one_mul]

end Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)}

theorem continuous_sigR' (σ : E →ₐ[F] E) : Continuous (sigR (Fv F v) σ) := by
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have h : ∀ x : Fv F v ⊗[F] E, sigR (Fv F v) σ x = (σ.toLinearMap.baseChange (Fv F v)) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have : (sigR (Fv F v) σ : Fv F v ⊗[F] E → Fv F v ⊗[F] E) = (σ.toLinearMap.baseChange (Fv F v)) :=
    funext h
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap _

namespace SD

variable (D : SD σ v)

theorem e_mul_f : D.e * (1 - D.e) = 0 := by
  rw [mul_sub, mul_one, D.he.eq, sub_self]

def shear {ι : Type} (τ : ι → ι) : (ι → Fv F v ⊗[F] E) ≃ₜ+ (ι → Fv F v ⊗[F] E) where
  toFun z k := z k + D.e * sigR (Fv F v) σ (z (τ k))
  invFun w k := w k - D.e * sigR (Fv F v) σ (w (τ k))
  left_inv z := by
    funext k
    simp only [map_add, map_mul, D.hσ]
    linear_combination (-(sigR (Fv F v) σ (sigR (Fv F v) σ (z (τ (τ k)))))) * D.e_mul_f
  right_inv w := by
    funext k
    simp only [map_sub, map_mul, D.hσ]
    linear_combination (-(sigR (Fv F v) σ (sigR (Fv F v) σ (w (τ (τ k)))))) * D.e_mul_f
  map_add' x y := by
    funext k
    simp only [Pi.add_apply, map_add]
    ring
  continuous_toFun := continuous_pi fun k =>
    (continuous_apply k).add (continuous_const.mul ((continuous_sigR' σ).comp (continuous_apply (τ k))))
  continuous_invFun := continuous_pi fun k =>
    (continuous_apply k).sub (continuous_const.mul ((continuous_sigR' σ).comp (continuous_apply (τ k))))

theorem shear_apply {ι : Type} (τ : ι → ι) (z : ι → Fv F v ⊗[F] E) (k : ι) :
    D.shear τ z k = z k + D.e * sigR (Fv F v) σ (z (τ k)) := rfl

theorem shear_first_coordinate {ι : Type} (τ : ι → ι) (z : ι → Fv F v ⊗[F] E) (k : ι) :
    D.p 0 (D.shear τ z k) = D.p 0 (z k) + D.p 1 (z (τ k)) := by
  rw [shear_apply, map_add, map_mul, D.p_e.1, (D.p_sig _).1, one_mul]

theorem shear_second_coordinate {ι : Type} (τ : ι → ι) (z : ι → Fv F v ⊗[F] E) (k : ι) :
    D.p 1 (D.shear τ z k) = D.p 1 (z k) := by
  rw [shear_apply, map_add, map_mul, D.p_e.2, zero_mul, add_zero]

theorem mem_box_iff {ι : Type} (z : ι → Fv F v ⊗[F] E) :
    z ∈ Obox (E := E) v ι ↔ ∀ k, D.p 0 (z k) ∈ v.adicCompletionIntegers F ∧
      D.p 1 (z k) ∈ v.adicCompletionIntegers F := by
  simp only [Obox, Set.mem_pi, Set.mem_univ, true_implies, D.mem_iff]

theorem shear_box {ι : Type} (τ : ι → ι) : D.shear τ ⁻¹' Obox (E := E) v ι = Obox (E := E) v ι := by
  ext z
  rw [Set.mem_preimage, D.mem_box_iff, D.mem_box_iff]
  simp only [D.shear_first_coordinate, D.shear_second_coordinate]
  constructor
  · intro h k
    refine ⟨?_, (h k).2⟩
    have := sub_mem (h k).1 (h (τ k)).2
    simpa using this
  · intro h k
    exact ⟨add_mem (h k).1 (h (τ k)).2, (h k).2⟩

theorem mem_sc_mul (t : Fv F v) (c : Fv F v ⊗[F] E) :
    sc (E := E) v t * c ∈ OEv (E := E) v ↔
      t * D.p 0 c ∈ v.adicCompletionIntegers F ∧ t * D.p 1 c ∈ v.adicCompletionIntegers F := by
  rw [D.mem_iff, map_mul, map_mul, D.p_sc, D.p_sc]

def pt (s t : Fv F v) : Fv F v ⊗[F] E := s • D.e + t • (1 - D.e)

theorem p_pt (s t : Fv F v) : D.p 0 (D.pt s t) = s ∧ D.p 1 (D.pt s t) = t := D.p_pair s t

theorem isUnit_pt {s t : Fv F v} (hs : s ≠ 0) (ht : t ≠ 0) : IsUnit (D.pt s t) := by
  refine IsUnit.of_mul_eq_one (D.pt s⁻¹ t⁻¹) (D.ext ?_ ?_)
  · rw [map_mul, (D.p_pt _ _).1, (D.p_pt _ _).1, map_one, mul_inv_cancel₀ hs]
  · rw [map_mul, (D.p_pt _ _).2, (D.p_pt _ _).2, map_one, mul_inv_cancel₀ ht]

theorem mem_pt_mul (s t : Fv F v) (c : Fv F v ⊗[F] E) :
    D.pt s t * c ∈ OEv (E := E) v ↔
      s * D.p 0 c ∈ v.adicCompletionIntegers F ∧ t * D.p 1 c ∈ v.adicCompletionIntegers F := by
  rw [D.mem_iff, map_mul, map_mul, (D.p_pt _ _).1, (D.p_pt _ _).2]

theorem norm_pt (s t : Fv F v) : Algebra.norm (Fv F v) (D.pt s t) = s * t := by
  rw [D.norm_eq, (D.p_pt _ _).1, (D.p_pt _ _).2]

end SD

theorem obox_compact (ι : Type) [Finite ι] : IsCompact (Obox (E := E) v ι) :=
  isCompact_univ_pi fun _ => (integer_ring_topology (E := E) v).1

theorem obox_open (ι : Type) [Finite ι] : IsOpen (Obox (E := E) v ι) :=
  isOpen_set_pi Set.finite_univ fun _ _ => (integer_ring_topology (E := E) v).2.1

theorem obox_nonempty (ι : Type) : (Obox (E := E) v ι).Nonempty :=
  ⟨0, fun _ _ => Sd.oev_zero v⟩

end PI.UnitaryGroupMassFormula.LocJacTyp
