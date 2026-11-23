import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.FlagLevelCharacterEqPsiDivN

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting PI.UnitaryDimensionFormula.unitaryCongruence Matrix

namespace PI.UnitaryDimensionFormula.NormCutK

section Dual

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def repr0 (v : VA X.B.I) : VA X.B.I :=
  (∑ a, hA X.B.I (X.f0 a) v • X.e0 a) + (∑ a, hA X.B.I (X.e0 a) v • X.f0 a) - hA X.B.I X.z0 v • X.z0 +
    (∑ l, hA X.B.I (X.bwd l) v • X.bw l) + (∑ l, hA X.B.I (X.bw l) v • X.bwd l)

theorem Z_smul_mL {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} {u : VA X.B.I} (hc : ZMod' X.B.I X.B.g c)
    (hu : u ∈ X.B.I.Lf) : c • u ∈ mL X.B.I X.B.g := by
  obtain ⟨t, ht, rfl⟩ := hc
  rw [mul_comm, mul_smul]
  exact Submodule.smul_mem (mL X.B.I X.B.g) (⟨t, ht⟩ : IntAf X.B.I.F X.B.I.E) (smul_mem_mL X.B.I hu)

theorem reference_repr_add (v w : VA X.B.I) : repr0 X (v + w) = repr0 X v + repr0 X w := by
  simp only [repr0, hA_add_right, add_smul, Finset.sum_add_distrib]
  abel

theorem reference_repr_smul (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (v : VA X.B.I) : repr0 X (c • v) = c • repr0 X v := by
  simp only [repr0, hA_smul_right, mul_smul, ← Finset.smul_sum, smul_add, smul_sub]

theorem frame_Lf : (∀ a, X.e0 a ∈ X.B.I.Lf) ∧ (∀ a, X.f0 a ∈ X.B.I.Lf) ∧ X.z0 ∈ X.B.I.Lf ∧
    (∀ l, X.bw l ∈ X.B.I.Lf) ∧ (∀ l, X.bwd l ∈ X.B.I.Lf) := ⟨fun a => (X.vectorsInLattice.1 a).1, fun a => (X.vectorsInLattice.1 a).2, X.vectorsInLattice.2.1,
    fun l => (X.vectorsInLattice.2.2 l).1, fun l => (X.vectorsInLattice.2.2 l).2⟩

theorem reference_repr_mem_lattice {v : VA X.B.I} (hv : v ∈ X.B.I.Lf) : repr0 X v ∈ X.B.I.Lf := by
  obtain ⟨he, hf, hz, hb, hbd⟩ := frame_Lf X
  have sm : ∀ {u w : VA X.B.I}, u ∈ X.B.I.Lf → w ∈ X.B.I.Lf → hA X.B.I u v • w ∈ X.B.I.Lf :=
    fun {u w} hu hw =>
      (Submodule.smul_mem X.B.I.Lf (⟨hA X.B.I u v, hA_int X.B.I hu hv⟩ : IntAf X.B.I.F X.B.I.E) hw : _)
  unfold repr0
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · exact Submodule.sum_mem _ fun a _ => sm (hf a) (he a)
  · exact Submodule.sum_mem _ fun a _ => sm (he a) (hf a)
  · exact sm hz hz
  · exact Submodule.sum_mem _ fun l _ => sm (hbd l) (hb l)
  · exact Submodule.sum_mem _ fun l _ => sm (hb l) (hbd l)

def ReprSub : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I) where
  carrier := {v | v - repr0 X v ∈ mL X.B.I X.B.g}
  add_mem' {v w} hv hw := by
    show v + w - repr0 X (v + w) ∈ mL X.B.I X.B.g
    rw [reference_repr_add, show v + w - (repr0 X v + repr0 X w) = (v - repr0 X v) + (w - repr0 X w) by abel]
    exact add_mem hv hw
  zero_mem' := by
    show (0 : VA X.B.I) - repr0 X 0 ∈ mL X.B.I X.B.g
    have : repr0 X 0 = 0 := by simpa using reference_repr_smul X 0 0
    rw [this, sub_zero]; exact zero_mem _
  smul_mem' c v hv := by
    show (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • v - repr0 X ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • v) ∈ mL X.B.I X.B.g
    rw [reference_repr_smul, ← smul_sub]
    exact Submodule.smul_mem _ c hv

theorem T_gen (s : VA X.B.I) (tA tB : Fin D.R.rS → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
    (tC : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (tP tQ : Fin D.R.k → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
    (hs : s = (∑ a, tA a • X.e0 a) + (∑ a, tB a • X.f0 a) - tC • X.z0 + (∑ l, tP l • X.bw l) +
      (∑ l, tQ l • X.bwd l))
    (h1 : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) s - tA a))
    (h2 : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) s - tB a))
    (h3 : ZMod' X.B.I X.B.g (hA X.B.I X.z0 s - tC))
    (h4 : ∀ l, ZMod' X.B.I X.B.g (hA X.B.I (X.bwd l) s - tP l))
    (h5 : ∀ l, ZMod' X.B.I X.B.g (hA X.B.I (X.bw l) s - tQ l)) :
    s ∈ ReprSub X := by
  have neg : ∀ {x y : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}, ZMod' X.B.I X.B.g (x - y) →
      ZMod' X.B.I X.B.g (y - x) := fun {x y} h => by
    have := Z_sub X.B.I X.B.g (Z_zero X.B.I X.B.g) h
    rwa [zero_sub, neg_sub] at this
  obtain ⟨he, hf, hz, hb, hbd⟩ := frame_Lf X
  have key : ∀ t : VA X.B.I, t = (∑ a, tA a • X.e0 a) + (∑ a, tB a • X.f0 a) - tC • X.z0 +
      (∑ l, tP l • X.bw l) + (∑ l, tQ l • X.bwd l) →
      t - repr0 X s = (∑ a, (tA a - hA X.B.I (X.f0 a) s) • X.e0 a) +
        (∑ a, (tB a - hA X.B.I (X.e0 a) s) • X.f0 a) - (tC - hA X.B.I X.z0 s) • X.z0 +
        (∑ l, (tP l - hA X.B.I (X.bwd l) s) • X.bw l) + (∑ l, (tQ l - hA X.B.I (X.bw l) s) • X.bwd l) := by
    intro t ht
    rw [ht, repr0]
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  show s - repr0 X s ∈ mL X.B.I X.B.g
  rw [key s hs]
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · exact Submodule.sum_mem _ fun a _ => Z_smul_mL X (neg (h1 a)) (he a)
  · exact Submodule.sum_mem _ fun a _ => Z_smul_mL X (neg (h2 a)) (hf a)
  · exact Z_smul_mL X (neg h3) hz
  · exact Submodule.sum_mem _ fun l _ => Z_smul_mL X (neg (h4 l)) (hb l)
  · exact Submodule.sum_mem _ fun l _ => Z_smul_mL X (neg (h5 l)) (hbd l)

theorem Z_of_sym {u w : VA X.B.I} {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (h : ZMod' X.B.I X.B.g (hA X.B.I w u - sigA X.B.I c)) : ZMod' X.B.I X.B.g (hA X.B.I u w - c) := by
  have e : hA X.B.I u w - c = sigA X.B.I (hA X.B.I w u - sigA X.B.I c) := by
    rw [map_sub, sigA_sigA, hA_symm X.B.I w u]
  rw [e]
  exact Z_sig X.B.I X.B.g h

theorem Z0 {x : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (h : ZMod' X.B.I X.B.g x) : ZMod' X.B.I X.B.g (x - 0) := by
  simpa using h

theorem hA_bw_bw (l m : Fin D.R.k) : hA X.B.I (X.bw l) (X.bw m) = 0 := by
  rw [X.bw_w l, X.bw_w m, hA_smul_left, hA_smul_right, ← mul_assoc, mul_comm (sigA X.B.I X.ew) X.ew,
    X.ew_orth, zero_mul]

theorem hA_bwd_bwd (l m : Fin D.R.k) : hA X.B.I (X.bwd l) (X.bwd m) = 0 := by
  rw [X.bwd_w l, X.bwd_w m, hA_smul_left, hA_smul_right, sigA_sigA, ← mul_assoc, X.ew_orth, zero_mul]

theorem dual_coords {v : VA X.B.I} (hv : v ∈ X.B.I.Lf) : v - repr0 X v ∈ mL X.B.I X.B.g := by
  have sym : ∀ {u w : VA X.B.I}, ZMod' X.B.I X.B.g (hA X.B.I w u) → ZMod' X.B.I X.B.g (hA X.B.I u w) :=
    fun {u w} h => by
      have := Z_of_sym X (u := u) (w := w) (c := 0) (by rwa [map_zero, sub_zero])
      rwa [sub_zero] at this
  have mem_e : ∀ b, X.e0 b ∈ ReprSub X := fun b => by
    refine T_gen X (X.e0 b) (fun a => if a = b then 1 else 0) 0 0 0 0 ?_ ?_ ?_ ?_ ?_ ?_
    · simp [ite_smul]
    · intro a
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl]
        exact Z_of_sym X (by rw [map_one]; simpa using (X.gramIntegral a a).2.2)
      · rw [if_neg hab, sub_zero]
        exact sym (by simpa [Ne.symm hab] using (X.gramIntegral b a).2.2)
    · intro a; simpa using (X.gramIntegral a b).1
    · simpa using sym (X.formsAtZero.2 b).1
    · intro l; simpa using sym ((X.weightVectorsIntegral l).2.2 b).2.2.1
    · intro l; simpa using sym ((X.weightVectorsIntegral l).2.2 b).1
  have mem_f : ∀ b, X.f0 b ∈ ReprSub X := fun b => by
    refine T_gen X (X.f0 b) 0 (fun a => if a = b then 1 else 0) 0 0 0 ?_ ?_ ?_ ?_ ?_ ?_
    · simp [ite_smul]
    · intro a; simpa using (X.gramIntegral a b).2.1
    · intro a; exact (X.gramIntegral a b).2.2
    · simpa using sym (X.formsAtZero.2 b).2
    · intro l; simpa using sym ((X.weightVectorsIntegral l).2.2 b).2.2.2
    · intro l; simpa using sym ((X.weightVectorsIntegral l).2.2 b).2.1
  have zeta_mem_function_algebra : X.z0 ∈ ReprSub X := by
    refine T_gen X X.z0 0 0 (-1) 0 0 ?_ ?_ ?_ ?_ ?_ ?_
    · simp
    · intro a; simpa using (X.formsAtZero.2 a).2
    · intro a; simpa using (X.formsAtZero.2 a).1
    · rw [sub_neg_eq_add]; exact X.formsAtZero.1
    · intro l; simpa using sym (X.weightVectorsIntegral l).2.1
    · intro l; simpa using sym (X.weightVectorsIntegral l).1
  have mem_bw : ∀ m, X.bw m ∈ ReprSub X := fun m => by
    refine T_gen X (X.bw m) 0 0 0 (fun l => if l = m then X.ew else 0) 0 ?_ ?_ ?_ ?_ ?_ ?_
    · simpa [ite_smul] using X.bw_w m
    · intro a; simpa using ((X.weightVectorsIntegral m).2.2 a).2.1
    · intro a; simpa using ((X.weightVectorsIntegral m).2.2 a).1
    · simpa using (X.weightVectorsIntegral m).1
    · intro l; exact X.bw_dual l m
    · intro l; rw [hA_bw_bw X l m]; simpa using Z_zero X.B.I X.B.g
  have mem_bwd : ∀ m, X.bwd m ∈ ReprSub X := fun m => by
    refine T_gen X (X.bwd m) 0 0 0 0 (fun l => if l = m then sigA X.B.I X.ew else 0) ?_ ?_ ?_ ?_ ?_ ?_
    · simpa [ite_smul] using X.bwd_w m
    · intro a; simpa using ((X.weightVectorsIntegral m).2.2 a).2.2.2
    · intro a; simpa using ((X.weightVectorsIntegral m).2.2 a).2.2.1
    · simpa using (X.weightVectorsIntegral m).2.1
    · intro l; rw [hA_bwd_bwd X l m]; simpa using Z_zero X.B.I X.B.g
    · intro l
      refine Z_of_sym X ?_
      by_cases hlm : l = m
      · subst hlm
        rw [if_pos rfl, sigA_sigA]
        simpa using X.bw_dual l l
      · rw [if_neg hlm, map_zero]
        simpa [Ne.symm hlm] using X.bw_dual m l
  have hmL : mL X.B.I X.B.g ≤ ReprSub X := by
    unfold mL
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    show _ - repr0 X _ ∈ mL X.B.I X.B.g
    rw [reference_repr_smul, ← smul_sub]
    exact smul_mem_mL X.B.I (sub_mem hx (reference_repr_mem_lattice X hx))
  have hS : (Set.range X.e0 ∪ Set.range X.f0 ∪ {X.z0} ∪ Set.range X.bw ∪ Set.range X.bwd) ⊆
      (ReprSub X : Set (VA X.B.I)) := by
    rintro _ ((((⟨b, rfl⟩ | ⟨b, rfl⟩) | rfl) | ⟨m, rfl⟩) | ⟨m, rfl⟩)
    exacts [mem_e b, mem_f b, zeta_mem_function_algebra, mem_bw m, mem_bwd m]
  have hv' : v ∈ Submodule.span (IntAf X.B.I.F X.B.I.E)
      (Set.range X.e0 ∪ Set.range X.f0 ∪ {X.z0} ∪ Set.range X.bw ∪ Set.range X.bwd) ⊔
        mL X.B.I X.B.g := X.latticeSpan v hv
  exact (sup_le (Submodule.span_le.2 hS) hmL) hv'

end Dual

end PI.UnitaryDimensionFormula.NormCutK
