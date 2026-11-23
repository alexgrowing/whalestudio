import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCC

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Phi

variable {ι : Type} [Fintype ι] {r k : ℕ}

def Φc (x : ∀ p : CBlk r, CSpc ι k p) (i : ι × LsNc5.CIdx r k) : ℝ :=
  match i with
  | (v, Sum.inl (Sum.inl (p, t))) => LsNc5.reim ((x (Sum.inl (Sum.inl p)) : ι → ℂ) v) t
  | (v, Sum.inl (Sum.inr (b, t))) => LsNc5.reim ((x (Sum.inl (Sum.inr b)) : ι → Fin (k + 1) → ℂ) v (Fin.last k)) t
  | (v, Sum.inr (Sum.inl (b, j, t))) =>
      LsNc5.reim ((x (Sum.inl (Sum.inr b)) : ι → Fin (k + 1) → ℂ) v (Fin.castSucc j)) t
  | (v, Sum.inr (Sum.inr (Sum.inl (p, t)))) => LsNc5.reim ((x (Sum.inr (Sum.inl p)) : ι → ℂ) v) t
  | (v, Sum.inr (Sum.inr (Sum.inr a))) => (x (Sum.inr (Sum.inr a)) : ι → ℝ) v

theorem measurable_Φc : Measurable (Φc (ι := ι) (r := r) (k := k)) := by
  refine measurable_pi_lambda _ fun i => ?_
  rcases i with ⟨v, ((⟨p, t⟩ | ⟨b, t⟩) | (⟨b, j, t⟩ | (⟨p, t⟩ | a)))⟩
  · exact (reim_cont t).measurable.comp ((measurable_pi_apply v).comp
      (measurable_pi_apply (Sum.inl (Sum.inl p) : CBlk r)))
  · exact (reim_cont t).measurable.comp ((measurable_pi_apply (Fin.last k)).comp ((measurable_pi_apply v).comp
      (measurable_pi_apply (Sum.inl (Sum.inr b) : CBlk r))))
  · exact (reim_cont t).measurable.comp ((measurable_pi_apply (Fin.castSucc j)).comp ((measurable_pi_apply v).comp
      (measurable_pi_apply (Sum.inl (Sum.inr b) : CBlk r))))
  · exact (reim_cont t).measurable.comp ((measurable_pi_apply v).comp
      (measurable_pi_apply (Sum.inr (Sum.inl p) : CBlk r)))
  · exact (measurable_pi_apply v).comp (measurable_pi_apply (Sum.inr (Sum.inr a) : CBlk r))

def Ψc (y : ι × LsNc5.CIdx r k → ℝ) : ∀ p : CBlk r, CSpc ι k p
  | Sum.inl (Sum.inl p) => fun v => (⟨y (v, Sum.inl (Sum.inl (p, false))), y (v, Sum.inl (Sum.inl (p, true)))⟩ : ℂ)
  | Sum.inl (Sum.inr b) => fun v j =>
      if h : j.val < k then (⟨y (v, Sum.inr (Sum.inl (b, ⟨j.val, h⟩, false))),
        y (v, Sum.inr (Sum.inl (b, ⟨j.val, h⟩, true)))⟩ : ℂ)
      else (⟨y (v, Sum.inl (Sum.inr (b, false))), y (v, Sum.inl (Sum.inr (b, true)))⟩ : ℂ)
  | Sum.inr (Sum.inl p) => fun v =>
      (⟨y (v, Sum.inr (Sum.inr (Sum.inl (p, false)))), y (v, Sum.inr (Sum.inr (Sum.inl (p, true))))⟩ : ℂ)
  | Sum.inr (Sum.inr a) => fun v => y (v, Sum.inr (Sum.inr (Sum.inr a)))

theorem Φc_Ψc (y : ι × LsNc5.CIdx r k → ℝ) : Φc (Ψc y) = y := by
  funext i
  rcases i with ⟨v, ((⟨p, t⟩ | ⟨b, t⟩) | (⟨b, j, t⟩ | (⟨p, t⟩ | a)))⟩
  · cases t <;> rfl
  · have hj : ¬ (Fin.last k).val < k := by simp
    cases t <;> simp [Φc, Ψc, hj, LsNc5.reim]
  · have hj : (Fin.castSucc j).val < k := j.isLt
    cases t <;> simp [Φc, Ψc, hj, LsNc5.reim]
  · cases t <;> rfl
  · rfl

theorem Ψc_Φc (x : ∀ p : CBlk r, CSpc ι k p) : Ψc (Φc x) = x := by
  funext p
  rcases p with ((p | b) | (p | a))
  · funext v; apply Complex.ext <;> rfl
  · funext v j
    show (if h : j.val < k then _ else _) = _
    split_ifs with h
    · apply Complex.ext
      · show LsNc5.reim (_ : ℂ) false = _
        simp only [LsNc5.reim, Bool.false_eq_true, if_false]
        congr 2
      · show LsNc5.reim (_ : ℂ) true = _
        simp only [LsNc5.reim, if_true]
        congr 2
    · have hj : j = Fin.last k := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
      subst hj
      apply Complex.ext <;> rfl
  · funext v; apply Complex.ext <;> rfl
  · rfl

theorem measurable_Ψc : Measurable (Ψc (ι := ι) (r := r) (k := k)) := by
  have hC : ∀ f g : (ι × LsNc5.CIdx r k → ℝ) → ℝ, Measurable f → Measurable g →
      Measurable fun y => (⟨f y, g y⟩ : ℂ) := fun f g hf hg =>
    Complex.measurableEquivRealProd.symm.measurable.comp (hf.prodMk hg)
  refine measurable_pi_lambda _ fun p => ?_
  rcases p with ((p | b) | (p | a))
  · exact measurable_pi_lambda _ fun v => hC _ _ (measurable_pi_apply _) (measurable_pi_apply _)
  · refine measurable_pi_lambda _ fun v => measurable_pi_lambda _ fun j => ?_
    show Measurable fun y : ι × LsNc5.CIdx r k → ℝ => (if h : j.val < k then (⟨y (v, Sum.inr (Sum.inl (b, ⟨j.val, h⟩, false))),
        y (v, Sum.inr (Sum.inl (b, ⟨j.val, h⟩, true)))⟩ : ℂ)
      else (⟨y (v, Sum.inl (Sum.inr (b, false))), y (v, Sum.inl (Sum.inr (b, true)))⟩ : ℂ))
    split_ifs with h
    · exact hC _ _ (measurable_pi_apply _) (measurable_pi_apply _)
    · exact hC _ _ (measurable_pi_apply _) (measurable_pi_apply _)
  · exact measurable_pi_lambda _ fun v => hC _ _ (measurable_pi_apply _) (measurable_pi_apply _)
  · exact measurable_pi_lambda _ fun v => measurable_pi_apply _

end Phi

section Box

variable {ι : Type} [Fintype ι] {r k : ℕ}

def cRow (b : Fin r) (j : Fin (k + 1)) (t : Bool) : LsNc5.CIdx r k :=
  if h : j.val < k then Sum.inr (Sum.inl (b, ⟨j.val, h⟩, t)) else Sum.inl (Sum.inr (b, t))

def Sbox (s : ι × LsNc5.CIdx r k → Set ℝ) : ∀ p : CBlk r, Set (CSpc ι k p)
  | Sum.inl (Sum.inl p) => Set.univ.pi fun v => {z : ℂ | LsNc5.reim z false ∈ s (v, Sum.inl (Sum.inl (p, false))) ∧
      LsNc5.reim z true ∈ s (v, Sum.inl (Sum.inl (p, true)))}
  | Sum.inl (Sum.inr b) => Set.univ.pi fun v => Set.univ.pi fun j : Fin (k + 1) =>
      {z : ℂ | LsNc5.reim z false ∈ s (v, cRow b j false) ∧ LsNc5.reim z true ∈ s (v, cRow b j true)}
  | Sum.inr (Sum.inl p) => Set.univ.pi fun v => {z : ℂ | LsNc5.reim z false ∈ s (v, Sum.inr (Sum.inr (Sum.inl (p, false)))) ∧
      LsNc5.reim z true ∈ s (v, Sum.inr (Sum.inr (Sum.inl (p, true))))}
  | Sum.inr (Sum.inr a) => Set.univ.pi fun v => s (v, Sum.inr (Sum.inr (Sum.inr a)))

theorem Φc_row (x : ∀ p : CBlk r, CSpc ι k p) (v : ι) (b : Fin r) (j : Fin (k + 1)) (t : Bool) :
    Φc x (v, cRow b j t) = LsNc5.reim ((x (Sum.inl (Sum.inr b)) : ι → Fin (k + 1) → ℂ) v j) t := by
  unfold cRow
  split_ifs with h
  · rfl
  · have hj : j = Fin.last k := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
    subst hj; rfl

theorem pre_box (s : ι × LsNc5.CIdx r k → Set ℝ) :
    Φc ⁻¹' Set.univ.pi s = Set.univ.pi (Sbox (ι := ι) (k := k) s) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_univ_pi]
  constructor
  · intro h p
    rcases p with ((p | b) | (p | a))
    · intro v _; exact ⟨h (v, Sum.inl (Sum.inl (p, false))), h (v, Sum.inl (Sum.inl (p, true)))⟩
    · intro v _ j _
      refine ⟨?_, ?_⟩
      · have := h (v, cRow b j false); rwa [Φc_row] at this
      · have := h (v, cRow b j true); rwa [Φc_row] at this
    · intro v _; exact ⟨h (v, Sum.inr (Sum.inr (Sum.inl (p, false)))), h (v, Sum.inr (Sum.inr (Sum.inl (p, true))))⟩
    · intro v _; exact h (v, Sum.inr (Sum.inr (Sum.inr a)))
  · intro h i
    rcases i with ⟨v, ((⟨p, t⟩ | ⟨b, t⟩) | (⟨b, j, t⟩ | (⟨p, t⟩ | a)))⟩
    · have := h (Sum.inl (Sum.inl p)) v (Set.mem_univ v); cases t; exacts [this.1, this.2]
    · have := h (Sum.inl (Sum.inr b)) v (Set.mem_univ v) (Fin.last k) (Set.mem_univ _)
      have e : ∀ t, cRow (k := k) b (Fin.last k) t = Sum.inl (Sum.inr (b, t)) := fun t => by simp [cRow]
      have h2 := Φc_row x v b (Fin.last k) t
      rw [e] at h2
      rw [h2]
      cases t
      · have := this.1; rwa [e] at this
      · have := this.2; rwa [e] at this
    · have := h (Sum.inl (Sum.inr b)) v (Set.mem_univ v) (Fin.castSucc j) (Set.mem_univ _)
      have e : ∀ t, cRow (k := k) b (Fin.castSucc j) t = Sum.inr (Sum.inl (b, j, t)) := fun t => by
        simp [cRow]
      have h2 := Φc_row x v b (Fin.castSucc j) t
      rw [e] at h2
      rw [h2]
      cases t
      · have := this.1; rwa [e] at this
      · have := this.2; rwa [e] at this
    · have := h (Sum.inr (Sum.inl p)) v (Set.mem_univ v); cases t; exacts [this.1, this.2]
    · exact h (Sum.inr (Sum.inr a)) v (Set.mem_univ v)

theorem cMeas_Sbox (s : ι × LsNc5.CIdx r k → Set ℝ) (hs : ∀ i, MeasurableSet (s i)) (p : CBlk r) :
    cMeas ι k p (Sbox s p) =
      match p with
      | Sum.inl (Sum.inl p) => ∏ v, volume (s (v, Sum.inl (Sum.inl (p, false)))) * volume (s (v, Sum.inl (Sum.inl (p, true))))
      | Sum.inl (Sum.inr b) => ∏ v, ∏ j : Fin (k + 1), volume (s (v, cRow b j false)) * volume (s (v, cRow b j true))
      | Sum.inr (Sum.inl p) => ∏ v, volume (s (v, Sum.inr (Sum.inr (Sum.inl (p, false))))) *
          volume (s (v, Sum.inr (Sum.inr (Sum.inl (p, true)))))
      | Sum.inr (Sum.inr a) => ∏ v, volume (s (v, Sum.inr (Sum.inr (Sum.inr a)))) := by
  rcases p with ((p | b) | (p | a))
  · show (volume : Measure (ι → ℂ)) (Set.univ.pi _) = _
    rw [volume_pi_pi]
    exact Finset.prod_congr rfl fun v _ => volume_reim _ _ (hs _) (hs _)
  · show (volume : Measure (ι → Fin (k + 1) → ℂ)) (Set.univ.pi _) = _
    rw [volume_pi_pi]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [volume_pi_pi]
    exact Finset.prod_congr rfl fun j _ => volume_reim _ _ (hs _) (hs _)
  · show (volume : Measure (ι → ℂ)) (Set.univ.pi _) = _
    rw [volume_pi_pi]
    exact Finset.prod_congr rfl fun v _ => volume_reim _ _ (hs _) (hs _)
  · show (volume : Measure (ι → ℝ)) (Set.univ.pi _) = _
    rw [volume_pi_pi]

theorem map_Φc : (Measure.pi (cMeas ι k (r := r))).map Φc = volume := by
  refine (Measure.pi_eq (μ := fun _ : ι × LsNc5.CIdx r k => (volume : Measure ℝ))
    (μ' := (Measure.pi (cMeas ι k (r := r))).map Φc) fun s hs => ?_).symm
  rw [Measure.map_apply measurable_Φc (MeasurableSet.univ_pi hs), pre_box, Measure.pi_pi]
  simp_rw [cMeas_Sbox s hs]
  rw [Fintype.prod_prod_type]
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_bool, Fin.prod_univ_castSucc,
    Finset.prod_mul_distrib]
  have e1 : ∀ (b : Fin r) (t : Bool), cRow (k := k) b (Fin.last k) t = Sum.inl (Sum.inr (b, t)) := fun b t => by
    simp [cRow]
  have e2 : ∀ (b : Fin r) (j : Fin k) (t : Bool), cRow (k := k) b (Fin.castSucc j) t = Sum.inr (Sum.inl (b, j, t)) :=
    fun b j t => by simp [cRow]
  simp only [e1, e2]
  have swap : ∀ {β : Type} [Fintype β] (f : ι → β → ℝ≥0∞), ∏ v, ∏ b, f v b = ∏ b, ∏ v, f v b :=
    fun f => Finset.prod_comm
  simp only [swap]
  ring

end Box

theorem kap_eq_Φc {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (s : X.B.I.Ginf) :
    LsNc5.kap X u s = Φc (blk X u s) := by
  funext i
  rcases i with ⟨v, ((⟨p, t⟩ | ⟨b, t⟩) | (⟨b, j, t⟩ | (⟨p, t⟩ | a)))⟩
  · rfl
  · show LsNc5.reim (LsNc5.yVec X u v s b) t = LsNc5.reim (blk X u s (Sum.inl (Sum.inr b)) v (Fin.last D.R.k)) t
    simp [blk]
  · show LsNc5.reim (LsNc5.phiMat X u v s b j) t =
      LsNc5.reim (blk X u s (Sum.inl (Sum.inr b)) v (Fin.castSucc j)) t
    simp [blk]
  · rfl
  · rfl

end Formalism.L2.SG.Pf.NcReal.JX
