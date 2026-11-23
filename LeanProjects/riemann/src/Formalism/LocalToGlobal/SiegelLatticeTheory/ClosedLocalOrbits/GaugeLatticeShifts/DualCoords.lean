import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.unitaryCongruence Matrix

namespace Formalism.L2.SG.NormCut

section Dual

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def repr0 (v : VA X.B.I) : VA X.B.I :=
  (∑ a, hA X.B.I (X.f0 a) v • X.e0 a) + (∑ a, hA X.B.I (X.e0 a) v • X.f0 a) - hA X.B.I X.z0 v • X.z0 +
    (∑ l, hA X.B.I (X.bwd l) v • X.bw l) + (∑ l, hA X.B.I (X.bw l) v • X.bwd l)

theorem Z_smul_mL {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} {u : VA X.B.I} (hc : ZMod' X.B.I X.B.g c)
    (hu : u ∈ X.B.I.Lf) : c • u ∈ mL X.B.I X.B.g := by
  obtain ⟨t, ht, rfl⟩ := hc
  unfold mL
  refine Submodule.subset_span ⟨(⟨t, ht⟩ : IntAf X.B.I.F X.B.I.E) • u, Submodule.smul_mem _ _ hu, ?_⟩
  rw [mul_smul]
  rfl

theorem reference_repr_add (v w : VA X.B.I) : repr0 X (v + w) = repr0 X v + repr0 X w := by
  have hadd : ∀ x, hA X.B.I x (v + w) = hA X.B.I x v + hA X.B.I x w := fun x => by
    simp only [hA, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  simp only [repr0, hadd, add_smul, Finset.sum_add_distrib]
  abel

theorem reference_repr_smul (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (v : VA X.B.I) : repr0 X (c • v) = c • repr0 X v := by
  have hsm : ∀ x, hA X.B.I x (c • v) = c * hA X.B.I x v := fun x => by
    simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [repr0, hsm, mul_smul, smul_add, smul_sub, Finset.smul_sum]

theorem frame_Lf : (∀ a, X.e0 a ∈ X.B.I.Lf) ∧ (∀ a, X.f0 a ∈ X.B.I.Lf) ∧ X.z0 ∈ X.B.I.Lf ∧
    (∀ l, X.bw l ∈ X.B.I.Lf) ∧ (∀ l, X.bwd l ∈ X.B.I.Lf) := by
  exact ⟨fun a => (X.vectorsInLattice.1 a).1, fun a => (X.vectorsInLattice.1 a).2, X.vectorsInLattice.2.1, fun l => (X.vectorsInLattice.2.2 l).1,
    fun l => (X.vectorsInLattice.2.2 l).2⟩

theorem reference_repr_mem_lattice {v : VA X.B.I} (hv : v ∈ X.B.I.Lf) : repr0 X v ∈ X.B.I.Lf := by
  have hincl : ∀ e : X.B.I.E, sigA X.B.I (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) e) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (star e) := by
    intro e
    first
      | rfl
      | simp [sigA, Formalism.UG.sigR, Formalism.UG.inclE, Formalism.BasicNotions.CMData.sig]
  have hInt : ∀ s ∈ IntAf X.B.I.F X.B.I.E, sigA X.B.I s ∈ IntAf X.B.I.F X.B.I.E := by
    have hle : IntAf X.B.I.F X.B.I.E ≤ (IntAf X.B.I.F X.B.I.E).comap (sigA X.B.I) := by
      show Subring.closure _ ≤ _
      rw [Subring.closure_le]
      rintro _ (⟨⟨x, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
      · rw [SetLike.mem_coe, Subring.mem_comap]
        refine Subring.subset_closure (Or.inl ⟨⟨_, RingOfIntegers.mapRingEquiv (starRingAut : RingAut X.B.I.E) a, rfl⟩, ?_⟩)
        first
          | rfl
          | simp [sigA, Formalism.UG.sigR, Formalism.BasicNotions.CMData.sig]
      · rw [SetLike.mem_coe, Subring.mem_comap]
        refine Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, ?_⟩)
        simp [sigA, Formalism.UG.sigR]
    exact fun s hs => hle hs
  have hzl : ∀ v : VA X.B.I, hA X.B.I 0 v = 0 := fun v => by simp [hA, Formalism.UG.hform]
  have hzr : ∀ x : VA X.B.I, hA X.B.I x 0 = 0 := fun x => by simp [hA, Formalism.UG.hform]
  have hal : ∀ x x' v : VA X.B.I, hA X.B.I (x + x') v = hA X.B.I x v + hA X.B.I x' v := fun x x' v => by
    simp only [hA, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  have har : ∀ x v v' : VA X.B.I, hA X.B.I x (v + v') = hA X.B.I x v + hA X.B.I x v' := fun x v v' => by
    simp only [hA, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hsl : ∀ (s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (x y : VA X.B.I),
      hA X.B.I (s • x) y = sigA X.B.I s * hA X.B.I x y := by
    intro s x y
    simp only [hA, sigA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsr : ∀ (s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (x y : VA X.B.I),
      hA X.B.I x (s • y) = s * hA X.B.I x y := by
    intro s x y
    simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsl' : ∀ (r : IntAf X.B.I.F X.B.I.E) (x y : VA X.B.I),
      hA X.B.I (r • x) y = sigA X.B.I r * hA X.B.I x y := fun r x y => hsl r x y
  have hsr' : ∀ (r : IntAf X.B.I.F X.B.I.E) (x y : VA X.B.I),
      hA X.B.I x (r • y) = r * hA X.B.I x y := fun r x y => hsr r x y
  have hgen : ∀ y ∈ X.B.I.L, ∀ y' ∈ X.B.I.L,
      hA X.B.I (fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (y i))
        (fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (y' i)) ∈ IntAf X.B.I.F X.B.I.E := by
    intro y hy y' hy'
    obtain ⟨b, hb⟩ := (X.B.I.L_dual y').1 hy' y hy
    have e : hA X.B.I (fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (y i))
        (fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (y' i)) =
        Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (Formalism.UG.hform (starRingEnd _) X.B.I.J y y') := by
      simp only [hA, Formalism.UG.hform, map_sum, map_mul, Matrix.map_apply, hincl, starRingEnd_apply]
    rw [e, ← hb]
    show _ ∈ Subring.closure _
    exact Subring.subset_closure (Or.inl ⟨⟨_, b, rfl⟩, rfl⟩)
  have hpair : ∀ x ∈ X.B.I.Lf, ∀ w ∈ X.B.I.Lf, hA X.B.I x w ∈ IntAf X.B.I.F X.B.I.E := by
    intro x hx w hw
    unfold AutInst.Lf lamAf at hx hw
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨y, hy⟩, rfl⟩ := hz
      induction hw using Submodule.span_induction with
      | mem z' hz' =>
        obtain ⟨⟨y', hy'⟩, rfl⟩ := hz'
        exact hgen y hy y' hy'
      | zero => rw [hzr]; exact zero_mem _
      | add a b _ _ ha hb => rw [har]; exact add_mem ha hb
      | smul r a _ ha => rw [hsr']; exact mul_mem r.2 ha
    | zero => rw [hzl]; exact zero_mem _
    | add a b _ _ ha hb => rw [hal]; exact add_mem ha hb
    | smul r a _ ha => rw [hsl']; exact mul_mem (hInt _ r.2) ha
  obtain ⟨he, hf, hz, hb, hbd⟩ := frame_Lf X
  have hterm : ∀ x ∈ X.B.I.Lf, ∀ u ∈ X.B.I.Lf, hA X.B.I x v • u ∈ X.B.I.Lf := fun x hx u hu =>
    Submodule.smul_mem _ (⟨_, hpair x hx v hv⟩ : IntAf X.B.I.F X.B.I.E) hu
  unfold repr0
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) (hterm _ hz _ hz)) ?_) ?_
  · exact Submodule.sum_mem _ fun a _ => hterm _ (hf a) _ (he a)
  · exact Submodule.sum_mem _ fun a _ => hterm _ (he a) _ (hf a)
  · exact Submodule.sum_mem _ fun l _ => hterm _ (hbd l) _ (hb l)
  · exact Submodule.sum_mem _ fun l _ => hterm _ (hb l) _ (hbd l)

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
  have hneg' : ∀ x y, ZMod' X.B.I X.B.g (x - y) → ZMod' X.B.I X.B.g (y - x) := by
    rintro x y ⟨t, ht, e⟩
    exact ⟨-t, neg_mem ht, by rw [mul_neg, ← e, neg_sub]⟩
  obtain ⟨he, hf, hz, hb, hbd⟩ := frame_Lf X
  show s - repr0 X s ∈ mL X.B.I X.B.g
  have h0 : s - repr0 X s = ((∑ a, tA a • X.e0 a) + (∑ a, tB a • X.f0 a) - tC • X.z0 + (∑ l, tP l • X.bw l) +
      (∑ l, tQ l • X.bwd l)) - repr0 X s := congrArg (· - repr0 X s) hs
  rw [h0]
  have hexp : ((∑ a, tA a • X.e0 a) + (∑ a, tB a • X.f0 a) - tC • X.z0 + (∑ l, tP l • X.bw l) +
      (∑ l, tQ l • X.bwd l)) - repr0 X s =
      (∑ a, (tA a - hA X.B.I (X.f0 a) s) • X.e0 a) + (∑ a, (tB a - hA X.B.I (X.e0 a) s) • X.f0 a) -
        (tC - hA X.B.I X.z0 s) • X.z0 + (∑ l, (tP l - hA X.B.I (X.bwd l) s) • X.bw l) +
        (∑ l, (tQ l - hA X.B.I (X.bw l) s) • X.bwd l) := by
    unfold repr0
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  rw [hexp]
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) (Z_smul_mL X (hneg' _ _ h3) hz)) ?_) ?_
  · exact Submodule.sum_mem _ fun a _ => Z_smul_mL X (hneg' _ _ (h1 a)) (he a)
  · exact Submodule.sum_mem _ fun a _ => Z_smul_mL X (hneg' _ _ (h2 a)) (hf a)
  · exact Submodule.sum_mem _ fun l _ => Z_smul_mL X (hneg' _ _ (h4 l)) (hb l)
  · exact Submodule.sum_mem _ fun l _ => Z_smul_mL X (hneg' _ _ (h5 l)) (hbd l)

theorem Z_of_sym {u w : VA X.B.I} {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (h : ZMod' X.B.I X.B.g (hA X.B.I w u - sigA X.B.I c)) : ZMod' X.B.I X.B.g (hA X.B.I u w - c) := by
  have hinv : ∀ t, sigA X.B.I (sigA X.B.I t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      first
        | simp [sigA, Formalism.UG.sigR, Formalism.BasicNotions.CMData.sig]
        | (show TensorProduct.tmul X.B.I.F (X.B.I.cm.sig (X.B.I.cm.sig a)) b = TensorProduct.tmul X.B.I.F a b
           rw [show X.B.I.cm.sig (X.B.I.cm.sig a) = a from star_star a])
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hincl : ∀ e : X.B.I.E, sigA X.B.I (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) e) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (star e) := by
    intro e
    first
      | rfl
      | simp [sigA, Formalism.UG.sigR, Formalism.UG.inclE, Formalism.BasicNotions.CMData.sig]
  have hsym : hA X.B.I u w = sigA X.B.I (hA X.B.I w u) := by
    simp only [hA, Formalism.UG.hform, map_sum, map_mul, hinv, Matrix.map_apply, hincl]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hJ : star (X.B.I.J i j) = X.B.I.J j i := by
      have e := congrFun (congrFun X.B.I.J_herm j) i
      simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at e
      exact e
    rw [hJ]
    ring
  have hInt : ∀ s ∈ IntAf X.B.I.F X.B.I.E, sigA X.B.I s ∈ IntAf X.B.I.F X.B.I.E := by
    have hle : IntAf X.B.I.F X.B.I.E ≤ (IntAf X.B.I.F X.B.I.E).comap (sigA X.B.I) := by
      show Subring.closure _ ≤ _
      rw [Subring.closure_le]
      rintro _ (⟨⟨x, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
      · rw [SetLike.mem_coe, Subring.mem_comap]
        refine Subring.subset_closure (Or.inl ⟨⟨_, RingOfIntegers.mapRingEquiv (starRingAut : RingAut X.B.I.E) a, rfl⟩, ?_⟩)
        first
          | rfl
          | simp [sigA, Formalism.UG.sigR, Formalism.BasicNotions.CMData.sig]
      · rw [SetLike.mem_coe, Subring.mem_comap]
        refine Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, ?_⟩)
        simp [sigA, Formalism.UG.sigR]
    exact fun s hs => hle hs
  obtain ⟨t, ht, e⟩ := h
  refine ⟨sigA X.B.I t, hInt t ht, ?_⟩
  have e' : hA X.B.I w u = sigA X.B.I c + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t := by
    rw [← e]
    ring
  rw [hsym, e', map_add, hinv, map_mul, map_natCast]
  ring

theorem Z0 {x : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (h : ZMod' X.B.I X.B.g x) : ZMod' X.B.I X.B.g (x - 0) := by
  rw [sub_zero]
  exact h

theorem hA_bw_bw (l m : Fin D.R.k) : hA X.B.I (X.bw l) (X.bw m) = 0 := by
  have hsl : ∀ (s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (x y : VA X.B.I),
      hA X.B.I (s • x) y = sigA X.B.I s * hA X.B.I x y := by
    intro s x y
    simp only [hA, sigA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsr : ∀ (s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (x y : VA X.B.I),
      hA X.B.I x (s • y) = s * hA X.B.I x y := by
    intro s x y
    simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [X.bw_w l, X.bw_w m, hsl, hsr, ← mul_assoc, mul_comm (sigA X.B.I X.ew) X.ew, X.ew_orth, zero_mul]

theorem hA_bwd_bwd (l m : Fin D.R.k) : hA X.B.I (X.bwd l) (X.bwd m) = 0 := by
  have hsl : ∀ (s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (x y : VA X.B.I),
      hA X.B.I (s • x) y = sigA X.B.I s * hA X.B.I x y := by
    intro s x y
    simp only [hA, sigA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsr : ∀ (s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (x y : VA X.B.I),
      hA X.B.I x (s • y) = s * hA X.B.I x y := by
    intro s x y
    simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hinv : ∀ t, sigA X.B.I (sigA X.B.I t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      first
        | simp [sigA, Formalism.UG.sigR, Formalism.BasicNotions.CMData.sig]
        | (show TensorProduct.tmul X.B.I.F (X.B.I.cm.sig (X.B.I.cm.sig a)) b = TensorProduct.tmul X.B.I.F a b
           rw [show X.B.I.cm.sig (X.B.I.cm.sig a) = a from star_star a])
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [X.bwd_w l, X.bwd_w m, hsl, hsr, hinv, ← mul_assoc, X.ew_orth, zero_mul]

theorem dual_coords {v : VA X.B.I} (hv : v ∈ X.B.I.Lf) : v - repr0 X v ∈ mL X.B.I X.B.g := by
  have hinv : ∀ t, sigA X.B.I (sigA X.B.I t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      first
        | simp [sigA, Formalism.UG.sigR, Formalism.BasicNotions.CMData.sig]
        | (show TensorProduct.tmul X.B.I.F (X.B.I.cm.sig (X.B.I.cm.sig a)) b = TensorProduct.tmul X.B.I.F a b
           rw [show X.B.I.cm.sig (X.B.I.cm.sig a) = a from star_star a])
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have zsym : ∀ u w : VA X.B.I, ZMod' X.B.I X.B.g (hA X.B.I w u) → ZMod' X.B.I X.B.g (hA X.B.I u w - 0) := by
    intro u w h
    apply Z_of_sym X
    rw [map_zero, sub_zero]
    exact h
  have zz : ZMod' X.B.I X.B.g ((0 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) - 0) := ⟨0, zero_mem _, by simp⟩
  have hmL : mL X.B.I X.B.g ≤ ReprSub X := by
    unfold mL
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    show _ - repr0 X _ ∈ mL X.B.I X.B.g
    rw [reference_repr_smul, ← smul_sub]
    unfold mL
    exact Submodule.subset_span ⟨x - repr0 X x, sub_mem hx (reference_repr_mem_lattice X hx), rfl⟩
  have hS : Set.range X.e0 ∪ Set.range X.f0 ∪ {X.z0} ∪ Set.range X.bw ∪ Set.range X.bwd ⊆ ReprSub X := by
    rintro _ ((((⟨a, rfl⟩ | ⟨a, rfl⟩) | rfl) | ⟨l, rfl⟩) | ⟨l, rfl⟩)
    · refine T_gen X (X.e0 a) (fun a' => if a' = a then 1 else 0) 0 0 0 0 ?_ ?_ ?_ ?_ ?_ ?_
      · simp [ite_smul]
      · intro a'
        apply Z_of_sym X
        have e : sigA X.B.I (if a' = a then 1 else 0) = if a = a' then 1 else 0 := by
          by_cases h : a = a'
          · subst h
            simp
          · simp [h, Ne.symm h]
        rw [e]
        exact (X.gramIntegral a a').2.2
      · exact fun a' => Z0 X (X.gramIntegral a' a).1
      · exact zsym _ _ ((X.formsAtZero.2 a).1)
      · exact fun l => zsym _ _ (((X.weightVectorsIntegral l).2.2 a).2.2.1)
      · exact fun l => zsym _ _ (((X.weightVectorsIntegral l).2.2 a).1)
    · refine T_gen X (X.f0 a) 0 (fun a' => if a' = a then 1 else 0) 0 0 0 ?_ ?_ ?_ ?_ ?_ ?_
      · simp [ite_smul]
      · exact fun a' => Z0 X (X.gramIntegral a' a).2.1
      · exact fun a' => (X.gramIntegral a' a).2.2
      · exact zsym _ _ ((X.formsAtZero.2 a).2)
      · exact fun l => zsym _ _ (((X.weightVectorsIntegral l).2.2 a).2.2.2)
      · exact fun l => zsym _ _ (((X.weightVectorsIntegral l).2.2 a).2.1)
    · refine T_gen X X.z0 0 0 (-1) 0 0 ?_ ?_ ?_ ?_ ?_ ?_
      · simp
      · exact fun a' => Z0 X ((X.formsAtZero.2 a').2)
      · exact fun a' => Z0 X ((X.formsAtZero.2 a').1)
      · rw [sub_neg_eq_add]
        exact X.formsAtZero.1
      · exact fun l => zsym _ _ ((X.weightVectorsIntegral l).2.1)
      · exact fun l => zsym _ _ ((X.weightVectorsIntegral l).1)
    · refine T_gen X (X.bw l) 0 0 0 (fun l' => if l' = l then X.ew else 0) 0 ?_ ?_ ?_ ?_ ?_ ?_
      · have hw := X.bw_w l
        simpa [ite_smul] using hw
      · exact fun a' => Z0 X (((X.weightVectorsIntegral l).2.2 a').2.1)
      · exact fun a' => Z0 X (((X.weightVectorsIntegral l).2.2 a').1)
      · exact Z0 X ((X.weightVectorsIntegral l).1)
      · exact fun l' => X.bw_dual l' l
      · intro l'
        rw [hA_bw_bw]
        exact zz
    · refine T_gen X (X.bwd l) 0 0 0 0 (fun l' => if l' = l then sigA X.B.I X.ew else 0) ?_ ?_ ?_ ?_ ?_ ?_
      · have hw := X.bwd_w l
        simpa [ite_smul] using hw
      · exact fun a' => Z0 X (((X.weightVectorsIntegral l).2.2 a').2.2.2)
      · exact fun a' => Z0 X (((X.weightVectorsIntegral l).2.2 a').2.2.1)
      · exact Z0 X ((X.weightVectorsIntegral l).2.1)
      · intro l'
        rw [hA_bwd_bwd]
        exact zz
      · intro l'
        apply Z_of_sym X
        have e : sigA X.B.I (if l' = l then sigA X.B.I X.ew else 0) = if l = l' then X.ew else 0 := by
          by_cases h : l = l'
          · subst h
            simp [hinv]
          · simp [h, Ne.symm h]
        rw [e]
        exact X.bw_dual l l'
  have hle : Submodule.span (IntAf X.B.I.F X.B.I.E)
      (Set.range X.e0 ∪ Set.range X.f0 ∪ {X.z0} ∪ Set.range X.bw ∪ Set.range X.bwd) ⊔ mL X.B.I X.B.g ≤ ReprSub X :=
    sup_le (Submodule.span_le.2 hS) hmL
  exact hle (X.latticeSpan v hv)

end Dual

end Formalism.L2.SG.NormCut
