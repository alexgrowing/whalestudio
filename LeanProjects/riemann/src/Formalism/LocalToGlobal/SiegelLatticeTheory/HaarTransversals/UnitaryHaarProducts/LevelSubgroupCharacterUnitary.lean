import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting

noncomputable section

namespace Formalism.L2.SG.Pf.unitaryCongruence

open MeasureTheory NumberField Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped TensorProduct

section Gen

variable (I : AutInst)

theorem fmat_mul (x y : I.Gf) : I.fmat (x * y) = I.fmat x * I.fmat y := rfl
theorem fmat_one : I.fmat 1 = 1 := rfl
theorem fmat_inv_mul (x : I.Gf) : I.fmat x⁻¹ * I.fmat x = 1 := by
  rw [← fmat_mul, inv_mul_cancel, fmat_one]

theorem K_one : (1 : I.Gf) ∈ I.Kset := by
  exact (Formalism.UG.stabGL I.Lf).one_mem
theorem K_inv {x : I.Gf} (hx : x ∈ I.Kset) : x⁻¹ ∈ I.Kset := by
  exact (Formalism.UG.stabGL I.Lf).inv_mem hx
theorem K_mv {x : I.Gf} (hx : x ∈ I.Kset) {y : VA I} (hy : y ∈ I.Lf) : I.fmat x *ᵥ y ∈ I.Lf := by
  have h : ∀ z, z ∈ I.Lf ↔ I.fmat x *ᵥ z ∈ I.Lf := hx
  exact (h y).1 hy
theorem K_sub_mv {x : I.Gf} (hx : x ∈ I.Kset) {y : VA I} (hy : y ∈ I.Lf) :
    (I.fmat x - 1) *ᵥ y ∈ I.Lf := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  exact I.Lf.sub_mem (K_mv I hx hy) hy

def mvO (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) : VA I →ₗ[IntAf I.F I.E] VA I where
  toFun v := M *ᵥ v
  map_add' := Matrix.mulVec_add M
  map_smul' c v := by
    show M *ᵥ ((c : I.E ⊗[I.F] Af I.F) • v) = (c : I.E ⊗[I.F] Af I.F) • (M *ᵥ v)
    exact Matrix.mulVec_smul M _ v

def Mo (g : ℕ) (S : Set (VA I)) : Submodule (IntAf I.F I.E) (VA I) :=
  Submodule.span (IntAf I.F I.E) S ⊔ mL I g

theorem smul_mem_mL {g : ℕ} {y : VA I} (hy : y ∈ I.Lf) :
    ((g : I.E ⊗[I.F] Af I.F) • y) ∈ mL I g := by
  unfold mL
  exact Submodule.subset_span ⟨y, hy, rfl⟩

theorem Mo_mono {g : ℕ} {S T : Set (VA I)} (h : S ⊆ T) : Mo I g S ≤ Mo I g T := by
  exact sup_le_sup_right (Submodule.span_mono h) _
theorem sub_Mo {g : ℕ} {S : Set (VA I)} : S ⊆ Mo I g S := by
  intro s hs
  exact Submodule.mem_sup_left (Submodule.subset_span hs)
theorem mL_Mo {g : ℕ} {S : Set (VA I)} : mL I g ≤ Mo I g S := by
  exact le_sup_right

theorem mv_mem (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (g : ℕ) (S : Set (VA I))
    (N : Submodule (IntAf I.F I.E) (VA I)) (hS : ∀ s ∈ S, M *ᵥ s ∈ N)
    (hm : ∀ y ∈ I.Lf, M *ᵥ ((g : I.E ⊗[I.F] Af I.F) • y) ∈ N) :
    ∀ v ∈ Mo I g S, M *ᵥ v ∈ N := by
  intro v hv
  have h : Mo I g S ≤ N.comap (mvO I M) := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      intro s hs
      exact hS s hs
    · unfold mL
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      exact hm y hy
  exact h hv

theorem mL_mv {M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hM : ∀ y ∈ I.Lf, M *ᵥ y ∈ I.Lf)
    (g : ℕ) {N : Submodule (IntAf I.F I.E) (VA I)} (hN : mL I g ≤ N) :
    ∀ y ∈ I.Lf, M *ᵥ ((g : I.E ⊗[I.F] Af I.F) • y) ∈ N := by
  intro y hy
  rw [Matrix.mulVec_smul]
  exact hN (smul_mem_mL I (hM y hy))

theorem pres {x : I.Gf} (hx : x ∈ I.Kset) (g : ℕ) (S : Set (VA I)) (N : Submodule (IntAf I.F I.E) (VA I))
    (hSN : S ⊆ N) (hS : ∀ s ∈ S, (I.fmat x - 1) *ᵥ s ∈ N) (hN : mL I g ≤ N) :
    ∀ v ∈ Mo I g S, I.fmat x *ᵥ v ∈ N := by
  refine mv_mem I (I.fmat x) g S N (fun s hs => ?_) (mL_mv I (fun y hy => K_mv I hx hy) g hN)
  have e : I.fmat x *ᵥ s = (I.fmat x - 1) *ᵥ s + s := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  rw [e]
  exact N.add_mem (hS s hs) (hSN hs)

theorem pres1 {x : I.Gf} (hx : x ∈ I.Kset) (g : ℕ) (S : Set (VA I)) (N : Submodule (IntAf I.F I.E) (VA I))
    (hS : ∀ s ∈ S, (I.fmat x - 1) *ᵥ s ∈ N) (hN : mL I g ≤ N) :
    ∀ v ∈ Mo I g S, (I.fmat x - 1) *ᵥ v ∈ N := by
  exact mv_mem I (I.fmat x - 1) g S N hS (mL_mv I (fun y hy => K_sub_mv I hx hy) g hN)

theorem mul_id (x y : I.Gf) (v : VA I) :
    (I.fmat (x * y) - 1) *ᵥ v = I.fmat x *ᵥ ((I.fmat y - 1) *ᵥ v) + (I.fmat x - 1) *ᵥ v := by
  simp only [fmat_mul, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
  abel

theorem inv_id (x : I.Gf) (v : VA I) :
    (I.fmat x⁻¹ - 1) *ᵥ v = -(I.fmat x⁻¹ *ᵥ ((I.fmat x - 1) *ᵥ v)) := by
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, fmat_inv_mul I x]
  abel

theorem fmat_mul_identity (x y : I.Gf) (v : VA I) :
    I.fmat (x * y) *ᵥ v = (I.fmat x - 1) *ᵥ ((I.fmat y - 1) *ᵥ v) + I.fmat x *ᵥ v + I.fmat y *ᵥ v - v := by
  have h1 : (I.fmat x - 1) *ᵥ ((I.fmat y - 1) *ᵥ v) =
      I.fmat x *ᵥ (I.fmat y *ᵥ v) - I.fmat x *ᵥ v - I.fmat y *ᵥ v + v := by
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
    abel
  rw [h1, fmat_mul, ← Matrix.mulVec_mulVec]
  abel

theorem sigA_tmul (a : I.E) (b : Af I.F) : sigA I (a ⊗ₜ[I.F] b) = star a ⊗ₜ[I.F] b := by
  show (Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F))) (a ⊗ₜ[I.F] b) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem sigA_sigA (a : I.E ⊗[I.F] Af I.F) : sigA I (sigA I a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x y => rw [sigA_tmul, sigA_tmul, star_star]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sigA_inclE (a : I.E) : sigA I (Formalism.UG.inclE (F := I.F) (Af I.F) a) =
    Formalism.UG.inclE (F := I.F) (Af I.F) (star a) := by
  exact sigA_tmul I a 1

theorem star_intOE {a : I.E} (ha : a ∈ Formalism.UG.intOE I.E) : star a ∈ Formalism.UG.intOE I.E := by
  obtain ⟨o, rfl⟩ := ha
  exact ⟨⟨star (o : I.E), (NumberField.RingOfIntegers.isIntegral_coe o).map (starRingEnd I.E).toIntAlgHom⟩, rfl⟩

theorem sigA_mem {a : I.E ⊗[I.F] Af I.F} (ha : a ∈ IntAf I.F I.E) : sigA I a ∈ IntAf I.F I.E := by
  have hsub : (Set.range (fun x : Formalism.UG.intOE I.E => (x : I.E) ⊗ₜ[I.F] (1 : Af I.F)) ∪
      Set.range (fun y : Formalism.UG.intAd I.F => (1 : I.E) ⊗ₜ[I.F] (y : Af I.F))) ⊆
      ((IntAf I.F I.E).comap (sigA I) : Set (I.E ⊗[I.F] Af I.F)) := by
    rintro _ (⟨x, rfl⟩ | ⟨y, rfl⟩)
    · show sigA I _ ∈ IntAf I.F I.E
      rw [sigA_tmul]
      exact Subring.subset_closure (Or.inl ⟨⟨star (x : I.E), star_intOE I x.2⟩, rfl⟩)
    · show sigA I _ ∈ IntAf I.F I.E
      rw [sigA_tmul, star_one]
      exact Subring.subset_closure (Or.inr ⟨y, rfl⟩)
  exact Subring.closure_le.2 hsub ha

theorem inclE_mem {a : I.E} (ha : a ∈ Formalism.UG.intOE I.E) :
    Formalism.UG.inclE (F := I.F) (Af I.F) a ∈ IntAf I.F I.E := by
  exact Subring.subset_closure (Or.inl ⟨⟨a, ha⟩, rfl⟩)

theorem hA_add_right (u v w : VA I) : hA I u (v + w) = hA I u v + hA I u w := by
  simp only [hA, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hA_smul_right (u v : VA I) (c : I.E ⊗[I.F] Af I.F) : hA I u (c • v) = c * hA I u v := by
  simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hA_add_left (u u' v : VA I) : hA I (u + u') v = hA I u v + hA I u' v := by
  simp only [hA, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hA_smul_left (u v : VA I) (c : I.E ⊗[I.F] Af I.F) : hA I (c • u) v = sigA I c * hA I u v := by
  simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def hL (u : VA I) : VA I →ₗ[I.E ⊗[I.F] Af I.F] (I.E ⊗[I.F] Af I.F) where
  toFun := hA I u
  map_add' := hA_add_right I u
  map_smul' c v := hA_smul_right I u v c

theorem hL_apply (u v : VA I) : hL I u v = hA I u v := rfl

theorem hA_incl (x y : Fin I.n → I.E) : hA I (incl I x) (incl I y) =
    Formalism.UG.inclE (F := I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by
  have key : ∀ a : I.E, Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) a) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (star a) := sigA_inclE I
  simp only [hA, Formalism.UG.hform, incl, Matrix.map_apply, map_sum, map_mul, key, starRingEnd_apply]

theorem J_conj (i j : Fin I.n) : star (I.J i j) = I.J j i := by
  have hh : Formalism.UG.cT (starRingEnd I.E) I.J = I.J := I.J_herm
  have h := congrFun (congrFun hh j) i
  simpa [Formalism.UG.cT, starRingEnd_apply] using h

theorem hA_symm (u v : VA I) : hA I v u = sigA I (hA I u v) := by
  have hs : ∀ a, Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.sigR I.cm.sig (Af I.F) a) = a := sigA_sigA I
  have hJ : ∀ i j, Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) (I.J i j)) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (I.J j i) := by
    intro i j
    rw [← J_conj I i j]
    exact sigA_inclE I _
  simp only [hA, Formalism.UG.hform, map_sum, map_mul, Matrix.map_apply, hs, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hA_int {u v : VA I} (hu : u ∈ I.Lf) (hv : v ∈ I.Lf) : hA I u v ∈ IntAf I.F I.E := by
  have hz : ∀ w : VA I, hA I w 0 = 0 := by
    intro w
    simp only [hA, Formalism.UG.hform, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  have hz' : ∀ w : VA I, hA I 0 w = 0 := by
    intro w
    simp only [hA, Formalism.UG.hform, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]
  have hgen : ∀ x ∈ I.L, ∀ w ∈ I.Lf, hA I (incl I x) w ∈ IntAf I.F I.E := by
    intro x hx w hw
    have hw2 : w ∈ Submodule.span (IntAf I.F I.E)
        (Set.range fun y : I.L => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((y : Fin I.n → I.E) i)) := hw
    clear hw
    induction hw2 using Submodule.span_induction with
    | mem w hw' =>
      obtain ⟨⟨y, hy⟩, rfl⟩ := hw'
      show hA I (incl I x) (incl I y) ∈ _
      rw [hA_incl]
      exact inclE_mem I ((I.L_dual y).1 hy x hx)
    | zero => rw [hz]; exact (IntAf I.F I.E).zero_mem
    | add a b _ _ ha hb => rw [hA_add_right]; exact add_mem ha hb
    | smul c w _ hw' =>
      show hA I _ ((c : I.E ⊗[I.F] Af I.F) • w) ∈ _
      rw [hA_smul_right]
      exact mul_mem c.2 hw'
  have hu2 : u ∈ Submodule.span (IntAf I.F I.E)
      (Set.range fun y : I.L => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((y : Fin I.n → I.E) i)) := hu
  clear hu
  induction hu2 using Submodule.span_induction with
  | mem w hw' =>
    obtain ⟨⟨y, hy⟩, rfl⟩ := hw'
    exact hgen y hy v hv
  | zero => rw [hz']; exact (IntAf I.F I.E).zero_mem
  | add a b _ _ ha hb => rw [hA_add_left]; exact add_mem ha hb
  | smul c w _ hw' =>
    show hA I ((c : I.E ⊗[I.F] Af I.F) • w) _ ∈ _
    rw [hA_smul_left]
    exact mul_mem (sigA_mem I c.2) hw'

theorem hA_sub_right (u v w : VA I) : hA I u (v - w) = hA I u v - hA I u w := by
  simp only [hA, Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

end Gen

section Cong

theorem lt_sub {r : ℕ} {p q : ℕ} (h : p ≤ q) : {c : Fin r | c.1 < p} ⊆ {c | c.1 < q} := by
  intro c hc
  exact lt_of_lt_of_le hc h

variable (I : AutInst) (g : ℕ) {r k : ℕ} (e0 : Fin r → VA I) (z0 : VA I) (bw : Fin k → VA I)

theorem SE {x : I.Gf} (hx : x ∈ I.Kset)
    (hc : ∀ a : Fin r, (I.fmat x - 1) *ᵥ e0 a ∈ Mo I g (e0 '' {b | b.1 < a.1})) (m : ℕ) :
    ∀ v ∈ Mo I g (e0 '' {b | b.1 < m}), I.fmat x *ᵥ v ∈ Mo I g (e0 '' {b | b.1 < m}) := by
  refine pres I hx g _ _ (sub_Mo I) ?_ (mL_Mo I)
  rintro _ ⟨b, hb, rfl⟩
  exact Mo_mono I (Set.image_mono (lt_sub hb.le)) (hc b)

theorem SR {x : I.Gf} (hx : x ∈ I.Kset)
    (hc : ∀ a : Fin r, (I.fmat x - 1) *ᵥ e0 a ∈ Mo I g (e0 '' {b | b.1 < a.1})) :
    ∀ v ∈ Mo I g (Set.range e0), I.fmat x *ᵥ v ∈ Mo I g (Set.range e0) := by
  refine pres I hx g _ _ (sub_Mo I) ?_ (mL_Mo I)
  rintro _ ⟨a, rfl⟩
  exact Mo_mono I (Set.image_subset_range _ _) (hc a)

theorem SB {x : I.Gf} (hx : x ∈ I.Kset)
    (hc1 : ∀ a : Fin r, (I.fmat x - 1) *ᵥ e0 a ∈ Mo I g (e0 '' {b | b.1 < a.1}))
    (hc3 : ∀ i : Fin k, (I.fmat x - 1) *ᵥ bw i ∈ Mo I g (Set.range e0 ∪ bw '' {j | j.1 < i.1})) (m : ℕ) :
    ∀ v ∈ Mo I g (Set.range e0 ∪ bw '' {j | j.1 < m}),
      I.fmat x *ᵥ v ∈ Mo I g (Set.range e0 ∪ bw '' {j | j.1 < m}) := by
  refine pres I hx g _ _ (sub_Mo I) ?_ (mL_Mo I)
  rintro _ (⟨a, rfl⟩ | ⟨j, hj, rfl⟩)
  · exact Mo_mono I ((Set.image_subset_range _ _).trans Set.subset_union_left) (hc1 a)
  · exact Mo_mono I (Set.union_subset_union_right _ (Set.image_mono (lt_sub hj.le))) (hc3 j)

theorem cong_mul {x y : I.Gf} (hx : x ∈ I.Kset) (hcx : K2cong I g e0 z0 bw x)
    (hcy : K2cong I g e0 z0 bw y) : K2cong I g e0 z0 bw (x * y) := by
  unfold K2cong at hcx hcy ⊢
  obtain ⟨hx1, hx2, hx3⟩ := hcx
  obtain ⟨hy1, hy2, hy3⟩ := hcy
  refine ⟨fun a => ?_, ?_, fun i => ?_⟩
  · show _ ∈ Mo I g _
    rw [mul_id]
    exact add_mem (SE I g e0 hx hx1 a.1 _ (hy1 a)) (hx1 a)
  · show _ ∈ Mo I g _
    rw [mul_id]
    exact add_mem (SR I g e0 hx hx1 _ hy2) hx2
  · show _ ∈ Mo I g _
    rw [mul_id]
    exact add_mem (SB I g e0 bw hx hx1 hx3 i.1 _ (hy3 i)) (hx3 i)

theorem inv_e {x : I.Gf} (hx : x ∈ I.Kset)
    (hc : ∀ a : Fin r, (I.fmat x - 1) *ᵥ e0 a ∈ Mo I g (e0 '' {b | b.1 < a.1})) :
    ∀ a : Fin r, (I.fmat x⁻¹ - 1) *ᵥ e0 a ∈ Mo I g (e0 '' {b | b.1 < a.1}) := by
  have hxi : x⁻¹ ∈ I.Kset := K_inv I hx
  have key : ∀ m : ℕ, ∀ v ∈ Mo I g (e0 '' {b | b.1 < m}),
      I.fmat x⁻¹ *ᵥ v ∈ Mo I g (e0 '' {b | b.1 < m}) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      refine mv_mem I _ g _ _ ?_ (mL_mv I (fun y hy => K_mv I hxi hy) g (mL_Mo I))
      rintro _ ⟨b, hb, rfl⟩
      have h1 : I.fmat x⁻¹ *ᵥ e0 b = e0 b + (I.fmat x⁻¹ - 1) *ᵥ e0 b := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        abel
      rw [h1, inv_id]
      refine add_mem (sub_Mo I (Set.mem_image_of_mem e0 hb)) (neg_mem ?_)
      exact Mo_mono I (Set.image_mono (lt_sub hb.le)) (ih b.1 hb _ (hc b))
  intro a
  rw [inv_id]
  exact neg_mem (key a.1 _ (hc a))

theorem inv_b {x : I.Gf} (hx : x ∈ I.Kset)
    (hc1 : ∀ a : Fin r, (I.fmat x - 1) *ᵥ e0 a ∈ Mo I g (e0 '' {b | b.1 < a.1}))
    (hc3 : ∀ i : Fin k, (I.fmat x - 1) *ᵥ bw i ∈ Mo I g (Set.range e0 ∪ bw '' {j | j.1 < i.1})) :
    ∀ i : Fin k, (I.fmat x⁻¹ - 1) *ᵥ bw i ∈ Mo I g (Set.range e0 ∪ bw '' {j | j.1 < i.1}) := by
  have hxi : x⁻¹ ∈ I.Kset := K_inv I hx
  have he := inv_e I g e0 hx hc1
  have key : ∀ m : ℕ, ∀ v ∈ Mo I g (Set.range e0 ∪ bw '' {j | j.1 < m}),
      I.fmat x⁻¹ *ᵥ v ∈ Mo I g (Set.range e0 ∪ bw '' {j | j.1 < m}) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      refine mv_mem I _ g _ _ ?_ (mL_mv I (fun y hy => K_mv I hxi hy) g (mL_Mo I))
      have hsplit : ∀ w : VA I, I.fmat x⁻¹ *ᵥ w = w + (I.fmat x⁻¹ - 1) *ᵥ w := by
        intro w
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        abel
      rintro _ (⟨a, rfl⟩ | ⟨j, hj, rfl⟩)
      · rw [hsplit]
        exact add_mem (sub_Mo I (Or.inl ⟨a, rfl⟩))
          (Mo_mono I ((Set.image_subset_range _ _).trans Set.subset_union_left) (he a))
      · rw [hsplit, inv_id]
        refine add_mem (sub_Mo I (Or.inr ⟨j, hj, rfl⟩)) (neg_mem ?_)
        exact Mo_mono I (Set.union_subset_union_right _ (Set.image_mono (lt_sub hj.le)))
          (ih j.1 hj _ (hc3 j))
  intro i
  rw [inv_id]
  exact neg_mem (key i.1 _ (hc3 i))

theorem cong_inv {x : I.Gf} (hx : x ∈ I.Kset) (hcx : K2cong I g e0 z0 bw x) :
    K2cong I g e0 z0 bw x⁻¹ := by
  unfold K2cong at hcx ⊢
  obtain ⟨h1, h2, h3⟩ := hcx
  refine ⟨inv_e I g e0 hx h1, ?_, inv_b I g e0 bw hx h1 h3⟩
  show _ ∈ Mo I g _
  rw [inv_id]
  exact neg_mem (SR I g e0 (K_inv I hx) (inv_e I g e0 hx h1) _ h2)

theorem cong_one : K2cong I g e0 z0 bw 1 := by
  unfold K2cong
  refine ⟨fun a => ?_, ?_, fun i => ?_⟩ <;>
  · show _ ∈ Mo I g _
    rw [fmat_one, sub_self, Matrix.zero_mulVec]
    exact zero_mem _

theorem K_mul {x y : I.Gf} (hx : x ∈ I.Kset) (hy : y ∈ I.Kset) : x * y ∈ I.Kset := by
  exact (Formalism.UG.stabGL I.Lf).mul_mem hx hy

end Cong

section Chi

variable (I : AutInst) (g : ℕ)

theorem Z_zero : ZMod' I g 0 := by
  unfold ZMod'
  exact ⟨0, (IntAf I.F I.E).zero_mem, by rw [mul_zero]⟩
theorem Z_add {a b : I.E ⊗[I.F] Af I.F} (ha : ZMod' I g a) (hb : ZMod' I g b) : ZMod' I g (a + b) := by
  unfold ZMod' at *
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  exact ⟨s + t, add_mem hs ht, by rw [mul_add]⟩
theorem Z_sub {a b : I.E ⊗[I.F] Af I.F} (ha : ZMod' I g a) (hb : ZMod' I g b) : ZMod' I g (a - b) := by
  unfold ZMod' at *
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  exact ⟨s - t, sub_mem hs ht, by rw [mul_sub]⟩
theorem Z_sum {ι : Type*} (s : Finset ι) (f : ι → I.E ⊗[I.F] Af I.F) (h : ∀ i ∈ s, ZMod' I g (f i)) :
    ZMod' I g (∑ i ∈ s, f i) := by
  exact Finset.sum_induction f (ZMod' I g) (fun a b ha hb => Z_add I g ha hb) (Z_zero I g) h
theorem Z_smul {c a : I.E ⊗[I.F] Af I.F} (hc : c ∈ IntAf I.F I.E) (ha : ZMod' I g a) : ZMod' I g (c * a) := by
  unfold ZMod' at *
  obtain ⟨t, ht, rfl⟩ := ha
  exact ⟨c * t, mul_mem hc ht, by ring⟩
theorem Z_sig {a : I.E ⊗[I.F] Af I.F} (ha : ZMod' I g a) : ZMod' I g (sigA I a) := by
  unfold ZMod' at *
  obtain ⟨t, ht, rfl⟩ := ha
  exact ⟨sigA I t, sigA_mem I ht, by rw [map_mul, map_natCast]⟩

def Qs (f : VA I) : Submodule (IntAf I.F I.E) (VA I) where
  carrier := {v | ZMod' I g (hA I f v)}
  add_mem' {v w} hv hw := by
    show ZMod' I g (hA I f (v + w)); rw [hA_add_right]; exact Z_add I g hv hw
  zero_mem' := by
    show ZMod' I g (hL I f 0); rw [map_zero]; exact Z_zero I g
  smul_mem' c v hv := by
    show ZMod' I g (hA I f ((c : I.E ⊗[I.F] Af I.F) • v)); rw [hA_smul_right]; exact Z_smul I g c.2 hv

theorem mL_Qs {f : VA I} (hf : f ∈ I.Lf) : mL I g ≤ Qs I g f := by
  unfold mL
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  show ZMod' I g (hA I f ((g : I.E ⊗[I.F] Af I.F) • x))
  rw [hA_smul_right]
  unfold ZMod'
  exact ⟨hA I f x, hA_int I hf hx, rfl⟩

theorem divN_add (a b : I.E ⊗[I.F] Af I.F) : divN I g (a + b) = divN I g a + divN I g b := by
  simp only [divN, mul_add]

theorem inv_g (hg : g ≠ 0) :
    algebraMap I.F (I.E ⊗[I.F] Af I.F) ((g : I.F)⁻¹) * (g : I.E ⊗[I.F] Af I.F) = 1 := by
  rw [← map_natCast (algebraMap I.F (I.E ⊗[I.F] Af I.F)) g, ← map_mul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 hg), map_one]

theorem divN_gmul (hg : g ≠ 0) (t : I.E ⊗[I.F] Af I.F) : divN I g ((g : I.E ⊗[I.F] Af I.F) * t) = t := by
  unfold divN
  rw [← mul_assoc, inv_g I g hg, one_mul]

theorem gmul_divN (hg : g ≠ 0) (c : I.E ⊗[I.F] Af I.F) : (g : I.E ⊗[I.F] Af I.F) * divN I g c = c := by
  unfold divN
  rw [← mul_assoc, mul_comm (g : I.E ⊗[I.F] Af I.F), inv_g I g hg, one_mul]

variable {ψ : I.E ⊗[I.F] Af I.F → ℂ} (hadd : ∀ x y, ψ (x + y) = ψ x * ψ y)
  (hint : ∀ x ∈ IntAf I.F I.E, ψ x = 1)
include hadd hint

theorem psi_Z (hg : g ≠ 0) {c : I.E ⊗[I.F] Af I.F} (hc : ZMod' I g c) : ψ (divN I g c) = 1 := by
  unfold ZMod' at hc
  obtain ⟨t, ht, rfl⟩ := hc
  rw [divN_gmul I g hg]
  exact hint t ht

theorem psi_mul_of_Z (hg : g ≠ 0) {a b c : I.E ⊗[I.F] Af I.F} (h : ZMod' I g (c - a - b)) :
    ψ (divN I g c) = ψ (divN I g a) * ψ (divN I g b) := by
  have e : divN I g c = divN I g (c - a - b) + divN I g a + divN I g b := by
    rw [← divN_add, ← divN_add]
    congr 1
    abel
  rw [e, hadd, hadd, psi_Z I g hadd hint hg h, one_mul]

theorem psi_pow (n : ℕ) (a : I.E ⊗[I.F] Af I.F) : ψ ((n : I.E ⊗[I.F] Af I.F) * a) = ψ a ^ n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_mul, pow_zero]
    exact hint 0 (IntAf I.F I.E).zero_mem
  | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, hadd, ih, pow_succ]

theorem psi_norm (hg : g ≠ 0) {c : I.E ⊗[I.F] Af I.F} (hc : c ∈ IntAf I.F I.E) : ‖ψ (divN I g c)‖ = 1 := by
  have h : ψ (divN I g c) ^ g = 1 := by
    rw [← psi_pow I hadd hint g, gmul_divN I g hg]
    exact hint c hc
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hg).1 (by rw [← norm_pow, h, norm_one])

end Chi

section Frame

variable (I : AutInst) (g : ℕ) {r k : ℕ} (e0 f0 : Fin r → VA I) (z0 : VA I) (bw bwd : Fin k → VA I)

def Afun (x : I.Gf) : I.E ⊗[I.F] Af I.F :=
  (∑ a, hA I (f0 a) (I.fmat x *ᵥ nxt e0 z0 a)) +
    ∑ i : Fin k, if h : i.1 + 1 < k then hA I (bwd i) (I.fmat x *ᵥ bw ⟨i.1 + 1, h⟩) else 0

theorem flagLevelCharacter_eq_psi_divN (ψ : I.E ⊗[I.F] Af I.F → ℂ) (x : I.Gf) :
    chi2f I ψ g e0 f0 z0 bw bwd x = ψ (divN I g (Afun I e0 f0 z0 bw bwd x)) := rfl

theorem term_Z {x y : I.Gf} (f n : VA I) (hn : ZMod' I g (hA I f n))
    (hq : (I.fmat x - 1) *ᵥ ((I.fmat y - 1) *ᵥ n) ∈ Qs I g f) :
    ZMod' I g (hA I f (I.fmat (x * y) *ᵥ n) - hA I f (I.fmat x *ᵥ n) - hA I f (I.fmat y *ᵥ n)) := by
  rw [fmat_mul_identity, hA_sub_right, hA_add_right, hA_add_right]
  have e : hA I f ((I.fmat x - 1) *ᵥ ((I.fmat y - 1) *ᵥ n)) + hA I f (I.fmat x *ᵥ n) +
      hA I f (I.fmat y *ᵥ n) - hA I f n - hA I f (I.fmat x *ᵥ n) - hA I f (I.fmat y *ᵥ n) =
      hA I f ((I.fmat x - 1) *ᵥ ((I.fmat y - 1) *ᵥ n)) - hA I f n := by
    abel
  rw [e]
  exact Z_sub I g hq hn

theorem congruence_fixed_term {x : I.Gf} (f n : VA I) (hn : ZMod' I g (hA I f n))
    (hq : (I.fmat x - 1) *ᵥ n ∈ Qs I g f) : ZMod' I g (hA I f (I.fmat x *ᵥ n)) := by
  have e : I.fmat x *ᵥ n = (I.fmat x - 1) *ᵥ n + n := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  rw [e, hA_add_right]
  exact Z_add I g hq hn

theorem Me_Q (hf0 : ∀ a, f0 a ∈ I.Lf) (hfe : ∀ a b : Fin r, a ≠ b → ZMod' I g (hA I (f0 a) (e0 b)))
    (a : Fin r) : Mo I g (e0 '' {b | b.1 < a.1}) ≤ Qs I g (f0 a) := by
  unfold Mo
  refine sup_le ?_ (mL_Qs I g (hf0 a))
  rw [Submodule.span_le]
  rintro _ ⟨b, hb, rfl⟩
  exact hfe a b (ne_of_gt (show b < a from hb))

theorem Mb_Q (hbwd : ∀ i, bwd i ∈ I.Lf) (hbe : ∀ i a, ZMod' I g (hA I (bwd i) (e0 a)))
    (hbb : ∀ i j : Fin k, i ≠ j → ZMod' I g (hA I (bwd i) (bw j))) (i : Fin k) :
    Mo I g (Set.range e0 ∪ bw '' {j | j.1 < i.1}) ≤ Qs I g (bwd i) := by
  unfold Mo
  refine sup_le ?_ (mL_Qs I g (hbwd i))
  rw [Submodule.span_le]
  rintro _ (⟨a, rfl⟩ | ⟨j, hj, rfl⟩)
  · exact hbe i a
  · exact hbb i j (ne_of_gt (show j < i from hj))

theorem nxt_Z (hfe : ∀ a b : Fin r, a ≠ b → ZMod' I g (hA I (f0 a) (e0 b)))
    (hfz : ∀ a, ZMod' I g (hA I (f0 a) z0)) (a : Fin r) : ZMod' I g (hA I (f0 a) (nxt e0 z0 a)) := by
  unfold nxt
  split_ifs with h
  · refine hfe a _ (fun e => ?_)
    have := congrArg Fin.val e
    simp at this
  · exact hfz a

theorem nxt_mem (he0 : ∀ a, e0 a ∈ I.Lf) (hz0 : z0 ∈ I.Lf) (a : Fin r) : nxt e0 z0 a ∈ I.Lf := by
  unfold nxt
  split_ifs
  · exact he0 _
  · exact hz0

theorem nxt_cong {y : I.Gf} (hcy : K2cong I g e0 z0 bw y) (a : Fin r) :
    (I.fmat y - 1) *ᵥ nxt e0 z0 a ∈ Mo I g (e0 '' {b | b.1 < a.1 + 1}) := by
  unfold K2cong at hcy
  obtain ⟨h1, h2, -⟩ := hcy
  unfold nxt
  split_ifs with h
  · exact h1 ⟨a.1 + 1, h⟩
  · refine Mo_mono I ?_ h2
    rintro _ ⟨b, rfl⟩
    exact ⟨b, lt_of_lt_of_le b.2 (not_lt.1 h), rfl⟩

theorem e_step {x : I.Gf} (hx : x ∈ I.Kset) (hcx : K2cong I g e0 z0 bw x) (a : Fin r) :
    ∀ v ∈ Mo I g (e0 '' {b | b.1 < a.1 + 1}),
      (I.fmat x - 1) *ᵥ v ∈ Mo I g (e0 '' {b | b.1 < a.1}) := by
  unfold K2cong at hcx
  refine pres1 I hx g _ _ ?_ (mL_Mo I)
  rintro _ ⟨b, hb, rfl⟩
  exact Mo_mono I (Set.image_mono (lt_sub (Nat.lt_succ_iff.1 hb))) (hcx.1 b)

theorem b_step {x : I.Gf} (hx : x ∈ I.Kset) (hcx : K2cong I g e0 z0 bw x) (i : Fin k) :
    ∀ v ∈ Mo I g (Set.range e0 ∪ bw '' {j | j.1 < i.1 + 1}),
      (I.fmat x - 1) *ᵥ v ∈ Mo I g (Set.range e0 ∪ bw '' {j | j.1 < i.1}) := by
  unfold K2cong at hcx
  obtain ⟨h1, -, h3⟩ := hcx
  refine pres1 I hx g _ _ ?_ (mL_Mo I)
  rintro _ (⟨a, rfl⟩ | ⟨j, hj, rfl⟩)
  · exact Mo_mono I ((Set.image_subset_range _ _).trans Set.subset_union_left) (h1 a)
  · exact Mo_mono I (Set.union_subset_union_right _ (Set.image_mono (lt_sub (Nat.lt_succ_iff.1 hj))))
      (h3 j)

theorem Afun_mul {x y : I.Gf} (hx : x ∈ I.Kset) (hcx : K2cong I g e0 z0 bw x)
    (hcy : K2cong I g e0 z0 bw y)
    (hf0 : ∀ a, f0 a ∈ I.Lf) (hbwd : ∀ i, bwd i ∈ I.Lf)
    (hfe : ∀ a b : Fin r, a ≠ b → ZMod' I g (hA I (f0 a) (e0 b)))
    (hfz : ∀ a, ZMod' I g (hA I (f0 a) z0))
    (hbe : ∀ i a, ZMod' I g (hA I (bwd i) (e0 a)))
    (hbb : ∀ i j : Fin k, i ≠ j → ZMod' I g (hA I (bwd i) (bw j))) :
    ZMod' I g (Afun I e0 f0 z0 bw bwd (x * y) - Afun I e0 f0 z0 bw bwd x - Afun I e0 f0 z0 bw bwd y) := by
  have h : Afun I e0 f0 z0 bw bwd (x * y) - Afun I e0 f0 z0 bw bwd x - Afun I e0 f0 z0 bw bwd y =
      (∑ a, (hA I (f0 a) (I.fmat (x * y) *ᵥ nxt e0 z0 a) - hA I (f0 a) (I.fmat x *ᵥ nxt e0 z0 a) -
        hA I (f0 a) (I.fmat y *ᵥ nxt e0 z0 a))) +
      ∑ i : Fin k, ((if h : i.1 + 1 < k then hA I (bwd i) (I.fmat (x * y) *ᵥ bw ⟨i.1 + 1, h⟩) else 0) -
        (if h : i.1 + 1 < k then hA I (bwd i) (I.fmat x *ᵥ bw ⟨i.1 + 1, h⟩) else 0) -
        (if h : i.1 + 1 < k then hA I (bwd i) (I.fmat y *ᵥ bw ⟨i.1 + 1, h⟩) else 0)) := by
    simp only [Afun, Finset.sum_sub_distrib]; ring
  rw [h]
  refine Z_add I g (Z_sum I g _ _ fun a _ => ?_) (Z_sum I g _ _ fun i _ => ?_)
  · exact term_Z I g _ _ (nxt_Z I g e0 f0 z0 hfe hfz a)
      (Me_Q I g e0 f0 hf0 hfe a (e_step I g e0 z0 bw hx hcx a _ (nxt_cong I g e0 z0 bw hcy a)))
  · by_cases h : i.1 + 1 < k
    · simp only [dif_pos h]
      exact term_Z I g _ _ (hbb i _ (fun he => by rw [Fin.ext_iff] at he; simp at he))
        (Mb_Q I g e0 bw bwd hbwd hbe hbb i (b_step I g e0 z0 bw hx hcx i _ (hcy.2.2 ⟨i.1 + 1, h⟩)))
    · simp only [dif_neg h, sub_self]; exact Z_zero I g

theorem Afun_int {x : I.Gf} (hx : x ∈ I.Kset) (he0 : ∀ a, e0 a ∈ I.Lf) (hf0 : ∀ a, f0 a ∈ I.Lf)
    (hz0 : z0 ∈ I.Lf) (hbw : ∀ i, bw i ∈ I.Lf) (hbwd : ∀ i, bwd i ∈ I.Lf) :
    Afun I e0 f0 z0 bw bwd x ∈ IntAf I.F I.E := by
  unfold Afun
  refine add_mem (sum_mem fun a _ => hA_int I (hf0 a) (K_mv I hx (nxt_mem I e0 z0 he0 hz0 a)))
    (sum_mem fun i _ => ?_)
  split_ifs with h
  · exact hA_int I (hbwd i) (K_mv I hx (hbw _))
  · exact (IntAf I.F I.E).zero_mem

theorem Kg_sub {x : I.Gf} (hx : x ∈ I.Kg g) : ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ mL I g := by
  intro y hy
  have hx' : x ∈ I.Kset ∧ ∀ y ∈ I.Lf, ∃ z ∈ I.Lf, (I.fmat x - 1) *ᵥ y = (g : I.E ⊗[I.F] Af I.F) • z := hx
  obtain ⟨z, hz, e⟩ := hx'.2 y hy
  rw [e]
  exact smul_mem_mL I hz

theorem cong_Kg {x : I.Gf} (hx : x ∈ I.Kg g) (he0 : ∀ a, e0 a ∈ I.Lf) (hz0 : z0 ∈ I.Lf)
    (hbw : ∀ i, bw i ∈ I.Lf) : K2cong I g e0 z0 bw x := by
  have h := Kg_sub I g hx
  unfold K2cong
  exact ⟨fun a => mL_Mo I (h _ (he0 a)), mL_Mo I (h _ hz0), fun i => mL_Mo I (h _ (hbw i))⟩

theorem Afun_Kg {x : I.Gf} (hx : x ∈ I.Kg g) (he0 : ∀ a, e0 a ∈ I.Lf) (hf0 : ∀ a, f0 a ∈ I.Lf)
    (hz0 : z0 ∈ I.Lf) (hbw : ∀ i, bw i ∈ I.Lf) (hbwd : ∀ i, bwd i ∈ I.Lf)
    (hfe : ∀ a b : Fin r, a ≠ b → ZMod' I g (hA I (f0 a) (e0 b)))
    (hfz : ∀ a, ZMod' I g (hA I (f0 a) z0))
    (hbb : ∀ i j : Fin k, i ≠ j → ZMod' I g (hA I (bwd i) (bw j))) :
    ZMod' I g (Afun I e0 f0 z0 bw bwd x) := by
  have h := Kg_sub I g hx
  unfold Afun
  refine Z_add I g (Z_sum I g _ _ fun a _ => ?_) (Z_sum I g _ _ fun i _ => ?_)
  · exact congruence_fixed_term I g (f0 a) (nxt e0 z0 a) (nxt_Z I g e0 f0 z0 hfe hfz a)
      (mL_Qs I g (hf0 a) (h _ (nxt_mem I e0 z0 he0 hz0 a)))
  · split_ifs with hi
    · have hj : (⟨i.1 + 1, hi⟩ : Fin k) ≠ i := fun e => by
        have := congrArg Fin.val e
        simp at this
      exact congruence_fixed_term I g (bwd i) (bw ⟨i.1 + 1, hi⟩) (hbb i _ (Ne.symm hj))
        (mL_Qs I g (hbwd i) (h _ (hbw _)))
    · exact Z_zero I g

end Frame

end Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.Pf

open MeasureTheory Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.unitaryCongruence

def AutKCompact : Prop := ∀ I : AutInst, IsCompact I.Kset

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D)

theorem modulus_g_ne_zero : X.B.g ≠ 0 := by
  rw [X.g_eq]
  exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

theorem reference_frame_congruences :
    (∀ a b, a ≠ b → ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) (X.e0 b))) ∧
    (∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) X.z0)) ∧
    (∀ i a, ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.e0 a))) ∧
    (∀ i j, i ≠ j → ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.bw j))) := by
  refine ⟨fun a b hab => ?_, fun a => (X.formsAtZero.2 a).2, fun i a => ?_, fun i j hij => ?_⟩
  · have h := (X.gramIntegral b a).2.2
    rw [if_neg (Ne.symm hab), sub_zero] at h
    rw [hA_symm X.B.I (X.e0 b)]; exact Z_sig _ _ h
  · rw [hA_symm X.B.I (X.e0 a)]; exact Z_sig _ _ ((X.weightVectorsIntegral i).2.2 a).2.2.1
  · have h := X.bw_dual i j
    rwa [if_neg hij, sub_zero] at h

theorem level_subgroup_character_unitary : X.LevelSubgroupCharacter := by
  have hg := modulus_g_ne_zero X
  obtain ⟨hfe, hfz, hbe, hbb⟩ := reference_frame_congruences X
  obtain ⟨hef, hz0, hbb'⟩ := X.vectorsInLattice
  have he0 : ∀ a, X.e0 a ∈ X.B.I.Lf := fun a => (hef a).1
  have hf0 : ∀ a, X.f0 a ∈ X.B.I.Lf := fun a => (hef a).2
  have hbw : ∀ i, X.bw i ∈ X.B.I.Lf := fun i => (hbb' i).1
  have hbwd : ∀ i, X.bwd i ∈ X.B.I.Lf := fun i => (hbb' i).2
  unfold HidaSetting.LevelSubgroupCharacter HidaSetting.K2 HidaSetting.chi2 K2set
  refine ⟨⟨K_one _, cong_one _ _ _ _ _⟩, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨hx, hcx⟩ y ⟨hy, hcy⟩
    exact ⟨K_mul _ hx hy, cong_mul _ _ _ _ _ hx hcx hcy⟩
  · rintro x ⟨hx, hcx⟩
    exact ⟨K_inv _ hx, cong_inv _ _ _ _ _ hx hcx⟩
  · rintro x ⟨hx, hcx⟩ y ⟨hy, hcy⟩
    rw [flagLevelCharacter_eq_psi_divN, flagLevelCharacter_eq_psi_divN, flagLevelCharacter_eq_psi_divN]
    exact psi_mul_of_Z _ _ X.psiEf_add X.psiEf_int hg
      (Afun_mul _ _ _ _ _ _ _ hx hcx hcy hf0 hbwd hfe hfz hbe hbb)
  · rintro x ⟨hx, -⟩
    rw [flagLevelCharacter_eq_psi_divN]
    exact psi_norm _ _ X.psiEf_add X.psiEf_int hg (Afun_int _ _ _ _ _ _ hx he0 hf0 hz0 hbw hbwd)

theorem levelSubgroupNormalized_of_compact (hK : AutKCompact) : X.LevelSubgroupNormalized := by
  have hg := modulus_g_ne_zero X
  obtain ⟨hfe, hfz, hbe, hbb⟩ := reference_frame_congruences X
  obtain ⟨hef, hz0, hbb'⟩ := X.vectorsInLattice
  have he0 : ∀ a, X.e0 a ∈ X.B.I.Lf := fun a => (hef a).1
  have hf0 : ∀ a, X.f0 a ∈ X.B.I.Lf := fun a => (hef a).2
  have hbw : ∀ i, X.bw i ∈ X.B.I.Lf := fun i => (hbb' i).1
  have hbwd : ∀ i, X.bwd i ∈ X.B.I.Lf := fun i => (hbb' i).2
  have hKg : ∀ x ∈ X.B.I.Kg X.B.g, x ∈ X.K2 ∧ X.chi2 x = 1 := by
    intro x hx
    have hx' : x ∈ X.B.I.Kset ∧ ∀ y ∈ X.B.I.Lf, ∃ z ∈ X.B.I.Lf,
        Matrix.mulVec (X.B.I.fmat x - 1) y = (X.B.g : TensorProduct X.B.I.F X.B.I.E (Af X.B.I.F)) • z := hx
    refine ⟨(⟨hx'.1, cong_Kg _ _ _ _ _ hx he0 hz0 hbw⟩ :
      x ∈ X.B.I.Kset ∧ K2cong X.B.I X.B.g X.e0 X.z0 X.bw x), ?_⟩
    show chi2f X.B.I X.psiEf X.B.g X.e0 X.f0 X.z0 X.bw X.bwd x = 1
    rw [flagLevelCharacter_eq_psi_divN]
    exact psi_Z _ _ X.psiEf_add X.psiEf_int hg (Afun_Kg _ _ _ _ _ _ _ hx he0 hf0 hz0 hbw hbwd hfe hfz hbb)
  have hsub : X.K2 ⊆ X.B.I.Kset := fun x hx => hx.1
  have hKgsub : X.B.I.Kg X.B.g ⊆ X.K2 := fun x hx => (hKg x hx).1
  have hopen : IsOpen (X.B.I.Kg X.B.g) := X.B.I.topf_open X.B.g (Nat.one_le_iff_ne_zero.2 hg)
  have hone : (1 : X.B.I.Gf) ∈ X.B.I.Kg X.B.g := by
    show (1 : X.B.I.Gf) ∈ X.B.I.Kset ∧ ∀ y ∈ X.B.I.Lf, ∃ z ∈ X.B.I.Lf,
      Matrix.mulVec (X.B.I.fmat 1 - 1) y = (X.B.g : TensorProduct X.B.I.F X.B.I.E (Af X.B.I.F)) • z
    refine ⟨K_one _, fun y _ => ⟨0, zero_mem _, ?_⟩⟩
    rw [fmat_one, sub_self, Matrix.zero_mulVec, smul_zero]
  refine ⟨hKg, fun x hx => hsub hx, ?_, ?_⟩
  · exact (hopen.measure_pos X.B.μf ⟨1, hone⟩).trans_le (measure_mono hKgsub)
  · exact (measure_mono hsub).trans_lt ((hK X.B.I).measure_lt_top)

end Formalism.L2.SG.Pf
