import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarMinors

noncomputable section

open scoped Classical
open Matrix

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

open Formalism.MainNotions.S

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

def lin {ι : Type*} [Fintype ι] (u : ι → S.V) (c : ι → E) : S.V := ∑ i, c i • u i

theorem hT_lin_right {ι : Type*} [Fintype ι] (u : ι → S.V) (c : ι → E) (x : S.V) :
    S.hT x (lin u c) = ∑ i, c i * S.hT x (u i) := by
  simp [lin, map_sum, map_smul, smul_eq_mul]

theorem hT_lin_left {ι : Type*} [Fintype ι] (u : ι → S.V) (c : ι → E) (x : S.V) :
    S.hT (lin u c) x = ∑ i, star (c i) * S.hT (u i) x := by
  simp only [lin, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply]

theorem hT_lin_lin {ι : Type*} [Fintype ι] (u : ι → S.V) (c d : ι → E) :
    S.hT (lin u c) (lin u d) = ∑ i, ∑ j, star (c i) * d j * S.hT (u i) (u j) := by
  rw [hT_lin_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hT_lin_right, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem lin_add {ι : Type*} [Fintype ι] (u : ι → S.V) (c d : ι → E) : lin u (c + d) = lin u c + lin u d := by
  simp [lin, add_smul, Finset.sum_add_distrib]

theorem lin_smul {ι : Type*} [Fintype ι] (u : ι → S.V) (t : E) (c : ι → E) : lin u (t • c) = t • lin u c := by
  simp [lin, smul_smul, Finset.smul_sum]

theorem lin_sub {ι : Type*} [Fintype ι] (u : ι → S.V) (c : ι → E) : lin u c ∈ Submodule.span E (Set.range u) :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def pc {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) (v : S.V) : ι → E :=
  (gram S u u)⁻¹ *ᵥ fun k => S.hT (u k) v

theorem pc_add {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) (x y : S.V) :
    pc u (x + y) = pc u x + pc u y := by
  unfold pc
  rw [← Matrix.mulVec_add]
  congr 1
  funext k
  simp

theorem pc_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) (t : E) (x : S.V) :
    pc u (t • x) = t • pc u x := by
  unfold pc
  rw [← Matrix.mulVec_smul]
  congr 1
  funext k
  simp

theorem hT_u_lin {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) (c : ι → E) (k : ι) :
    S.hT (u k) (lin u c) = (gram S u u *ᵥ c) k := by
  rw [hT_lin_right]
  simp [Matrix.mulVec, dotProduct, gram, mul_comm]

theorem hT_u_rem {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) (hdet : (gram S u u).det ≠ 0) (v : S.V)
    (k : ι) : S.hT (u k) (v - lin u (pc u v)) = 0 := by
  rw [map_sub, hT_u_lin]
  unfold pc
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  simp

theorem hT_span_rem {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) (hdet : (gram S u u).det ≠ 0) (v z : S.V)
    (hz : z ∈ Submodule.span E (Set.range u)) : S.hT z (v - lin u (pc u v)) = 0 ∧ S.hT (v - lin u (pc u v)) z = 0 := by
  have first : S.hT z (v - lin u (pc u v)) = 0 := by
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact hT_u_rem u hdet v k
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [LinearMap.map_smulₛₗ₂, hx]
  refine ⟨first, ?_⟩
  rw [← S.herm.eq z, first]
  simp

def isoG {ι : Type*} [Fintype ι] [DecidableEq ι] (u u' : ι → S.V) : S.V →ₗ[E] S.V where
  toFun v := v - lin u (pc u v) + lin u' (pc u v)
  map_add' x y := by
    rw [pc_add, lin_add, lin_add]; abel
  map_smul' t x := by
    rw [pc_smul, lin_smul, lin_smul, RingHom.id_apply, smul_add, smul_sub]

theorem isoG_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (u u' : ι → S.V) (v : S.V) :
    isoG u u' v = v - lin u (pc u v) + lin u' (pc u v) := rfl

theorem pc_self {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) (hdet : (gram S u u).det ≠ 0) (m : ι) :
    pc u (u m) = Pi.single m 1 := by
  have hcol : (fun k => S.hT (u k) (u m)) = gram S u u *ᵥ Pi.single m 1 := by
    funext k
    simp [Matrix.mulVec, dotProduct, gram, Pi.single_apply]
  unfold pc
  rw [hcol, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]

theorem lin_single {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) (m : ι) : lin u (Pi.single m 1) = u m := by
  simp [lin, Pi.single_apply, ite_smul]

private theorem hT_isoG_of_gram_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (u u' : ι → S.V) (hG : gram S u' u' = gram S u u)
    (hdet : (gram S u u).det ≠ 0) (hsp : ∀ i, u' i ∈ Submodule.span E (Set.range u)) (x y : S.V) :
    S.hT (isoG u u' x) (isoG u u' y) = S.hT x y := by
  have hlin : ∀ (w : ι → S.V) (c : ι → E), (∀ i, w i ∈ Submodule.span E (Set.range u)) →
      lin w c ∈ Submodule.span E (Set.range u) := by
    intro w c hw
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hw i)
  have hu : ∀ i, u i ∈ Submodule.span E (Set.range u) := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hgram : ∀ (w : ι → S.V) (c d : ι → E), S.hT (lin w c) (lin w d) =
      ∑ i, ∑ j, star (c i) * d j * gram S w w i j := by
    intro w c d
    rw [hT_lin_lin]
    simp [gram]
  have ex : x = (x - lin u (pc u x)) + lin u (pc u x) := by abel
  have ey : y = (y - lin u (pc u y)) + lin u (pc u y) := by abel
  have gx : isoG u u' x = (x - lin u (pc u x)) + lin u' (pc u x) := by rw [isoG_apply]
  have gy : isoG u u' y = (y - lin u (pc u y)) + lin u' (pc u y) := by rw [isoG_apply]
  have o1 := fun z hz => (hT_span_rem u hdet x z hz)
  have o2 := fun z hz => (hT_span_rem u hdet y z hz)
  have A1 := (o2 _ (hlin u' (pc u x) hsp)).1
  have A2 := (o1 _ (hlin u' (pc u y) hsp)).2
  have B1 := (o2 _ (hlin u (pc u x) hu)).1
  have B2 := (o1 _ (hlin u (pc u y) hu)).2
  conv_rhs => rw [ex, ey]
  rw [gx, gy]
  simp only [map_add, LinearMap.add_apply]
  rw [A1, A2, B1, B2, hgram u', hgram u, hG]

theorem isom_ext {ι : Type*} [Fintype ι] [DecidableEq ι] (u u' : ι → S.V) (hG : gram S u' u' = gram S u u)
    (hdet : (gram S u u).det ≠ 0) (hsp : ∀ i, u' i ∈ Submodule.span E (Set.range u)) :
    ∃ g : S.V ≃ₗ[E] S.V, (∀ x y, S.hT (g x) (g y) = S.hT x y) ∧ (∀ i, g (u i) = u' i) ∧
      (∀ w, (∀ k, S.hT (u k) w = 0) → g w = w) ∧
      ∀ v, g v = v + ∑ k, S.hT (u k) v • ∑ m, (gram S u u)⁻¹ m k • (u' m - u m) := by
  haveI := S.fd
  have hinj : Function.Injective (isoG u u') := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply S.nondeg.1 x
    intro y
    rw [← hT_isoG_of_gram_eq u u' hG hdet hsp x y, hx]
    simp
  have hsurj : Function.Surjective (isoG u u') := LinearMap.injective_iff_surjective.mp hinj
  have hbij : Function.Bijective (isoG u u') := ⟨hinj, hsurj⟩
  refine ⟨LinearEquiv.ofBijective (isoG u u') hbij, ?_, ?_, ?_, ?_⟩
  · intro x y
    exact hT_isoG_of_gram_eq u u' hG hdet hsp x y
  · intro i
    simp only [LinearEquiv.ofBijective_apply, isoG_apply, pc_self u hdet, lin_single]
    abel
  · intro w hw
    have hp : pc u w = 0 := by
      unfold pc
      have : (fun k => S.hT (u k) w) = 0 := funext hw
      rw [this, Matrix.mulVec_zero]
    simp only [LinearEquiv.ofBijective_apply, isoG_apply, hp]
    simp [lin]
  · intro v
    simp only [LinearEquiv.ofBijective_apply, isoG_apply]
    have key : lin u' (pc u v) - lin u (pc u v) =
        ∑ k, S.hT (u k) v • ∑ m, (gram S u u)⁻¹ m k • (u' m - u m) := by
      simp only [lin, pc, Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib, ← smul_sub,
        Finset.sum_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
      rw [mul_comm]
    rw [← key]
    abel

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA
