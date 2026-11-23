import Mathlib

noncomputable section

namespace Formalism.L2.Pj

section Graded

variable {K R M W : Type} [Field K] [CommRing R] [Algebra K R] [AddCommMonoid M] (key : W → M)
  (C : W → Submodule K R)

def incG (w : W) : C w →ₗ[K] AddMonoidAlgebra R M where
  toFun F := AddMonoidAlgebra.single (key w) (F : R)
  map_add' F F' := by simp [AddMonoidAlgebra.single_add]
  map_smul' a F := by simp [AddMonoidAlgebra.smul_single]

theorem incG_apply (w : W) (F : C w) : incG key C w F = AddMonoidAlgebra.single (key w) (F : R) := rfl

def cfG (K : Type) [Field K] [Algebra K R] (m : M) : AddMonoidAlgebra R M →ₗ[K] R where
  toFun x := x.coeff m
  map_add' x y := by simp
  map_smul' a x := by simp

open Classical in
theorem coeff_incG (m : M) (w : W) (F : C w) :
    (incG key C w F).coeff m = if key w = m then (F : R) else 0 := by
  rw [incG_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem incG_inj (w : W) : Function.Injective (incG key C w) := fun F F' h => by
  have h1 := congrArg (fun x : AddMonoidAlgebra R M => x.coeff (key w)) h
  simp only [coeff_incG, if_true] at h1
  exact Subtype.ext h1

theorem incG_indep (hkey : Function.Injective key) :
    iSupIndep fun w : W => LinearMap.range (incG key C w) := by
  intro w
  rw [Submodule.disjoint_def]
  intro x hx hx'
  obtain ⟨F, rfl⟩ := LinearMap.mem_range.mp hx
  have hle : (⨆ (u) (_ : u ≠ w), LinearMap.range (incG key C u)) ≤ LinearMap.ker (cfG K (key w)) := by
    refine iSup₂_le fun u hu => ?_
    rintro _ ⟨G', rfl⟩
    rw [LinearMap.mem_ker]
    change (incG key C u G').coeff (key w) = 0
    rw [coeff_incG, if_neg (fun h => hu (hkey h))]
  have h0 : (incG key C w F).coeff (key w) = 0 := hle hx'
  rw [coeff_incG, if_pos rfl] at h0
  rw [show F = 0 from Subtype.ext h0, map_zero]

theorem incG_mul {w w' u : W} (hu : key u = key w + key w') (F : C w) (F' : C w')
    (h : (F : R) * (F' : R) ∈ C u) : incG key C w F * incG key C w' F' = incG key C u ⟨_, h⟩ := by
  rw [incG_apply, incG_apply, incG_apply, AddMonoidAlgebra.single_mul_single, hu]

def vG (v : R → EReal) (x : AddMonoidAlgebra R M) : EReal := ⨅ m, v (x.coeff m)

variable {v : R → EReal}

theorem vG_zero (h0 : v 0 = ⊤) : vG v (0 : AddMonoidAlgebra R M) = ⊤ := by simp [vG, h0]

theorem vG_single (h0 : v 0 = ⊤) (m : M) (r : R) : vG v (AddMonoidAlgebra.single m r) = v r := by
  classical
  apply le_antisymm
  · exact (iInf_le _ m).trans (by rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same])
  · refine le_iInf fun u => ?_
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs
    · exact le_rfl
    · rw [h0]; exact le_top

theorem vG_incG (h0 : v 0 = ⊤) (w : W) (F : C w) : vG v (incG key C w F) = v F := vG_single h0 _ _

theorem vG_add (ha : ∀ r s, min (v r) (v s) ≤ v (r + s)) (x y : AddMonoidAlgebra R M) :
    min (vG v x) (vG v y) ≤ vG v (x + y) := by
  refine le_iInf fun m => ?_
  have : (x + y).coeff m = x.coeff m + y.coeff m := by simp
  rw [this]
  exact (min_le_min (iInf_le _ m) (iInf_le _ m)).trans (ha _ _)

theorem ereal_add_iInf {ι : Type} (c : ℝ) (f : ι → EReal) :
    (c : EReal) + ⨅ i, f i = ⨅ i, ((c : EReal) + f i) := by
  have hc : ∀ x : EReal, ((-c : ℝ) : EReal) + ((c : EReal) + x) = x := by
    intro x
    induction x using EReal.rec with
    | bot => simp
    | top => simp
    | coe x => norm_cast; ring
  have hc' : ∀ x : EReal, (c : EReal) + (((-c : ℝ) : EReal) + x) = x := by
    intro x
    induction x using EReal.rec with
    | bot => simp
    | top => simp
    | coe x => norm_cast; ring
  apply le_antisymm
  · exact le_iInf fun i => add_le_add le_rfl (iInf_le f i)
  · have h1 : ((-c : ℝ) : EReal) + ⨅ i, ((c : EReal) + f i) ≤ ⨅ i, f i :=
      le_iInf fun i => (add_le_add le_rfl (iInf_le (fun i => (c : EReal) + f i) i)).trans (hc (f i)).le
    have h2 := add_le_add (le_refl (c : EReal)) h1
    rwa [hc'] at h2

theorem vG_smul {a : K} {t : ℝ} (hs : ∀ r, v (a • r) = (t : EReal) + v r) (x : AddMonoidAlgebra R M) :
    vG v (a • x) = (t : EReal) + vG v x := by
  unfold vG
  rw [ereal_add_iInf]
  refine iInf_congr fun m => ?_
  have : (a • x).coeff m = a • x.coeff m := by simp
  rw [this, hs]

theorem vG_ne_bot (h0 : v 0 = ⊤) (hb : ∀ r, v r ≠ ⊥) (x : AddMonoidAlgebra R M) : vG v x ≠ ⊥ := by
  classical
  have hT : x.coeff.support.inf (fun m => v (x.coeff m)) ≤ vG v x := by
    refine le_iInf fun m => ?_
    by_cases hm : m ∈ x.coeff.support
    · exact Finset.inf_le hm
    · rw [Finsupp.notMem_support_iff.mp hm, h0]; exact le_top
  have hne : x.coeff.support.inf (fun m => v (x.coeff m)) ≠ ⊥ := by
    rw [Ne, Finset.inf_eq_bot_iff]; push Not
    exact fun m _ => hb _
  intro h
  exact hne (le_bot_iff.mp (h ▸ hT))

theorem vG_mul (h0 : v 0 = ⊤) (hm : ∀ r s, v (r * s) = v r + v s) (w w' : W) (F : C w) (F' : C w') :
    vG v (incG key C w F * incG key C w' F') = vG v (incG key C w F) + vG v (incG key C w' F') := by
  rw [incG_apply, incG_apply, AddMonoidAlgebra.single_mul_single, vG_single h0, vG_single h0, vG_single h0, hm]

end Graded

end Formalism.L2.Pj
