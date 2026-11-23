import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.EichLApply

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def skL (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) :
    (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id + ∑ a, ∑ a', S a a' • ((VS D).hT (D.sp.hypE a')).smulRight (D.sp.hypE a)

theorem skL_apply (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (v : (VS D).V) :
    skL D S v = v + ∑ a, (∑ a', S a a' * (VS D).hT (D.sp.hypE a') v) • D.sp.hypE a := by
  simp only [skL, LinearMap.add_apply, LinearMap.id_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.smulRight_apply, smul_smul, Finset.sum_smul]

theorem hE_skL (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (b : Fin D.R.rS)
    (v : (VS D).V) : (VS D).hT (D.sp.hypE b) (skL D S v) = (VS D).hT (D.sp.hypE b) v := by
  rw [skL_apply, map_add, map_sum]
  simp [D.sp.hyp_ee]

theorem skL_inv (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (v : (VS D).V) :
    skL D (-S) (skL D S v) = v := by
  rw [skL_apply D (-S) (skL D S v)]
  simp only [hE_skL]
  rw [skL_apply]
  have e : ∀ a, (∑ a', (-S) a a' * (VS D).hT (D.sp.hypE a') v) =
      -(∑ a', S a a' * (VS D).hT (D.sp.hypE a') v) := fun a => by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Matrix.neg_apply, neg_mul]
  simp_rw [e, neg_smul, Finset.sum_neg_distrib]
  exact add_neg_cancel_right _ _

def skE (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  LinearEquiv.ofLinear (skL D S) (skL D (-S))
    (LinearMap.ext fun v => by
      have h := skL_inv D (-S) v
      rw [neg_neg] at h
      exact h)
    (LinearMap.ext fun v => skL_inv D S v)

theorem skE_apply (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (v : (VS D).V) :
    skE D S v = skL D S v := rfl

theorem dsum_cancel {K : Type} [CommRing K] {r : ℕ} (S : Matrix (Fin r) (Fin r) K) (X Y : Fin r → K) :
    ∑ a, (∑ a', S a a' * X a') * Y a + ∑ a, (∑ a', -S a' a * Y a') * X a = 0 := by
  have e : ∑ a, (∑ a', -S a' a * Y a') * X a = -∑ a, (∑ a', S a a' * X a') * Y a := by
    simp only [Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    ring
  rw [e, add_neg_cancel]

theorem skL_isom (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (hS : ∀ i j, star (S j i) = -S i j) (u v : (VS D).V) :
    (VS D).hT (skL D S u) (skL D S v) = (VS D).hT u v := by
  have hue : ∀ b, (VS D).hT u (D.sp.hypE b) = star ((VS D).hT (D.sp.hypE b) u) := fun b =>
    ((VS D).herm.eq (D.sp.hypE b) u).symm
  have key := dsum_cancel S (fun b => (VS D).hT (D.sp.hypE b) v) (fun b => star ((VS D).hT (D.sp.hypE b) u))
  beta_reduce at key
  rw [skL_apply, skL_apply]
  simp only [map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, map_smul,
    D.sp.hyp_ee, hue, smul_eq_mul, mul_zero, Finset.sum_const_zero, add_zero, starRingEnd_apply, star_sum,
    star_mul', hS]
  linear_combination key

theorem hE_int (D : Formalism.BasicNotions.D7) {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T}
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hF : FixedOK D F0 Λ) (a : Fin D.R.rS) {v : (VS D).V}
    (hv : v ∈ Λ) : ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (VS D).hT (D.sp.hypE a) v := by
  have he : D.sp.hypE a ∈ Λ := by
    have h1 := hF.2.2.2.1 a
    rwa [hF.2.2.1] at h1
  have hU' : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hF.2.1
  have hv' : v ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by rw [hU']; exact hv
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply] at hv'
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hv' _ he)
  exact ⟨o, ho⟩

theorem skL_lat (D : Formalism.BasicNotions.D7) {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T}
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hF : FixedOK D F0 Λ) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (hO : ∀ i j, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = S i j) {v : (VS D).V} (hv : v ∈ Λ) :
    skL D S v ∈ Λ := by
  rw [skL_apply]
  refine Λ.add_mem hv (Λ.sum_mem fun a _ => ?_)
  have he : D.sp.hypE a ∈ Λ := by
    have h1 := hF.2.2.2.1 a
    rwa [hF.2.2.1] at h1
  have hc : (∑ a', S a a' * (VS D).hT (D.sp.hypE a') v) ∈ (algebraMap (𝓞 D.host.E) D.host.E).range :=
    sum_mem fun a' _ => mul_mem (hO a a') (hE_int D hF a' hv)
  obtain ⟨o, ho⟩ := hc
  rw [← ho, algebraMap_smul]
  exact Λ.smul_mem o he

theorem skL_X (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) {x : (VS D).V}
    (hx : x ∈ Submodule.span D.host.E (Set.range D.sp.hypE)) : skL D S x = x := by
  have h0 : ∀ a', (VS D).hT (D.sp.hypE a') x = 0 := by
    intro a'
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      exact D.sp.hyp_ee a' b
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
    | smul c y _ hy => rw [map_smul, hy, smul_zero]
  rw [skL_apply]
  simp [h0]

theorem skL_sub_mem (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (x : (VS D).V) :
    skL D S x - x ∈ Submodule.span D.host.E (Set.range D.sp.hypE) := by
  rw [skL_apply, add_sub_cancel_left]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem skE_mem (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (hS : ∀ i j, star (S j i) = -S i j)
    (hO : ∀ i j, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = S i j) :
    skE D S ∈ N0 F0 Λ := by
  have hFe : F0.e = D.sp.hypE := hF.2.2.1
  have hspan : ∀ x ∈ Submodule.span D.host.E (Set.range F0.e), skE D S x = x := by
    intro x hx
    rw [hFe] at hx
    exact skL_X D S hx
  have hO' : ∀ i j, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (-S) i j := fun i j => by
    obtain ⟨o, ho⟩ := hO i j
    exact ⟨-o, by rw [map_neg, ho, Matrix.neg_apply]⟩
  have hzm : ∀ a', (VS D).hT (D.sp.hypE a') D.sp.zm = 0 := fun a' => by
    rw [← (VS D).herm.eq D.sp.zm (D.sp.hypE a'), (D.sp.hyp_orthz a').1, map_zero]
  simp only [N0, NLam, IsAutLam, Set.mem_setOf_eq]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · intro x y
    exact skL_isom D S hS x y
  · apply le_antisymm
    · exact Submodule.map_le_iff_le_comap.mpr fun v hv => skL_lat D hF S hO hv
    · intro v hv
      refine Submodule.mem_map.mpr ⟨skL D (-S) v, skL_lat D hF (-S) hO' hv, ?_⟩
      have h1 := skL_inv D (-S) v
      rw [neg_neg] at h1
      exact h1
  · intro j x hx
    have hx' : x ∈ Submodule.span D.host.E (Set.range F0.e) :=
      Submodule.span_mono (Set.image_subset_range _ _) hx
    rw [hspan x hx', sub_self]
    exact Submodule.zero_mem _
  · intro x _
    have h1 := skL_sub_mem D S x
    rw [← hFe] at h1
    exact h1
  · intro a
    exact hspan _ (Submodule.subset_span ⟨a, rfl⟩)
  · obtain ⟨c, _, hcz⟩ := hF.2.2.2.2
    rw [hcz, map_smul]
    congr 1
    rw [skE_apply, skL_apply]
    simp [hzm]

private theorem pW_skL (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (w : (VS D).V) : pW D (skL D S w) = pW D w := by
  have hf : ∀ a b, (VS D).hT (D.sp.hypF b) (D.sp.hypE a) = if a = b then 1 else 0 := fun a b => by
    rw [← (VS D).herm.eq (D.sp.hypE a) (D.sp.hypF b), D.sp.hyp_ef]
    split_ifs <;> simp
  have hz : ∀ a, (VS D).hT D.sp.zm (D.sp.hypE a) = 0 := fun a => (D.sp.hyp_orthz a).1
  rw [skL_apply]
  simp only [pW, map_add, map_sum, map_smul, hf, hz, D.sp.hyp_ee, smul_eq_mul, mul_zero, add_zero,
    mul_ite, mul_one, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, add_smul,
    Finset.sum_add_distrib, Finset.sum_const_zero, zero_smul]
  module

theorem pWf_skE (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (x : (Fin D.R.rS → (VS D).V) × (VS D).V) : pWf D (act D (skE D S) x) = pWf D x := by
  funext b
  have hfr : fr D (act D (skE D S) x) b = skL D S (fr D x b) := by
    simp only [fr, act]
    exact (congrFun (Fin.comp_snoc (fun w => (skE D S) w) x.1 x.2) b).symm
  simp only [pWf]
  rw [hfr, pW_skL]

theorem alM_skE (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ) (Z : MatZ D)
    (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) {x : (Fin D.R.rS → (VS D).V) × (VS D).V}
    (hx : Good D T' F0 Λ Z x) : alM D (act D (skE D S) x) = alM D x + S * betaZ D Z := by
  ext a b
  have hf : ∀ c, (VS D).hT (D.sp.hypF a) (D.sp.hypE c) = if c = a then 1 else 0 := fun c => by
    rw [← (VS D).herm.eq (D.sp.hypE c) (D.sp.hypF a), D.sp.hyp_ef]
    split_ifs <;> simp
  have hZ : ∀ c', (VS D).hT (D.sp.hypE c') (fr D x b) = Z (Fin.castSucc c') b := fun c' => by
    have h1 := hx.2.1 (Fin.castSucc c') b
    simp only [Formalism.MainNotions.S.brS, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc, hF.2.2.1] at h1
    exact h1
  have hfr : fr D (act D (skE D S) x) b = skL D S (fr D x b) := by
    simp only [fr, act]
    exact (congrFun (Fin.comp_snoc (fun w => (skE D S) w) x.1 x.2) b).symm
  simp only [alM, Matrix.add_apply, Matrix.mul_apply, betaZ, Matrix.submatrix_apply, id]
  rw [hfr, skL_apply, map_add, map_sum]
  simp only [map_smul, smul_eq_mul, hf, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, hZ]

end PI.UnitaryGroupMassFormula.CntFormula
