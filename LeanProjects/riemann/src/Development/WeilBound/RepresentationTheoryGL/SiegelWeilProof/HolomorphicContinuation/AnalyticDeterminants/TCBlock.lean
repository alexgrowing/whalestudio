import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCHeights
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCBlockC

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def vv (σ : Equiv.Perm (Fin n)) (r : Fin n) : Matrix (Fin n) (Fin n) ℂ := single r (σ r) 1

def epsE (j : ℕ) : Fin (Fintype.card (blkA (n := n) j) + Fintype.card (blkB (n := n) j)) ≃ Fin n :=
  finSumFinEquiv.symm.trans (((Fintype.equivFin (blkA (n := n) j)).symm.sumCongr
    (Fintype.equivFin (blkB (n := n) j)).symm).trans
      (((Equiv.refl _).sumCongr (eBq j)).trans (Equiv.sumCompl fun x => x ∈ blkA (n := n) j)))

theorem epsE_left (j : ℕ) (i : Fin (Fintype.card (blkA (n := n) j))) :
    epsE j (Fin.castAdd _ i) = ((Fintype.equivFin (blkA (n := n) j)).symm i : Fin n) := by
  simp [epsE]

theorem epsE_right (j : ℕ) (i : Fin (Fintype.card (blkB (n := n) j))) :
    epsE j (Fin.natAdd _ i) = ((Fintype.equivFin (blkB (n := n) j)).symm i : Fin n) := by
  simp [epsE, eBq]

theorem prod_coef (j : ℕ) (c c' : ℂ) :
    (∏ r : Fin n, if r ∈ blkA (n := n) j then c else c') = c ^ (blkA (n := n) j).card * c' ^ (blkB (n := n) j).card := by
  classical
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  congr 2
  · congr 1
    ext x
    simp
  · congr 1
    ext x
    simp [blkB]

theorem lhs_eq (hA : IterAffine) (j : ℕ) (c c' : ℂ) (ψ : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (Ω : Set (Matrix (Fin n) (Fin n) ℂ)) (hΩ : IsOpen Ω) (h0 : 0 ∈ Ω) (hψ : ContDiffOn ℂ ∞ ψ Ω) :
    detD (fun t => ψ (bdiag j c c' t)) =
      c ^ (blkA (n := n) j).card * c' ^ (blkB (n := n) j).card *
        ∑ σ : Equiv.Perm (Fin n), if (∀ r, r ∈ blkA (n := n) j ↔ σ r ∈ blkA (n := n) j) then
          (Equiv.Perm.sign σ : ℂ) * iteratedFDeriv ℂ (Fintype.card (Fin n)) ψ 0 (vv σ ∘ (Fintype.equivFin (Fin n)).symm)
          else 0 := by
  classical
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := bdiag j c c'
        map_add' := fun x y => by
          ext a b; simp only [bdiag, Matrix.add_apply]; split_ifs <;> ring
        map_smul' := fun m x => by
          ext a b; simp only [bdiag, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring }
  have hL : ∀ t, L t = bdiag j c c' t := fun t => rfl
  have hfun : (fun t => ψ (bdiag j c c' t)) = fun w => ψ (0 + L w) := by
    funext w; rw [zero_add, hL]
  have hκ : ∀ (σ : Equiv.Perm (Fin n)) (r : Fin n), L (vv σ r) =
      (if r ∈ blkA (n := n) j ∧ σ r ∈ blkA (n := n) j then c
        else if r ∈ blkB (n := n) j ∧ σ r ∈ blkB (n := n) j then c' else 0) • vv σ r := by
    intro σ r
    ext a b
    rw [hL]
    simp only [bdiag, vv, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases hab : r = a ∧ σ r = b
    · obtain ⟨rfl, rfl⟩ := hab; simp
    · simp [hab]
  have hD := hA (Matrix (Fin n) (Fin n) ℂ) (Matrix (Fin n) (Fin n) ℂ) ψ Ω hΩ hψ 0 h0 L (Fintype.card (Fin n))
  unfold detD
  rw [hfun]
  erw [hD]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  erw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hv : (fun i => L (single ((Fintype.equivFin (Fin n)).symm i) (σ ((Fintype.equivFin (Fin n)).symm i)) 1))
      = fun i => (fun r => if r ∈ blkA (n := n) j ∧ σ r ∈ blkA (n := n) j then c
        else if r ∈ blkB (n := n) j ∧ σ r ∈ blkB (n := n) j then c' else 0) ((Fintype.equivFin (Fin n)).symm i) •
          (vv σ ∘ (Fintype.equivFin (Fin n)).symm) i := by
    funext i
    exact hκ σ _
  erw [hv, ContinuousMultilinearMap.map_smul_univ,
    Equiv.prod_comp (Fintype.equivFin (Fin n)).symm (fun r => if r ∈ blkA (n := n) j ∧ σ r ∈ blkA (n := n) j then c
        else if r ∈ blkB (n := n) j ∧ σ r ∈ blkB (n := n) j then c' else 0)]
  split_ifs with hp
  · have hprod : (∏ r : Fin n, if r ∈ blkA (n := n) j ∧ σ r ∈ blkA (n := n) j then c
        else if r ∈ blkB (n := n) j ∧ σ r ∈ blkB (n := n) j then c' else 0)
        = ∏ r : Fin n, if r ∈ blkA (n := n) j then c else c' := by
      refine Finset.prod_congr rfl fun r _ => ?_
      by_cases hr : r ∈ blkA (n := n) j
      · simp [hr, (hp r).mp hr]
      · have hr' : σ r ∉ blkA (n := n) j := fun h => hr ((hp r).mpr h)
        simp [hr, hr', blkB]
    rw [hprod, prod_coef, smul_eq_mul]
    ring
  · push_neg at hp
    obtain ⟨r, hr⟩ := hp
    have hz : (∏ r : Fin n, if r ∈ blkA (n := n) j ∧ σ r ∈ blkA (n := n) j then c
        else if r ∈ blkB (n := n) j ∧ σ r ∈ blkB (n := n) j then c' else 0) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ r) ?_
      rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp [h1, h2, blkB]
      · simp [h1, h2, blkB]
    rw [hz, zero_smul, mul_zero, mul_zero]

theorem append_eq (j : ℕ) (σA : Equiv.Perm (blkA (n := n) j)) (τ : Equiv.Perm (blkB (n := n) j)) :
    Fin.append (fun i => embL (blkA (n := n) j) (single ((Fintype.equivFin (blkA (n := n) j)).symm i)
        (σA ((Fintype.equivFin (blkA (n := n) j)).symm i)) (1 : ℂ)))
      (fun i => embL (blkB (n := n) j) (single ((Fintype.equivFin (blkB (n := n) j)).symm i)
        (τ ((Fintype.equivFin (blkB (n := n) j)).symm i)) (1 : ℂ))) = vv (piP j σA τ) ∘ epsE j := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [Fin.append_left, Function.comp_apply, epsE_left]
    generalize (Fintype.equivFin (blkA (n := n) j)).symm i = a
    have hp : piP j σA τ a = σA a := by
      simp [piP, Equiv.Perm.subtypeCongr.left_apply _ _ a.2]
    ext p q
    simp only [vv, hp, embL]
    simp only [embOn, Matrix.single_apply, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
    by_cases hpq : (a : Fin n) = p ∧ (σA a : Fin n) = q
    · obtain ⟨rfl, rfl⟩ := hpq
      simp
    · rw [if_neg hpq]
      split_ifs with h1 h2
      · exact absurd ⟨by rw [h2.1], by rw [h2.2]⟩ hpq
      · rfl
      · rfl
  · simp only [Fin.append_right, Function.comp_apply, epsE_right]
    generalize (Fintype.equivFin (blkB (n := n) j)).symm i = b
    have hp : piP j σA τ b = τ b := by
      have hb : (b : Fin n) ∉ blkA (n := n) j := by
        have := b.2; simpa [blkB] using this
      simp [piP, Equiv.Perm.subtypeCongr.right_apply _ _ hb, eBq]
      exact Subtype.ext rfl
    ext p q
    simp only [vv, hp, embL]
    simp only [embOn, Matrix.single_apply, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
    by_cases hpq : (b : Fin n) = p ∧ (τ b : Fin n) = q
    · obtain ⟨rfl, rfl⟩ := hpq
      simp
    · rw [if_neg hpq]
      split_ifs with h1 h2
      · exact absurd ⟨by rw [h2.1], by rw [h2.2]⟩ hpq
      · rfl
      · rfl

private theorem iteratedFDeriv_comp_equiv_eq_of_contDiffOn (hS : IterSymm) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (ψ : V → ℂ) (Ω : Set V) (hΩ : IsOpen Ω) (hψ : ContDiffOn ℂ ∞ ψ Ω) (c : V) (hc : c ∈ Ω)
    {k m p : ℕ} (e1 : Fin k ≃ Fin p) (e2 : Fin m ≃ Fin p) (v : Fin p → V) :
    iteratedFDeriv ℂ k ψ c (v ∘ e1) = iteratedFDeriv ℂ m ψ c (v ∘ e2) := by
  obtain rfl : k = m := Fin.equiv_iff_eq.mp ⟨e1.trans e2.symm⟩
  rw [← hS V ψ Ω hΩ hψ c hc k (v ∘ e2) (e1.trans e2.symm)]
  congr 1
  funext i
  simp

private theorem iteratedFDeriv_sum_mul_eq_sum_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type} (u : Finset ι)
    (f : ι → E → ℂ) (a : ι → ℂ) (x : E) (k : ℕ) (h : ∀ i ∈ u, ContDiffAt ℂ k (f i) x) :
    iteratedFDeriv ℂ k (fun y => ∑ i ∈ u, a i * f i y) x = ∑ i ∈ u, a i • iteratedFDeriv ℂ k (f i) x := by
  have h1 : (fun y => ∑ i ∈ u, a i * f i y) = ∑ i ∈ u, (fun y => a i • f i y) := by
    funext y
    simp [Finset.sum_apply]
  rw [h1, ← iteratedFDerivWithin_univ, iteratedFDerivWithin_sum_apply uniqueDiffOn_univ (Set.mem_univ _)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [iteratedFDerivWithin_univ]
    exact iteratedFDeriv_const_smul_apply' (h i hi)
  · intro i hi
    exact ((h i hi).const_smul (a i)).contDiffWithinAt

theorem rhs_eq (hA : IterAffine) (hS : IterSymm) (hN : IterNested) (j : ℕ) (ψ : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (Ω : Set (Matrix (Fin n) (Fin n) ℂ)) (hΩ : IsOpen Ω) (h0 : 0 ∈ Ω) (hψ : ContDiffOn ℂ ∞ ψ Ω) :
    detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      ψ (embOn (blkA j) T + embOn (blkB j) S))) =
    ∑ σA : Equiv.Perm (blkA (n := n) j), ∑ τ : Equiv.Perm (blkB (n := n) j),
      (Equiv.Perm.sign σA : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card (Fin n)) ψ 0 (vv (piP j σA τ) ∘ (Fintype.equivFin (Fin n)).symm) := by
  classical
  have hψ0 : ContDiffAt ℂ ∞ ψ 0 := hψ.contDiffAt (hΩ.mem_nhds h0)
  have hG : ∀ w : Fin (Fintype.card (blkB (n := n) j)) → Matrix (blkB (n := n) j) (blkB (n := n) j) ℂ,
      ContDiffAt ℂ (Fintype.card (blkA (n := n) j)) (fun T : Matrix (blkA (n := n) j) (blkA (n := n) j) ℂ =>
        iteratedFDeriv ℂ (Fintype.card (blkB (n := n) j))
          (fun S : Matrix (blkB (n := n) j) (blkB (n := n) j) ℂ => ψ (embOn (blkA j) T + embOn (blkB j) S)) 0 w) 0 := by
    intro w
    have hmem : ∀ᶠ T in 𝓝 (0 : Matrix (blkA (n := n) j) (blkA (n := n) j) ℂ), embL (blkA (n := n) j) T ∈ Ω := by
      apply (embL (blkA (n := n) j)).continuous.continuousAt.preimage_mem_nhds
      simpa using hΩ.mem_nhds h0
    have hev : (fun T : Matrix (blkA (n := n) j) (blkA (n := n) j) ℂ =>
        iteratedFDeriv ℂ (Fintype.card (blkB (n := n) j))
          (fun S : Matrix (blkB (n := n) j) (blkB (n := n) j) ℂ => ψ (embOn (blkA j) T + embOn (blkB j) S)) 0 w)
        =ᶠ[𝓝 0] fun T => iteratedFDeriv ℂ (Fintype.card (blkB (n := n) j)) ψ (embL (blkA (n := n) j) T)
          (fun i => embL (blkB (n := n) j) (w i)) := by
      filter_upwards [hmem] with T hT
      have := hA (Matrix (Fin n) (Fin n) ℂ) (Matrix (blkB (n := n) j) (blkB (n := n) j) ℂ) ψ Ω hΩ hψ
        (embL (blkA (n := n) j) T) hT (embL (blkB (n := n) j)) (Fintype.card (blkB (n := n) j))
      exact congrArg (fun M => M w) this
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    have h1 : ContDiffAt ℂ (Fintype.card (blkA (n := n) j))
        (iteratedFDeriv ℂ (Fintype.card (blkB (n := n) j)) ψ) (embL (blkA (n := n) j) 0) := by
      rw [map_zero]
      exact hψ0.iteratedFDeriv_right (by first | exact_mod_cast le_top | (norm_cast; exact le_top) | (exact WithTop.coe_le_coe.mpr le_top) | simp [← Nat.cast_add]; exact_mod_cast le_top)
    have h2 := h1.comp (0 : Matrix (blkA (n := n) j) (blkA (n := n) j) ℂ) (embL (blkA (n := n) j)).contDiff.contDiffAt
    exact (ContinuousMultilinearMap.apply ℂ _ ℂ (fun i => embL (blkB (n := n) j) (w i))).contDiff.contDiffAt.comp _ h2
  unfold detD
  refine Finset.sum_congr rfl fun σA _ => ?_
  rw [iteratedFDeriv_sum_mul_eq_sum_smul _ _ _ _ _ (fun τ _ => hG _), ContinuousMultilinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  have hN' := hN (Matrix (Fin n) (Fin n) ℂ) (Matrix (blkA (n := n) j) (blkA (n := n) j) ℂ)
    (Matrix (blkB (n := n) j) (blkB (n := n) j) ℂ) ψ Ω hΩ hψ 0 h0 (embL (blkA (n := n) j)) (embL (blkB (n := n) j))
    (Fintype.card (blkA (n := n) j)) (Fintype.card (blkB (n := n) j))
    (fun i => single ((Fintype.equivFin (blkA (n := n) j)).symm i) (σA ((Fintype.equivFin (blkA (n := n) j)).symm i)) (1 : ℂ))
    (fun i => single ((Fintype.equivFin (blkB (n := n) j)).symm i) (τ ((Fintype.equivFin (blkB (n := n) j)).symm i)) (1 : ℂ))
  simp only [zero_add] at hN'
  erw [hN', append_eq j σA τ, iteratedFDeriv_comp_equiv_eq_of_contDiffOn hS ψ Ω hΩ hψ 0 h0 (epsE j) (Fintype.equivFin (Fin n)).symm (vv (piP j σA τ))]
  ring

theorem detDBlock_of (hA : IterAffine) (hS : IterSymm) (hN : IterNested) : DetDBlock := by
  intro m j c c' ψ Ω hΩ h0 hψ
  rw [lhs_eq hA j c c' ψ Ω hΩ h0 hψ, rhs_eq hA hS hN j ψ Ω hΩ h0 hψ]
  congr 1
  rw [← Finset.sum_filter, ← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun p _ => piP j p.1 p.2) ?_ ?_ ?_ ?_
  · intro p _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro r
    by_cases hr : r ∈ blkA (n := m) j
    · rw [piP, Equiv.Perm.subtypeCongr.left_apply _ _ hr]
      exact iff_of_true hr (p.1 ⟨r, hr⟩).2
    · rw [piP, Equiv.Perm.subtypeCongr.right_apply _ _ hr]
      exact iff_of_false hr ((eBq j).permCongr p.2 ⟨r, hr⟩).2
  · rintro ⟨a1, b1⟩ _ ⟨a2, b2⟩ _ h
    simp only at h
    refine Prod.ext (Equiv.ext fun ⟨x, hx⟩ => Subtype.ext ?_) (Equiv.ext fun ⟨x, hx⟩ => ?_)
    · have h1 := DFunLike.congr_fun h x
      rwa [piP, piP, Equiv.Perm.subtypeCongr.left_apply _ _ hx, Equiv.Perm.subtypeCongr.left_apply _ _ hx] at h1
    · have hx' : x ∉ blkA (n := m) j := by simpa [blkB] using hx
      have h1 := DFunLike.congr_fun h x
      rw [piP, piP, Equiv.Perm.subtypeCongr.right_apply _ _ hx', Equiv.Perm.subtypeCongr.right_apply _ _ hx'] at h1
      have he : (eBq j).symm ⟨x, hx'⟩ = ⟨x, hx⟩ := rfl
      have h2 := Subtype.ext h1
      rw [Equiv.permCongr_apply, Equiv.permCongr_apply, he] at h2
      exact (eBq j).injective h2
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    refine ⟨(σ.subtypePerm (fun x => (hσ x).symm), (eBq j).symm.permCongr
      (σ.subtypePerm (p := fun x => x ∉ blkA (n := m) j) (fun x => not_congr (hσ x).symm))), by simp, ?_⟩
    ext x
    by_cases hx : x ∈ blkA (n := m) j
    · simp only [piP]
      rw [Equiv.Perm.subtypeCongr.left_apply _ _ hx]
      rfl
    · simp only [piP]
      rw [Equiv.Perm.subtypeCongr.right_apply _ _ hx]
      rfl
  · intro p _
    simp only [piP, Equiv.Perm.sign_subtypeCongr, Equiv.Perm.sign_permCongr, Units.val_mul, Int.cast_mul]
    congr
    exact Subsingleton.elim _ _

end PositivityTheory.Rg.Sw.LVs.TC
