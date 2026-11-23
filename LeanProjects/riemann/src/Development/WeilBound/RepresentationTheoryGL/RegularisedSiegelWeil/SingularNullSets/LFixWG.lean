import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWF

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open scoped Matrix NNReal TensorProduct
open IsDedekindDomain NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.AdelicU
  GlobalTheory.MixModel GlobalTheory.StdUnn GlobalTheory.Doubling Filter MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L.LFixW

variable {D : D7} {n : ℕ}

theorem adj_neg_one : adj (-1 : Mx D n n) = -1 := by
  rw [adj_neg]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h; simp [adj]
  · simp [adj, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]

theorem intOff_neg {S : Finset (Pl D)} {a b : ℕ} (x : Mx D a b) : IntOff S (-x) ↔ IntOff S x := by
  rw [intOff_iff, intOff_iff]
  refine ⟨fun h i j => ?_, fun h i j => (h i j).neg⟩
  have := (h i j).neg
  rwa [Matrix.neg_apply, neg_neg] at this

theorem absA_ne (u : (AE D)ˣ) : absA D u ≠ 0 := by
  intro h0
  have := map_mul (absA D) u u⁻¹
  rw [mul_inv_cancel, map_one, h0, zero_mul] at this
  exact zero_ne_one this.symm

theorem npow_ne (r : ℝ≥0) (hr : r ≠ 0) (t : ℂ) : npow r t ≠ 0 := by
  intro h
  have := (Complex.cpow_eq_zero_iff _ _).1 h
  exact hr (by exact_mod_cast this.1)

theorem fixWc (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → ∀ (n : ℕ) (θ : InfFam D) (μ : Measure (Mx D V.rank n))
      (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (χ : (AE D)ˣ →* Circle), IsWeilSch ψ χ θ V μ ω →
      μ.IsAddHaarMeasure → ∀ w u : G D n, IsW w → IsN u → u ∈ KOff D n S → ∀ Φ : schwartzA θ V.rank n,
        Good S e Φ.1 → ω (w * u * w⁻¹) Φ = Φ := by
  classical
  obtain ⟨S₁, hS₁⟩ := fixN V hψ
  obtain ⟨S₂, hS₂⟩ := ft_supp V.gram (gram_det_ne V) hψ
  refine ⟨S₁ ∪ S₂, fun S hS e he n θ μ ω χ hω hμ w u hw hNu hu Φ hΦ => ?_⟩
  set Φ' := ω (w⁻¹ * w⁻¹) Φ with hΦ'
  have hmw : mat (w * w) = blk4 ((-1 : GL (Fin n) (AE D)) : Mx D n n) 0 0
      (adj (((-1 : GL (Fin n) (AE D))⁻¹ : GL (Fin n) (AE D)) : Mx D n n)) := by
    rw [LFixTh.mat_mul, hw, block_matrix_mul_comm_ring, inv_neg, inv_one, Units.val_neg, Units.val_one, adj_neg_one]
    simp
  set c : ℂ := (χ (Matrix.GeneralLinearGroup.det (-1 : GL (Fin n) (AE D))) : ℂ) *
    npow (absA D (Matrix.GeneralLinearGroup.det (-1 : GL (Fin n) (AE D)))) ((V.rank : ℂ) / 2) with hcdef
  have hc0 : c ≠ 0 := mul_ne_zero (Circle.coe_ne_zero _) (npow_ne _ (absA_ne _) _)
  have hww : ω (w * w) Φ' = Φ := by
    rw [hΦ', ← Module.End.mul_apply, ← map_mul]
    have : w * w * (w⁻¹ * w⁻¹) = 1 := by group
    rw [this, map_one, Module.End.one_apply]
  have hc : ∀ y, Φ.1 y = c * Φ'.1 (-y) := by
    intro y
    have h := hω.levi (w * w) (-1) hmw Φ' y
    rw [hww] at h
    rw [h, Units.val_neg, Units.val_one, Matrix.mul_neg, Matrix.mul_one]
  have hc' : ∀ y, Φ'.1 y = c⁻¹ * Φ.1 (-y) := by
    intro y
    rw [hc (-y), neg_neg, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hgood : Good S e Φ'.1 := by
    refine good_of he (fun y hy => ?_) (fun y z hz => ?_)
    · rw [hc', good_supp hΦ (fun h => hy ((intOff_neg y).1 h)), mul_zero]
    · rw [hc', hc', neg_add, good_shift he hΦ (-y) (z := -z) (fun i j => (hz i j).neg)]
  have hsupp : ∀ x, ¬ IntOff S x → (ω w⁻¹ Φ).1 x = 0 := by
    intro x hx
    have e1 : ω w⁻¹ Φ = ω w Φ' := by
      rw [hΦ', ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    rw [e1, hω.weyl w hw Φ' x]
    exact hS₂ S (fun v h => hS (Finset.mem_union_right _ h)) e he n μ hμ Φ'.1 hgood x hx
  have hfix := hS₁ S (fun v h => hS (Finset.mem_union_left _ h)) n θ μ ω χ hω u hu hNu (ω w⁻¹ Φ) hsupp
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfix, ← Module.End.mul_apply, ← map_mul,
    mul_inv_cancel, map_one, Module.End.one_apply]

end PositivityTheory.Rg.Rsw.L.LFixW

end
