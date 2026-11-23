import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ManyEdges

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

theorem w_ne_zero {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (hS : HidaSetting p n' W Qq O Kf ι σ j w) :
    algebraMap O Kf w ≠ 0 := by
  intro h
  have := hS.frac_alt
  have h2 : algebraMap O Kf ((p : ℕ) : O) = 0 := by
    rw [← hS.w_sq, map_pow, h, zero_pow two_ne_zero]
  have h3 : ι (algebraMap W Qq ((p : ℕ) : W)) = 0 := by
    rw [hS.ι_comp, map_natCast j]
    exact h2
  have h4 : algebraMap W Qq ((p : ℕ) : W) = 0 := (map_eq_zero ι).mp h3
  have h5 : ((p : ℕ) : W) = 0 := IsFractionRing.injective W Qq (by rw [h4, map_zero])
  exact hS.p_unif.ne_zero h5

section Scale

variable {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X] [Module O X]
  [IsScalarTower O Kf X]

theorem mem_scale {c : Kf} {M : Submodule O X} {x : X} : x ∈ scale c M ↔ ∃ y ∈ M, c • y = x := by
  simp only [scale, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]

theorem scale_neg_mono (w : O) (hw : algebraMap O Kf w ≠ 0) {s t : ℕ} (hst : s ≤ t) (M : Submodule O X) :
    scale (algebraMap O Kf w ^ (-(s : ℤ))) M ≤ scale (algebraMap O Kf w ^ (-(t : ℤ))) M := by
  intro x hx
  rw [mem_scale] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨w ^ (t - s) • y, M.smul_mem _ hy, ?_⟩
  rw [← algebraMap_smul Kf (w ^ (t - s)) y, smul_smul, map_pow, ← zpow_natCast, ← zpow_add₀ hw,
    show -(t : ℤ) + ((t - s : ℕ) : ℤ) = -(s : ℤ) by omega]

theorem scale_pos_le (w : O) (c : ℕ) (M : Submodule O X) : scale (algebraMap O Kf w ^ (c : ℤ)) M ≤ M := by
  intro x hx
  rw [mem_scale] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [zpow_natCast, ← map_pow, algebraMap_smul]
  exact M.smul_mem _ hy

end Scale

theorem ValLe.mono {O Kf : Type*} [CommRing O] [Field Kf] [Algebra O Kf] {π : O} {D D' : ℕ} {x : Kf}
    (h : ValLe π D x) (hD : D ≤ D') : ValLe π D' x := by
  obtain ⟨a, b, hx, hab⟩ := h
  refine ⟨a, b * π ^ (D' - D), hx, ?_⟩
  rw [← mul_assoc, hab, ← pow_add, Nat.add_sub_cancel' hD]

theorem asm : Asm := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS m r lam0 t D κ cStar L E nE hE hF hcard
  classical
  have hw := w_ne_zero hS
  unfold EdgeFam at hF
  choose tS tT D1 htS htT hD1 F hF1 hF2 hF3 using hF
  unfold SrcTests
  refine ⟨E, nE, fun e => if h : e ∈ E then F e h else fun _ => 0, hE, ?_, ?_, ?_, hcard⟩
  · intro e he i
    simp only [dif_pos he]
    unfold Nsrc
    refine Submodule.mem_inf.mpr ⟨scale_neg_mono w hw (htS e he) _ (hF1 e he i).1, ?_⟩
    refine (Submodule.mem_iInf _).mpr fun e' => (Submodule.mem_iInf _).mpr fun he' => ?_
    by_cases hee : e' = e
    · subst hee
      exact (hF1 e' he i).2
    · exact scale_pos_le w cStar _ (hF2 e he i e' he'.1 he'.2 hee)
  · intro e he i e' he' hsrc hne
    simp only [dif_pos he]
    exact hF2 e he i e' he' hsrc hne
  · intro e he c hc
    obtain ⟨G, hG1, hG2, hG3, hG4⟩ := hF3 e he c hc
    refine ⟨G, ?_, ?_, ?_⟩
    · rw [(hE e he).2] at hG1
      unfold Ntgt
      refine Submodule.mem_inf.mpr ⟨scale_neg_mono w hw (htT e he) _ hG1, ?_⟩
      refine (Submodule.mem_iInf _).mpr fun e' => (Submodule.mem_iInf _).mpr fun he' => ?_
      by_cases hee : e' = e
      · subst hee
        exact hG2
      · exact scale_pos_le w cStar _ (hG3 e' he'.1 (he'.2.trans (hE e he).2.symm) hee)
    · simp only [dif_pos he]
      exact ValLe.mono hG4 (hD1 e he)
    · intro e' he' hne
      exact hG3 e' (hE e' he').1 ((hE e' he').2.trans (hE e he).2.symm) hne

end Formalism.MainNotions.Pf14
