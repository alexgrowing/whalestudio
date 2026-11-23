import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreRoot
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreSupp

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

theorem star_inj_quot {M T : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup T] [Module ℂ T]
    (D : Module.End ℂ M) (D' : Module.End ℂ T) (π : M →ₗ[ℂ] T) (hπ : ∀ x, D' (π x) = π (D x))
    (Y : Submodule ℂ M) [FiniteDimensional ℂ Y] (hY : ∀ y ∈ Y, D y ∈ Y) (hi : ∀ y ∈ Y, D y = 0 → y = 0)
    {y : M} (hy : y ∈ Y) (h0 : D' (π y) = 0) : π y = 0 := by
  let Z : Submodule ℂ M := Y ⊓ LinearMap.ker π
  haveI : FiniteDimensional ℂ Z := Submodule.finiteDimensional_of_le (S₂ := Y) inf_le_left
  have hZ : ∀ z ∈ Z, D z ∈ Z := by
    intro z hz
    refine ⟨hY z hz.1, ?_⟩
    have h2 : π z = 0 := hz.2
    show π (D z) = 0
    rw [← hπ, h2, map_zero]
  have hinj : Function.Injective (D.restrict hZ) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    have h3 : D z.1 = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 hz)
    exact Subtype.ext (hi z.1 z.2.1 h3)
  have hsurj := LinearMap.injective_iff_surjective.1 hinj
  have hDy : D y ∈ Z := ⟨hY y hy, by
    show π (D y) = 0
    rw [← hπ, h0]⟩
  obtain ⟨z, hz⟩ := hsurj ⟨D y, hDy⟩
  have hz' : D z.1 = D y := congrArg Subtype.val hz
  have h4 : y - z.1 = 0 := hi _ (Y.sub_mem hy z.2.1) (by rw [map_sub, hz', sub_self])
  have h5 : y = z.1 := sub_eq_zero.1 h4
  rw [h5]
  exact z.2.2

theorem star_casK_mem {r s : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
    {ρ : Ix r s → Ix r s → Module.End ℂ M} {Y : Submodule ℂ M} (hY : KSt ρ Y) {y : M} (hy : y ∈ Y) :
    casK ρ y ∈ Y := by
  unfold casK
  rw [LinearMap.sum_apply]
  refine Y.sum_mem fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Y.sum_mem fun b _ => ?_
  split_ifs with h
  · exact hY a b h _ (hY b a (PI.FHS.sameBlock_symm h) _ hy)
  · simp

theorem star_trace {r s : ℕ} (a b : Ix r s) : (Eab a b).trace = if a = b then 1 else 0 := by
  unfold Eab
  split_ifs with h
  · subst h; simp
  · exact Matrix.trace_single_eq_of_ne _ _ _ h

theorem star_tw {p q r s : ℕ} (τ : ℂ) (a b : Ix r s) (g : Pol p q r s) :
    units (twAct p q r s τ) a b g =
      units (fockAct2 p q r s) a b g + (if a = b then τ else 0) • g := by
  unfold units
  rw [twAct_apply, star_trace]
  split_ifs <;> simp

theorem star_cas_mk {p q r s : ℕ} (c τ : ℂ) (g : Pol p q r s) :
    casK (units (thAct p q r s c τ)) (thMkC p q r s c g) =
      thMkC p q r s c (casK (units (twAct p q r s τ)) g) := by
  unfold casK
  simp only [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · simp only [Module.End.mul_apply, units, thAct_mk]
  · simp

theorem star_sb_refl {r s : ℕ} (a : Ix r s) : sameBlock a a := by
  cases a <;> trivial

theorem star_th {p q r s : ℕ} (c τ : ℂ) (c0 τ0 : ℚ) (hc : c = c0) (hτ : τ = τ0) (La : Ix r s → ℚ)
    (hC : CombOK p q c0 τ0 La) (d0 : ℕ) (hd : (d0 : ℚ) = degW (cPair r s) (fun _ : Ix p q => c0)) :
    StarK (thAct p q r s c τ) ((homog (Ix p q × Ix r s) d0).map (thMkC p q r s c))
      ((casW (fun x => La x + τ0) : ℚ) : ℝ) := by
  intro t ht x hx hcas
  let Y : Submodule ℂ (Pol p q r s) :=
    harm1 p q r s ⊓ polChi p q r s c ⊓ homog (Ix p q × Ix r s) (d0 + 2)
  haveI : FiniteDimensional ℂ (homog (Ix p q × Ix r s) (d0 + 2)) :=
    Module.Finite.iff_fg.2 (homogeneousSubmodule_fg _ ℂ (d0 + 2))
  haveI : FiniteDimensional ℂ Y :=
    Submodule.finiteDimensional_of_le (S₂ := homog (Ix p q × Ix r s) (d0 + 2)) inf_le_right
  have hYK : KSt (units (fockAct2 p q r s)) Y := fun a b hab y hy =>
    ⟨⟨harmonic_stable_second_action a b hab y hy.1.1, polChi_stable_second_action c _ hy.1.2⟩, homogeneous_stable_second_action (d0 + 2) a b hab y hy.2⟩
  have hYT : KSt (units (twAct p q r s τ)) Y := by
    intro a b hab y hy
    rw [star_tw]
    exact Y.add_mem (hYK a b hab y hy) (Y.smul_mem _ hy)
  have hgl : GlK (units (twAct p q r s τ)) := glK_of_lie (lie_tw p q r s τ)

  have hx1 : x ∈ (homog (Ix p q × Ix r s) (d0 + 2)).map (thMkC p q r s c) := by
    refine Submodule.span_le.2 ?_ hx
    rintro _ ⟨a, b, hab, _, ⟨g, hg, rfl⟩, rfl⟩
    have hne : a ≠ b := by
      rintro rfl
      exact hab (star_sb_refl a)
    have hlow : thMkC p q r s c (PI.FockOneDegW.lowOp (p := p) (q := q) a b g) = 0 := by
      by_cases h2 : d0 < 2
      · rw [low_homog_small a b h2 hg, map_zero]
      · obtain ⟨e, rfl⟩ : ∃ e, d0 = e + 2 := ⟨d0 - 2, by omega⟩
        refine th_small c c0 hc e ?_ (low_homog a b hg)
        rw [← hd]; push_cast; linarith
    refine ⟨_, second_action_add_lowering hab hg, ?_⟩
    rw [map_add, hlow, add_zero, thAct_mk, twAct_apply, star_trace, if_neg hne]
    simp
  obtain ⟨y, hy, rfl⟩ := th_next c c0 hc d0 hd hx1
  let D : Module.End ℂ (Pol p q r s) := casK (units (twAct p q r s τ)) - (t : ℂ) • 1
  have hD : ∀ g, D g = casK (units (twAct p q r s τ)) g - (t : ℂ) • g := fun g => rfl
  refine star_inj_quot D (casK (units (thAct p q r s c τ)) - (t : ℂ) • 1) (thMkC p q r s c) ?_ Y ?_ ?_ hy ?_
  · intro g
    rw [hD, map_sub, map_smul, ← star_cas_mk]
    rfl
  · intro g hg
    rw [hD]
    exact Y.sub_mem (star_casK_mem hYT hg) (Y.smul_mem _ hg)
  · intro g0 hg0 hDg0
    by_contra hne
    let U : Submodule ℂ (Pol p q r s) := Y ⊓ LinearMap.ker D
    haveI : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le (S₂ := Y) inf_le_left
    have hU0 : U ≠ ⊥ := by
      intro h
      have : g0 ∈ U := ⟨hg0, hDg0⟩
      rw [h] at this
      exact hne ((Submodule.mem_bot ℂ).1 this)
    have hUT : KSt (units (twAct p q r s τ)) U := by
      intro a b hab u hu
      refine ⟨hYT a b hab u hu.1, ?_⟩
      have h1 : D u = 0 := hu.2
      have h2 := LinearMap.congr_fun (cas_comm hgl hab) u
      simp only [Module.End.mul_apply] at h2
      show D _ = 0
      rw [hD] at h1 ⊢
      rw [h2, ← map_smul, ← map_sub, h1, map_zero]
    have hUK : KSt (units (fockAct2 p q r s)) U := by
      intro a b hab u hu
      have h1 := U.sub_mem (hUT a b hab u hu) (U.smul_mem (if a = b then τ else 0) hu)
      rw [star_tw, add_sub_cancel_right] at h1
      exact h1
    obtain ⟨ν, g, hgU, hw⟩ := hwExist2 U hU0 hUK
    obtain ⟨⟨a, b, hab, hroot⟩, hdeg⟩ := root_of_hw c c0 hc La hC.2.1 d0 hd hgU.1 hw
    have hlt := hC.2.2 ν a b hab hroot (dom2 hw) (supp2 hw) hdeg
    have hK := hwK_of_hwSub.1 hw.2
    have hKT : HwK (units (twAct p q r s τ)) (fun x => ν x + τ0) g := by
      refine ⟨fun a => ?_, fun a b h => ?_⟩
      · rw [star_tw, hK.1 a, if_pos rfl, hτ, ← add_smul]
        push_cast; rfl
      · rw [star_tw, hK.2 a b h, if_neg (PI.FockOneDegW.Core.posC_ne a b h)]
        simp
    have h1 : D g = 0 := hgU.2
    rw [hD, cas_hw hgl hKT, ← sub_smul, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · have h2 : ((casW (fun x => ν x + τ0) : ℚ) : ℝ) = t := by
        have h3 : (((casW (fun x => ν x + τ0) : ℚ) : ℝ) : ℂ) = (t : ℂ) := by
          rw [← sub_eq_zero.1 h1]; simp
        exact_mod_cast h3
      have h4 : ((casW (fun x => La x + τ0) : ℚ) : ℝ) + ((r : ℝ) + s) <
          ((casW (fun x => ν x + τ0) : ℚ) : ℝ) := by exact_mod_cast hlt
      linarith
    · exact hw.1 h1
  · show casK (units (thAct p q r s c τ)) _ - (t : ℂ) • _ = 0
    exact sub_eq_zero.2 hcas

end PositivityTheory.KReal

end
