import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult GlobalTheory.TensorHW GlobalTheory.BlockReps

noncomputable section

namespace GlobalTheory.CasimirBound

variable {R S : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
  {actW : Mat R S →ₗ[ℂ] Module.End ℂ W} {B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ}

lemma unitK_adj (hB : IsUnitary actW B) (a b : Ix R S) (x y : W) :
    B (unitK actW a b x) y = B x (unitK actW b a y) := by
  by_cases h : sameBlock a b
  · have h' : sameBlock b a := by cases a <;> cases b <;> simp_all [sameBlock]
    rw [unitK, unitK, if_pos h, if_pos h']
    exact hB.2.2 a b h x y
  · have h' : ¬ sameBlock b a := by cases a <;> cases b <;> simp_all [sameBlock]
    simp [unitK, h, h']

lemma casK_adj (hB : IsUnitary actW B) (x y : W) :
    B (casK actW x) y = B x (casK actW y) := by
  simp only [casK, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [unitK_adj hB, unitK_adj hB]

lemma finrank_map_add_inf_ker [FiniteDimensional ℂ W] (U : Submodule ℂ W) (f : Module.End ℂ W) :
    Module.finrank ℂ (U.map f) + Module.finrank ℂ (U ⊓ LinearMap.ker f : Submodule ℂ W) =
      Module.finrank ℂ U := by
  have h := (f.domRestrict U).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    ← Submodule.finrank_map_subtype_eq U, Submodule.map_comap_subtype] at h
  exact h

lemma finiteRing_sq_sub_mul_sq_eq_of_card [FiniteDimensional ℂ W] (hL : IsKLieAct actW)
    (hd : ∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub actW μ) (hB : IsUnitary actW B) (c₀ : ℚ) (n : ℕ) :
    ∀ U : Submodule ℂ W, Module.finrank ℂ U ≤ n → KStable actW U →
    (∀ (ν : Ix R S → ℚ) y, y ∈ U → IsHW actW ν y → c₀ < casVal ν) →
    ∀ x ∈ U, x ≠ 0 → (c₀ : ℝ) * (B x x).re < (B x (casK actW x)).re := by
  induction n with
  | zero =>
    intro U hU _ _ x hx h0
    have : U = ⊥ := Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hU)
    subst this
    exact absurd ((Submodule.mem_bot ℂ).1 hx) h0
  | succ n ih =>
    intro U hU hUs hc x hx h0
    obtain ⟨ν, v, hvU, hv⟩ := exists_hw hL hUs (fun w _ => hd w) ((Submodule.ne_bot_iff U).2 ⟨x, hx, h0⟩)
    set c : ℂ := ((casVal ν : ℚ) : ℂ) with hcdef
    set f : Module.End ℂ W := casK actW - c • 1 with hf
    set E : Submodule ℂ W := U ⊓ LinearMap.ker f with hE
    set U₂ : Submodule ℂ W := U.map f with hU₂
    have hstar : starRingEnd ℂ c = c := by rw [hcdef, map_ratCast]
    have hfadj : ∀ y z, B (f y) z = B y (f z) := by
      intro y z
      simp only [hf, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
        LinearMap.map_smulₛₗ₂, LinearMap.sub_apply, hstar, casK_adj hB, smul_eq_mul, LinearMap.smul_apply, map_smul]
    have hfU : ∀ u ∈ U, f u ∈ U := fun u hu => U.sub_mem (casK_mem hUs hu) (U.smul_mem _ hu)
    have hU₂U : U₂ ≤ U := Submodule.map_le_iff_le_comap.2 fun u hu => hfU u hu
    have hcomm : ∀ a b, sameBlock a b → ∀ y, actW (Eab a b) (f y) = f (actW (Eab a b) y) := by
      intro a b hab y
      rw [← Module.End.mul_apply, ← Module.End.mul_apply]
      congr 1
      exact ((casK_comm hL hab).sub_right ((Commute.one_right _).smul_right _)).eq
    have hU₂s : KStable actW U₂ := by
      intro Z hZ w hw
      obtain ⟨u, hu, rfl⟩ := hw
      refine kc_ind actW U₂ (f u) (fun a b hab => ?_) hZ
      rw [hcomm a b hab]
      exact ⟨_, hUs _ (isKC_Eab hab) u hu, rfl⟩
    have horth : ∀ e ∈ E, ∀ z ∈ U₂, B e z = 0 := by
      intro e he z hz
      obtain ⟨u, -, rfl⟩ := hz
      rw [← hfadj, LinearMap.mem_ker.1 he.2, map_zero, LinearMap.zero_apply]
    have hdisj : E ⊓ U₂ = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Submodule.mem_bot]
      by_contra hz0
      have := hB.2.1 z hz0
      rw [horth z hz.1 z hz.2] at this
      simp at this
    have hdim : Module.finrank ℂ U₂ + Module.finrank ℂ E = Module.finrank ℂ U :=
      finrank_map_add_inf_ker U f
    have hsup : E ⊔ U₂ = U := by
      have h1 : Module.finrank ℂ (E ⊔ U₂ : Submodule ℂ W) + Module.finrank ℂ (E ⊓ U₂ : Submodule ℂ W) =
          Module.finrank ℂ E + Module.finrank ℂ U₂ := Submodule.finrank_sup_add_finrank_inf_eq E U₂
      rw [hdisj, finrank_bot] at h1
      exact Submodule.eq_of_le_of_finrank_eq (sup_le inf_le_left hU₂U) (by omega)
    have hvE : v ∈ E := ⟨hvU, by simp [hf, casK_hw hL hv.2, hcdef]⟩
    have hlt : Module.finrank ℂ U₂ < Module.finrank ℂ U := by
      apply Submodule.finrank_lt_finrank_of_lt
      refine lt_of_le_of_ne hU₂U fun h => hv.1 ?_
      have : v ∈ E ⊓ U₂ := ⟨hvE, h ▸ hvU⟩
      rwa [hdisj, Submodule.mem_bot] at this
    have hcv := hc ν v hvU hv
    obtain ⟨e, he, z, hz, rfl⟩ := Submodule.mem_sup.1 (hsup ▸ hx : x ∈ E ⊔ U₂)
    have hce : casK actW e = c • e := by
      have := LinearMap.mem_ker.1 he.2
      simp only [hf, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at this
      exact sub_eq_zero.1 this
    have hze : B z e = 0 := by rw [← hB.1, horth e he z hz, star_zero]
    have hcz : B e (casK actW z) = 0 := by
      rw [← casK_adj hB, hce, LinearMap.map_smulₛₗ₂, horth e he z hz, smul_zero]
    have hIH : z ≠ 0 → (c₀ : ℝ) * (B z z).re < (B z (casK actW z)).re := fun hz0 =>
      ih U₂ (by omega) hU₂s (fun ν y hy => hc ν y (hU₂U hy)) z hz hz0
    have ex1 : B (e + z) (e + z) = B e e + B z z := by
      simp only [map_add, LinearMap.add_apply, horth e he z hz, hze]; ring
    have ex2 : B (e + z) (casK actW (e + z)) = c * B e e + B z (casK actW z) := by
      simp only [map_add, LinearMap.add_apply, hce, LinearMap.map_smul, hcz, hze, smul_eq_mul]; ring
    have hcr : (c * B e e).re = (casVal ν : ℝ) * (B e e).re := by
      simp [hcdef, Complex.mul_re]
    have hc' : (c₀ : ℝ) < (casVal ν : ℝ) := by exact_mod_cast hcv
    rw [ex1, ex2, Complex.add_re, Complex.add_re, hcr]
    by_cases he0 : e = 0
    · subst he0
      have hz0 : z ≠ 0 := by simpa using h0
      have := hIH hz0
      simp only [map_zero, LinearMap.zero_apply, Complex.zero_re, mul_zero, zero_add]
      exact this
    · have hpos := hB.2.1 e he0
      have h2 : (c₀ : ℝ) * (B z z).re ≤ (B z (casK actW z)).re := by
        by_cases hz0 : z = 0
        · subst hz0; simp
        · exact (hIH hz0).le
      nlinarith

theorem casimir_form_gt : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (c₀ : ℚ), IsKLieAct actW →
    (∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub actW μ) → IsUnitary actW B → ∀ U : Submodule ℂ W, KStable actW U →
    (∀ (ν : Ix R S → ℚ) y, y ∈ U → IsHW actW ν y → c₀ < GlobalTheory.BlockReps.casVal ν) →
    ∀ x ∈ U, x ≠ 0 → (c₀ : ℝ) * (B x x).re < (B x (GlobalTheory.BlockReps.casK actW x)).re := by
  intro R S W _ _ _ actW B c₀ hL hd hB U hU hc
  exact finiteRing_sq_sub_mul_sq_eq_of_card hL hd hB c₀ _ U le_rfl hU hc

end GlobalTheory.CasimirBound
