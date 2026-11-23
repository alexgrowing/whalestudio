import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqualCoeffsOfSymmetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeRenameInvariant

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

namespace GlobalTheory.Mean4.EqualCoeff

section General

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

omit [DecidableEq ι] in
theorem rename_linRoot (σ : Equiv.Perm ι) (u : ι → Fin N → ℝ) :
    rename (Prod.map σ id) (linRoot (fun τ => u (σ τ))) = linRoot u := by
  unfold linRoot
  rw [map_neg, map_sum]
  congr 1
  rw [← Equiv.sum_comp (σ.prodCongr (Equiv.refl (Fin N))) (fun x => C (u x.1 x.2) * X x)]
  refine Finset.sum_congr rfl fun x _ => ?_
  obtain ⟨a, b⟩ := x
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem ev_comp (σ : Equiv.Perm ι) (u : ι → Fin N → ℝ) (P : Pol ι N) :
    ev (fun τ => u (σ τ)) P = ev u (rename (fun x : ι × Fin N => (σ x.1, x.2)) P) := by
  unfold ev
  rw [eval_rename]
  rfl

omit [DecidableEq ι] in
theorem linRoot_isHomogeneous (u : ι → Fin N → ℝ) : (linRoot u).IsHomogeneous 1 := by
  unfold linRoot
  exact (IsHomogeneous.sum _ _ _ fun x _ => (isHomogeneous_X _ _).C_mul _).neg

theorem flagDeg_comp (σ : Equiv.Perm ι) (u : ι → Fin N → ℝ) :
    flagDeg ι N (fun τ => u (σ τ)) = flagDeg ι N u := by
  unfold flagDeg
  rw [← GlobalTheory.FlagPerm.degFl_rename_perm ι N σ, map_pow, rename_linRoot]

omit [DecidableEq ι] in
theorem ev_invForm (j : ℕ) (al be : ι → ℝ) (u : ι → Fin N → ℝ) :
    ev u (invForm j al be) = ∑ τ, (al τ * ev u (pLow j τ 1) + be τ * ev u (pHigh j τ 1)) := by
  unfold ev invForm
  simp [map_sum]

theorem average (j d : ℕ) (G : Subgroup (Equiv.Perm ι)) [MulAction.IsPretransitive G ι]
    (φ hh : Pol ι N →ₗ[ℝ] ℝ) (v k e : ℝ)
    (hφ : ∀ σ ∈ G, ∀ F : Pol ι N, F.IsHomogeneous d → φ (rename (Prod.map σ id) F) = φ F)
    (hhh : ∀ σ ∈ G, ∀ F : Pol ι N, F.IsHomogeneous d → hh (rename (Prod.map σ id) F) = hh F)
    (al be : ι → ℝ) (E : Pol ι N) (hE : E.IsHomogeneous d) (hc : CoefLe E e)
    (h : ∀ u : ι → Fin N → ℝ, φ (linRoot u ^ d) =
      v * (hh (linRoot u ^ d) + k * flagDeg ι N u * ev u (invForm j al be)) + ev u E) :
    ∃ (a b : ℝ) (E' : Pol ι N), E'.IsHomogeneous d ∧ CoefLe E' e ∧ ∀ u : ι → Fin N → ℝ, φ (linRoot u ^ d) =
      v * (hh (linRoot u ^ d) + k * flagDeg ι N u * ev u (invForm j (fun _ => a) (fun _ => b))) + ev u E' := by
  obtain ⟨a, ha⟩ := sum_inv_smul_const (G := G) al
  obtain ⟨b, hb⟩ := sum_inv_smul_const (G := G) be
  set n : ℝ := (Fintype.card G : ℝ) with hn
  have hpos : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  refine ⟨a / n, b / n, C n⁻¹ * ∑ g : G, rename (fun x : ι × Fin N => ((g : Equiv.Perm ι) x.1, x.2)) E, ?_, ?_, ?_⟩
  · exact (IsHomogeneous.sum _ _ _ fun g _ => hE.rename_isHomogeneous).C_mul _
  · intro m
    rw [coeff_C_mul, coeff_sum, abs_mul, abs_of_pos (inv_pos.mpr hpos), inv_mul_le_iff₀ hpos]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun (g : G) _ => hc.rename_perm (g : Equiv.Perm ι) m).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn]
  · intro u
    have key : ∀ g : G, φ (linRoot u ^ d) =
        v * (hh (linRoot u ^ d) + k * flagDeg ι N u *
          ev u (invForm j (fun τ => al (g⁻¹ • τ)) (fun τ => be (g⁻¹ • τ)))) +
          ev u (rename (fun x : ι × Fin N => ((g : Equiv.Perm ι) x.1, x.2)) E) := by
      intro g
      have h1 := h (fun τ => u ((g : Equiv.Perm ι) τ))
      have hom : (linRoot (fun τ => u ((g : Equiv.Perm ι) τ)) ^ d).IsHomogeneous d := by
        simpa using (linRoot_isHomogeneous (fun τ => u ((g : Equiv.Perm ι) τ))).pow d
      rw [← hφ g g.2 _ hom, ← hhh g g.2 _ hom, map_pow, rename_linRoot, flagDeg_comp, ev_comp, ev_comp,
        rename_perm_invForm] at h1
      exact h1
    have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset G)) rfl fun g _ => key g
    have hinv : ∑ g : G, ev u (invForm j (fun τ => al (g⁻¹ • τ)) (fun τ => be (g⁻¹ • τ))) =
        n * ev u (invForm j (fun _ => a / n) (fun _ => b / n)) := by
      simp only [ev_invForm]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ha, hb]
      field_simp
    have hev : ev u (C n⁻¹ * ∑ g : G, rename (fun x : ι × Fin N => ((g : Equiv.Perm ι) x.1, x.2)) E) =
        n⁻¹ * ∑ g : G, ev u (rename (fun x : ι × Fin N => ((g : Equiv.Perm ι) x.1, x.2)) E) := by
      unfold ev
      rw [map_mul, eval_C, map_sum]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, hinv,
      Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, ← hn] at hs
    rw [hev]
    refine mul_left_cancel₀ hpos.ne' ?_
    rw [hs, mul_add, mul_add n, mul_inv_cancel_left₀ hpos.ne']
    ring

def stab {κ : Type} (Φ : κ → Pol ι N →ₗ[ℝ] ℝ) (p : κ → Prop) : Subgroup (Equiv.Perm ι) where
  carrier := {σ | ∀ B, p B → ∀ F : Pol ι N, Φ B (rename (Prod.map σ id) F) = Φ B F}
  one_mem' := by
    intro B _ F
    simp
  mul_mem' := by
    intro σ ρ hσ hρ B hB F
    have : rename (Prod.map (σ * ρ : Equiv.Perm ι) id) F = rename (Prod.map σ id) (rename (Prod.map ρ id) F) := by
      rw [rename_rename]; rfl
    rw [this, hσ B hB, hρ B hB]
  inv_mem' := by
    intro σ hσ B hB F
    have : rename (Prod.map σ id) (rename (Prod.map (σ⁻¹ : Equiv.Perm ι) id) F) = F := by
      rw [rename_rename]
      have e : (Prod.map σ id ∘ Prod.map (σ⁻¹ : Equiv.Perm ι) id : ι × Fin N → ι × Fin N) = id := by
        funext x; obtain ⟨a, b⟩ := x; simp
      rw [e, rename_id_apply]
    rw [← hσ B hB, this]

end General

theorem shapeC_of_shapeT : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (Φ : ℝ → Fn Y) (hh : Fn Y), 0 < Y.vol → Relabel Φ → FlagHt D.what₂.Tau Y.N hh → ShapeT Φ hh → ShapeC Φ hh := by
  intro D Y Φ hh _ hrel hfl hT
  obtain ⟨C, B₁, hT⟩ := hT
  refine ⟨C, max B₁ 2, fun B hB => ?_⟩
  obtain ⟨al, be, E, hE, hc, h⟩ := hT B (le_trans (le_max_left _ _) hB)
  have hB2 : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast le_trans (le_max_right _ _) hB
  have : MulAction.IsPretransitive (stab Φ (fun B : ℝ => 2 ≤ B)) D.what₂.Tau := ⟨fun τ τ' => by
    obtain ⟨σ, h1, h2⟩ := hrel τ τ'
    exact ⟨⟨σ, h2⟩, h1⟩⟩
  exact average Y.j (dimY Y + 1) (stab Φ (fun B : ℝ => 2 ≤ B)) (Φ B) hh Y.vol ((dimY Y : ℝ) + 1) _
    (fun σ hσ F _ => hσ B hB2 F) (fun σ _ F hF => hfl.2.2.2 σ F hF) al be E hE hc h

end GlobalTheory.Mean4.EqualCoeff
