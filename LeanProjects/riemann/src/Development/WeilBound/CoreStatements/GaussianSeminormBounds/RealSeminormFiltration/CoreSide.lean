import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreStar
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreGen

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

namespace GoodSideLattices

variable {p q r s : ℕ}

theorem sd_trace_Eab (a b : Ix r s) : (Eab a b).trace = if a = b then 1 else 0 := by
  unfold Eab
  split_ifs with h
  · subst h
    simp [Matrix.trace]
  · simp [Matrix.trace, Matrix.single, h, Ne.symm h]

theorem sd_sb_trans {a b c : Ix r s} (h1 : sameBlock a b) (h2 : sameBlock b c) : sameBlock a c := by
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> simp_all [sameBlock]

theorem sd_sb_symm {a b : Ix r s} (h1 : sameBlock a b) : sameBlock b a := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]

theorem sd_sb_refl (a : Ix r s) : sameBlock a a := by
  rcases a with a | a <;> simp [sameBlock]

def sd_hA (p q r s d : ℕ) : Submodule ℂ (FV p q r s) := homog (Ix p q × Ix r s) d

instance sd_hA_fd (d : ℕ) : FiniteDimensional ℂ (sd_hA p q r s d) :=
  Module.Finite.iff_fg.2 (homogeneousSubmodule_fg (Ix p q × Ix r s) ℂ d)

def sd_fvTw (p q r s : ℕ) (τ : ℂ) : Mat r s →ₗ[ℂ] Module.End ℂ (FV p q r s) := twAct p q r s τ

theorem sd_fvTw_apply (τ : ℂ) (W : Mat r s) (u : FV p q r s) :
    sd_fvTw p q r s τ W u = fvAct2 p q r s W u + (τ * W.trace) • u :=
  twAct_apply p q r s τ W u

private theorem isHomogeneous_X_mul_pderiv {σ : Type} (i j : σ) {n : ℕ} {φ : MvPolynomial σ ℂ}
    (h : φ.IsHomogeneous n) : (X i * pderiv j φ).IsHomogeneous n := by
  have e : X i * pderiv j φ = pderiv j (X i * φ) - pderiv j (X i) * φ := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
  rw [e, ← mem_homogeneousSubmodule]
  refine Submodule.sub_mem _ ?_ ?_
  · rw [mem_homogeneousSubmodule]
    simpa using ((isHomogeneous_X (R := ℂ) i).mul h).pderiv (i := j)
  · rw [mem_homogeneousSubmodule]
    by_cases hij : j = i
    · subst hij
      simpa using h
    · rw [pderiv_X_of_ne (Ne.symm hij), zero_mul]
      exact isHomogeneous_zero _ _ _

private theorem omE_mem_homogeneousSubmodule_of_sameBlock {d : ℕ} (i : Ix p q) {a b : Ix r s} (hab : sameBlock a b)
    {x : Pol p q r s} (hx : x ∈ homogeneousSubmodule (Ix p q × Ix r s) ℂ d) :
    omE (i, a) (i, b) x ∈ homogeneousSubmodule (Ix p q × Ix r s) ℂ d := by
  have hl : linePos (i, a) = linePos (i, b) := by
    rcases i with i | i <;> rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock, linePos]
  rw [mem_homogeneousSubmodule] at hx
  simp only [omE, LinearMap.add_apply, Module.End.mul_apply]
  refine Submodule.add_mem _ ?_ ?_
  · simp only [raiB, lowB, ← hl]
    split_ifs with h
    · rw [LinearMap.mulLeft_apply, mem_homogeneousSubmodule]
      exact isHomogeneous_X_mul_pderiv _ _ hx
    · rw [LinearMap.neg_apply, LinearMap.mulLeft_apply]
      refine Submodule.neg_mem _ ?_
      rw [mem_homogeneousSubmodule]
      simpa using ((isHomogeneous_X (R := ℂ) (i, b)).mul hx).pderiv (i := (i, a))
  · split_ifs
    · exact Submodule.smul_mem _ _ ((mem_homogeneousSubmodule _ _).2 hx)
    · exact Submodule.zero_mem _

theorem sd_fvTw_mem (τ : ℂ) (d : ℕ) {a b : Ix r s} (hab : sameBlock a b) :
    ∀ x ∈ sd_hA p q r s d, sd_fvTw p q r s τ (Eab a b) x ∈ sd_hA p q r s d := by
  intro x hx
  rw [sd_fvTw_apply]
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ hx)
  have e := fockAct2_unit (p := p) (q := q) a b (show Pol p q r s from x)
  have key : (fockAct2 p q r s (Eab a b)) (show Pol p q r s from x) ∈
      homogeneousSubmodule (Ix p q × Ix r s) ℂ d := by
    rw [e]
    exact Submodule.sum_mem _ (fun i _ => omE_mem_homogeneousSubmodule_of_sameBlock i hab hx)
  exact key

def sd_rhoA (p q r s : ℕ) (τ : ℂ) (d : ℕ) (a b : Ix r s) : Module.End ℂ (sd_hA p q r s d) :=
  if h : sameBlock a b then (sd_fvTw p q r s τ (Eab a b)).restrict (sd_fvTw_mem τ d h) else 0

theorem sd_rhoA_coe (τ : ℂ) (d : ℕ) {a b : Ix r s} (hab : sameBlock a b) (u : sd_hA p q r s d) :
    (sd_rhoA p q r s τ d a b u : FV p q r s) = sd_fvTw p q r s τ (Eab a b) u := by
  unfold sd_rhoA
  rw [dif_pos hab]
  rfl

theorem sd_rhoA_adj (τ : ℂ) (τ0 : ℚ) (hτ : τ = τ0) (d : ℕ) : AdjK (sd_rhoA p q r s τ d) := by
  intro a b hab u v
  rw [Submodule.coe_inner, Submodule.coe_inner, sd_rhoA_coe τ d hab,
    sd_rhoA_coe τ d (sd_sb_symm hab), sd_fvTw_apply, sd_fvTw_apply, inner_add_left,
    inner_add_right, inner_smul_left, inner_smul_right, adj2 p q r s a b, sd_trace_Eab,
    sd_trace_Eab]
  by_cases h : a = b
  · subst h
    simp [epsB, hab, hτ]
  · simp [epsB, hab, hτ, h, Ne.symm h]

private theorem Eab_mul_Eab (a b c e : Ix r s) :
    Eab a b * Eab c e = if b = c then Eab a e else 0 := by
  unfold Eab
  split_ifs with h
  · subst h
    simp
  · simp [h]

theorem sd_rhoA_gl (τ : ℂ) (d : ℕ) : GlK (sd_rhoA p q r s τ d) := by
  intro a b c e hab hce
  have hM : Eab a b * Eab c e - Eab c e * Eab a b =
      (if b = c then Eab a e else 0) - (if e = a then Eab c b else 0) := by
    rw [Eab_mul_Eab, Eab_mul_Eab]
  have hL : IsLie (sd_fvTw p q r s τ) := lie_tw p q r s τ
  have hu : ∀ u : FV p q r s,
      sd_fvTw p q r s τ (Eab a b) (sd_fvTw p q r s τ (Eab c e) u) -
        sd_fvTw p q r s τ (Eab c e) (sd_fvTw p q r s τ (Eab a b) u) =
      sd_fvTw p q r s τ ((if b = c then Eab a e else 0) - (if e = a then Eab c b else 0)) u := by
    intro u
    rw [← hM, ← hL]
    rfl
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  rw [LinearMap.sub_apply, Submodule.coe_sub, Module.End.mul_apply, Module.End.mul_apply,
    sd_rhoA_coe τ d hab, sd_rhoA_coe τ d hce, sd_rhoA_coe τ d hce, sd_rhoA_coe τ d hab, hu]
  have s1 : b = c → sameBlock a e := fun h1 => sd_sb_trans hab (by rw [h1]; exact hce)
  have s2 : e = a → sameBlock c b := fun h2 => sd_sb_trans hce (by rw [h2]; exact hab)
  split_ifs with h1 h2 h2
  · rw [map_sub, LinearMap.sub_apply, LinearMap.sub_apply, Submodule.coe_sub,
      sd_rhoA_coe τ d (s1 h1), sd_rhoA_coe τ d (s2 h2)]
  · rw [sub_zero, sub_zero, sd_rhoA_coe τ d (s1 h1)]
  · rw [zero_sub, zero_sub, map_neg, LinearMap.neg_apply, LinearMap.neg_apply,
      Submodule.coe_neg, sd_rhoA_coe τ d (s2 h2)]
  · simp

def sd_fvMk (p q r s : ℕ) (c : ℂ) : FV p q r s →ₗ[ℂ] ThC p q r s c := thMkC p q r s c

theorem sd_mem_genG {M : Type} [AddCommGroup M] [Module ℂ M] (act : Mat r s →ₗ[ℂ] Module.End ℂ M)
    (S : Submodule ℂ M) : S ≤ genG act S ∧ ∀ W, ∀ x ∈ genG act S, act W x ∈ genG act S := by
  refine ⟨fun x hx => ?_, fun W x hx => ?_⟩
  · exact Submodule.mem_sInf.2 (fun N hN => hN.1 hx)
  · rw [genG, Submodule.mem_sInf] at hx ⊢
    intro N hN
    exact hN.2 W x (hx N hN)

end GoodSideLattices

open GoodSideLattices in
theorem side_of {p q r s : ℕ} (c τ : ℂ) (c0 τ0 : ℚ) (hc : c = c0) (hτ : τ = τ0) (La : Ix r s → ℚ)
    (hC : CombOK p q c0 τ0 La) (hN : Nontrivial (ThC p q r s c)) :
    Side (fun x => La x + τ0) (ThC p q r s c) (thAct p q r s c τ) := by
  obtain ⟨d0, f0, hd0, hf0, hhw, hmin⟩ := exists_gen c c0 hc La hC.1 hC.2.1
  have hne : ∀ a b : Ix r s, posC a b → a ≠ b := by
    rintro a b h rfl
    rcases a with a | a <;> simp [posC] at h
  let f : sd_hA p q r s d0 := ⟨f0, hf0⟩
  let ι : sd_hA p q r s d0 →ₗ[ℂ] ThC p q r s c := (sd_fvMk p q r s c).comp (sd_hA p q r s d0).subtype
  have hι : ∀ u : sd_hA p q r s d0, ι u = thMkC p q r s c (show Pol p q r s from (u : FV p q r s)) :=
    fun u => rfl
  refine ⟨lie_th p q r s c τ, hN, sd_hA p q r s d0, inferInstance, inferInstance, inferInstance,
    sd_rhoA p q r s τ d0, ι, f, sd_rhoA_adj τ τ0 hτ d0, sd_rhoA_gl τ d0, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro a
    apply Subtype.ext
    rw [sd_rhoA_coe τ d0 (sd_sb_refl a), sd_fvTw_apply, sd_trace_Eab, if_pos rfl]
    have h1 : fvAct2 p q r s (Eab a a) (f : FV p q r s) = ((La a : ℚ) : ℂ) • (f : FV p q r s) :=
      hhw.1 a
    rw [h1, Submodule.coe_smul, hτ]
    push_cast
    rw [mul_one, add_smul]
  · intro a b hab
    by_cases hs : sameBlock a b
    · apply Subtype.ext
      rw [sd_rhoA_coe τ d0 hs, sd_fvTw_apply, sd_trace_Eab, if_neg (hne a b hab)]
      have h1 : fvAct2 p q r s (Eab a b) (f : FV p q r s) = 0 := hhw.2 a b hab
      rw [h1]
      simp
    · simp [sd_rhoA, hs]
  · intro a b hab u
    rw [hι, hι, thAct_mk, sd_rhoA_coe τ d0 hab]
    rfl
  · set N := genG (thAct p q r s c τ) (ℂ ∙ ι f) with hNdef
    have hst := (sd_mem_genG (thAct p q r s c τ) (ℂ ∙ ι f)).2
    refine th_gen_harm c τ c0 hc N ?_ hst
    rw [Submodule.map_le_iff_le_comap]
    apply hmin
    · show thMkC p q r s c f0 ∈ N
      exact (sd_mem_genG (thAct p q r s c τ) (ℂ ∙ ι f)).1 (Submodule.mem_span_singleton_self _)
    · intro a b _ x hx
      rw [Submodule.mem_comap] at hx ⊢
      have e : thMkC p q r s c (units (fockAct2 p q r s) a b x) =
          thAct p q r s c τ (Eab a b) (thMkC p q r s c x) -
            (τ * (Eab a b).trace) • thMkC p q r s c x := by
        rw [thAct_mk, twAct_apply, map_add, map_smul]
        simp [units]
      rw [e]
      exact N.sub_mem (hst _ _ hx) (N.smul_mem _ hx)
  · have e : LinearMap.range ι = Submodule.map (thMkC p q r s c) (homog (Ix p q × Ix r s) d0) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
      rfl
    rw [e]
    exact star_th c τ c0 τ0 hc hτ La hC d0 hd0

end PositivityTheory.KReal

end
