import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.NcVOneDecomp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpEigGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.Numerics

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

section OneB

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem ncV_one_decomp (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) {x : Big n 1 M} (hx : x ∈ ncV ε V 1) :
    ∃ xm ∈ Wm ε E V, ∃ xp ∈ Wp ε E V, x = xm + xp := by
  classical
  have hinv : ∀ y ∈ ncV ε V 1, crossOp ε E 1 0 y ∈ ncV ε V 1 :=
    fun y hy => crossOp_mem_ncV hV.2.1 1 0 hy
  haveI : FiniteDimensional ℂ (ncV ε V 1) := finiteDimensional_ncV hV.1 1
  let T' : Module.End ℂ (ncV ε V 1) := (crossOp ε E 1 0).restrict hinv
  have hT' : T'.IsSymmetric := fun u v => crossOp_symm hU 1 0 u v
  have htop : (⨆ μ, Module.End.eigenspace T' μ) = ⊤ := by
    have := hT'.orthogonalComplement_iSup_eigenspaces_eq_bot
    rwa [Submodule.orthogonal_eq_bot_iff] at this
  have hx' : (⟨x, hx⟩ : ncV ε V 1) ∈ ⨆ μ, Module.End.eigenspace T' μ := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨g, hg, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx'
  have hreal : ∀ μ, g μ ≠ 0 → μ = ((μ.re : ℝ) : ℂ) := by
    intro μ hμ
    have hev : Module.End.HasEigenvalue T' μ :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨hg μ, hμ⟩
    exact (Complex.conj_eq_iff_re.1 (hT'.conj_eigenvalue_eq_self hev)).symm
  have hmem : ∀ μ, ((g μ : ncV ε V 1) : Big n 1 M) ∈
      Module.End.eigenspace (crossOp ε E 1 0) μ ⊓ ncV ε V 1 := by
    intro μ
    refine Submodule.mem_inf.2 ⟨?_, (g μ).2⟩
    rw [Module.End.mem_eigenspace_iff]
    exact congrArg Subtype.val (Module.End.mem_eigenspace_iff.1 (hg μ))
  have hmem' : ∀ μ, g μ ≠ 0 → ((g μ : ncV ε V 1) : Big n 1 M) ∈
      Module.End.eigenspace (crossOp ε E 1 0) ((μ.re : ℝ) : ℂ) ⊓ ncV ε V 1 := by
    intro μ hμ
    have h1 := hmem μ
    rwa [← hreal μ hμ]
  have hne : ∀ μ, g μ ≠ 0 → ((g μ : ncV ε V 1) : Big n 1 M) ≠ 0 := by
    intro μ hμ h0
    exact hμ (Subtype.ext h0)
  have hxsum : x = ∑ μ ∈ g.support, ((g μ : ncV ε V 1) : Big n 1 M) := by
    have := congrArg Subtype.val hsum
    simpa [Finsupp.sum] using this.symm
  refine ⟨∑ μ ∈ g.support.filter (fun μ => μ.re < 0), ((g μ : ncV ε V 1) : Big n 1 M), ?_,
    ∑ μ ∈ g.support.filter (fun μ => ¬ μ.re < 0), ((g μ : ncV ε V 1) : Big n 1 M), ?_, ?_⟩
  · show _ ∈ ⨆ (θ : ℝ) (_ : θ < 0), Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1
    refine Submodule.sum_mem _ fun μ hμ => ?_
    by_cases h0 : g μ = 0
    · rw [h0]; exact Submodule.zero_mem _
    · exact Submodule.mem_iSup_of_mem μ.re
        (Submodule.mem_iSup_of_mem (Finset.mem_filter.1 hμ).2 (hmem' μ h0))
  · show _ ∈ ⨆ (θ : ℝ) (_ : 0 < θ), Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1
    refine Submodule.sum_mem _ fun μ hμ => ?_
    by_cases h0 : g μ = 0
    · rw [h0]; exact Submodule.zero_mem _
    · have hnn : ¬ μ.re < 0 := (Finset.mem_filter.1 hμ).2
      have hpos : 0 < μ.re := by
        rcases crossOp_eig_gap hE hU hV hmono hh hbig (hmem' μ h0) (hne μ h0) with h1 | h1
        · linarith [h1.1, h1.2]
        · exact absurd (by linarith [h1.1, h1.2]) hnn
      exact Submodule.mem_iSup_of_mem μ.re (Submodule.mem_iSup_of_mem hpos (hmem' μ h0))
  · rw [Finset.sum_filter_add_sum_filter_not]
    exact hxsum

private lemma nsq_add_root_sub_nsq (w : Fin n → ℝ) {r s : Fin n} (hrs : r ≠ s) :
    nsq (w + root r s) - nsq w = 2 * (w r - w s) + 2 := by
  have key : ∀ i, (w + root r s) i * (w + root r s) i - w i * w i =
      (if i = r then 2 * w r + 1 else 0) + (if i = s then -(2 * w s) + 1 else 0) := by
    intro i
    simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    by_cases h1 : i = r
    · subst h1
      simp [hrs]
      ring
    · by_cases h2 : i = s
      · subst h2
        simp [h1]
        ring
      · simp [h1, h2]
  unfold nsq dot
  rw [← Finset.sum_sub_distrib]
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

private lemma abs_rhoN_le_half (ε : Fin n → Bool) (a : Fin n) :
    -(n : ℝ) / 2 ≤ rhoN ε a ∧ rhoN ε a ≤ (n : ℝ) / 2 := by
  have key : ∀ t : Finset (Fin n), (t.card : ℝ) ≤ n := fun t => by
    have := Finset.card_le_univ t
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  simp only [rhoN]
  constructor
  · linarith [key (Finset.filter (fun b => b < a ∧ ε b ≠ ε a) Finset.univ),
      (Nat.cast_nonneg (Finset.filter (fun b => a < b ∧ ε b ≠ ε a) Finset.univ).card : (0 : ℝ) ≤ _)]
  · linarith [key (Finset.filter (fun b => a < b ∧ ε b ≠ ε a) Finset.univ),
      (Nat.cast_nonneg (Finset.filter (fun b => b < a ∧ ε b ≠ ε a) Finset.univ).card : (0 : ℝ) ≤ _)]

theorem Wm_khw (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) {x : Big n 1 M} (hx : x ∈ Wm ε E V) (hx0 : x ≠ 0) {ν : Fin n → ℝ}
    (hν : IsKHWVec ε (bAct E 1) ν x) :
    ∃ a b : Fin n, a < b ∧ ε a ≠ ε b ∧ ν = lowK ε lam - root a b := by
  have hle : Wm ε E V ≤ ncV ε V 1 := by
    show (⨆ (θ : ℝ) (_ : θ < 0),
      Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1) ≤ ncV ε V 1
    exact iSup₂_le fun θ _ => inf_le_right
  have hxN : x ∈ ncV ε V 1 := hle hx
  obtain ⟨r, s, hrs, hν', hC⟩ := crossOp_khw hE hU hV hxN hx0 hν
  have hne : r ≠ s := fun h' => hrs (h' ▸ rfl)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exfalso
    have hdiff : casValK ε ν - casValK ε (lowK ε lam) =
        2 * ((lowK ε lam + rhoC ε) r - (lowK ε lam + rhoC ε) s) + 2 := by
      rw [hν']
      unfold casValK
      rw [add_right_comm]
      linarith [nsq_add_root_sub_nsq (lowK ε lam + rhoC ε) hne]
    have hw : ∀ i, (lowK ε lam + rhoC ε) i = lam i + rhoN ε i := by
      intro i
      simp [lowK]
    have hgap : h ≤ lam r - lam s := by
      have h1 := hh r s hrs
      rwa [abs_of_pos (sub_pos.2 (hmono hlt))] at h1
    have hcpos : 0 < (casValK ε ν - n - casValK ε (lowK ε lam)) / 2 := by
      rw [hw r, hw s] at hdiff
      linarith [(abs_rhoN_le_half ε r).1, (abs_rhoN_le_half ε s).2]
    have heig : crossOp ε E 1 0 x =
        (((casValK ε ν - n - casValK ε (lowK ε lam)) / 2 : ℝ) : ℂ) • x := by
      have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
      calc crossOp ε E 1 0 x = (2 : ℂ)⁻¹ • ((2 : ℂ) • crossOp ε E 1 0 x) := by
            rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
        _ = (2 : ℂ)⁻¹ • (((casValK ε ν - n - casValK ε (lowK ε lam) : ℝ) : ℂ) • x) := by
            rw [hC]
        _ = _ := by
            rw [smul_smul]
            congr 1
            push_cast
            ring
    have hxP : x ∈ Wp ε E V := by
      show x ∈ ⨆ (θ : ℝ) (_ : 0 < θ),
        Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1
      exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hcpos
        (Submodule.mem_inf.2 ⟨Module.End.mem_eigenspace_iff.2 heig, hxN⟩))
    exact hx0 (inner_self_eq_zero.1 (Wm_perp_Wp hU hx hxP))
  · refine ⟨s, r, hgt, fun h' => hrs h'.symm, ?_⟩
    rw [hν']
    unfold root
    abel

private lemma mul_norm_sq_sum_le_re_inner_of_orthogonal_eigen {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (T : Module.End ℂ W) (hT : ∀ u v, inner ℂ (T u) v = inner ℂ u (T v)) (c : ℝ)
    {ι : Type*} [DecidableEq ι] (θ : ι → ℝ) (y : ι → W) (s : Finset ι)
    (hy : ∀ i ∈ s, T (y i) = ((θ i : ℝ) : ℂ) • y i)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℂ (y i) (y j) = 0)
    (hc : ∀ i ∈ s, y i ≠ 0 → c ≤ θ i) :
    c * ‖∑ i ∈ s, y i‖ ^ 2 ≤ RCLike.re (inner ℂ (T (∑ i ∈ s, y i)) (∑ i ∈ s, y i)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have IH := ih (fun j hj => hy j (Finset.mem_insert_of_mem hj))
      (fun a ha b hb hab => horth a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab)
      (fun j hj => hc j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert hi]
    have h0 : inner ℂ (y i) (∑ j ∈ s, y j) = 0 := by
      rw [inner_sum]
      exact Finset.sum_eq_zero fun j hj => horth i (Finset.mem_insert_self i s) j
        (Finset.mem_insert_of_mem hj) (fun h => hi (h ▸ hj))
    have h0' : inner ℂ (∑ j ∈ s, y j) (y i) = 0 := by
      rw [← inner_conj_symm, h0, map_zero]
    have hTi : T (y i) = ((θ i : ℝ) : ℂ) • y i := hy i (Finset.mem_insert_self i s)
    have h1 : inner ℂ (T (y i)) (∑ j ∈ s, y j) = 0 := by
      rw [hTi, inner_smul_left, h0, mul_zero]
    have h2 : inner ℂ (T (∑ j ∈ s, y j)) (y i) = 0 := by
      rw [hT, hTi, inner_smul_right, h0', mul_zero]
    have h3 : RCLike.re (inner ℂ (T (y i)) (y i)) = θ i * ‖y i‖ ^ 2 := by
      rw [hTi, inner_smul_left, Complex.conj_ofReal, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
      exact Complex.re_ofReal_mul _ _
    have hn : ‖y i + ∑ j ∈ s, y j‖ ^ 2 = ‖y i‖ ^ 2 + ‖∑ j ∈ s, y j‖ ^ 2 := by
      rw [@norm_add_sq ℂ, h0]; simp
    have hre : RCLike.re (inner ℂ (T (y i + ∑ j ∈ s, y j)) (y i + ∑ j ∈ s, y j)) =
        θ i * ‖y i‖ ^ 2 + RCLike.re (inner ℂ (T (∑ j ∈ s, y j)) (∑ j ∈ s, y j)) := by
      rw [map_add, inner_add_left, inner_add_right, inner_add_right, h1, h2, add_zero, zero_add,
        map_add, h3]
    rw [hn, hre]
    by_cases hyi : y i = 0
    · rw [hyi]; simp only [norm_zero]; nlinarith [IH]
    · have := hc i (Finset.mem_insert_self i s) hyi
      nlinarith [IH, mul_le_mul_of_nonneg_right this (sq_nonneg ‖y i‖)]

theorem Wp_bound (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) {x : Big n 1 M} (hx : x ∈ Wp ε E V) :
    2 * (h - n + 1) * ‖x‖ ^ 2 ≤ 2 * RCLike.re (inner ℂ (crossOp ε E 1 0 x) x) := by
  classical
  have hx' : x ∈ ⨆ θ : {θ : ℝ // 0 < θ},
      Module.End.eigenspace (crossOp ε E 1 0) (((θ : ℝ)) : ℂ) ⊓ ncV ε V 1 := by
    have h1 : x ∈ ⨆ (θ : ℝ) (_ : 0 < θ),
        Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1 := hx
    rwa [iSup_subtype'] at h1
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx'
  have key := mul_norm_sq_sum_le_re_inner_of_orthogonal_eigen (crossOp ε E 1 0) (crossOp_symm hU 1 0) (h - n + 1)
    (fun θ : {θ : ℝ // 0 < θ} => (θ : ℝ)) f f.support
    (fun i _ => Module.End.mem_eigenspace_iff.1 (hf i).1)
    (fun i _ j _ hij => inner_crossOp_eig_eq_zero hU (fun h' => hij (Subtype.ext h'))
      (Module.End.mem_eigenspace_iff.1 (hf i).1) (Module.End.mem_eigenspace_iff.1 (hf j).1))
    (fun i _ hi0 => by
      rcases crossOp_eig_gap hE hU hV hmono hh hbig (hf i) hi0 with h1 | h1
      · exact h1.2
      · exact absurd i.2 (by linarith [h1.1, h1.2]))
  simp only [Finsupp.sum]
  linarith [key]

end OneB

end ReciprocityTheory.ChartRestriction.DS.G2
