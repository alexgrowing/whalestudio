import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreLM

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.ThKF.Unit

open PositivityTheory.KReal

section Gen

variable {r s : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem casimir_eigenvalue_and_sub_smul_onto_proper_submodule (act : Mat r s →ₗ[ℂ] Module.End ℂ M) (hL : IsLie act) (La : Ix r s → ℚ)
    {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
    (ρ : Ix r s → Ix r s → Module.End ℂ A) (ι : A →ₗ[ℂ] M) (f : A)
    (hadj : AdjK ρ) (hgl : GlK ρ) (hw : HwK ρ La f)
    (hι : ∀ a b, sameBlock a b → ∀ u, ι (ρ a b u) = act (Eab a b) (ι u))
    (hs : StarK act (LinearMap.range ι) ((casW La : ℚ) : ℝ)) :
    casK (units act) (ι f) = ((casW La : ℚ) : ℂ) • ι f ∧ ∀ N : Submodule ℂ M, N ≤ genG act (Submodule.span ℂ {ι f}) →
      (∀ W, ∀ x ∈ N, act W x ∈ N) → N ≠ genG act (Submodule.span ℂ {ι f}) →
      ∀ x ∈ N, ∃ y, x = casK (units act) y - ((casW La : ℚ) : ℂ) • y := by
  classical
  let V : Submodule ℂ A := cycK ρ f
  let ρV : Ix r s → Ix r s → Module.End ℂ V := fun a b =>
    if h : sameBlock a b then (ρ a b).restrict (kSt_cycK ρ f a b h) else 0
  have hρV : ∀ a b, sameBlock a b → ∀ v : V, ((ρV a b v : V) : A) = ρ a b v := by
    intro a b h v
    simp only [ρV, dif_pos h]
    rfl
  let ιV : V →ₗ[ℂ] M := ι ∘ₗ V.subtype
  have hιV : ∀ a b, sameBlock a b → ∀ v, ιV (ρV a b v) = act (Eab a b) (ιV v) := by
    intro a b h v
    change ι ((ρV a b v : V) : A) = act (Eab a b) (ι (v : A))
    rw [hρV a b h, hι a b h]
  have hadjV : AdjK ρV := by
    intro a b h u v
    rw [Submodule.coe_inner, Submodule.coe_inner, hρV a b h, hρV b a (sameBlock_symm' h)]
    exact hadj a b h _ _
  set c0 : ℝ := ((casW La : ℚ) : ℝ) with hc0
  have hcc : (c0 : ℂ) = ((casW La : ℚ) : ℂ) := by simp [hc0]
  have hcV : casK ρV = (c0 : ℂ) • (1 : Module.End ℂ V) := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    have h1 := casK_intertw (ρ := ρV) (ρ' := ρ) V.subtype (fun a b h v => hρV a b h v) v
    change ((casK ρV v : V) : A) = (c0 : ℂ) • (v : A)
    rw [hcc, ← cas_cyc hgl hw v v.2]
    exact h1
  have hsV : StarK act (LinearMap.range ιV) c0 := by
    intro t ht x hx
    refine hs t ht x (Submodule.span_mono ?_ hx)
    rintro y ⟨a, b, hab, v, ⟨w, rfl⟩, rfl⟩
    exact ⟨a, b, hab, _, ⟨(w : A), rfl⟩, rfl⟩
  obtain ⟨hinj, hfin⟩ := cas_bound_gl act hL ρV hadjV c0 hcV ιV hιV hsV
  have hfV : f ∈ V := self_mem_cycK ρ f
  have hG : genG act (LinearMap.range ιV) = genG act (Submodule.span ℂ {ι f}) := by
    apply le_antisymm
    · refine genG_le' ?_ (genG_stable' _ _)
      rintro _ ⟨v, rfl⟩
      have : V ≤ (genG act (Submodule.span ℂ {ι f})).comap ι := by
        refine sInf_le ⟨le_genG' _ _ (Submodule.mem_span_singleton_self _), fun a b h x hx => ?_⟩
        rw [Submodule.mem_comap, hι a b h]
        exact genG_stable' _ _ _ _ hx
      exact this v.2
    · refine genG_le' ?_ (genG_stable' _ _)
      rw [Submodule.span_singleton_le_iff_mem]
      exact le_genG' _ _ ⟨⟨f, hfV⟩, rfl⟩
  rw [hG] at hinj hfin
  set G := genG act (Submodule.span ℂ {ι f}) with hGdef
  let C : Module.End ℂ M := casK (units act) - (c0 : ℂ) • 1
  have hC : ∀ x, C x = casK (units act) x - (c0 : ℂ) • x := fun x => rfl
  have hC0 : ∀ x ∈ LinearMap.range ιV, C x = 0 := by
    rintro _ ⟨v, rfl⟩
    rw [hC, ← casK_intertw (ρ := ρV) (ρ' := units act) ιV hιV v, hcV]
    simp
  refine ⟨?_, fun N hNG hNs hne => ?_⟩
  · have := hC0 (ι f) ⟨⟨f, hfV⟩, rfl⟩
    rw [hC, sub_eq_zero, hcc] at this
    exact this
  · have hdis : ∀ x ∈ N, x ∈ LinearMap.range ιV → x = 0 := by
      have hK : KSt ρ (V ⊓ N.comap ι) := by
        intro a b h x hx
        refine ⟨kSt_cycK ρ f a b h x hx.1, ?_⟩
        change ι (ρ a b x) ∈ N
        rw [hι a b h]
        exact hNs _ _ hx.2
      rcases cyc_irred hadj hgl hw (V ⊓ N.comap ι) inf_le_left hK with h | h
      · rintro _ hx ⟨v, rfl⟩
        have : (v : A) ∈ V ⊓ N.comap ι := ⟨v.2, hx⟩
        rw [h, Submodule.mem_bot] at this
        change ι (v : A) = 0
        rw [this, map_zero]
      · exfalso
        apply hne
        refine le_antisymm hNG (genG_le' ?_ hNs)
        rw [Submodule.span_singleton_le_iff_mem]
        have : f ∈ V ⊓ N.comap ι := h ▸ hfV
        exact this.2
    intro x hx
    obtain ⟨F, hF, hxF, hFK⟩ := hfin x (hNG hx)
    have hKN : KSt (units act) (N ⊓ F) := fun a b h y hy => ⟨hNs _ _ hy.1, hFK a b h y hy.2⟩
    have hCN : ∀ y ∈ N ⊓ F, C y ∈ N ⊓ F := fun y hy =>
      (N ⊓ F).sub_mem (casK_mem hKN hy) ((N ⊓ F).smul_mem _ hy)
    have : FiniteDimensional ℂ ↥(N ⊓ F) := Submodule.finiteDimensional_of_le inf_le_right
    have hi : Function.Injective (C.restrict hCN) := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro y hy
      have h1 : C (y : M) = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 hy)
      have h2 := hinj y (hNG y.2.1) (by rw [← hC, h1]; exact Submodule.zero_mem _)
      exact Subtype.ext (hdis y y.2.1 h2)
    obtain ⟨y, hy⟩ := LinearMap.injective_iff_surjective.1 hi ⟨x, hx, hxF⟩
    exact ⟨y, by rw [← hcc]; exact (congrArg Subtype.val hy).symm⟩

theorem exists_greatest_proper_invariant_submodule_of_side {La : Ix r s → ℚ} {act : Mat r s →ₗ[ℂ] Module.End ℂ M} (h : Side La M act) :
    ∃ K : Submodule ℂ M, K ≠ ⊤ ∧ (∀ W, ∀ x ∈ K, act W x ∈ K) ∧ (∀ N, (∀ W, ∀ x ∈ N, act W x ∈ N) → N ≠ ⊤ → N ≤ K) ∧
      ∀ β : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ, (∀ a b x y, β (act (Eab a b) x) y = epsB a b * β x (act (Eab b a) y)) → ∀ x ∈ K, β x = 0 := by
  obtain ⟨hL, hn, A, _, _, _, ρ, ι, f, hadj, hgl, hw, hι, hgen, hs⟩ := h
  obtain ⟨R, hR, hRN⟩ := local_of act hL La ρ ι f hadj hgl hw hι hs (ne_zero_of_gen act _ hgen)
  obtain ⟨hv, hC⟩ := casimir_eigenvalue_and_sub_smul_onto_proper_submodule act hL La ρ ι f hadj hgl hw hι hs
  rw [hgen] at hRN hC
  let K := sSup {N : Submodule ℂ M | (∀ W, ∀ x ∈ N, act W x ∈ N) ∧ N ≠ ⊤}
  have hne : K ≠ ⊤ := fun e => hR ((sSup_le fun N hN => hRN N le_top hN.1 hN.2 : K ≤ R) (show ι f ∈ K by rw [e]; trivial))
  have hst : ∀ W, ∀ x ∈ K, act W x ∈ K := fun W =>
    (sSup_le fun N hN x hx => le_sSup (s := {N : Submodule ℂ M | (∀ W, ∀ x ∈ N, act W x ∈ N) ∧ N ≠ ⊤}) hN (hN.1 W x hx) :
      K ≤ K.comap (act W))
  refine ⟨K, hne, hst, fun N h1 h2 => le_sSup (s := {N : Submodule ℂ M | (∀ W, ∀ x ∈ N, act W x ∈ N) ∧ N ≠ ⊤}) ⟨h1, h2⟩,
    fun β hβ x hx => ?_⟩
  have cas : ∀ u v, β (casK (units act) u) v = β u (casK (units act) v) := fun u v => by
    simp only [casK, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs with hab
    · simp only [Module.End.mul_apply, units, hβ, epsB, if_pos hab, if_pos (sameBlock_symm' hab), one_mul]
    · simp
  let O : Submodule ℂ M := ⨅ x : K, LinearMap.ker (β x)
  have mO : ∀ z, z ∈ O ↔ ∀ x ∈ K, β x z = 0 := fun z => by simp [O, Submodule.mem_iInf]
  have : genG act (Submodule.span ℂ {ι f}) ≤ O := by
    refine genG_le' ((Submodule.span_singleton_le_iff_mem _ _).2 ((mO _).2 fun x hx => ?_)) fun W z hz => (mO _).2 fun x hx => ?_
    · obtain ⟨y, rfl⟩ := hC K le_top hst hne x hx
      rw [map_sub, LinearMap.sub_apply, cas, hv, map_smul, LinearMap.map_smulₛₗ]
      simp
    · rw [matrix_eq_sum_single W]
      simp only [map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
      have e : single a b (W a b) = W a b • (Eab a b : Mat r s) := by simp [Eab]
      have h1 := hβ b a x z
      rw [(mO z).1 hz _ (hst _ x hx)] at h1
      have h2 : epsB b a ≠ 0 := by unfold epsB; split_ifs <;> simp
      rw [e, map_smul, LinearMap.smul_apply, map_smul, (mul_eq_zero.1 h1.symm).resolve_left h2, smul_zero]
  exact LinearMap.ext fun z => (mO z).1 (this (hgen ▸ Submodule.mem_top)) x hx

end Gen

def One (p q r s : ℕ) (c : ℂ) : Prop :=
  ∃ K : Submodule ℂ (Pol p q r s), K ≠ ⊤ ∧ (∀ W, ∀ x ∈ K, fockAct2 p q r s W x ∈ K) ∧
    (∀ N, K ≤ N → (∀ W, ∀ x ∈ N, fockAct2 p q r s W x ∈ N) → N = K ∨ N = ⊤) ∧
    ∀ β : Pol p q r s →ₗ⋆[ℂ] Pol p q r s →ₗ[ℂ] ℂ,
      (∀ Z x y, β (fockAct1 p q r s Z x - (c * Z.trace) • x) y = 0) → (∀ Z x y, β y (fockAct1 p q r s Z x - (c * Z.trace) • x) = 0) →
      (∀ a b x y, β (fockAct2 p q r s (Eab a b) x) y = epsB a b * β x (fockAct2 p q r s (Eab b a) y)) → ∀ x ∈ K, β x = 0

theorem one_of {p q r s : ℕ} {c : ℂ} (τ : ℚ) {La : Ix r s → ℚ} (h : Side La (ThC p q r s c) (thAct p q r s c τ)) :
    One p q r s c := by
  obtain ⟨K, h1, h2, h3, h4⟩ := exists_greatest_proper_invariant_submodule_of_side h
  have sj : Function.Surjective (thMkC p q r s c) := Submodule.mkQ_surjective _
  have ak : ∀ W x, thMkC p q r s c (fockAct2 p q r s W x) =
      thAct p q r s c τ W (thMkC p q r s c x) - ((τ : ℂ) * W.trace) • thMkC p q r s c x := fun W x => by
    rw [thAct_mk, twAct_apply, map_add, map_smul, add_sub_cancel_right]
  refine ⟨K.comap (thMkC p q r s c), fun e => h1 (eq_top_iff.2 fun y _ => ?_), fun W x hx => ?_, fun N hN hs => ?_,
    fun β b1 b2 b3 x hx => ?_⟩
  · obtain ⟨x, rfl⟩ := sj y
    exact (e ▸ Submodule.mem_top : x ∈ K.comap (thMkC p q r s c))
  · show thMkC p q r s c _ ∈ K
    rw [ak]
    exact K.sub_mem (h2 W _ hx) (K.smul_mem _ hx)
  · by_cases e : N.map (thMkC p q r s c) = ⊤
    · refine Or.inr (eq_top_iff.2 fun x _ => ?_)
      obtain ⟨y, hy, e'⟩ : thMkC p q r s c x ∈ N.map (thMkC p q r s c) := e ▸ Submodule.mem_top
      have : x - y ∈ N := hN (show thMkC p q r s c (x - y) ∈ K by rw [map_sub, e', sub_self]; exact K.zero_mem)
      simpa using N.add_mem this hy
    · refine Or.inl (le_antisymm (Submodule.map_le_iff_le_comap.1 (h3 _ ?_ e)) hN)
      rintro W _ ⟨y, hy, rfl⟩
      exact ⟨_, by rw [twAct_apply]; exact N.add_mem (hs W y hy) (N.smul_mem _ hy), (thAct_mk ..).symm⟩
  · obtain ⟨σ, hσ⟩ := (thMkC p q r s c).exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 sj)
    have hd : ∀ x, σ (thMkC p q r s c x) - x ∈ coinvSub (act1 p q r s) (chiTr c) := fun x => by
      rw [← Submodule.Quotient.mk_eq_zero]
      show thMkC p q r s c _ = 0
      rw [map_sub, ← LinearMap.comp_apply, hσ, LinearMap.id_apply, sub_self]
    have k1 : coinvSub (act1 p q r s) (chiTr c) ≤ LinearMap.ker β := iSup_le fun Z => by
      rintro _ ⟨x, rfl⟩
      exact LinearMap.ext fun y => b1 Z x y
    have k2 : ∀ y, coinvSub (act1 p q r s) (chiTr c) ≤ LinearMap.ker (β y) := fun y => iSup_le fun Z => by
      rintro _ ⟨x, rfl⟩
      exact b2 Z x y
    let β' : ThC p q r s c →ₗ⋆[ℂ] ThC p q r s c →ₗ[ℂ] ℂ := (β.compl₂ σ).comp σ
    have hβ' : ∀ x y, β' (thMkC p q r s c x) (thMkC p q r s c y) = β x y := fun x y => by
      show β (σ _) (σ _) = _
      have e1 := LinearMap.mem_ker.1 (k1 (hd x))
      have e2 := LinearMap.mem_ker.1 (k2 x (hd y))
      rw [map_sub, sub_eq_zero] at e1 e2
      rw [e1, e2]
    have := h4 β' (fun a b u v => by
      obtain ⟨u, rfl⟩ := sj u
      obtain ⟨v, rfl⟩ := sj v
      rw [thAct_mk, thAct_mk, hβ', hβ', twAct_apply, twAct_apply, map_add, map_add, LinearMap.add_apply, b3, map_smul (β u),
        LinearMap.map_smulₛₗ β, mul_add]
      congr 1
      by_cases e : a = b
      · subst e
        have : sameBlock a a := by cases a <;> trivial
        simp [Eab, epsB, this]
      · simp [Eab, trace_single_eq_of_ne, e, Ne.symm e]) _ hx
    exact LinearMap.ext fun y => by rw [← hβ', this]; rfl

theorem one_data (D : RealData) (h : D.Hyp) :
    One D.P D.Q D.R D.S ((D.κ : ℂ) / 2) ∧ One D.P' D.Q' D.R D.S (-((D.κ : ℂ) / 2)) := by
  obtain ⟨hn, hm, e1, e2, hP, hQ, hQ', hP'⟩ := nm_facts h
  have c1 : ((D.κ : ℂ) / 2) = (((D.κ : ℚ) / 2 : ℚ) : ℂ) := by push_cast; rfl
  have c2 : (-((D.κ : ℂ) / 2)) = ((-((D.κ : ℚ) / 2) : ℚ) : ℂ) := by push_cast; rfl
  have n1 : Nontrivial (ThV D) :=
    nontrivial_of_pair _ _ c1 (c1 ▸ pair_pos hP hQ hn hm _ e1 e2)
  have n2 : Nontrivial (ThV' D) :=
    nontrivial_of_pair _ _ c2 (c2 ▸ pair_neg hQ' hP' hn hm _ (by linarith) (by linarith))
  exact ⟨one_of 0 (side_of ((D.κ : ℂ) / 2) _ _ 0 c1 rfl _ (combV h) n1),
    one_of _ (side_of (-((D.κ : ℂ) / 2)) _ _ _ c2 rfl _ (combV' h) n2)⟩

end PositivityTheory.ThKF.Unit

end
