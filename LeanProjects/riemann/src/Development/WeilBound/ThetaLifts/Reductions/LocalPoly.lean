import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsGreatestProperInvariantSubmoduleOfSide

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.ThKR.Join

open PositivityTheory.KReal PositivityTheory.ThKF.Unit

theorem aeval_inter {V M : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M] (j : V →ₗ[ℂ] M)
    (T : Module.End ℂ V) (C : Module.End ℂ M) (h : ∀ y, j (T y) = C (j y)) (g : Polynomial ℂ) (y : V) :
    j (Polynomial.aeval T g y) = Polynomial.aeval C g (j y) := by
  have hp : ∀ (n : ℕ) y, j ((T ^ n) y) = (C ^ n) (j y) := fun n => by
    induction n with
    | zero => intro y; simp
    | succ n ih => intro y; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction g using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp [Polynomial.aeval_monomial, hp]

theorem poly_kill {M : Type} [AddCommGroup M] [Module ℂ M] (C : Module.End ℂ M) (U : Submodule ℂ M) [FiniteDimensional ℂ U]
    (hU : ∀ y ∈ U, C y ∈ U) (hi : Function.Injective (C.restrict hU)) {x : M} (hx : x ∈ U) :
    ∃ g : Polynomial ℂ, g.eval 0 = 1 ∧ Polynomial.aeval C g x = 0 := by
  have h0 : (C.restrict hU).charpoly.eval 0 ≠ 0 := fun e => by
    obtain ⟨m, h1, h2⟩ := (LinearMap.charpoly_constantCoeff_eq_zero_iff (C.restrict hU)).1
      (by rw [Polynomial.constantCoeff_apply, Polynomial.coeff_zero_eq_eval_zero, e])
    exact h1 (hi (h2.trans (map_zero _).symm))
  refine ⟨Polynomial.C ((C.restrict hU).charpoly.eval 0)⁻¹ * (C.restrict hU).charpoly, ?_, ?_⟩
  · rw [Polynomial.eval_mul, Polynomial.eval_C, inv_mul_cancel₀ h0]
  · have := aeval_inter U.subtype (C.restrict hU) C (fun _ => rfl) (C.restrict hU).charpoly ⟨x, hx⟩
    rw [LinearMap.aeval_self_charpoly] at this
    rw [map_mul, Module.End.mul_apply, show Polynomial.aeval C (C.restrict hU).charpoly x = 0 from this.symm, map_zero]

section Gen

variable {r s : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem local_poly (act : Mat r s →ₗ[ℂ] Module.End ℂ M) (hL : IsLie act) (La : Ix r s → ℚ)
    {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
    (ρ : Ix r s → Ix r s → Module.End ℂ A) (ι : A →ₗ[ℂ] M) (f : A)
    (hadj : AdjK ρ) (hgl : GlK ρ) (hw : HwK ρ La f)
    (hι : ∀ a b, sameBlock a b → ∀ u, ι (ρ a b u) = act (Eab a b) (ι u))
    (hs : StarK act (LinearMap.range ι) ((casW La : ℚ) : ℝ)) :
    casK (units act) (ι f) = ((casW La : ℚ) : ℂ) • ι f ∧ ∀ N : Submodule ℂ M, N ≤ genG act (Submodule.span ℂ {ι f}) →
      (∀ W, ∀ x ∈ N, act W x ∈ N) → N ≠ genG act (Submodule.span ℂ {ι f}) →
      ∀ x ∈ N, ∃ g : Polynomial ℂ, g.eval ((casW La : ℚ) : ℂ) = 1 ∧ Polynomial.aeval (casK (units act)) g x = 0 := by
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
    obtain ⟨g, g1, g2⟩ := poly_kill C (N ⊓ F) hCN hi ⟨hx, hxF⟩
    refine ⟨g.comp (Polynomial.X - Polynomial.C (c0 : ℂ)), by rw [← hcc]; simpa using g1, ?_⟩
    rw [Polynomial.aeval_comp, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
    exact g2

theorem cas_mem (act : Mat r s →ₗ[ℂ] Module.End ℂ M) : casK (units act) ∈ Algebra.adjoin ℂ (Set.range act) := by
  refine sum_mem fun a _ => sum_mem fun b _ => ?_
  split_ifs
  · exact mul_mem (Algebra.subset_adjoin ⟨_, rfl⟩) (Algebra.subset_adjoin ⟨_, rfl⟩)
  · exact zero_mem _

theorem side_nil {La : Ix r s → ℚ} {act : Mat r s →ₗ[ℂ] Module.End ℂ M} (h : Side La M act) :
    ∃ v : M, ∀ K : Submodule ℂ M, K ≠ ⊤ → (∀ W, ∀ x ∈ K, act W x ∈ K) → ∀ t : List M, (∀ x ∈ t, x ∈ K) → ∀ y,
      ∃ u ∈ Algebra.adjoin ℂ (Set.range act), u v = y ∧ ∀ x ∈ t, u x = 0 := by
  obtain ⟨hL, hn, A, _, _, _, ρ, ι, f, hadj, hgl, hw, hι, hgen, hs⟩ := h
  obtain ⟨hv, hC⟩ := local_poly act hL La ρ ι f hadj hgl hw hι hs
  rw [hgen] at hC
  refine ⟨ι f, fun K h1 h2 t ht y => ?_⟩
  have a1 : ∃ g : Polynomial ℂ, g.eval ((casW La : ℚ) : ℂ) = 1 ∧ ∀ x ∈ t, Polynomial.aeval (casK (units act)) g x = 0 := by
    induction t with
    | nil => exact ⟨1, by simp, by simp⟩
    | cons z t ih =>
      obtain ⟨g, g1, g2⟩ := ih fun x hx => ht x (List.mem_cons_of_mem _ hx)
      obtain ⟨g', g1', g2'⟩ := hC K le_top h2 h1 z (ht z List.mem_cons_self)
      refine ⟨g * g', by rw [Polynomial.eval_mul, g1, g1', one_mul], fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [map_mul, Module.End.mul_apply, g2', map_zero]
      · rw [mul_comm, map_mul, Module.End.mul_apply, g2 x hx, map_zero]
  obtain ⟨g, g1, g2⟩ := a1
  have a2 : genG act (Submodule.span ℂ {ι f}) ≤
      (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range act))).map (LinearMap.applyₗ (ι f)) := by
    refine genG_le' ((Submodule.span_singleton_le_iff_mem _ _).2 ⟨1, one_mem (Algebra.adjoin ℂ (Set.range act)), rfl⟩) ?_
    rintro W _ ⟨u, hu, rfl⟩
    exact ⟨act W * u, mul_mem (s := Algebra.adjoin ℂ (Set.range act)) (Algebra.subset_adjoin ⟨W, rfl⟩) hu, rfl⟩
  obtain ⟨u, hu, e⟩ := a2 (hgen ▸ Submodule.mem_top : y ∈ _)
  refine ⟨u * Polynomial.aeval (casK (units act)) g, mul_mem hu ?_, ?_, fun x hx => ?_⟩
  · exact Algebra.adjoin_le (S := Algebra.adjoin ℂ (Set.range act)) (Set.singleton_subset_iff.2 (cas_mem act))
      (Polynomial.aeval_mem_adjoin_singleton ℂ _)
  · rw [Module.End.mul_apply, Module.End.aeval_apply_of_mem_apply_eq_smul hv, g1, one_smul]
    exact e
  · rw [Module.End.mul_apply, g2 x hx, map_zero]

end Gen

def Two (p q r s : ℕ) (c : ℂ) : Prop :=
  ∃ K : Submodule ℂ (Pol p q r s), K ≠ ⊤ ∧ (∀ W, ∀ x ∈ K, fockAct2 p q r s W x ∈ K) ∧
    (∀ N, K ≤ N → (∀ W, ∀ x ∈ N, fockAct2 p q r s W x ∈ N) → N = K ∨ N = ⊤) ∧
    ∃ v : Pol p q r s, ∀ t : List (Pol p q r s), (∀ x ∈ t, x ∈ K) → ∀ y,
      ∃ u ∈ Algebra.adjoin ℂ (Set.range (fockAct2 p q r s)), u v - y ∈ coinvSub (act1 p q r s) (chiTr c) ∧
        ∀ x ∈ t, u x ∈ coinvSub (act1 p q r s) (chiTr c)

theorem two_of {p q r s : ℕ} {c : ℂ} (τ : ℚ) {La : Ix r s → ℚ} (h : Side La (ThC p q r s c) (thAct p q r s c τ)) :
    Two p q r s c := by
  obtain ⟨K, h1, h2, h3, -⟩ := exists_greatest_proper_invariant_submodule_of_side h
  obtain ⟨v, hv⟩ := side_nil h
  have sj : Function.Surjective (thMkC p q r s c) := Submodule.mkQ_surjective _
  have ak : ∀ W x, thMkC p q r s c (fockAct2 p q r s W x) =
      thAct p q r s c τ W (thMkC p q r s c x) - ((τ : ℂ) * W.trace) • thMkC p q r s c x := fun W x => by
    rw [thAct_mk, twAct_apply, map_add, map_smul, add_sub_cancel_right]
  obtain ⟨v, rfl⟩ := sj v
  refine ⟨K.comap (thMkC p q r s c), fun e => h1 (eq_top_iff.2 fun y _ => ?_), fun W x hx => ?_, fun N hN hs => ?_,
    v, fun t ht y => ?_⟩
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
  · have lift : ∀ u ∈ Algebra.adjoin ℂ (Set.range (thAct p q r s c τ)),
        ∃ u' ∈ Algebra.adjoin ℂ (Set.range (fockAct2 p q r s)), ∀ x, thMkC p q r s c (u' x) = u (thMkC p q r s c x) := by
      intro u hu
      induction hu using Algebra.adjoin_induction with
      | mem u hu =>
        obtain ⟨W, rfl⟩ := hu
        refine ⟨fockAct2 p q r s W + ((τ : ℂ) * W.trace) • 1,
          add_mem (Algebra.subset_adjoin ⟨W, rfl⟩) (Subalgebra.smul_mem _ (one_mem _) _), fun x => ?_⟩
        rw [thAct_mk, twAct_apply]; rfl
      | algebraMap a => exact ⟨algebraMap ℂ _ a, Subalgebra.algebraMap_mem _ a, fun x => by simp⟩
      | add a b _ _ ha hb =>
        obtain ⟨a', a1, a2⟩ := ha
        obtain ⟨b', b1, b2⟩ := hb
        exact ⟨a' + b', add_mem a1 b1, fun x => by simp [a2, b2]⟩
      | mul a b _ _ ha hb =>
        obtain ⟨a', a1, a2⟩ := ha
        obtain ⟨b', b1, b2⟩ := hb
        exact ⟨a' * b', mul_mem a1 b1, fun x => by simp [a2, b2]⟩
    obtain ⟨u, hu, e1, e2⟩ := hv K h1 h2 (t.map (thMkC p q r s c)) (by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
      exact ht z hz) (thMkC p q r s c y)
    obtain ⟨u', hu', e⟩ := lift u hu
    refine ⟨u', hu', (Submodule.Quotient.mk_eq_zero _).1 ?_, fun x hx => (Submodule.Quotient.mk_eq_zero _).1 ?_⟩
    · show thMkC p q r s c _ = 0
      rw [map_sub, e, e1, sub_self]
    · show thMkC p q r s c _ = 0
      rw [e, e2 _ (List.mem_map_of_mem hx)]

theorem two_data (D : RealData) (h : D.Hyp) :
    Two D.P D.Q D.R D.S ((D.κ : ℂ) / 2) ∧ Two D.P' D.Q' D.R D.S (-((D.κ : ℂ) / 2)) := by
  obtain ⟨hn, hm, e1, e2, hP, hQ, hQ', hP'⟩ := nm_facts h
  have c1 : ((D.κ : ℂ) / 2) = (((D.κ : ℚ) / 2 : ℚ) : ℂ) := by push_cast; rfl
  have c2 : (-((D.κ : ℂ) / 2)) = ((-((D.κ : ℚ) / 2) : ℚ) : ℂ) := by push_cast; rfl
  have n1 : Nontrivial (ThV D) :=
    nontrivial_of_pair _ _ c1 (c1 ▸ pair_pos hP hQ hn hm _ e1 e2)
  have n2 : Nontrivial (ThV' D) :=
    nontrivial_of_pair _ _ c2 (c2 ▸ pair_neg hQ' hP' hn hm _ (by linarith) (by linarith))
  exact ⟨two_of 0 (side_of ((D.κ : ℂ) / 2) _ _ 0 c1 rfl _ (combV h) n1),
    two_of _ (side_of (-((D.κ : ℂ) / 2)) _ _ _ c2 rfl _ (combV' h) n2)⟩

end PositivityTheory.ThKR.Join

end
