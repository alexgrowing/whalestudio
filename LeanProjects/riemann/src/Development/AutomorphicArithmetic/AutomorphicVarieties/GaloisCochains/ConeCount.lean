import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

noncomputable section

namespace UpperTheory.V.GC.ConeCnt

section Lin

variable {k A W L O S : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup W] [Module k W]
  [AddCommGroup L] [Module k L] [AddCommGroup O] [Module k O] [AddCommGroup S] [Module k S]

private theorem count [Module.Finite k A] [Module.Finite k L] [Module.Finite k S]
    (f : A →ₗ[k] L) (π : W →ₗ[k] L) (hπ : Function.Surjective π) (g : W →ₗ[k] O) (h : O →ₗ[k] S)
    (h1 : LinearMap.ker g = (LinearMap.range f).comap π) (h2 : LinearMap.ker h = LinearMap.range g) :
    Module.Finite k O ∧ finrank k O + finrank k A =
      finrank k (LinearMap.range h) + finrank k L + finrank k (LinearMap.ker f) := by
  have e1 : LinearMap.ker ((LinearMap.range f).mkQ ∘ₗ π) = LinearMap.ker g := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, h1]
  have hs : Function.Surjective ((LinearMap.range f).mkQ ∘ₗ π) :=
    (Submodule.mkQ_surjective _).comp hπ
  let e : LinearMap.range g ≃ₗ[k] L ⧸ LinearMap.range f :=
    g.quotKerEquivRange.symm.trans ((Submodule.quotEquivOfEq _ _ e1.symm).trans
      (LinearMap.quotKerEquivOfSurjective _ hs))
  haveI : Module.Finite k (LinearMap.range g) := Module.Finite.equiv e.symm
  have a5 : finrank k (LinearMap.ker h) = finrank k (LinearMap.range g) := by rw [h2]
  haveI : Module.Finite k (LinearMap.ker h) := by rw [h2]; infer_instance
  haveI : Module.Finite k O := by
    apply Module.rank_lt_aleph0_iff.mp
    rw [← LinearMap.rank_range_add_rank_ker h]
    exact Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 k _) (Module.rank_lt_aleph0 k _)
  refine ⟨inferInstance, ?_⟩
  have a1 := LinearMap.finrank_range_add_finrank_ker f
  have a2 := LinearMap.finrank_range_add_finrank_ker h
  have a3 := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  have a4 := e.finrank_eq
  omega

end Lin

variable {k Γ M V : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module k M]
  [TopologicalSpace M] [DiscreteTopology M] {Gv : V → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  (loc : ∀ v, Gv v →* Γ) (hloc : ∀ v, Continuous (loc v)) (ρ : Representation k Γ M)
  {Q : V → Type} [∀ v, AddCommGroup (Q v)] [∀ v, Module k (Q v)] [∀ v, TopologicalSpace (Q v)]
  [∀ v, DiscreteTopology (Q v)] (σ : ∀ v, Representation k (Gv v) (Q v)) (q : ∀ v, M →ₗ[k] Q v)
  (hq : ∀ v s m, q v (ρ (loc v s) m) = σ v s (q v m))
  (r : ∀ v, Q v →ₗ[k] M) (hr : ∀ v y, q v (r v y) = y)

private theorem first_differential_eq {G N : Type} [Group G] [AddCommGroup N] [Module k N] (τ : Representation k G N) (c : G → N) :
    d1 τ c = Alg.dOne τ c := by
  funext p
  show τ p.1 (c p.2) - c (p.1 * p.2) + c p.1 = c p.1 + τ p.1 (c p.2) - c (p.1 * p.2)
  abel

private def f0 : H0 ρ →ₗ[k] (∀ v, H0 (σ v)) where
  toFun x := fun v => ⟨q v x.1, fun g => by rw [← hq, x.2]⟩
  map_add' _ _ := funext fun v => Subtype.ext (map_add _ _ _)
  map_smul' _ _ := funext fun v => Subtype.ext (map_smul _ _ _)

private def f1 : H1 ρ →ₗ[k] (∀ v, H1 (σ v)) :=
  LinearMap.pi fun v => pairH1DecompositionMap ρ (σ v) (loc v) (hloc v) (q v) continuous_of_discreteTopology (hq v)

private def g1Z : (∀ v, H0 (σ v)) →ₗ[k] Z1C loc ρ (fun v => LinearMap.ker (q v)) where
  toFun y := ⟨(0, fun v => r v (y v).1), IsLocallyConstant.const 0, by simp, fun v s => by
    have := (y v).2 s
    simp [hq, hr, this]⟩
  map_add' _ _ := Subtype.ext (Prod.ext (by simp) (funext fun v => by simp))
  map_smul' _ _ := Subtype.ext (Prod.ext (by simp) (funext fun v => by simp))

private def g1 : (∀ v, H0 (σ v)) →ₗ[k] H1C loc ρ (fun v => LinearMap.ker (q v)) :=
  Submodule.mkQ _ ∘ₗ g1Z loc ρ σ q hq r hr

private def h1Z : Z1C loc ρ (fun v => LinearMap.ker (q v)) →ₗ[k] Z1 ρ where
  toFun x := ⟨x.1.1, x.2.1.continuous, x.2.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def h1 : H1C loc ρ (fun v => LinearMap.ker (q v)) →ₗ[k] H1 ρ :=
  Submodule.mapQ _ _ (h1Z loc ρ q) fun x hx => by
    obtain ⟨X, a1, -⟩ := hx
    exact (mem_coboundaries1 _ _).2 ⟨X, a1⟩

private theorem ker_g1_eq_range_f0 : LinearMap.ker (g1 loc ρ σ q hq r hr) =
    (LinearMap.range (f0 loc ρ σ q hq)).comap LinearMap.id := by
  rw [Submodule.comap_id]
  ext y
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hy
    have hy' : g1Z loc ρ σ q hq r hr y ∈ Submodule.comap (Z1C loc ρ fun v => LinearMap.ker (q v)).subtype
        (continuousCoboundaries1 ρ fun v => LinearMap.ker (q v)) :=
      (Submodule.Quotient.mk_eq_zero _).1 hy
    obtain ⟨X, h1, h2⟩ := hy'
    refine ⟨⟨X, fun g => ?_⟩, ?_⟩
    · have : ρ g X - X = 0 := (h1 g).symm
      exact sub_eq_zero.1 this
    · funext v
      apply Subtype.ext
      have := h2 v
      change r v (y v).1 - X ∈ LinearMap.ker (q v) at this
      rw [LinearMap.mem_ker, map_sub, hr] at this
      exact (sub_eq_zero.1 this).symm
  · rintro ⟨x, rfl⟩
    apply (Submodule.Quotient.mk_eq_zero _).2
    refine ⟨x.1, fun s => ?_, fun v => ?_⟩
    · exact (sub_eq_zero.2 (x.2 s)).symm
    · show r v (q v x.1) - x.1 ∈ LinearMap.ker (q v)
      rw [LinearMap.mem_ker, map_sub, hr, sub_self]

private theorem ker_h1_eq_range_g1 : LinearMap.ker (h1 loc ρ q) = LinearMap.range (g1 loc ρ σ q hq r hr) := by
  ext c
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hc
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    have hx : h1Z loc ρ q x ∈ Submodule.comap (Z1 ρ).subtype (B1 ρ) :=
      (Submodule.Quotient.mk_eq_zero _).1 hc
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hx
    have hm' : ∀ s, x.1.1 s = ρ s m - m := hm
    have key : ∀ v (s : Gv v), σ v s (q v (x.1.2 v - m)) = q v (x.1.2 v - m) := by
      intro v s
      have h3 := x.2.2.2 v s
      rw [LinearMap.mem_ker] at h3
      rw [← hq, ← sub_eq_zero, ← map_sub]
      have e : ρ (loc v s) (x.1.2 v - m) - (x.1.2 v - m) =
          -(x.1.1 (loc v s) - (ρ (loc v s) (x.1.2 v) - x.1.2 v)) := by
        rw [hm', map_sub]; abel
      rw [e, map_neg, h3, neg_zero]
    refine ⟨fun v => ⟨q v (x.1.2 v - m), key v⟩, ?_⟩
    show Submodule.Quotient.mk (g1Z loc ρ σ q hq r hr _) = Submodule.Quotient.mk x
    rw [Submodule.Quotient.eq]
    refine ⟨-m, fun s => ?_, fun v => ?_⟩
    · show (0 : M) - x.1.1 s = ρ s (-m) - -m
      rw [hm' s, map_neg]; abel
    · show r v (q v (x.1.2 v - m)) - x.1.2 v - -m ∈ LinearMap.ker (q v)
      rw [LinearMap.mem_ker, map_sub, map_sub, hr, map_neg, map_sub]; abel
  · rintro ⟨y, rfl⟩
    show Submodule.Quotient.mk (h1Z loc ρ q (g1Z loc ρ σ q hq r hr y)) = 0
    exact (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨0, fun g => by
      show (0 : M) = ρ g 0 - 0
      simp⟩)

include hr in
private theorem range_h1_eq_ker_f1 : LinearMap.range (h1 loc ρ q) = LinearMap.ker (f1 loc hloc ρ σ q hq) := by
  ext c
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨c', rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c'
    funext v
    show (Submodule.Quotient.mk (compatiblePairCocycles1 ρ (σ v) (loc v) (hloc v) (q v) continuous_of_discreteTopology (hq v)
      (h1Z loc ρ q x)) : H1 (σ v)) = 0
    apply (Submodule.Quotient.mk_eq_zero _).2
    refine (mem_coboundaries1 _ _).2 ⟨q v (x.1.2 v), fun s => ?_⟩
    have h3 := x.2.2.2 v s
    rw [LinearMap.mem_ker, map_sub, map_sub, hq] at h3
    show q v (x.1.1 (loc v s)) = σ v s (q v (x.1.2 v)) - q v (x.1.2 v)
    exact sub_eq_zero.1 h3
  · intro hc
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    have hv : ∀ v, ∃ m, ∀ s : Gv v, q v (z.1 (loc v s)) = σ v s m - m := by
      intro v
      have h0 : (Submodule.Quotient.mk (compatiblePairCocycles1 ρ (σ v) (loc v) (hloc v) (q v) continuous_of_discreteTopology (hq v)
          z) : H1 (σ v)) = 0 := congrFun hc v
      have h' : compatiblePairCocycles1 ρ (σ v) (loc v) (hloc v) (q v) continuous_of_discreteTopology (hq v) z ∈
          Submodule.comap (Z1 (σ v)).subtype (B1 (σ v)) := (Submodule.Quotient.mk_eq_zero _).1 h0
      exact (mem_coboundaries1 _ _).1 h'
    choose m hm using hv
    refine ⟨Submodule.Quotient.mk ⟨(z.1, fun v => r v (m v)), (IsLocallyConstant.iff_continuous _).2 z.2.1,
      z.2.2, fun v s => ?_⟩, rfl⟩
    show z.1 (loc v s) - (ρ (loc v s) (r v (m v)) - r v (m v)) ∈ LinearMap.ker (q v)
    rw [LinearMap.mem_ker, map_sub, map_sub, hq, hr, hm, sub_self]

private def kerF0EquivInvariants : LinearMap.ker (f0 loc ρ σ q hq) ≃ₗ[k] coneH0 ρ (fun v => LinearMap.ker (q v)) where
  toFun x := ⟨x.1.1, x.1.2, fun v => congrArg Subtype.val (congrFun x.2 v)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := ⟨⟨x.1, x.2.1⟩, funext fun v => Subtype.ext (x.2.2 v)⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def h2Z : continuousCocycles2 loc ρ (fun v => LinearMap.ker (q v)) →ₗ[k] Z2 ρ where
  toFun x := ⟨x.1.1, x.2.1.continuous, fun s t u => by
    have := x.2.2.2.1 s t u
    rw [sub_add_eq_add_sub, this]; abel⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def h2 : coneH2 loc ρ (fun v => LinearMap.ker (q v)) →ₗ[k] H2 ρ :=
  Submodule.mapQ _ _ (h2Z loc ρ q) fun x hx => by
    obtain ⟨h, y, a1, a3, -⟩ := hx
    exact (separated_dvr_second_cohomology_mem _ _).2 ⟨h, a1.continuous, by rw [first_differential_eq]; exact a3.symm⟩

private def g2Z : (∀ v, Z1 (σ v)) →ₗ[k] continuousCocycles2 loc ρ (fun v => LinearMap.ker (q v)) where
  toFun a := ⟨(0, fun v s => r v ((a v).1 s)), IsLocallyConstant.const 0,
    fun v => ((IsLocallyConstant.iff_continuous _).2 (a v).2.1).comp (r v), by simp,
    fun v s t => by
      change q v _ = 0
      simp only [Alg.dOne, (a v).2.2 s t, Pi.zero_apply, map_sub, map_add, MonoidHom.comp_apply, hq, hr, map_zero,
        sub_self]⟩
  map_add' _ _ := Subtype.ext (Prod.ext (by simp) (funext fun v => funext fun s => by simp))
  map_smul' _ _ := Subtype.ext (Prod.ext (by simp) (funext fun v => funext fun s => by simp))

private def g2 : (∀ v, Z1 (σ v)) →ₗ[k] coneH2 loc ρ (fun v => LinearMap.ker (q v)) :=
  Submodule.mkQ _ ∘ₗ g2Z loc ρ σ q hq r hr

private def pL : (∀ v, Z1 (σ v)) →ₗ[k] (∀ v, H1 (σ v)) where
  toFun a := fun v => Submodule.Quotient.mk (a v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem pL_surj : Function.Surjective (pL σ) := by
  intro a
  choose a' ha using fun v => Submodule.Quotient.mk_surjective _ (a v)
  exact ⟨a', funext ha⟩

include hr in
private theorem range_h2_eq_inf_ker_pairing : LinearMap.range (h2 loc ρ q) =
    ⨅ v, LinearMap.ker (compatiblePairH2 ρ (σ v) (loc v) (hloc v) (q v) continuous_of_discreteTopology (hq v)) := by
  ext c
  rw [LinearMap.mem_range, Submodule.mem_iInf]
  constructor
  · rintro ⟨c', rfl⟩ v
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c'
    rw [LinearMap.mem_ker]
    show (Submodule.Quotient.mk (compatiblePairCocycles2 ρ (σ v) (loc v) (hloc v) (q v) continuous_of_discreteTopology (hq v)
      (h2Z loc ρ q x)) : H2 (σ v)) = 0
    apply (Submodule.Quotient.mk_eq_zero _).2
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun s => q v (x.1.2 v s), ((x.2.2.1 v).comp (q v)).continuous, ?_⟩
    rw [first_differential_eq]
    funext p
    have h4 := x.2.2.2.2 v p.1 p.2
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h4
    show _ = q v (x.1.1 (loc v p.1, loc v p.2))
    rw [h4]
    simp only [Alg.dOne, map_sub, map_add, MonoidHom.comp_apply, hq]
  · intro hc
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    have hv : ∀ v, ∃ cv : Gv v → Q v, Continuous cv ∧
        d1 (σ v) cv = fun p => q v (z.1 (loc v p.1, loc v p.2)) := by
      intro v
      have h0 : (Submodule.Quotient.mk (compatiblePairCocycles2 ρ (σ v) (loc v) (hloc v) (q v) continuous_of_discreteTopology (hq v)
          z) : H2 (σ v)) = 0 := LinearMap.mem_ker.1 (hc v)
      have h' : compatiblePairCocycles2 ρ (σ v) (loc v) (hloc v) (q v) continuous_of_discreteTopology (hq v) z ∈
          Submodule.comap (Z2 (σ v)).subtype (B2 (σ v)) := (Submodule.Quotient.mk_eq_zero _).1 h0
      exact (separated_dvr_second_cohomology_mem _ _).1 h'
    choose cv hcv hd using hv
    refine ⟨Submodule.Quotient.mk ⟨(z.1, fun v s => r v (cv v s)), (IsLocallyConstant.iff_continuous _).2 z.2.1,
      fun v => ((IsLocallyConstant.iff_continuous _).2 (hcv v)).comp (r v), fun s t u => ?_, fun v s t => ?_⟩, rfl⟩
    · have := z.2.2 s t u
      show ρ s (z.1 (t, u)) + z.1 (s, t * u) = z.1 (s * t, u) + z.1 (s, t)
      rw [← sub_eq_zero, ← this]; abel
    · show z.1 (loc v s, loc v t) - Alg.dOne (ρ.comp (loc v)) (fun s => r v (cv v s)) (s, t) ∈ LinearMap.ker (q v)
      have e := congrFun (hd v) (s, t)
      rw [first_differential_eq] at e
      rw [LinearMap.mem_ker, map_sub, ← e]
      simp only [Alg.dOne, map_sub, map_add, MonoidHom.comp_apply, hq, hr, sub_self]

include hloc in
private theorem ker_h2_eq_range_g2 : LinearMap.ker (h2 loc ρ q) = LinearMap.range (g2 loc ρ σ q hq r hr) := by
  ext c
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hc
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    have hx : h2Z loc ρ q x ∈ Submodule.comap (Z2 ρ).subtype (B2 ρ) :=
      (Submodule.Quotient.mk_eq_zero _).1 hc
    obtain ⟨β, hβ, hd⟩ := (separated_dvr_second_cohomology_mem _ _).1 hx
    rw [first_differential_eq] at hd
    have hd' : x.1.1 = Alg.dOne ρ β := hd.symm
    have hcoc : ∀ v (s t : Gv v), q v (x.1.2 v (s * t) - β (loc v (s * t))) =
        q v (x.1.2 v s - β (loc v s)) + σ v s (q v (x.1.2 v t - β (loc v t))) := by
      intro v s t
      have h4 := x.2.2.2.2 v s t
      rw [hd', LinearMap.mem_ker] at h4
      simp only [Alg.dOne, MonoidHom.comp_apply, map_mul, map_sub, map_add, hq] at h4 ⊢
      rw [← sub_eq_zero, ← h4]; abel
    refine ⟨fun v => ⟨fun s => q v (x.1.2 v s - β (loc v s)), ?_, hcoc v⟩, ?_⟩
    · exact (continuous_of_discreteTopology (f := q v)).comp
        ((x.2.2.1 v).continuous.sub (hβ.comp (hloc v)))
    · show Submodule.Quotient.mk (g2Z loc ρ σ q hq r hr _) = Submodule.Quotient.mk x
      rw [Submodule.Quotient.eq]
      refine ⟨-β, fun _ => 0, (IsLocallyConstant.iff_continuous _).2 hβ.neg, ?_, fun v s => ?_⟩
      · show (0 : Γ × Γ → M) - x.1.1 = Alg.dOne ρ (-β)
        rw [hd']
        funext p
        simp only [Alg.dOne, Pi.sub_apply, Pi.zero_apply, Pi.neg_apply, map_neg]
        abel
      · show r v (q v (x.1.2 v s - β (loc v s))) - x.1.2 v s - ((-β) (loc v s) - (ρ (loc v s) 0 - 0)) ∈
          LinearMap.ker (q v)
        rw [LinearMap.mem_ker]
        simp only [map_sub, hr, Pi.neg_apply, map_neg, map_zero, sub_zero]
        abel
  · rintro ⟨a, rfl⟩
    show Submodule.Quotient.mk (h2Z loc ρ q (g2Z loc ρ σ q hq r hr a)) = 0
    apply (Submodule.Quotient.mk_eq_zero _).2
    exact (separated_dvr_second_cohomology_mem _ _).2 ⟨0, continuous_const, by rw [map_zero]; rfl⟩

private theorem ker_g2_eq_comap_range_f1 : LinearMap.ker (g2 loc ρ σ q hq r hr) =
    (LinearMap.range (f1 loc hloc ρ σ q hq)).comap (pL σ) := by
  ext a
  rw [LinearMap.mem_ker, Submodule.mem_comap, LinearMap.mem_range]
  constructor
  · intro ha
    have ha' : g2Z loc ρ σ q hq r hr a ∈ Submodule.comap (continuousCocycles2 loc ρ fun v => LinearMap.ker (q v)).subtype
        (continuousCoboundaries2 loc ρ fun v => LinearMap.ker (q v)) := (Submodule.Quotient.mk_eq_zero _).1 ha
    obtain ⟨β, Y, hβ, h0, hY⟩ := ha'
    have hz : β ∈ Z1 ρ := by
      refine ⟨hβ.continuous, fun s t => ?_⟩
      have e : (0 : M) = β s + ρ s (β t) - β (s * t) := congrFun h0 (s, t)
      rw [eq_sub_iff_add_eq, zero_add] at e
      exact e
    refine ⟨Submodule.Quotient.mk ⟨β, hz⟩, ?_⟩
    funext v
    show (Submodule.Quotient.mk (compatiblePairCocycles1 ρ (σ v) (loc v) (hloc v) (q v) continuous_of_discreteTopology (hq v)
      ⟨β, hz⟩) : H1 (σ v)) = Submodule.Quotient.mk (a v)
    rw [Submodule.Quotient.eq]
    refine (mem_coboundaries1 _ _).2 ⟨q v (Y v), fun s => ?_⟩
    have h3 : r v ((a v).1 s) - (β (loc v s) - (ρ (loc v s) (Y v) - Y v)) ∈ LinearMap.ker (q v) := hY v s
    rw [LinearMap.mem_ker, map_sub, map_sub, map_sub, hr, hq, sub_eq_zero] at h3
    show q v (β (loc v s)) - (a v).1 s = σ v s (q v (Y v)) - q v (Y v)
    rw [h3]; abel
  · rintro ⟨c, hc⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    have hv : ∀ v, ∃ m, ∀ s, q v (z.1 (loc v s)) - (a v).1 s = σ v s m - m := by
      intro v
      have h1' : (Submodule.Quotient.mk (compatiblePairCocycles1 ρ (σ v) (loc v) (hloc v) (q v) continuous_of_discreteTopology (hq v)
          z) : H1 (σ v)) = Submodule.Quotient.mk (a v) := congrFun hc v
      rw [Submodule.Quotient.eq] at h1'
      exact (mem_coboundaries1 _ _).1 h1'
    choose m hm using hv
    show Submodule.Quotient.mk (g2Z loc ρ σ q hq r hr a) = 0
    apply (Submodule.Quotient.mk_eq_zero _).2
    refine ⟨z.1, fun v => r v (m v), (IsLocallyConstant.iff_continuous _).2 z.2.1, ?_, fun v s => ?_⟩
    · funext p
      show (0 : M) = z.1 p.1 + ρ p.1 (z.1 p.2) - z.1 (p.1 * p.2)
      rw [z.2.2, sub_self]
    · show r v ((a v).1 s) - (z.1 (loc v s) - (ρ (loc v s) (r v (m v)) - r v (m v))) ∈ LinearMap.ker (q v)
      rw [LinearMap.mem_ker]
      simp only [map_sub, hq, hr]
      rw [← hm v s]; abel

end UpperTheory.V.GC.ConeCnt

end

open UpperTheory.V.GC.ConeCnt in
theorem UpperTheory.V.GC.coneCount :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (V : Type) [Fintype V] (Gv : V → Type) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] [∀ v, CompactSpace (Gv v)] [∀ v, T2Space (Gv v)] [∀ v, TotallyDisconnectedSpace (Gv v)] (loc : ∀ v, Gv v →* Γ) (hloc : ∀ v, Continuous (loc v)) (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k Γ M), ContAction ρ →
    ∀ (Q : V → Type) [∀ v, AddCommGroup (Q v)] [∀ v, Module k (Q v)] [∀ v, TopologicalSpace (Q v)] [∀ v, DiscreteTopology (Q v)] (σ : ∀ v, Representation k (Gv v) (Q v)) (q : ∀ v, M →ₗ[k] Q v)
    (hq : ∀ v s m, q v (ρ (loc v s) m) = σ v s (q v m)), (∀ v, Function.Surjective (q v)) → Module.Finite k (H1 ρ) → Module.Finite k (H2 ρ) → (∀ v, Module.Finite k (H1 (σ v))) →
    Module.Finite k (H1C loc ρ fun v => LinearMap.ker (q v)) ∧ Module.Finite k (coneH2 loc ρ fun v => LinearMap.ker (q v)) ∧
    finrank k (coneH2 loc ρ fun v => LinearMap.ker (q v)) + finrank k (coneH0 ρ fun v => LinearMap.ker (q v)) + finrank k (H1 ρ) + ∑ v, finrank k (H0 (σ v)) =
      finrank k (H1C loc ρ fun v => LinearMap.ker (q v)) + finrank k (H0 ρ) + ∑ v, finrank k (H1 (σ v)) +
      finrank k (⨅ v, LinearMap.ker (compatiblePairH2 ρ (σ v) (loc v) (hloc v) (q v) continuous_of_discreteTopology (hq v)) : Submodule k (H2 ρ)) := by
  intro l _ Γ _ _ _ _ _ _ V _ Gv _ _ _ _ _ _ loc hloc k _ _ _ M _ _ _ _ _ ρ _ Q _ _ _ _ σ q hq hqs hH1 hH2 hH1v
  obtain ⟨r, hr⟩ : ∃ r : ∀ v, Q v →ₗ[k] M, ∀ v y, q v (r v y) = y := by
    choose r hr using fun v => (q v).exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 (hqs v))
    exact ⟨r, fun v y => LinearMap.congr_fun (hr v) y⟩
  haveI : ∀ v, Module.Finite k (Q v) := fun v => Module.Finite.of_surjective (q v) (hqs v)
  obtain ⟨fin1, e1⟩ := count (f0 loc ρ σ q hq) LinearMap.id Function.surjective_id (g1 loc ρ σ q hq r hr)
    (h1 loc ρ q) (ker_g1_eq_range_f0 loc ρ σ q hq r hr) (ker_h1_eq_range_g1 loc ρ σ q hq r hr)
  obtain ⟨fin2, e2⟩ := count (f1 loc hloc ρ σ q hq) (pL σ) (pL_surj σ) (g2 loc ρ σ q hq r hr)
    (h2 loc ρ q) (ker_g2_eq_comap_range_f1 loc hloc ρ σ q hq r hr) (ker_h2_eq_range_g2 loc hloc ρ σ q hq r hr)
  refine ⟨fin1, fin2, ?_⟩
  rw [range_h1_eq_ker_f1 loc hloc ρ σ q hq r hr] at e1
  rw [range_h2_eq_inf_ker_pairing loc hloc ρ σ q hq r hr] at e2
  rw [(kerF0EquivInvariants loc ρ σ q hq).finrank_eq, Module.finrank_pi_fintype] at e1
  rw [Module.finrank_pi_fintype] at e2
  omega
