import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

noncomputable section

namespace UpperTheory.V.X.FrameOb

section Lin

variable {k A W L O S : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup W] [Module k W]
  [AddCommGroup L] [Module k L] [AddCommGroup O] [Module k O] [AddCommGroup S] [Module k S]

private theorem count [Module.Finite k A] [Module.Finite k L] [Module.Finite k S]
    (f : A →ₗ[k] L) (π : W →ₗ[k] L) (hπ : Function.Surjective π) (g : W →ₗ[k] O) (h : O →ₗ[k] S)
    (h1 : LinearMap.ker g = (LinearMap.range f).comap π) (h2 : LinearMap.ker h = LinearMap.range g) :
    Module.Finite k O ∧ finrank k O + finrank k A =
      finrank k (LinearMap.range h) + finrank k L + finrank k (LinearMap.ker f) := by
  have hs : Function.Surjective ((LinearMap.range f).mkQ ∘ₗ π) :=
    (Submodule.mkQ_surjective _).comp hπ
  have hk : LinearMap.ker g = LinearMap.ker ((LinearMap.range f).mkQ ∘ₗ π) := by
    rw [h1, LinearMap.ker_comp, Submodule.ker_mkQ]
  have e : LinearMap.ker h ≃ₗ[k] (L ⧸ LinearMap.range f) :=
    (LinearEquiv.ofEq _ _ h2).trans (g.quotKerEquivRange.symm.trans
      ((Submodule.quotEquivOfEq _ _ hk).trans (LinearMap.quotKerEquivOfSurjective _ hs)))
  haveI : Module.Finite k (LinearMap.ker h) := Module.Finite.equiv e.symm
  haveI : Module.Finite k (O ⧸ LinearMap.ker h) := Module.Finite.equiv h.quotKerEquivRange.symm
  haveI hO : Module.Finite k O := Module.Finite.of_submodule_quotient (LinearMap.ker h)
  refine ⟨hO, ?_⟩
  have a1 := h.finrank_range_add_finrank_ker
  have a2 := f.finrank_range_add_finrank_ker
  have a3 := (LinearMap.range f).finrank_quotient_add_finrank
  have a4 := e.finrank_eq
  omega

private theorem rk {I J : Type} [Fintype I] [Fintype J] (P : I → Type) (Q : J → Type) [∀ i, AddCommGroup (P i)]
    [∀ i, Module k (P i)] [∀ i, AddCommGroup (Q i)] [∀ i, Module k (Q i)] [∀ i, Module.Finite k (P i)]
    [∀ i, Module.Finite k (Q i)] (U : ∀ j, Submodule k (Q j)) :
    finrank k ((∀ i, P i) × (∀ j, Q j ⧸ U j)) + ∑ j, finrank k (U j) =
      ∑ i, finrank k (P i) + ∑ j, finrank k (Q j) := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_pi_fintype, add_assoc,
    ← Finset.sum_add_distrib]
  exact congrArg _ (Finset.sum_congr rfl fun q _ => Submodule.finrank_quotient_add_finrank _)

end Lin

variable {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module k M]
  [TopologicalSpace M] [DiscreteTopology M] (F : Alg.Frame Γ) (ρ : Representation k Γ M)

private theorem mem_coboundaries_compact (x : F.C2 M) : x ∈ F.framedTwoCoboundaries ρ ↔
    ∃ (h : Γ → M) (y : F.T → M) (e : ∀ q, F.Gq q → M), IsLocallyConstant h ∧
    (∀ q, IsLocallyConstant (e q) ∧ (∀ s t, e q (s * t) = e q s + ρ (F.ψ q s) (e q t)) ∧ ∀ n ∈ F.N q, e q n = 0) ∧
    x.1 = Alg.dOne ρ h ∧ (∀ v s, x.2.1 v s = h (F.φ v s) - (ρ (F.φ v s) (y v) - y v)) ∧
    ∀ q s, x.2.2 q s = h (F.ψ q s) - e q s := by
  refine ⟨fun hx => ?_, fun hx => Submodule.subset_span hx⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    exact ⟨0, 0, 0, IsLocallyConstant.const 0, fun q => ⟨IsLocallyConstant.const 0, by simp, by simp⟩,
      by funext p; simp [Alg.dOne], by simp, by simp⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨h, y, e, a1, a2, a3, a4, a5⟩ := hx
    obtain ⟨h', y', e', b1, b2, b3, b4, b5⟩ := hx'
    refine ⟨h + h', y + y', e + e', a1.add b1, fun q => ⟨(a2 q).1.add (b2 q).1, fun s t => ?_, fun n hn => ?_⟩,
      ?_, fun v s => ?_, fun q s => ?_⟩
    · simp only [Pi.add_apply, (a2 q).2.1, (b2 q).2.1, map_add]; abel
    · simp [(a2 q).2.2 n hn, (b2 q).2.2 n hn]
    · funext p
      simp only [Prod.fst_add, Pi.add_apply, a3, b3, Alg.dOne, map_add]; abel
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, a4, b4, map_add]; abel
    · simp only [Prod.snd_add, Pi.add_apply, a5, b5]; abel
  | smul c x _ hx =>
    obtain ⟨h, y, e, a1, a2, a3, a4, a5⟩ := hx
    refine ⟨c • h, c • y, c • e, a1.comp (c • ·), fun q => ⟨(a2 q).1.comp (c • ·), fun s t => ?_, fun n hn => ?_⟩,
      ?_, fun v s => ?_, fun q s => ?_⟩
    · simp [(a2 q).2.1]
    · simp [(a2 q).2.2 n hn]
    · funext p
      simp [a3, Alg.dOne, smul_sub]
    · simp [a4, smul_sub]
    · simp [a5, smul_sub]

private theorem first_differential_eq {G : Type} [Group G] [TopologicalSpace G] (σ : Representation k G M) (c : G → M) :
    d1 σ c = Alg.dOne σ c := by
  funext p
  obtain ⟨s, t⟩ := p
  simp only [d1_apply, Alg.dOne]; abel

private def hZ : F.framedTwoCocycles ρ →ₗ[k] Z2 ρ where
  toFun x := ⟨x.1.1, x.2.1.continuous, fun s t u => by
    have := x.2.2.2.2.1 s t u
    rw [sub_add_eq_add_sub, this]; abel⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def hO : F.Ob ρ →ₗ[k] H2 ρ :=
  Submodule.mapQ _ _ (hZ F ρ) fun x hx => by
    obtain ⟨h, y, e, a1, -, a3, -⟩ := (mem_coboundaries_compact F ρ _).1 hx
    exact (separated_dvr_second_cohomology_mem _ _).2 ⟨h, a1.continuous, by rw [first_differential_eq]; exact a3.symm⟩

private abbrev WW := (∀ v, Z1 (ρ.comp (F.φ v))) × (∀ q, Z1 (ρ.comp (F.ψ q)))

private abbrev LL := (∀ v, H1 (ρ.comp (F.φ v))) × (∀ q, H1 (ρ.comp (F.ψ q)) ⧸ H1ur (ρ.comp (F.ψ q)) (F.N q))

private def gZ : WW F ρ →ₗ[k] F.framedTwoCocycles ρ where
  toFun a := ⟨(0, fun v => (a.1 v).1, fun q => (a.2 q).1), IsLocallyConstant.const 0,
    fun v => (IsLocallyConstant.iff_continuous _).2 (a.1 v).2.1,
    fun q => (IsLocallyConstant.iff_continuous _).2 (a.2 q).2.1, by simp,
    fun v s t => by simp only [Alg.dOne, (a.1 v).2.2 s t, sub_self, Pi.zero_apply],
    fun q s t => by simp only [Alg.dOne, (a.2 q).2.2 s t, sub_self, Pi.zero_apply]⟩
  map_add' _ _ := Subtype.ext (Prod.ext (by simp) rfl)
  map_smul' _ _ := Subtype.ext (Prod.ext (by simp) rfl)

private def gO : WW F ρ →ₗ[k] F.Ob ρ := Submodule.mkQ _ ∘ₗ gZ F ρ

private def pL : WW F ρ →ₗ[k] LL F ρ where
  toFun a := (fun v => Submodule.Quotient.mk (a.1 v), fun q => Submodule.Quotient.mk (Submodule.Quotient.mk (a.2 q)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def fL : H1 ρ →ₗ[k] LL F ρ where
  toFun a := (fun v => resH1 ρ (F.φ v) (F.hφ v) a, fun q => Submodule.Quotient.mk (resH1 ρ (F.ψ q) (F.hψ q) a))
  map_add' _ _ := by simp only [map_add]; rfl
  map_smul' _ _ := by simp only [map_smul]; rfl

private theorem pL_surj : Function.Surjective (pL F ρ) := by
  rintro ⟨a, b⟩
  choose a' ha using fun v => Submodule.Quotient.mk_surjective _ (a v)
  choose b' hb using fun q => Submodule.Quotient.mk_surjective _ (b q)
  choose b'' hb' using fun q => Submodule.Quotient.mk_surjective _ (b' q)
  refine ⟨(a', b''), Prod.ext (funext ha) (funext fun q => ?_)⟩
  change Submodule.Quotient.mk (Submodule.Quotient.mk (b'' q)) = b q
  rw [hb', hb]

private theorem ker_fL : LinearMap.ker (fL F ρ) = selF F ρ := by
  ext x
  simp only [selF, LinearMap.mem_ker, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, Prod.ext_iff,
    funext_iff]
  refine and_congr Iff.rfl (forall_congr' fun q => ?_)
  exact Submodule.Quotient.mk_eq_zero _

private theorem range_hO : LinearMap.range (hO F ρ) = shaF F ρ := by
  ext x
  obtain ⟨κ, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [shaF, LinearMap.mem_ker, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← hy]
    refine ⟨fun v => ?_, fun q => ?_⟩
    · refine (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨y.1.2.1 v, (y.2.2.1 v).continuous, ?_⟩)
      rw [first_differential_eq]
      funext p
      exact (y.2.2.2.2.2.1 v p.1 p.2).symm
    · refine (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨y.1.2.2 q, (y.2.2.2.1 q).continuous, ?_⟩)
      rw [first_differential_eq]
      funext p
      exact (y.2.2.2.2.2.2 q p.1 p.2).symm
  · rintro ⟨h1, h2⟩
    choose a ha ha' using fun v => (separated_dvr_second_cohomology_mem _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 (h1 v))
    choose b hb hb' using fun q => (separated_dvr_second_cohomology_mem _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 (h2 q))
    refine ⟨Submodule.Quotient.mk ⟨(κ.1, a, b), (IsLocallyConstant.iff_continuous _).2 κ.2.1,
      fun v => (IsLocallyConstant.iff_continuous _).2 (ha v),
      fun q => (IsLocallyConstant.iff_continuous _).2 (hb q), fun s t u => ?_, fun v s t => ?_, fun q s t => ?_⟩, rfl⟩
    · have := κ.2.2 s t u
      rw [← sub_eq_zero, ← this]; abel
    · rw [← first_differential_eq, ha']; rfl
    · rw [← first_differential_eq, hb']; rfl

private theorem ker_hO : LinearMap.ker (hO F ρ) = LinearMap.range (gO F ρ) := by
  ext x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  constructor
  · intro hx
    obtain ⟨c, hc, hc'⟩ := (separated_dvr_second_cohomology_mem _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hx)
    rw [first_differential_eq] at hc'
    have hc2 : x.1.1 = Alg.dOne ρ c := hc'.symm
    obtain ⟨x, a1, a2, a3, a4, a5, a6⟩ := x
    dsimp only at hc2
    refine ⟨(fun v => ⟨fun s => x.2.1 v s - c (F.φ v s), (a2 v).continuous.sub (hc.comp (F.hφ v)), fun s t => ?_⟩,
      fun q => ⟨fun s => x.2.2 q s - c (F.ψ q s), (a3 q).continuous.sub (hc.comp (F.hψ q)), fun s t => ?_⟩), ?_⟩
    · have := a5 v s t
      rw [hc2] at this
      simp only [Alg.dOne, MonoidHom.comp_apply, map_sub, map_mul] at this ⊢
      rw [← sub_eq_zero] at this ⊢
      rw [← this]; abel
    · have := a6 q s t
      rw [hc2] at this
      simp only [Alg.dOne, MonoidHom.comp_apply, map_sub, map_mul] at this ⊢
      rw [← sub_eq_zero] at this ⊢
      rw [← this]; abel
    · symm
      refine (Submodule.Quotient.eq _).2 ((mem_coboundaries_compact F ρ _).2 ⟨c, 0, 0, (IsLocallyConstant.iff_continuous _).2 hc,
        fun q => ⟨IsLocallyConstant.const 0, by simp, by simp⟩, ?_, fun v s => ?_, fun q s => ?_⟩)
      · change x.1 - 0 = _
        rw [sub_zero, hc2]
      · change x.2.1 v s - (x.2.1 v s - c (F.φ v s)) = _
        simp
      · change x.2.2 q s - (x.2.2 q s - c (F.ψ q s)) = _
        simp
  · rintro ⟨a, ha⟩
    rw [← ha]
    refine (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨0, continuous_const, ?_⟩)
    rw [map_zero]; rfl

private theorem ker_gO (hN : ∀ q, ∀ n ∈ F.N q, ρ (F.ψ q n) = 1) :
    LinearMap.ker (gO F ρ) = (LinearMap.range (fL F ρ)).comap (pL F ρ) := by
  ext a
  constructor
  · intro ha
    have ha' : gZ F ρ a ∈ (F.framedTwoCoboundaries ρ).comap (F.framedTwoCocycles ρ).subtype := (Submodule.Quotient.mk_eq_zero _).1 ha
    obtain ⟨h, y, e, a1, a2, a3, a4, a5⟩ := (mem_coboundaries_compact F ρ (gZ F ρ a).1).1 ha'
    have hz : h ∈ Z1 ρ := ⟨a1.continuous, fun s t => by
      have : (0 : M) = Alg.dOne ρ h (s, t) := congrFun a3 (s, t)
      simp only [Alg.dOne] at this
      exact (sub_eq_zero.1 this.symm).symm⟩
    refine ⟨Submodule.Quotient.mk ⟨h, hz⟩, Prod.ext (funext fun v => ?_) (funext fun q => ?_)⟩
    · refine (Submodule.Quotient.eq _).2 ((mem_coboundaries1 _ _).2 ⟨y v, fun s => ?_⟩)
      have : (a.1 v).1 s = _ := a4 v s
      change h (F.φ v s) - (a.1 v).1 s = ρ (F.φ v s) (y v) - y v
      rw [this]; abel
    · refine (Submodule.Quotient.eq _).2 ((Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨0, fun s => ?_⟩))
      have : (a.2 q).1 s = _ := a5 q s
      change h (F.ψ q s) - (a.2 q).1 s = _
      rw [this, (a2 q).2.2 s s.2]; simp
  · rintro ⟨h, hh⟩
    obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    choose y hy using fun v => (mem_coboundaries1 _ _).1 ((Submodule.Quotient.eq _).1 (congrFun (congrArg Prod.fst hh) v))
    choose m hm using fun q => (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1
      ((Submodule.Quotient.eq _).1 (congrFun (congrArg Prod.snd hh) q)))
    refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries_compact F ρ _).2 ⟨h.1, y, fun q s => h.1 (F.ψ q s) - (a.2 q).1 s,
      (IsLocallyConstant.iff_continuous _).2 h.2.1, fun q => ⟨(IsLocallyConstant.iff_continuous _).2
        ((h.2.1.comp (F.hψ q)).sub (a.2 q).2.1), fun s t => ?_, fun n hn => ?_⟩, ?_, fun v s => ?_, fun q s => ?_⟩)
    · simp only [map_mul, h.2.2, (a.2 q).2.2 s t, map_sub, MonoidHom.comp_apply]; abel
    · have : h.1 (F.ψ q n) - (a.2 q).1 n = ρ (F.ψ q n) (m q) - m q := hm q ⟨n, hn⟩
      refine this.trans ?_
      rw [hN q n hn]; simp
    · funext p
      change (0 : M) = _
      simp only [Alg.dOne, h.2.2, sub_self]
    · have : h.1 (F.φ v s) - (a.1 v).1 s = ρ (F.φ v s) (y v) - y v := hy v s
      change (a.1 v).1 s = _
      rw [← this]; abel
    · exact (sub_sub_cancel _ _).symm

end UpperTheory.V.X.FrameOb

end

open UpperTheory.V.X.FrameOb in
theorem UpperTheory.V.X.frameOb :
    ∀ {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (F : Alg.Frame Γ) (ρ : Representation k Γ M), ContAction ρ → (∀ q, ∀ n ∈ F.N q, ρ (F.ψ q n) = 1) → Module.Finite k (H1 ρ) → Module.Finite k (H2 ρ) → (∀ v, Module.Finite k (H1 (ρ.comp (F.φ v)))) → (∀ q, Module.Finite k (H1 (ρ.comp (F.ψ q)))) → Module.Finite k (F.Ob ρ) ∧ finrank k (F.Ob ρ) + finrank k (H1 ρ) + ∑ q, finrank k (H1ur (ρ.comp (F.ψ q)) (F.N q)) = finrank k (shaF F ρ) + ∑ v, finrank k (H1 (ρ.comp (F.φ v))) + ∑ q, finrank k (H1 (ρ.comp (F.ψ q))) + finrank k (selF F ρ) := by
  intro k Γ M _ _ _ _ _ _ _ _ _ F ρ _ hN i1 i2 i3 i4
  obtain ⟨c1, c2⟩ := count (fL F ρ) (pL F ρ) (pL_surj F ρ) (gO F ρ) (hO F ρ) (ker_gO F ρ hN) (ker_hO F ρ)
  refine ⟨c1, ?_⟩
  rw [range_hO, ker_fL] at c2
  have c3 : finrank k (LL F ρ) + _ = _ := rk (k := k) (fun v => H1 (ρ.comp (F.φ v))) (fun q => H1 (ρ.comp (F.ψ q)))
    (fun q => H1ur (ρ.comp (F.ψ q)) (F.N q))
  omega
