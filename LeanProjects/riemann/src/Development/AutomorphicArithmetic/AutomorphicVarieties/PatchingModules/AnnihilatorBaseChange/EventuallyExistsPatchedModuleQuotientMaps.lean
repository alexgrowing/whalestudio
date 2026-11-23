import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PiCong
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpCong
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.FoCong
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem power_maximal_ideal_le_map_power_smul_top (Λ B M : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [Finite (ResidueField Λ)]
    [CommRing B] [IsLocalRing B] [AddCommGroup M] [Module B M] [Module Λ M] [Module.Finite Λ M] (t : Λ →+* B)
    (ht : ∀ (a : Λ) (x : M), a • x = t a • x) (j : ℕ) :
    ∃ e : ℕ, (maximalIdeal B ^ e • ⊤ : Submodule B M) ≤ (maximalIdeal Λ ^ j).map t • ⊤ := by
  haveI h0 : Finite (Λ ⧸ maximalIdeal Λ) := ‹Finite (ResidueField Λ)›
  haveI h1 : Finite (Λ ⧸ maximalIdeal Λ ^ j) := Ideal.finite_quotient_pow (IsNoetherian.noetherian _) j
  haveI h2 : Finite (M ⧸ (maximalIdeal Λ ^ j • ⊤ : Submodule Λ M)) :=
    Submodule.finite_quotient_smul _ (Module.Finite.fg_top)
  have hle : ∀ x ∈ (maximalIdeal Λ ^ j • ⊤ : Submodule Λ M), x ∈ ((maximalIdeal Λ ^ j).map t • ⊤ : Submodule B M) := by
    intro x hx
    refine Submodule.smul_induction_on hx ?_ fun a b ha hb => Submodule.add_mem _ ha hb
    intro a ha y _
    rw [ht]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) Submodule.mem_top
  let Q := M ⧸ ((maximalIdeal Λ ^ j).map t • ⊤ : Submodule B M)
  let g : (M ⧸ (maximalIdeal Λ ^ j • ⊤ : Submodule Λ M)) → Q := fun q =>
    Quotient.liftOn' q (fun x => Submodule.Quotient.mk x)
      (fun a b h => (Submodule.Quotient.eq _).2 (hle _ ((Submodule.quotientRel_def _).1 h)))
  haveI : Finite Q := by
    refine Finite.of_surjective g fun z => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  let F : ℕ →o (Submodule B Q)ᵒᵈ :=
    ⟨fun n => OrderDual.toDual (maximalIdeal B ^ n • (⊤ : Submodule B Q)), fun m n h =>
      OrderDual.toDual_le_toDual.2 (Submodule.smul_mono_left (Ideal.pow_le_pow_right h))⟩
  obtain ⟨c, hc⟩ := IsArtinian.monotone_stabilizes F
  have h3 : (maximalIdeal B ^ c • (⊤ : Submodule B Q)) = maximalIdeal B ^ (c + 1) • (⊤ : Submodule B Q) :=
    congrArg OrderDual.ofDual (hc (c + 1) (Nat.le_succ c))
  have h4 : (maximalIdeal B ^ c • (⊤ : Submodule B Q)) = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal B) _ (IsNoetherian.noetherian _) ?_ ?_
    · rw [← mul_smul, ← pow_succ', ← h3]
    · rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  refine ⟨c, Submodule.smul_le.2 fun a ha z _ => ?_⟩
  have h5 : a • (Submodule.Quotient.mk z : Q) ∈ (maximalIdeal B ^ c • (⊤ : Submodule B Q)) :=
    Submodule.smul_mem_smul ha Submodule.mem_top
  rw [h4, Submodule.mem_bot] at h5
  exact (Submodule.Quotient.mk_eq_zero _).1 h5

private theorem mem_map_smul_top_iff_mem_smul_top {R S X : Type} [CommRing R] [CommRing S] [AddCommGroup X] [Module R X] [Module S X]
    (π : R →+* S) (h : ∀ (a : R) (x : X), a • x = π a • x) (K : Ideal R) (x : X) :
    x ∈ (K.map π • ⊤ : Submodule S X) ↔ x ∈ (K • ⊤ : Submodule R X) := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ fun a b ha hb => Submodule.add_mem _ ha hb
    intro t ht y _
    refine Submodule.span_induction (p := fun t _ => ∀ y : X, t • y ∈ (K • ⊤ : Submodule R X)) ?_ ?_ ?_ ?_ ht y
    · rintro _ ⟨z, hz, rfl⟩ y
      rw [← h]
      exact Submodule.smul_mem_smul hz Submodule.mem_top
    · intro y
      simp
    · intro a b _ _ ha hb y
      rw [add_smul]
      exact Submodule.add_mem _ (ha y) (hb y)
    · intro a b _ hb y
      rw [smul_eq_mul, mul_comm, mul_smul]
      exact hb _
  · intro hx
    refine Submodule.smul_induction_on hx ?_ fun a b ha hb => Submodule.add_mem _ ha hb
    intro a ha y _
    rw [h]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) Submodule.mem_top

private theorem quotient_addEquiv_of_restricted_scalars {R S X : Type} [CommRing R] [CommRing S] [AddCommGroup X] [Module R X] [Module S X]
    (π : R →+* S) (h : ∀ (a : R) (x : X), a • x = π a • x) (K : Ideal R) (KS : Ideal S) (hK : K.map π = KS) :
    ∃ e : (X ⧸ (K • ⊤ : Submodule R X)) ≃+ (X ⧸ (KS • ⊤ : Submodule S X)), ∀ (a : R) z, e (a • z) = π a • e z := by
  subst hK
  have h1 : (K • ⊤ : Submodule R X).toAddSubgroup = (K.map π • ⊤ : Submodule S X).toAddSubgroup := by
    ext x
    exact (mem_map_smul_top_iff_mem_smul_top π h K x).symm
  refine ⟨QuotientAddGroup.quotientAddEquivOfEq h1, fun a z => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  change (Submodule.Quotient.mk (a • x) : X ⧸ (K.map π • ⊤ : Submodule S X)) = π a • Submodule.Quotient.mk x
  rw [h, Submodule.Quotient.mk_smul]

private theorem quotient_linear_equiv_of_factorization {R X Y Z M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module R Z] [AddCommGroup M] [Module R M] (K : Ideal R) (f f' : R) (hf : f - f' ∈ K)
    (κ : (X ⧸ (K • ⊤ : Submodule R X)) ≃ₗ[R] (Y ⧸ (K • ⊤ : Submodule R Y)))
    (p : M →ₗ[R] Z) (hp : Function.Surjective p) (hk : LinearMap.ker p ≤ K • ⊤)
    (φ : Y →ₗ[R] Z) (ψ : Z →ₗ[R] Y) (h1 : ∀ z, φ (ψ z) = f' • z) (h2 : ∀ z, ψ (φ z) = f' • z) :
    ∃ (φ : (X ⧸ (K • ⊤ : Submodule R X)) →ₗ[R] (M ⧸ (K • ⊤ : Submodule R M)))
      (ψ : (M ⧸ (K • ⊤ : Submodule R M)) →ₗ[R] (X ⧸ (K • ⊤ : Submodule R X))),
      (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z := by
  have hm : ∀ {A B : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] (g : A →ₗ[R] B),
      (K • ⊤ : Submodule R A) ≤ (K • ⊤ : Submodule R B).comap g := by
    intro A B _ _ _ _ g
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact smul_mono_right _ le_top
  have hff : ∀ {A : Type} [AddCommGroup A] [Module R A] (x : A),
      (Submodule.Quotient.mk (f' • x) : A ⧸ (K • ⊤ : Submodule R A)) = f • Submodule.Quotient.mk x := by
    intro A _ _ x
    rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq, ← sub_smul]
    exact Submodule.smul_mem_smul hf Submodule.mem_top
  have hb : Function.Bijective (Submodule.mapQ _ _ p (hm p)) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro z hz
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, ← LinearMap.range_eq_top.2 hp, ← Submodule.map_top,
        ← Submodule.map_smul''] at hz
      obtain ⟨y, hy, hxy⟩ := hz
      rw [Submodule.Quotient.mk_eq_zero]
      have h3 : x - y ∈ LinearMap.ker p := by rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
      simpa using Submodule.add_mem _ (hk h3) hy
    · intro z
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      obtain ⟨y, rfl⟩ := hp x
      exact ⟨Submodule.Quotient.mk y, rfl⟩
  let e := LinearEquiv.ofBijective _ hb
  have h3 : ∀ z, Submodule.mapQ _ _ φ (hm φ) (Submodule.mapQ _ _ ψ (hm ψ) z) = f • z := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, h1, hff]
  have h4 : ∀ z, Submodule.mapQ _ _ ψ (hm ψ) (Submodule.mapQ _ _ φ (hm φ) z) = f • z := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, h2, hff]
  refine ⟨e.symm.toLinearMap ∘ₗ Submodule.mapQ _ _ φ (hm φ) ∘ₗ κ.toLinearMap,
    κ.symm.toLinearMap ∘ₗ Submodule.mapQ _ _ ψ (hm ψ) ∘ₗ e.toLinearMap, fun z => ?_, fun z => ?_⟩
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, h3, map_smul,
      LinearEquiv.symm_apply_apply]
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, h4, map_smul,
      LinearEquiv.symm_apply_apply]

private theorem quotient_equiv_of_compatible_ring_homs {R R' S S' X Y M : Type} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [AddCommGroup X] [Module R X] [Module S X] [AddCommGroup Y] [Module S' Y] [AddCommGroup M] [Module R M] [Module R' M]
    (π : R →+* S) (ρ : R →+* R') (θ : R' →+* S') (hX : ∀ (a : R) (x : X), a • x = π a • x)
    (hM : ∀ (a : R) (x : M), a • x = ρ a • x) (K : Ideal R) (KS : Ideal S) (KS' : Ideal S') (Iy : Ideal R')
    (hKS : K.map π = KS) (hKS' : K.map (θ.comp ρ) = KS') (hI : Iy ≤ K.map ρ) (f f' : R) (hf : f - f' ∈ K)
    (κ : (X ⧸ (KS • ⊤ : Submodule S X)) ≃+ (Y ⧸ (KS' • ⊤ : Submodule S' Y)))
    (hκ : ∀ a x, κ (π a • x) = θ (ρ a) • κ x)
    (φ : Y →+ M ⧸ (Iy • ⊤ : Submodule R' M)) (ψ : (M ⧸ (Iy • ⊤ : Submodule R' M)) →+ Y)
    (hφ : ∀ t z, φ (θ t • z) = t • φ z) (hψ : ∀ t z, ψ (t • z) = θ t • ψ z)
    (h1 : ∀ z, φ (ψ z) = ρ f' • z) (h2 : ∀ z, ψ (φ z) = θ (ρ f') • z) :
    ∃ (φ : (X ⧸ (K • ⊤ : Submodule R X)) →ₗ[R] (M ⧸ (K • ⊤ : Submodule R M)))
      (ψ : (M ⧸ (K • ⊤ : Submodule R M)) →ₗ[R] (X ⧸ (K • ⊤ : Submodule R X))),
      (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z := by
  letI : Module R Y := Module.compHom Y (θ.comp ρ)
  letI : Module R (M ⧸ (Iy • ⊤ : Submodule R' M)) := Module.compHom _ ρ
  obtain ⟨e, he⟩ := quotient_addEquiv_of_restricted_scalars π hX K KS hKS
  obtain ⟨e', he'⟩ := quotient_addEquiv_of_restricted_scalars (X := Y) (θ.comp ρ) (fun _ _ => rfl) K KS' hKS'
  let κ' : (X ⧸ (K • ⊤ : Submodule R X)) ≃ₗ[R] (Y ⧸ (K • ⊤ : Submodule R Y)) :=
    ((e.trans κ).trans e'.symm).toLinearEquiv fun a x => by
      simp only [AddEquiv.trans_apply]
      rw [AddEquiv.symm_apply_eq, he', AddEquiv.apply_symm_apply, he, hκ]
      rfl
  let p : M →ₗ[R] M ⧸ (Iy • ⊤ : Submodule R' M) :=
    { toFun := Submodule.Quotient.mk
      map_add' := fun _ _ => rfl
      map_smul' := fun a x => by
        rw [hM]
        rfl }
  let φ' : Y →ₗ[R] M ⧸ (Iy • ⊤ : Submodule R' M) :=
    { toFun := φ, map_add' := φ.map_add, map_smul' := fun a x => hφ (ρ a) x }
  let ψ' : (M ⧸ (Iy • ⊤ : Submodule R' M)) →ₗ[R] Y :=
    { toFun := ψ, map_add' := ψ.map_add, map_smul' := fun a x => hψ (ρ a) x }
  refine quotient_linear_equiv_of_factorization K f f' hf κ' p (Submodule.Quotient.mk_surjective _) (fun x hx => ?_) φ' ψ' h1 h2
  exact (mem_map_smul_top_iff_mem_smul_top ρ hM K x).1 (Submodule.smul_mono_left hI ((Submodule.Quotient.mk_eq_zero _).1 hx))

private theorem map_constant_coeff_power_ideal_eq {Λ B S σ : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing B] [CommRing S] (lam : Λ →+* B)
    (i : B →+* S) (g : MvPowerSeries σ Λ →+* S) (hg : ∀ z, g z = i (lam (MvPowerSeries.constantCoeff z))) (j : ℕ) :
    (kjIdeal Λ σ 1 j).map g = ((maximalIdeal Λ ^ j).map lam).map i := by
  have h1 : (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ Λ)) ^ 1).map g = ⊥ := by
    rw [pow_one, Ideal.map_span, Ideal.span_eq_bot]
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    simp [hg]
  have h2 : g.comp MvPowerSeries.C = i.comp lam := by
    ext a
    simp [hg]
  unfold kjIdeal
  rw [Ideal.map_sup, h1, bot_sup_eq, Ideal.map_map, Ideal.map_map, h2]

private theorem quotient_equiv_congr_of_surjective_algHom {B A S S' Q Q' : Type} [CommRing B] [CommRing A] [CommRing S] [CommRing S'] [Algebra B A]
    [Algebra B S] [Algebra B S'] [AddCommGroup Q] [Module S Q] [AddCommGroup Q'] [Module S' Q'] (f : A →ₐ[B] S)
    (f' : A →ₐ[B] S') (hf : Function.Surjective f) (hf' : Function.Surjective f') (κ : Q ≃+ Q')
    (hκ : ∀ z x, κ (f z • x) = f' z • κ x) (I : Ideal A) (h0 : ∀ z ∈ I, ∀ x : Q, f z • x = 0) (s : S) (s' : S')
    (h : ∀ z z', s = f z → s' = f' z' → z - z' ∈ I) (x : Q) : κ (s • x) = s' • κ x := by
  obtain ⟨z, rfl⟩ := hf s
  obtain ⟨z', rfl⟩ := hf' s'
  have h1 := h0 _ (h z z' rfl rfl) x
  rw [map_sub, sub_smul, sub_eq_zero] at h1
  rw [h1, hκ]

theorem UpperTheory.V.Pa.Core.eventually_exists_patchedModule_quotient_maps :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), T.ProL → Adapted T (r := r) → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ (φ : (X0 m ⧸ ((kjIdeal (abelian₂ O Unit D) (Fin T.q × Fin n) 1 j).map m.s.toRingHom • ⊤ : Submodule W.R (X0 m))) →ₗ[W.R] (MN m N ⧸ ((kjIdeal (abelian₂ O Unit D) (Fin T.q × Fin n) 1 j).map m.s.toRingHom • ⊤ : Submodule W.R (MN m N)))) (ψ : (MN m N ⧸ ((kjIdeal (abelian₂ O Unit D) (Fin T.q × Fin n) 1 j).map m.s.toRingHom • ⊤ : Submodule W.R (MN m N))) →ₗ[W.R] (X0 m ⧸ ((kjIdeal (abelian₂ O Unit D) (Fin T.q × Fin n) 1 j).map m.s.toRingHom • ⊤ : Submodule W.R (X0 m)))), (∀ z, φ (ψ z) = fo W • z) ∧ ∀ z, ψ (φ z) = fo W • z := by
  intro l hl L G0 T Λ n O _ _ _ hO _ r B _ _ _ u J D A W m hP hA j
  haveI := hO.complete
  haveI := hO.finite
  haveI hco : IsCO O (abelian₂ O Unit D) := co_mvps O O _
  haveI : Finite (ResidueField (abelian₂ O Unit D)) := Finite.of_surjective _ (resMap_bijective O (abelian₂ O Unit D)).2
  haveI := A.b.fin
  obtain ⟨e, he⟩ := power_maximal_ideal_le_map_power_smul_top (abelian₂ O Unit D) B A.b.M A.b.lam.toRingHom A.b.smul_lam j
  filter_upwards [piCong l L G0 T Λ n O r B u J D A W m hP hA e, Λ.U_le (eventually_ge_atTop j)] with N hN hjN
  obtain ⟨κ, hκ, hκ0⟩ := spCong B T.q n _ _ (fun j i => algebraMap O B (A.ut j i)) _ _ A.b.M hN.1 he
  obtain ⟨-, hf, c, hc⟩ := foCong l L G0 T Λ n O r B u J D A W m j N hjN
  have hlm : (l : abelian₂ O Unit D) ∈ maximalIdeal (abelian₂ O Unit D) := by
    intro hu
    have h1 := hu.map ((residue O).comp (MvPowerSeries.constantCoeff : abelian₂ O Unit D →+* O))
    haveI := hO.char
    rw [map_natCast, CharP.cast_eq_zero] at h1
    exact not_isUnit_zero h1
  have hs : ∀ Q : Fin T.q → Polynomial B, Function.Surjective (Sp.mk Q fun j i => algebraMap O B (A.ut j i)) :=
    fun Q => Ideal.Quotient.mkₐ_surjective B _
  have key := fun a : W.R => quotient_equiv_congr_of_surjective_algHom _ _ (hs _) (hs _) κ hκ _ hκ0 _ _ (hN.2 a)
  refine quotient_equiv_of_compatible_ring_homs (X := X0 m) (M := MN m N) m.π.toRingHom (m.ρ N).toRingHom (A.m N).θ.toRingHom (fun _ _ => rfl)
    (fun _ _ => rfl) _ _ _ (Ideal.span (Set.range fun p => (A.A N).s (MvPowerSeries.X p))) ?_ ?_ ?_ (fo W)
    (fEl (T.Nq N) W.t.U) ?_ κ ?_ (A.m N).φ (A.m N).ψ (A.m N).φ_smul (A.m N).ψ_smul ?_ ?_
  · rw [Ideal.map_map]
    exact map_constant_coeff_power_ideal_eq _ _ _ m.π_s j
  · rw [Ideal.map_map]
    refine map_constant_coeff_power_ideal_eq _ _ _ (fun z => ?_) j
    exact (congrArg (A.m N).θ (m.specializationMap_comp_universalSection N z)).trans ((A.m N).theta_coefficientMap_eq z)
  · rw [Ideal.span_le]
    rintro _ ⟨p, rfl⟩
    have h1 : MvPowerSeries.X p ∈ kjIdeal (abelian₂ O Unit D) (Fin T.q × Fin n) 1 j :=
      Ideal.mem_sup_left (by rw [pow_one]; exact Ideal.subset_span (Set.mem_range_self p))
    have h2 := Ideal.mem_map_of_mem (m.ρ N).toRingHom (Ideal.mem_map_of_mem m.s.toRingHom h1)
    have h3 := m.specializationMap_comp_universalSection N (MvPowerSeries.X p)
    exact (congrArg (· ∈ _) h3).mp h2
  · rw [hc]
    refine Ideal.mul_mem_right _ _ ?_
    have h1 : MvPowerSeries.C ((l : abelian₂ O Unit D) ^ j) ∈ kjIdeal (abelian₂ O Unit D) (Fin T.q × Fin n) 1 j :=
      Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow hlm j))
    have h2 := Ideal.mem_map_of_mem m.s.toRingHom h1
    rwa [map_pow, map_natCast, map_pow, map_natCast] at h2
  · exact key
  · intro z
    exact ((A.m N).φψ z).trans (congrArg (· • z) hf.symm)
  · intro z
    exact ((A.m N).ψφ z).trans (congrArg (fun t => (A.m N).θ t • z) hf.symm)
