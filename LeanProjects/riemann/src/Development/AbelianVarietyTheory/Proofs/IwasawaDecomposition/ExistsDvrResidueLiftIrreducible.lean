import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
open IsLocalRing GlobalTheory.LN Polynomial

namespace GlobalTheory.UnramExt

theorem mem_smul_top_iff_repr {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (I : Ideal R) (x : M) :
    x ∈ (I • ⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ I := by
  constructor
  · intro hx i
    have hle : (I • ⊤ : Submodule R M) ≤ Submodule.comap (b.coord i) I :=
      Submodule.smul_le.2 fun r hr m _ => by
        rw [Submodule.mem_comap, map_smul, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
    exact hle hx
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem isAdicComplete_of_finite_basis {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (I : Ideal R) [hI : IsAdicComplete I R] :
    IsAdicComplete I M := by
  have htop : ∀ k : ℕ, (I ^ k • ⊤ : Submodule R R) = I ^ k := fun k => by
    rw [smul_eq_mul, Ideal.mul_top]
  have hH : IsHausdorff I M := by
    refine ⟨fun x hx => ?_⟩
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    rw [map_zero, Finsupp.zero_apply]
    refine IsHausdorff.haus' (I := I) _ fun n => ?_
    have := hx n
    rw [SModEq.zero, mem_smul_top_iff_repr b] at this
    rw [SModEq.zero, htop]
    exact this i
  have hP' : IsPrecomplete I M := by
    rw [isPrecomplete_iff]
    intro F hF
    have hP := hI.toIsPrecomplete
    rw [isPrecomplete_iff] at hP
    have hc : ∀ i, ∃ L : R, ∀ k, b.repr (F k) i ≡ L [SMOD (I ^ k • ⊤ : Submodule R R)] := by
      intro i
      refine hP (fun k => b.repr (F k) i) fun {m n} hmn => ?_
      have := hF hmn
      rw [SModEq.sub_mem, mem_smul_top_iff_repr b] at this
      rw [SModEq.sub_mem, htop]
      simpa using this i
    choose L hL using hc
    refine ⟨∑ i, L i • b i, fun k => ?_⟩
    rw [SModEq.sub_mem, mem_smul_top_iff_repr b]
    intro i
    have := hL i k
    rw [SModEq.sub_mem, htop] at this
    have hr : b.repr (∑ j, L j • b j) i = L i := by
      have h := congrFun (b.equivFun.apply_symm_apply L) i
      rwa [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_apply] at h
    rw [map_sub, Finsupp.sub_apply, hr]
    exact this
  exact { toIsHausdorff := hH, toIsPrecomplete := hP' }

theorem exists_unit_mul_pow {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    {π : V} (hπ : maximalIdeal V = Ideal.span {π}) (x : V) (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : V), IsUnit u ∧ x = u * π ^ n := by
  classical
  have hK : ⨅ n : ℕ, (maximalIdeal V) ^ n = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal V).ne_top
  have hex : ∃ n, x ∉ (maximalIdeal V) ^ n := by
    by_contra h
    push_neg at h
    apply hx
    have : x ∈ ⨅ n : ℕ, (maximalIdeal V) ^ n := (Submodule.mem_iInf _).2 h
    rwa [hK] at this
  have hspec := Nat.find_spec hex
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h0 => ?_
    rw [h0, pow_zero, Ideal.one_eq_top] at hspec
    exact hspec Submodule.mem_top
  have hmem : x ∈ (maximalIdeal V) ^ k := by
    have := Nat.find_min hex (show k < Nat.find hex by omega)
    simpa using this
  rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
  obtain ⟨u, hu⟩ := hmem
  refine ⟨k, u, ?_, hu.symm⟩
  by_contra hnu
  have hu' : u ∈ maximalIdeal V := (mem_maximalIdeal u).2 hnu
  apply hspec
  rw [hk, ← hu, hπ, Ideal.span_singleton_pow, pow_succ]
  rw [hπ] at hu'
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hu'
  exact Ideal.mem_span_singleton'.2 ⟨c, by ring⟩

theorem isDomain_of_maximalIdeal_eq_span {V : Type} [CommRing V] [IsLocalRing V]
    [IsNoetherianRing V] {π : V} (hπ : maximalIdeal V = Ideal.span {π}) (hn : ∀ n : ℕ, π ^ n ≠ 0) :
    IsDomain V := by
  have : NoZeroDivisors V := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra h
    push_neg at h
    obtain ⟨n, u, hu, rfl⟩ := exists_unit_mul_pow hπ a h.1
    obtain ⟨m, w, hw, rfl⟩ := exists_unit_mul_pow hπ b h.2
    have : (u * w) * π ^ (n + m) = 0 := by rw [← hab]; ring
    exact hn (n + m) ((hu.mul hw).mul_right_eq_zero.1 this)
  exact NoZeroDivisors.to_isDomain V

end GlobalTheory.UnramExt

open GlobalTheory.UnramExt in

theorem GlobalTheory.exists_unramified_ext_residue : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ {L : Type} [Field L] (v : ResidueField W →+* L), v.Finite → v.FormallyUnramified → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : W →+* V) (τ : L →+* ResidueField V), CDvr V ∧ Function.Injective f ∧ IsLocalHom f ∧ (∀ ϖ : W, Irreducible ϖ → Irreducible (f ϖ)) ∧ ∀ w : W, τ (v (residue W w)) = residue V (f w) := by
  intro W _ _ _ hW L _ v hfin hfu
  obtain ⟨hdvr, hcomp, hchar⟩ := (cDvr_iff W).1 hW
  letI : Algebra (ResidueField W) L := v.toAlgebra
  haveI : Module.Finite (ResidueField W) L := hfin
  haveI : Algebra.FormallyUnramified (ResidueField W) L := hfu
  haveI : Algebra.IsSeparable (ResidueField W) L := Algebra.FormallyUnramified.isSeparable _ _
  let pb : PowerBasis (ResidueField W) L := Field.powerBasisOfFiniteOfSeparable _ L
  set gb := minpoly (ResidueField W) pb.gen with hgb
  have hgb_mon : gb.Monic := minpoly.monic pb.isIntegral_gen
  have hgb_irr : Irreducible gb := minpoly.irreducible pb.isIntegral_gen
  have hgb_deg : 0 < gb.natDegree := minpoly.natDegree_pos pb.isIntegral_gen
  have hlift : gb ∈ lifts (residue W) :=
    (lifts_iff_coeff_lifts gb).2 fun n => residue_surjective _
  obtain ⟨g, hgmap, hgdeg, hgmon⟩ := lifts_and_natDegree_eq_and_monic hlift hgb_mon
  have hgdeg' : g.degree ≠ 0 := by
    rw [degree_eq_natDegree hgmon.ne_zero, hgdeg]
    exact_mod_cast hgb_deg.ne'
  let V := AdjoinRoot g
  let f : W →+* V := algebraMap W V
  have hfof : f = AdjoinRoot.of g := AdjoinRoot.algebraMap_eq g
  have hfinj : Function.Injective f := by
    rw [hfof]; exact AdjoinRoot.of.injective_of_degree_ne_zero hgdeg'
  let pbV : PowerBasis W V := AdjoinRoot.powerBasis' hgmon
  haveI : Module.Finite W V := pbV.finite
  haveI : Algebra.IsIntegral W V := inferInstance
  haveI : IsNoetherianRing V := isNoetherian_of_tower W (inferInstance : IsNoetherian W V)
  set mW := maximalIdeal W with hmWdef
  set M : Ideal V := Ideal.map f mW with hMdef

  have hirr : Irreducible (g.map (Ideal.Quotient.mk mW)) := by
    have := hgb_irr
    rw [← hgmap] at this
    exact this
  haveI hmWmax : mW.IsMaximal := maximalIdeal.isMaximal W
  letI : Field (W ⧸ mW) := Ideal.Quotient.field mW
  have hM : M.IsMaximal := by
    have h1 := PrincipalIdealRing.isMaximal_of_irreducible hirr
    have h2 := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 h1
    rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
    have e := AdjoinRoot.quotEquivQuotMap g mW
    rw [hMdef, hfof]
    exact MulEquiv.isField h2 e.toRingEquiv.toMulEquiv
  have huniq : ∀ P : Ideal V, P.IsMaximal → P = M := by
    intro P hP
    have h1 : (P.comap (algebraMap W V)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
    have h2 : P.comap f = mW := IsLocalRing.eq_maximalIdeal h1
    have h3 : M ≤ P := Ideal.map_le_iff_le_comap.2 h2.ge
    exact (hM.eq_of_le hP.ne_top h3).symm
  haveI : IsLocalRing V := IsLocalRing.of_unique_max_ideal ⟨M, hM, fun P hP => huniq P hP⟩
  have hmV : maximalIdeal V = M := huniq _ (maximalIdeal.isMaximal V)
  have hspan : ∀ ϖ : W, Irreducible ϖ → maximalIdeal V = Ideal.span {f ϖ} := by
    intro ϖ hϖ
    rw [hmV, hMdef, hmWdef, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
      Set.image_singleton]
  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hpow : ∀ n : ℕ, f ϖ₀ ^ n ≠ 0 := by
    intro n h
    rw [← map_pow, ← map_zero f] at h
    exact pow_ne_zero n hϖ₀.ne_zero (hfinj h)
  haveI hdom : IsDomain V := isDomain_of_maximalIdeal_eq_span (hspan ϖ₀ hϖ₀) hpow
  have hirrV : Irreducible (f ϖ₀) := by
    have hprime : (Ideal.span {f ϖ₀}).IsPrime := by
      rw [← hspan ϖ₀ hϖ₀]; exact (maximalIdeal.isMaximal V).isPrime
    have hne : f ϖ₀ ≠ 0 := by simpa using hpow 1
    exact ((Ideal.span_singleton_prime hne).1 hprime).irreducible
  haveI hdvrV : IsDiscreteValuationRing V := by
    refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨f ϖ₀, hirrV, ?_⟩
    intro x hx
    obtain ⟨n, u, hu, rfl⟩ := exists_unit_mul_pow (hspan ϖ₀ hϖ₀) x hx
    exact ⟨n, hu.unit, by simp [mul_comm]⟩
  haveI hloc : IsLocalHom f := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : f a ∈ maximalIdeal V := by
      rw [hmV]; exact Ideal.mem_map_of_mem f ((mem_maximalIdeal a).2 hna)
    exact (mem_maximalIdeal _).1 this ha
  haveI : IsAdicComplete mW W := hcomp
  have hcompV : IsAdicComplete (maximalIdeal V) V := by
    rw [hmV, hMdef]
    exact (IsAdicComplete.map_algebraMap_iff mW V).2 (isAdicComplete_of_finite_basis pbV.basis mW)
  haveI : CharZero W := hchar
  have hcharV : CharZero V := charZero_of_injective_ringHom hfinj

  letI : Algebra (ResidueField W) (ResidueField V) := (ResidueField.map f).toAlgebra
  have hroot : aeval (residue V (AdjoinRoot.root g)) gb = 0 := by
    rw [aeval_def, ← hgmap, eval₂_map]
    change eval₂ ((ResidueField.map f).comp (residue W)) _ g = 0
    rw [ResidueField.map_comp_residue, ← hom_eval₂, hfof, AdjoinRoot.eval₂_root, map_zero]
  let τ : L →ₐ[ResidueField W] ResidueField V := pb.lift _ hroot
  refine ⟨V, inferInstance, hdom, inferInstance, f, τ.toRingHom, (cDvr_iff V).2 ⟨hdvrV, hcompV, hcharV⟩,
    hfinj, hloc, fun ϖ hϖ => ?_, fun w => ?_⟩
  · exact (IsDiscreteValuationRing.irreducible_iff_uniformizer (f ϖ)).2 (hspan ϖ hϖ)
  · have := τ.commutes (residue W w)
    exact this.trans (ResidueField.map_residue f w)
