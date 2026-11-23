import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.Places
import GroundTheory.ProfiniteCohomology.RealPlaces.LocalDualityPlace

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X.RealC

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem finrank_ker_sub_one_add_finrank_ker_add_one {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (h2 : (2 : k) ≠ 0) (σ : V →ₗ[k] V) (hσ : ∀ x, σ (σ x) = x) :
    Module.finrank k (LinearMap.ker (σ - 1)) + Module.finrank k (LinearMap.ker (σ + 1)) =
      Module.finrank k V := by
  have hr : LinearMap.range (σ + 1) = LinearMap.ker (σ - 1) := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply, Module.End.one_apply, map_add, hσ]
      abel
    · intro x hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
      refine ⟨(2 : k)⁻¹ • x, ?_⟩
      rw [LinearMap.add_apply, Module.End.one_apply, map_smul, hx, ← smul_add, ← two_smul k x, smul_smul,
        inv_mul_cancel₀ h2, one_smul]
  rw [← hr]
  exact LinearMap.finrank_range_add_finrank_ker (σ + 1)

variable {K : FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ}

theorem gsRoots_realConj (hℓ : 0 < ℓ)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (v : {v : InfinitePlace K.1 // v.IsReal}) (t : gsRoots S ℓ) :
    (gsRoots S ℓ).ρ (gsRealFamily S ιr v (realConj v.1 v.2)) t = -t := by
  obtain ⟨ζ, rfl⟩ : ∃ ζ : rootsOfUnity ℓ (maxUnramifiedOutside K.1 ℚ̄ S), Additive.ofMul ζ = t :=
    ⟨Additive.toMul t, rfl⟩
  change Additive.ofMul (galRootsOfUnityHom K.1 _ ℓ (gsRealFamily S ιr v (realConj v.1 v.2)) ζ) =
    Additive.ofMul ζ⁻¹
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [coe_galRootsOfUnityHom_apply]
  set f : maxUnramifiedOutside K.1 ℚ̄ S →ₐ[K.1] AlgebraicClosure v.1.Completion :=
    (ιr v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val
  have hf : Function.Injective f := f.injective
  apply hf
  set u : (AlgebraicClosure v.1.Completion)ˣ := Units.map (f : maxUnramifiedOutside K.1 ℚ̄ S →* AlgebraicClosure v.1.Completion) (ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)
  have hu : u ^ ℓ = 1 := by
    rw [← map_pow]
    have : (ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) ^ ℓ = 1 := (mem_rootsOfUnity _ _).1 ζ.2
    rw [this, map_one]
  have key := realConj_apply_of_pow_eq_one v.1 v.2 u hℓ hu
  have h1 : f ((gsRealFamily S ιr v (realConj v.1 v.2)) ((ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S)) =
      realConj v.1 v.2 (f ((ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S)) :=
    gsRealFamily_apply S ιr v _ _
  rw [h1]
  exact key

section TConj
variable [Fact ℓ.Prime]

theorem gsRootsZMod_rho_realConj_eq_neg (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (v : {v : InfinitePlace K.1 // v.IsReal}) (t : gsRootsZMod S ℓ) :
    (gsRootsZMod S ℓ).ρ (gsRealFamily S ιr v (realConj v.1 v.2)) t = -t := by
  have hℓ : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  obtain ⟨ζ, rfl⟩ : ∃ ζ : rootsOfUnity ℓ (maxUnramifiedOutside K.1 ℚ̄ S), Additive.ofMul ζ = t := ⟨t.toMul, rfl⟩
  show Additive.ofMul (galRootsOfUnityHom _ _ ℓ (gsRealFamily S ιr v (realConj v.1 v.2)) ζ) = Additive.ofMul ζ⁻¹
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [coe_galRootsOfUnityHom_apply]
  apply Subtype.val_injective
  apply (ιr v).injective
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [gsRealFamily_apply]
  set f : (maxUnramifiedOutside K.1 ℚ̄ S) →ₐ[K.1] AlgebraicClosure v.1.Completion :=
    (ιr v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val
  have hu : (Units.map f.toMonoidHom (ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ)) ^ ℓ = 1 := by
    rw [← map_pow, (mem_rootsOfUnity ℓ _).1 ζ.2, map_one]
  have := realConj_apply_of_pow_eq_one v.1 v.2 _ hℓ hu
  rw [← map_inv] at this
  exact this

theorem T_conj_gen (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (v : {v : InfinitePlace K.1 // v.IsReal}) (g : Gal(AlgebraicClosure v.1.Completion / v.1.Completion))
    (hg : g = realConj v.1 v.2) (σ : galUnramifiedOutside K.1 ℚ̄ S) (hσ : σ = gsRealFamily S ιr v g)
    (t : gsRootsZMod S ℓ) : (gsRootsZMod S ℓ).ρ σ t = -t := by
  subst hg hσ
  exact gsRootsZMod_rho_realConj_eq_neg ιr v t

end TConj

section Generic

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem invariants_eq_ker_of_two {H : Type*} [Group H] (ρ : Representation k H V) (c : H)
    (hG : ∀ g, g = 1 ∨ g = c) : ρ.invariants = LinearMap.ker (ρ c - 1) := by
  ext m
  rw [Representation.mem_invariants, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
    sub_eq_zero]
  refine ⟨fun h => h c, fun h g => ?_⟩
  rcases hG g with hg | hg
  · rw [hg, map_one, Module.End.one_apply]
  · rw [hg]
    exact h

theorem invariants_comp_subtype_eq_ker {H Γ : Type*} [Group H] [Group Γ] (ρ : Representation k Γ V)
    (D : Subgroup Γ) (ψ0 : H → Γ) (hD : ∀ τ, τ ∈ D ↔ ∃ h, ψ0 h = τ) (h1 : ψ0 1 = 1) (c : H)
    (hG : ∀ g, g = 1 ∨ g = c) :
    Representation.invariants (ρ.comp D.subtype) = LinearMap.ker (ρ (ψ0 c) - 1) := by
  ext m
  rw [Representation.mem_invariants, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
    sub_eq_zero]
  refine ⟨fun h => h ⟨ψ0 c, (hD _).2 ⟨c, rfl⟩⟩, fun h τ => ?_⟩
  obtain ⟨g, hg⟩ := (hD τ.1).1 τ.2
  change ρ τ.1 m = m
  rw [← hg]
  rcases hG g with rfl | rfl
  · rw [h1, map_one, Module.End.one_apply]
  · exact h

theorem finrank_invariants_comp_subtype_eq {H Γ : Type*} [Group H] [Group Γ] (ρ : Representation k Γ V)
    (D : Subgroup Γ) (ψ0 : H → Γ) (hD : ∀ τ, τ ∈ D ↔ ∃ h, ψ0 h = τ) (h1 : ψ0 1 = 1) (c : H)
    (hG : ∀ g, g = 1 ∨ g = c) (B : V →ₗ[k] V) (hB : ρ (ψ0 c) = B) :
    Module.finrank k (Representation.invariants (ρ.comp D.subtype)) =
      Module.finrank k (LinearMap.ker (B - 1)) := by
  rw [invariants_comp_subtype_eq_ker ρ D ψ0 hD h1 c hG, hB]

theorem finrank_ker_sub_one_of_neg {T M : Type*} [AddCommGroup T] [Module k T] [AddCommGroup M]
    [Module k M] [FiniteDimensional k M] (hT : Module.finrank k T = 1) (b : M →ₗ[k] M)
    (Ψ : (T →ₗ[k] M) →ₗ[k] (T →ₗ[k] M)) (hΨ : ∀ f t, Ψ f t = -b (f t)) :
    Module.finrank k (LinearMap.ker (Ψ - 1)) = Module.finrank k (LinearMap.ker (b + 1)) := by
  haveI : Module.Finite k T := Module.finite_of_finrank_eq_succ hT
  let b0 := Module.finBasisOfFinrankEq k T hT
  have hspan : ∀ t : T, b0.repr t 0 • b0 0 = t := fun t => by
    have := b0.sum_repr t
    rwa [Fin.sum_univ_one] at this
  let ev : (T →ₗ[k] M) →ₗ[k] M := LinearMap.applyₗ (b0 0)
  have hev : ∀ f, ev f = f (b0 0) := fun _ => rfl
  have hinj : Function.Injective ev := by
    intro f g hfg
    rw [hev, hev] at hfg
    exact b0.ext fun i => by rw [Subsingleton.elim i 0]; exact hfg
  have hsurj : Function.Surjective ev := fun m =>
    ⟨b0.constr k (fun _ => m), by rw [hev, b0.constr_basis]⟩
  let e := LinearEquiv.ofBijective ev ⟨hinj, hsurj⟩
  have hc : LinearMap.ker (Ψ - 1) = (LinearMap.ker (b + 1)).comap (e : (T →ₗ[k] M) →ₗ[k] M) := by
    ext f
    rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply]
    change _ ↔ b (f (b0 0)) + f (b0 0) = 0
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    constructor
    · intro h
      have := LinearMap.congr_fun h (b0 0)
      rw [hΨ] at this
      have h' : b (f (b0 0)) + f (b0 0) = b (f (b0 0)) + -b (f (b0 0)) := by rw [this]
      rw [h', add_neg_cancel]
    · intro h
      refine LinearMap.ext fun t => ?_
      have hb : -b (f (b0 0)) = f (b0 0) := by rw [eq_neg_of_add_eq_zero_left h, neg_neg]
      rw [hΨ, ← hspan t, map_smul, map_smul, ← smul_neg, hb]
  rw [hc, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]

end Generic

section Main

variable {L : FiniteSubfield} [Fact (K ≤ L)] [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) [Normal K.1 L.1]
  (hζ : ∃ ζ : L.1, IsPrimitiveRoot ζ ℓ)
  (M : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module.Finite (ZMod ℓ) M]
  (hM : ∀ (g : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (m : M), M.ρ g m = m)

theorem symm_gsRestrictGal (σ : galUnramifiedOutside K.1 ℚ̄ S) :
    (gsQuotientGalEquiv hL).symm (gsRestrictGal hL σ) = QuotientGroup.mk σ :=
  (gsQuotientGalEquiv hL).symm_apply_eq.2 (gsQuotientGalEquiv_mk hL σ).symm

omit [Module.Finite (ZMod ℓ) M] in

theorem nRep_gsRestrictGal (σ : galUnramifiedOutside K.1 ℚ̄ S) :
    nRep hL hζ M hM (gsRestrictGal hL σ) = (homRep (gsRootsZMod S ℓ) M).ρ σ :=
  (congrArg (quotientRep (PP hL) (homRep (gsRootsZMod S ℓ) M)
    (homRep_ρ_of_mem (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M (roots_trivial hL hζ) hM))
    (symm_gsRestrictGal hL σ)).trans (QuotientGroup.lift_mk _ _ _)

set_option maxHeartbeats 1000000 in

theorem real_place_H0_finrank_b (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (hcop : Nat.Coprime (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index ℓ)
    (hK : ℓ ≠ 2 ∨ IsTotallyComplex L.1) (v : {v : InfinitePlace K.1 // v.IsReal}) :
    (Module.finrank (ZMod ℓ) (cohomology (Rep.res (gsRealFamily S ιr v).toMonoidHom M) 0) : ℤ) +
        Module.finrank (ZMod ℓ) (Representation.invariants
          ((nRep hL hζ M hM).comp (gsRealDecompGroup S ιr hL v).subtype)) =
      Module.finrank (ZMod ℓ) M := by
  have hp : ℓ.Prime := Fact.out
  by_cases h2 : ℓ = 2
  ·
    exfalso
    subst h2
    have hTC : IsTotallyComplex L.1 := hK.resolve_left fun h => h rfl
    haveI : IsGalois K.1 L.1 := ⟨⟩
    have hcomap : (infPlaceOfEmbedding (ιr v) L : InfinitePlace L.1).comap (algebraMap K.1 L.1) = v.1 := by
      have := (infPlaceOfEmbedding (ιr v) L).2
      exact NumberField.InfinitePlace.LiesOver.comap_eq _ _
    have hram : ¬ NumberField.InfinitePlace.IsUnramified K.1
        (infPlaceOfEmbedding (ιr v) L : InfinitePlace L.1) := by
      rw [NumberField.InfinitePlace.isUnramified_iff, hcomap]
      exact not_or.2 ⟨NumberField.InfinitePlace.not_isReal_iff_isComplex.2 (hTC.isComplex _),
        NumberField.InfinitePlace.not_isComplex_iff_isReal.2 v.2⟩
    have hcard := NumberField.InfinitePlace.not_isUnramified_iff_card_stabilizer_eq_two.1 hram
    have hdvd := Subgroup.card_subgroup_dvd_card
      (MulAction.stabilizer (L.1 ≃ₐ[K.1] L.1) (infPlaceOfEmbedding (ιr v) L : InfinitePlace L.1))
    rw [hcard] at hdvd
    have hidx : Nat.card (L.1 ≃ₐ[K.1] L.1) =
        (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index :=
      (Nat.card_congr (gsQuotientGalEquiv hL).toEquiv).symm
    rw [hidx] at hdvd
    exact absurd (Nat.Coprime.coprime_dvd_left hdvd hcop) (by norm_num)
  · have h2k : (2 : ZMod ℓ) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
    let c := realConj v.1 v.2
    have hc_def : c = realConj v.1 v.2 := rfl
    have hG : ∀ g, g = 1 ∨ g = c := eq_one_or_eq_realConj v.1 v.2
    have hcinv : c⁻¹ = c := by
      rcases hG c⁻¹ with h | h
      · exact absurd (inv_eq_one.1 h) (realConj_ne_one v.1 v.2)
      · exact h
    have hcc : c * c = 1 := by
      calc c * c = c * c⁻¹ := by rw [hcinv]
        _ = 1 := mul_inv_cancel c
    let σ := gsRealFamily S ιr v c
    have hσ_def : σ = gsRealFamily S ιr v c := rfl
    have hσinv : σ⁻¹ = σ := by rw [hσ_def, ← map_inv, hcinv]
    have hσ1 : σ * σ = 1 := by rw [hσ_def, ← map_mul, hcc, map_one]
    have hσσ : ∀ x : M, M.ρ σ (M.ρ σ x) = x := fun x => by
      have h2 : M.ρ σ (M.ρ σ x) = M.ρ (σ * σ) x := (congrArg (fun A => A x) (map_mul M.ρ σ σ)).symm
      rw [h2, hσ1, map_one]
      rfl

    have e1 : Module.finrank (ZMod ℓ) (cohomology (Rep.res (gsRealFamily S ιr v).toMonoidHom M) 0) =
        Module.finrank (ZMod ℓ) (LinearMap.ker (M.ρ σ - 1)) :=
      ((H0Iso (Rep.res (gsRealFamily S ιr v).toMonoidHom M)).toLinearEquiv.finrank_eq).trans
        (LinearEquiv.ofEq _ _ (invariants_eq_ker_of_two
          (M.ρ.comp (gsRealFamily S ιr v).toMonoidHom) c hG)).finrank_eq

    have e2 : Module.finrank (ZMod ℓ) (Representation.invariants
          ((nRep hL hζ M hM).comp (gsRealDecompGroup S ιr hL v).subtype)) =
        Module.finrank (ZMod ℓ) (LinearMap.ker ((homRep (gsRootsZMod S ℓ) M).ρ σ - 1)) := by
      exact finrank_invariants_comp_subtype_eq (nRep hL hζ M hM) (gsRealDecompGroup S ιr hL v)
        (fun g => gsRestrictGal hL (gsRealFamily S ιr v g)) (fun τ => Iff.rfl) (by rw [map_one, map_one]) c hG
        _ (nRep_gsRestrictGal hL hζ M hM σ)

    have hTr : Module.finrank (ZMod ℓ) (gsRootsZMod S ℓ) = 1 := finrank_gsRootsZMod ℓ hℓS
    have hTneg := fun t : gsRootsZMod S ℓ => T_conj_gen (ℓ := ℓ) ιr v c hc_def σ⁻¹ (by rw [hσinv]) t
    have e3 : Module.finrank (ZMod ℓ) (LinearMap.ker ((homRep (gsRootsZMod S ℓ) M).ρ σ - 1)) =
        Module.finrank (ZMod ℓ) (LinearMap.ker (M.ρ σ + 1)) :=
      finrank_ker_sub_one_of_neg hTr (M.ρ σ) ((homRep (gsRootsZMod S ℓ) M).ρ σ) fun f t =>
        (LinearMap.congr_fun (homRep_ρ_apply (gsRootsZMod S ℓ) M σ f) t).trans (by
          change M.ρ σ (f ((gsRootsZMod S ℓ).ρ σ⁻¹ t)) = _
          exact (congrArg (fun x => M.ρ σ (f x)) (hTneg t)).trans (by rw [map_neg, map_neg]))
    have e4 := finrank_ker_sub_one_add_finrank_ker_add_one h2k (M.ρ σ) hσσ
    exact_mod_cast (congrArg₂ (· + ·) e1 (e2.trans e3)).trans e4

end Main

end PositivityTheory.Lit1.GEN.X.RealC

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) [Normal K.1 L.1]
  (hζ : ∃ ζ : L.1, IsPrimitiveRoot ζ ℓ)
  (M : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module.Finite (ZMod ℓ) M]
  (hM : ∀ (g : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (m : M), M.ρ g m = m)
  (hΓ : Nat.Coprime (Nat.card (L.1 ≃ₐ[K.1] L.1)) ℓ)

theorem real_place_H0_finrank (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (hcop : Nat.Coprime (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index ℓ)
    (hK : ℓ ≠ 2 ∨ IsTotallyComplex L.1) (v : {v : InfinitePlace K.1 // v.IsReal}) :
    (Module.finrank (ZMod ℓ) (cohomology (Rep.res (gsRealFamily S ιr v).toMonoidHom M) 0) : ℤ) +
        Module.finrank (ZMod ℓ) (Representation.invariants
          ((nRep hL hζ M hM).comp (gsRealDecompGroup S ιr hL v).subtype)) =
      Module.finrank (ZMod ℓ) M :=
  RealC.real_place_H0_finrank_b hL hζ M hM ιr hℓS hcop hK v

end PositivityTheory.Lit1.GEN.X
