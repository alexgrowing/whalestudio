import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAlgHomMulEquivDec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowCharPowEqSelf
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmp
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbol
import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.GlobalFields.LocalFieldAtPlace
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KummerCharacterTameFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharacterContinuousStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerOrderEqOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DecompositionGroupLocalGaloisStatement
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory

namespace GlobalTheory.CompanionTheory.KummerCup

noncomputable def muEquiv {Ω : Type} [Field Ω] {n : ℕ} [NeZero n] (ζ : Ωˣ) (hζ : IsPrimitiveRoot ζ n) :
    ZMod n ≃+ Additive (rootsOfUnity n Ω) :=
  let ζ' : rootsOfUnity n Ω := ⟨ζ, (mem_rootsOfUnity _ _).2 hζ.pow_eq_one⟩
  have h1 : ζ' ^ n = 1 := Subtype.ext hζ.pow_eq_one
  let f : ZMod n →+ Additive (rootsOfUnity n Ω) :=
    { toFun := fun m => Additive.ofMul (ζ' ^ m.val)
      map_zero' := by simp
      map_add' := fun a b => by
        rw [ZMod.val_add, ← pow_eq_pow_mod _ h1, pow_add, ofMul_mul] }
  AddEquiv.ofBijective f (by
    have hinj : Function.Injective f := by
      intro a b hab
      have h2 : ζ ^ a.val = ζ ^ b.val := by
        have := congrArg (fun w => ((Additive.toMul w : rootsOfUnity n Ω) : Ωˣ)) hab
        simpa [f, ζ'] using this
      have h3 := hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h2
      exact ZMod.val_injective n h3
    refine ⟨hinj, fun w => ?_⟩
    have hζ' : IsPrimitiveRoot (ζ : Ω) n := IsPrimitiveRoot.coe_units_iff.2 hζ
    have hw : (((Additive.toMul w : rootsOfUnity n Ω) : Ωˣ) : Ω) ^ n = 1 := by
      have := (mem_rootsOfUnity _ _).1 (Additive.toMul w).2
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    obtain ⟨i, hi, hie⟩ := hζ'.eq_pow_of_pow_eq_one hw
    refine ⟨(i : ZMod n), ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    change (((ζ' ^ ((i : ZMod n)).val : rootsOfUnity n Ω) : Ωˣ) : Ω) = _
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi, ← hie]
    simp [ζ'])

theorem muEquiv_apply {Ω : Type} [Field Ω] {n : ℕ} [NeZero n] (ζ : Ωˣ) (hζ : IsPrimitiveRoot ζ n) (m : ZMod n) :
    (((Additive.toMul (muEquiv ζ hζ m) : rootsOfUnity n Ω) : Ωˣ)) = ζ ^ m.val := by
  simp [muEquiv]

attribute [local instance 2000] Rep.hV2

theorem cochainOf_cyclesMap {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A B : Rep.{0} k G} [IsDiscreteRep A] [IsDiscreteRep B] (φ : A ⟶ B) (x : cocycles A 2) (s : Fin 2 → G) :
    cochainOf B (cocycleι B 2 ((HomologicalComplex.cyclesMap (cochainsMap φ) 2).hom x)) s =
      φ.hom (cochainOf A (cocycleι A 2 x) s) := by
  have e := congrArg (fun ψ => cochainOf B (ψ.hom x)) (HomologicalComplex.cyclesMap_i (cochainsMap φ) 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
  change cochainOf B (((cochainsComplex B).iCycles 2).hom _) s = _
  rw [e, cochainOf_cochainsMap_f]
  rfl

theorem inv_class (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [ValuativeRel Ω] [TopologicalSpace Ω]
    [IsValuativeTopology Ω] [ValuativeExtension K Ω] (n : ℕ) [NeZero n]
    (ζ y : Ωˣ) (a : Kˣ) (hζ : IsPrimitiveRoot ζ n)
    (ha : ord (a : K) = 1) (hy : (y : Ω) ^ n = algebraMap K Ω a)
    (κ χ : Gal(Ω/K) → ZMod n)
    (hκ : ∀ g : Gal(Ω/K), g (y : Ω) = (ζ : Ω) ^ (κ g).val * y)
    (hadd : ∀ g h, χ (g * h) = χ g + χ h) (hcont : Continuous χ)
    (hF : ∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ g = 1)
    (x : cocycles (galRootsOfUnity.{0} K Ω n) 2)
    (hx : ∀ s : Fin 2 → Gal(Ω/K), cochainOf _ (cocycleι _ 2 x) s = muEquiv ζ hζ (κ (s 0) * χ (s 1))) :
    brauerInv K Ω ((cohomologyMap (rootsOfUnityToUnits K Ω n) 2).hom (cohomologyπ _ 2 x)) = - zmodToQZ n 1 := by
  have hJx := ConcreteCategory.congr_hom (cohomologyπ_comp_cohomologyMap (rootsOfUnityToUnits K Ω n) 2) x
  have hJx' : (cohomologyMap (rootsOfUnityToUnits K Ω n) 2).hom (cohomologyπ _ 2 x) =
      cohomologyπ _ 2 ((HomologicalComplex.cyclesMap (cochainsMap (rootsOfUnityToUnits K Ω n)) 2).hom x) := hJx
  rw [hJx']
  refine GlobalTheory.T.kummer_character_tame_formula K Ω n ζ y a hζ.pow_eq_one ha hy κ χ hκ hadd hcont hF _ fun s => ?_
  rw [cochainOf_cyclesMap, hx, rootsOfUnityToUnits_hom_apply, muEquiv_apply]

theorem generates_of_inv {n : ℕ} [NeZero n] {H : Type} [AddCommGroup H] [Module (ZMod n) H] (T : H →+ QZ)
    (hT : Function.Injective T) (w : H) (h : T w = - zmodToQZ n 1) :
    Submodule.span (ZMod n) {w} = ⊤ := by
  have hTn : ∀ x, n • T x = 0 := by
    intro x
    rw [← map_nsmul]
    have : n • x = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
    rw [this, map_zero]
  rw [Submodule.eq_top_iff']
  intro x
  obtain ⟨b, hb⟩ := exists_zmodToQZ_eq (hTn x)
  have hx : x = (-b) • w := by
    apply hT
    rw [← hb]
    have : (-b) • w = ((-b).val) • w := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_zmod_val]
    rw [this, map_nsmul, h, ← map_neg, ← map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
    simp
  rw [hx]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem mu_equivariant (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (n : ℕ) [NeZero n]
    (c : Gal(Ω/K) →* (ZMod n)ˣ) (ζ : Ωˣ) (hζ : IsPrimitiveRoot ζ n)
    (hc : ∀ g : Gal(Ω/K), g (ζ : Ω) = (ζ : Ω) ^ ((c g : (ZMod n)ˣ) : ZMod n).val)
    (g : Gal(Ω/K)) (m : ZMod n) : muEquiv ζ hζ (charRep c g m) =
      (galRootsOfUnity.{0} K Ω n).ρ g (muEquiv ζ hζ m) := by
  rw [galRootsOfUnity_ρ_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  change (((Additive.toMul (muEquiv ζ hζ (charRep c g m)) : rootsOfUnity n Ω) : Ωˣ) : Ω) =
    g (((Additive.toMul (muEquiv ζ hζ m) : rootsOfUnity n Ω) : Ωˣ) : Ω)
  rw [muEquiv_apply, muEquiv_apply, charRep_apply, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
    map_pow, hc, ← pow_mul, ZMod.val_mul]
  have h1 : (ζ : Ω) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]
  rw [← pow_eq_pow_mod _ h1]

theorem core (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [ValuativeRel Ω] [TopologicalSpace Ω]
    [IsValuativeTopology Ω] [ValuativeExtension K Ω] (n : ℕ) [NeZero n] (hn : (n : K) ≠ 0)
    (c : Gal(Ω/K) →* (ZMod n)ˣ) (ζ y : Ωˣ) (a : Kˣ) (hζ : IsPrimitiveRoot ζ n)
    (hc : ∀ g : Gal(Ω/K), g (ζ : Ω) = (ζ : Ω) ^ ((c g : (ZMod n)ˣ) : ZMod n).val)
    (ha : ord (a : K) = 1) (hy : (y : Ω) ^ n = algebraMap K Ω a)
    (κ χ : Gal(Ω/K) → ZMod n)
    (hκ : ∀ g : Gal(Ω/K), g (y : Ω) = (ζ : Ω) ^ (κ g).val * y)
    (hadd : ∀ g h, χ (g * h) = χ g + χ h)
    (hF : ∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ g = 1)
    (z : Z2 (charRep c)) (hz : ∀ g h, z.1 (g, h) = κ g * χ h) :
    Submodule.span (ZMod n) {(Submodule.Quotient.mk z : H2 (charRep c))} = ⊤ := by
  have hcont := GlobalTheory.T.unramified_character_continuous K Ω n χ hadd hF
  have he := mu_equivariant K Ω n c ζ hζ hc
  obtain ⟨e2, hex, he2⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 Gal(Ω/K) (ZMod n) (ZMod n) (charRep c)
    (galRootsOfUnity.{0} K Ω n) (muEquiv ζ hζ) he
  have hJ : Function.Injective (cohomologyMap (rootsOfUnityToUnits K Ω n) 2).hom :=
    cohomologyMap_f_injective_of_subsingleton (kummerSequence_shortExact (K := K) (L := Ω) n hn) 1
      subsingleton_cohomology_one_galUnits
  let T : H2 (charRep c) →+ QZ := ((brauerInv K Ω).comp
    (cohomologyMap (rootsOfUnityToUnits K Ω n) 2).hom.toAddMonoidHom).comp e2.toAddMonoidHom
  have hTinj : Function.Injective T :=
    (brauerInv_bijective K Ω).1.comp (hJ.comp e2.injective)
  have hT1 : T (Submodule.Quotient.mk z) = - zmodToQZ n 1 := by
    obtain ⟨x, hx⟩ := hex z
    change brauerInv K Ω ((cohomologyMap (rootsOfUnityToUnits K Ω n) 2).hom (e2 (Submodule.Quotient.mk z))) = _
    rw [he2 z x hx]
    exact inv_class K Ω n ζ y a hζ ha hy κ χ hκ hadd hcont hF x fun s => by rw [hx, hz]
  exact generates_of_inv T hTinj _ hT1

theorem core_dec (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (n : ℕ) [NeZero n] (hn : (n : K) ≠ 0)
    (D : Type) [Group D] [TopologicalSpace D] (ε : Gal(Ω/K) ≃ₜ* D)
    (c : D →* (ZMod n)ˣ) (ζ y : Ωˣ) (a : Kˣ) (hζ : IsPrimitiveRoot ζ n)
    (hc : ∀ g : Gal(Ω/K), g (ζ : Ω) = (ζ : Ω) ^ ((c (ε g) : (ZMod n)ˣ) : ZMod n).val)
    (ha : ord (a : K) = 1) (hy : (y : Ω) ^ n = algebraMap K Ω a)
    (κ χ : D → ZMod n)
    (hκ : ∀ g : Gal(Ω/K), g (y : Ω) = (ζ : Ω) ^ (κ (ε g)).val * y)
    (hadd : ∀ g h, χ (g * h) = χ g + χ h)
    (hF : ∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ (ε g) = 1)
    (z : Z2 (charRep c)) (hz : ∀ g h, z.1 (g, h) = κ g * χ h) :
    Submodule.span (ZMod n) {(Submodule.Quotient.mk z : H2 (charRep c))} = ⊤ := by
  letI := algebraicValuativeRel K Ω
  letI := algebraicTopology K Ω
  haveI := algebraicValuativeRel_valuativeExtension K Ω
  haveI := algebraicTopology_isValuativeTopology K Ω
  let c' : Gal(Ω/K) →* (ZMod n)ˣ := c.comp (ε : Gal(Ω/K) →* D)
  let T := ReciprocityTheory.Neutral.Bridge.equivH2OfIso ε (charRep c) (charRep c') (fun _ _ => rfl)
  let z' : Z2 (charRep c') := ReciprocityTheory.Gal.compatiblePairCocycles2 (charRep c) (charRep c')
    (ε : Gal(Ω/K) →* D) (ReciprocityTheory.Neutral.Bridge.continuous_coe_iso ε) LinearMap.id continuous_id (fun _ _ => rfl) z
  have hspan := core K Ω n hn c' ζ y a hζ hc ha hy (fun g => κ (ε g)) (fun g => χ (ε g)) hκ
    (fun g h => by rw [map_mul, hadd]) hF z' (fun g h => hz _ _)
  rw [Submodule.eq_top_iff']
  intro x
  have hx : T x ∈ Submodule.span (ZMod n) {(Submodule.Quotient.mk z' : H2 (charRep c'))} := by
    rw [hspan]; trivial
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hx
  have : x = b • (Submodule.Quotient.mk z : H2 (charRep c)) := by
    apply T.injective
    rw [← hb, map_smul, show T (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' from
      ReciprocityTheory.Neutral.Bridge.equivH2OfIso_mk ε _ _ _ z]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem cyc_apply (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] [CharZero Ω] (l : ℕ)
    [Fact l.Prime] (r : ℕ) (ζ : Ω) (hζ : ζ ^ (l ^ r) = 1) (σ : G F Ω) :
    σ ζ = ζ ^ ((cycMod F Ω l r σ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by
  haveI : ∀ i, NeZero (l ^ i) := fun i => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  exact cyclotomicCharacter.spec (L := Ω) l (σ : Ω ≃+* Ω) ζ hζ

theorem span_class_eq_top : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (ϖ : 𝓞 F) (y : Ω) (κ χ : Dec (F := F) A → ZMod (l ^ r)) (z : Z2 (muLoc F l r A)), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → y ^ (l ^ r) = algebraMap F Ω (ϖ : F) → (∀ g : Dec (F := F) A, (g : G F Ω) y = ζ ^ (κ g).val * y) → (∀ g h, χ (g * h) = χ g + χ h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0) → (∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1) → (∀ g h, z.1 (g, h) = κ g * χ h) → Submodule.span (ZMod (l ^ r)) {(Submodule.Quotient.mk z : H2 (muLoc F l r A))} = ⊤ := by
  intro F Ω _ _ _ _ _ l _ r hr ζ hζ A v hA ϖ y κ χ z h1 h2 h3 h4 h5 h6 h7 h8
  have hl0 : l ^ r ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  haveI : NeZero (l ^ r) := ⟨hl0⟩
  obtain ⟨ι, e, hec, hes, hl⟩ := GlobalTheory.CompanionTheory.DecGal.exists_algHom_mulEquiv_dec F Ω A v hA
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  haveI : IsSepClosure (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)) :=
    ⟨inferInstance, inferInstance⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hϖ0 : (ϖ : F) ≠ 0 := by
    intro h
    have : ϖ = 0 := by exact_mod_cast h
    exact h2 (this ▸ Ideal.zero_mem _)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hl0] at h3
    exact hϖ0 ((map_eq_zero_iff _ (algebraMap F Ω).injective).1 h3.symm)
  have hιζ : IsPrimitiveRoot (ι ζ) (l ^ r) := hζ.map_of_injective ι.injective
  have hιy : ι y ≠ 0 := (map_ne_zero_iff _ ι.injective).2 hy0
  have ha0 : algebraMap F (v.adicCompletion F) (ϖ : F) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap F (v.adicCompletion F)).injective).2 hϖ0
  refine core_dec (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)) (l ^ r)
    (Nat.cast_ne_zero.2 hl0) (Dec (F := F) A) { e with continuous_toFun := hec, continuous_invFun := hes }
    ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) (Units.mk0 (ι ζ) (hιζ.ne_zero hl0)) (Units.mk0 (ι y) hιy)
    (Units.mk0 _ ha0) (IsPrimitiveRoot.coe_units_iff.1 hιζ) ?_ (GlobalTheory.T.uniformizer_order_eq_one F v ϖ h1 h2) ?_ κ χ ?_ h5 ?_ z h8
  · intro g
    change g (ι ζ) = (ι ζ) ^ _
    rw [← hl, cyc_apply F Ω l r ζ hζ.pow_eq_one, map_pow]
    rfl
  · change (ι y) ^ (l ^ r) = _
    rw [← map_pow, h3, ι.commutes]
    exact IsScalarTower.algebraMap_apply F _ _ _
  · intro g
    change g (ι y) = (ι ζ) ^ _ * ι y
    rw [← hl]
    refine (congrArg ι (h4 (e g))).trans ?_
    rw [map_mul, map_pow]
    rfl
  · intro g hg
    exact h7 _ (GlobalTheory.T.decomposition_group_local_galois F Ω A v hA ι _ g (e g).2 (hl g) hg)

end GlobalTheory.CompanionTheory.KummerCup
