import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem finite_notMem_coheight_le_one {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X] (U : X.Opens)
    (hU : (U : Set X).Nonempty) : {ξ : X | ξ ∉ U ∧ Order.coheight ξ ≤ 1}.Finite := by
  obtain ⟨S, hS, hcl, hirr, hun⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible U.isOpen.isClosed_compl
  have hg : genericPoint X ∈ U := (genericPoint_specializes hU.some).mem_open U.isOpen hU.some_mem
  refine (hS.biUnion (t := fun C => {κ | IsGenericPoint κ C}) fun C _ =>
    Set.Subsingleton.finite fun _ h _ h' => h.eq h').subset ?_
  rintro ξ ⟨hξ, h1⟩
  obtain ⟨C, hC, hξC⟩ : ξ ∈ ⋃₀ S := hun ▸ hξ
  obtain ⟨κ, hκ⟩ := QuasiSober.sober (hirr C hC) (hcl C hC)
  have hκU : κ ∈ (U : Set X)ᶜ := hun ▸ ⟨C, hC, hκ.mem⟩
  refine Set.mem_biUnion hC ?_
  by_cases h : ξ ⤳ κ
  · rwa [(h.antisymm (hκ.specializes hξC)).eq]
  · have hlt : ξ < κ := lt_of_le_not_ge (hκ.specializes hξC) h
    have hlt' : κ < genericPoint X := lt_of_le_not_ge (genericPoint_specializes κ)
      fun h' => hκU (((genericPoint_specializes κ).antisymm h').eq ▸ hg)
    have h2 := (add_le_add_left (le_add_self.trans (Order.coheight_add_one_le hlt')) 1).trans
      ((Order.coheight_add_one_le hlt).trans h1)
    exact absurd h2 (by decide)

namespace RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem isNoetherian [IsNoetherianRing o] : IsNoetherian M.Z :=
  have := M.lft
  have := M.qc
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have : CompactSpace M.Z := QuasiCompact.compactSpace_of_compactSpace M.s
  {}

theorem isNoetherianRing_O [IsNoetherianRing o] (z : M.Z) : IsNoetherianRing (M.O z) :=
  have := M.isNoetherian
  isNoetherianRing_of_ringEquiv _ (M.stalkEquiv z)

theorem coheight_le_one_of_valuationRing [IsNoetherianRing o] {ξ : M.Z} (h : ValuationRing (M.O ξ)) :
    Order.coheight ξ ≤ 1 := by
  have := M.isNoetherianRing_O ξ
  have : IsPrincipalIdealRing (M.O ξ) := IsPrincipalIdealRing.of_isNoetherianRing_of_isBezout
  have h1 : ringKrullDim (M.O ξ) ≤ 1 := Ring.krullDimLE_iff.1 inferInstance
  rw [← ringKrullDim_eq_of_ringEquiv (M.stalkEquiv ξ), ringKrullDim_stalk_eq_coheight] at h1
  exact_mod_cast h1

theorem exists_specializes_isLocalization (z : M.Z) (q : Ideal (M.O z)) [q.IsPrime] :
    ∃ (ξ : M.Z) (h : ξ ⤳ z),
      letI := (Subalgebra.inclusion (O_le_of_specializes h)).toRingHom.toAlgebra
      IsLocalization.AtPrime (M.O ξ) q := by
  obtain ⟨V, hV, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := z) trivial
  let ψ : ∀ {x : M.Z} (_ : x ∈ V), Γ(M.Z, V) →+* M.O x := fun {x} hx =>
    (M.stalkEquiv x).toRingHom.comp (M.Z.presheaf.germ V x hx).hom
  have hψ : ∀ {x : M.Z} (hx : x ∈ V) (f : Γ(M.Z, V)), ψ hx f = ⟨valF M.pt V f, valF_mem_O hx f⟩ :=
    fun hx f => stalkEquiv_germ hx f
  have hloc : ∀ (p : PrimeSpectrum Γ(M.Z, V)) (hp : hV.fromSpec p ∈ V),
      @IsLocalization.AtPrime _ _ (M.O (hV.fromSpec p)) _ (ψ hp).toAlgebra p.asIdeal _ := fun p hp => by
    let : Algebra Γ(M.Z, V) (M.Z.presheaf.stalk (hV.fromSpec p)) :=
      TopCat.Presheaf.algebra_section_stalk M.Z.presheaf (U := V) ⟨_, hp⟩
    let := (ψ hp).toAlgebra
    have : IsLocalization p.asIdeal.primeCompl (M.Z.presheaf.stalk (hV.fromSpec p)) :=
      hV.isLocalization_stalk' p hp
    exact IsLocalization.isLocalization_of_algEquiv p.asIdeal.primeCompl
      ({ M.stalkEquiv _ with commutes' := fun _ => rfl } :
        M.Z.presheaf.stalk (hV.fromSpec p) ≃ₐ[Γ(M.Z, V)] M.O (hV.fromSpec p))
  have hmem : ∀ p : PrimeSpectrum Γ(M.Z, V), hV.fromSpec p ∈ V := fun p => by
    rw [← SetLike.mem_coe, ← hV.range_fromSpec]
    exact ⟨_, rfl⟩
  obtain ⟨p₀, rfl⟩ : ∃ p₀ : PrimeSpectrum Γ(M.Z, V), hV.fromSpec p₀ = z :=
    (hV.range_fromSpec ▸ hz : z ∈ Set.range hV.fromSpec)
  let := (ψ hz).toAlgebra
  have h₀ := hloc p₀ hz
  let p : PrimeSpectrum Γ(M.Z, V) := ⟨q.comap (ψ hz), inferInstance⟩
  have hle : p.asIdeal ≤ p₀.asIdeal := fun a ha =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (M.O (hV.fromSpec p₀)) p₀.asIdeal a).1
      (IsLocalRing.le_maximalIdeal_of_isPrime q ha)
  have hs : hV.fromSpec p ⤳ hV.fromSpec p₀ :=
    ((PrimeSpectrum.le_iff_specializes p p₀).1 hle).map hV.fromSpec.continuous
  refine ⟨_, hs, ?_⟩
  let := (Subalgebra.inclusion (O_le_of_specializes hs)).toRingHom.toAlgebra
  let := (ψ (hmem p)).toAlgebra
  have h₁ := hloc p (hmem p)
  have : IsScalarTower Γ(M.Z, V) (M.O (hV.fromSpec p₀)) (M.O (hV.fromSpec p)) :=
    IsScalarTower.of_algebraMap_eq fun a => (hψ (hmem p) a).trans
      (congrArg (Subalgebra.inclusion (O_le_of_specializes hs)) (hψ hz a)).symm
  have h₂ := IsLocalization.isLocalization_of_submonoid_le (M.O (hV.fromSpec p₀)) (M.O (hV.fromSpec p))
    p₀.asIdeal.primeCompl p.asIdeal.primeCompl (fun a ha h => ha (hle h))
  refine IsLocalization.of_le_of_exists_dvd (p.asIdeal.primeCompl.map (algebraMap _ (M.O (hV.fromSpec p₀)))) _
    (by rintro _ ⟨a, ha, rfl⟩; exact ha) fun n hn => ?_
  obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj p₀.asIdeal.primeCompl n
  refine ⟨_, ⟨a, fun ha => ?_, rfl⟩, _, e.symm⟩
  have ha' : algebraMap _ (M.O (hV.fromSpec p₀)) a ∈ q := ha
  rw [← e] at ha'
  exact hn ((Ideal.mul_unit_mem_iff_mem q (IsLocalization.map_units _ s)).1 ha')

theorem mem_O_of_forall_valuationRing [IsNoetherianRing o] (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z)
    (z : M.Z) (φ : Ω) (h : ∀ ξ : M.Z, ξ ⤳ z → ValuationRing (M.O ξ) → φ ∈ M.O ξ) : φ ∈ M.O z := by
  have := M.isNoetherianRing_O z
  have := isIntegrallyClosed_O hn z
  obtain ⟨y, rfl⟩ : φ ∈ (algebraMap (M.O z) Ω).range := by
    refine (mem_range_algebraMap_iff_forall_height_eq_one φ).mpr fun q _ h1 => ?_
    obtain ⟨ξ, hξ, hloc⟩ := M.exists_specializes_isLocalization z q
    let := (Subalgebra.inclusion (O_le_of_specializes hξ)).toRingHom.toAlgebra
    have : IsScalarTower (M.O z) (M.O ξ) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have := isDiscreteValuationRing_of_height_eq_one q h1 (M.O ξ)
    exact (mem_range_algebraMap_iff_mem_primeLocalSubalgebra q (M.O ξ) φ).mp
      ⟨⟨φ, h ξ hξ inferInstance⟩, rfl⟩
  exact y.2

end RatModel

theorem normalModel_height_le_one :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) [IsNoetherianRing o],
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (z : M.Z),
      (∀ φ : Ω, (∀ ξ : M.Z, ξ ⤳ z → ValuationRing (M.O ξ) → φ ∈ M.O ξ) → φ ∈ M.O z) ∧
      IsNoetherianRing (M.O z) ∧
      ∀ U : M.Z.Opens, (U : Set M.Z).Nonempty → {ξ : M.Z | ξ ∉ U ∧ ValuationRing (M.O ξ)}.Finite := by
  intro o Ω _ _ _ M _ hn z
  have := M.isNoetherian
  exact ⟨M.mem_O_of_forall_valuationRing hn z, M.isNoetherianRing_O z, fun U hU =>
    (finite_notMem_coheight_le_one U hU).subset fun _ h => ⟨h.1, M.coheight_le_one_of_valuationRing h.2⟩⟩

end GlobalTheory.ZH
