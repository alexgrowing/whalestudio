import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LiftGens
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.H0Nu
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.RootVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ShaLeV

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

private theorem exists_ab (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {A : Type} [CommGroup A] (θ : G k Ω →* A) (hθ : IsOpen (θ.ker : Set (G k Ω))) :
    ∃ L : IntermediateField k Ω, FiniteDimensional k L ∧ IsAbelianGalois k L ∧ galOf k L Ω = θ.ker ∧
      ∀ x : Ω, (∀ g ∈ θ.ker, g x = x) → x ∈ L := by
  classical
  set K := IntermediateField.fixedField θ.ker with hK
  have hfix : K.fixingSubgroup = θ.ker :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨θ.ker, Subgroup.isClosed_of_isOpen _ hθ⟩
  have hfin : FiniteDimensional k K := by
    rw [← InfiniteGalois.isOpen_iff_finite, hfix]
    exact hθ
  have hgal : IsGalois k K := by
    rw [← InfiniteGalois.normal_iff_isGalois, hfix]
    exact θ.normal_ker
  refine ⟨K, hfin, ?_, ?_, ?_⟩
  · refine { toIsGalois := hgal, is_comm := ⟨fun x y => ?_⟩ }
    obtain ⟨x, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) Ω x
    obtain ⟨y, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) Ω y
    rw [← map_mul, ← map_mul, MonoidHom.eq_iff, IntermediateField.restrictNormalHom_ker, hfix,
      MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, mul_comm (θ y) (θ x), inv_mul_cancel]
  · ext σ
    rw [UpperTheory.V.Base.mem_galOf, ← hfix, IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x.1 x.2⟩
  · intro x hx
    exact (IntermediateField.mem_fixedField_iff _ _).2 hx

private theorem len_fin {R M : Type} [Ring R] [AddCommGroup M] [Module R M] (h : Finite M) :
    Module.length R M ≠ ⊤ := Module.length_ne_top

theorem UpperTheory.V.X.soFin :
    ∀ CK : ℝ, LemmaK CK → GlobalTheory.Published.PoitouTateDuality → LocalFinitenessK → LocalTateDualityK → ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ψ : G k Ω →* Oˣ), IsOpen (ψ.ker : Set (G k Ω)) → ∀ e : ℕ, 1 ≤ e → Chr.V l e ψ ≠ ⊤ := by
  intro CK hK hPT hLF hLT k Ω _ _ _ _ _ l _ O _ _ _ _ _ ψ hψ e he
  classical
  set N : ℕ := if l = 2 then 4 else l with hN
  have hN2 : 2 < N := by
    have := (Fact.out : l.Prime).two_le
    rw [hN]
    split_ifs with h <;> omega
  haveI : NeZero N := ⟨by omega⟩
  haveI : Fact (1 < N) := ⟨by omega⟩
  obtain ⟨L, hfin, hab, hgal, hmem⟩ := exists_ab k Ω (ψ.prod (Chr.cls k Ω N)) (by
    rw [MonoidHom.ker_prod, Subgroup.coe_inf]
    exact hψ.inter (Chr.clsFacts k Ω N).1)
  haveI := hfin
  haveI := hab
  haveI : NumberField L := NumberField.of_module_finite k L
  haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := k) L
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap k Ω).injective).1 inferInstance
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
  have hζL : ζ ∈ L := by
    apply hmem
    intro g hg
    have h1 : Chr.cls k Ω N g = 1 := (MonoidHom.mem_ker).1 (Subgroup.mem_inf.1 (by rwa [MonoidHom.ker_prod] at hg)).2
    rw [Chr.cls_spec N g ζ hζ.pow_eq_one, h1, Units.val_one, ZMod.val_one, pow_one]
  have hζ' : IsPrimitiveRoot (⟨ζ, hζL⟩ : L) N :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap L Ω) hζ (algebraMap L Ω).injective
  haveI htc : IsTotallyComplex L := NumberField.nrRealPlaces_eq_zero_iff.1
    (NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hN2 hζ')
  have hmu : HasMuQ l L := ⟨⟨ζ, hζL⟩, hζ'⟩
  obtain ⟨D⟩ := Formalism.GaloisCohomology.ldata_nonempty (F := L) (Ω := Ω) l
  have hsha : shaLen D (e : ℤ) ≠ ⊤ :=
    ne_top_of_le_ne_top (len_fin (R := ℤ_[l]) (hK l L Ω D htc hmu e he).1)
      (UpperTheory.V.PropA.shaLeV hPT hLF hLT L Ω l (UpperTheory.V.LDataCardLeFinrank.ptCase_of_isTotallyComplex L l) D e)
  have hle : galOf k L Ω ≤ ψ.ker := by
    rw [hgal, MonoidHom.ker_prod]
    exact inf_le_left
  have hup := Chr.upV k Ω L l O D e ψ hle Finset.univ (by rw [Finset.coe_univ, Subgroup.closure_univ])
  have heO : eO l O ≠ ⊤ := (Chr.rootVal l O 1 one_ne_zero).2.2.1
  have hopen : IsOpen (Subgroup.map (cycZ k Ω l) ψ.ker : Set ℤ_[l]ˣ) := by
    have h0 : IsOpen ((cycZ L Ω l).range : Set ℤ_[l]ˣ) := by
      rw [(UpperTheory.V.LDataCardLeFinrank.ranges L Ω l D).1]
      exact KStar.TotallyRealRoots.isOpen_galImage
    refine Subgroup.isOpen_mono ?_ h0
    rintro _ ⟨σ, rfl⟩
    refine ⟨galEmb k L Ω σ, hle ?_, ?_⟩
    · rw [← UpperTheory.V.Base.range_galEmb]
      exact ⟨σ, rfl⟩
    · rfl
  have hh0 : Chr.h0 l e ψ ⊤ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (le_trans ((Chr.h0Nu k Ω l O e ψ ⊤).1 ψ.ker le_top)
      ((Chr.h0Nu k Ω l O e ψ ψ.ker).2 le_rfl))
    exact WithTop.mul_ne_top (KStar.TotallyRealRoots.nu_ne_top hopen (by omega)) heO
  refine ne_top_of_le_ne_top ?_ hup
  exact WithTop.add_ne_top.2 ⟨WithTop.mul_ne_top hsha heO, WithTop.mul_ne_top (ENat.coe_ne_top _) hh0⟩
