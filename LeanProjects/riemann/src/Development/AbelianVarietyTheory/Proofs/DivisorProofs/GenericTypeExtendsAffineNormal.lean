import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomCompEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianTypeExtendsNormalSchemeStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

section Sections

variable {R A : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A] [Algebra R A] [Module.Finite R A]
  [Module.Flat R A]

theorem exists_section_comap_eq (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [IsAlgClosed K] (y : Ideal A)
    [y.IsPrime] : ∃ g : A →ₐ[R] R, y = (y.comap (algebraMap R A)).comap (g : A →+* R) := by
  haveI : y.LiesOver (y.comap (algebraMap R A)) := ⟨rfl⟩
  obtain ⟨P, hPy, hP, hPo⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal R)) (q := y.comap (algebraMap R A)) y bot_le
  have hPb : P.comap (algebraMap R A) = ⊥ := hPo.over.symm
  haveI : IsDomain (A ⧸ P) := Ideal.Quotient.isDomain P
  have hinj : Function.Injective (algebraMap R (A ⧸ P)) := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    rw [IsScalarTower.algebraMap_apply R A (A ⧸ P), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at hr
    have : r ∈ P.comap (algebraMap R A) := hr
    rwa [hPb, Ideal.mem_bot] at this
  haveI : Module.IsTorsionFree R (A ⧸ P) := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  haveI : Module.IsTorsionFree R K := Module.isTorsionFree_iff_algebraMap_injective.2 (IsFractionRing.injective R K)
  haveI : Algebra.IsAlgebraic R (A ⧸ P) := Algebra.IsIntegral.isAlgebraic
  let f : A ⧸ P →ₐ[R] K := IsAlgClosed.lift
  have hf : RingHom.ker (f : A ⧸ P →+* K) = ⊥ := by
    refine Ideal.eq_bot_of_comap_eq_bot (R := R) ?_
    ext r
    simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
    change f (algebraMap R (A ⧸ P) r) = 0 ↔ r = 0
    rw [f.commutes]
    exact ⟨fun h => IsFractionRing.injective R K (h.trans (map_zero _).symm), fun h => h ▸ map_zero _⟩
  let ψ : A →ₐ[R] K := f.comp (Ideal.Quotient.mkₐ R P)
  obtain ⟨g, hg⟩ := exists_algHom_comp_eq ψ
  have hker : ∀ a, g a = 0 → a ∈ y := fun a ha => by
    apply hPy
    have h1 : ψ a = 0 := by rw [← hg]; simp [ha]
    have h2 : Ideal.Quotient.mk P a ∈ RingHom.ker (f : A ⧸ P →+* K) := h1
    rwa [hf, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h2
  refine ⟨g, Ideal.ext fun a => ?_⟩
  have hsub : a - algebraMap R A (g a) ∈ y := hker _ (by simp)
  simp only [Ideal.mem_comap]
  constructor
  · intro ha
    have := y.sub_mem ha hsub
    simpa using this
  · intro ha
    have := y.add_mem hsub ha
    simpa using this

theorem mem_of_extends (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [IsAlgClosed K]
    (Vo : Set (PrimeSpectrum A)) (Q : Set (PrimeSpectrum R))
    (hext : ∀ (ψ : A →ₐ[R] K) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra R V] [Algebra V K]
      [IsScalarTower R V K] [IsFractionRing V K], PrimeSpectrum.comap (algebraMap R V) (IsLocalRing.closedPoint V) ∈ Q →
      ∃ χ : A →ₐ[R] V, (IsScalarTower.toAlgHom R V K).comp χ = ψ ∧ ∀ x, PrimeSpectrum.comap (χ : A →+* V) x ∈ Vo)
    (y : PrimeSpectrum A) (hy : PrimeSpectrum.comap (algebraMap R A) y ∈ Q) : y ∈ Vo := by
  set q := PrimeSpectrum.comap (algebraMap R A) y with hq
  obtain ⟨g, hg⟩ := exists_section_comap_eq (R := R) K y.asIdeal
  have hunit : ∀ s : q.asIdeal.primeCompl, IsUnit (algebraMap R K s) := fun s =>
    IsUnit.mk0 _ fun h => s.2 (by rw [IsFractionRing.injective R K (h.trans (map_zero _).symm)]; exact zero_mem _)
  let f : Localization.AtPrime q.asIdeal →+* K := IsLocalization.lift (M := q.asIdeal.primeCompl) hunit
  obtain ⟨W, hW, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  let h : Localization.AtPrime q.asIdeal →+* W := f.codRestrict W.toSubring hW
  letI : Algebra R W := (h.comp (algebraMap R (Localization.AtPrime q.asIdeal))).toAlgebra
  haveI : IsScalarTower R W K := IsScalarTower.of_algebraMap_eq fun r =>
    (IsLocalization.lift_eq (M := q.asIdeal.primeCompl) hunit r).symm
  have hcl : PrimeSpectrum.comap (algebraMap R W) (IsLocalRing.closedPoint W) = q := by
    haveI : IsLocalHom h := hloc
    change PrimeSpectrum.comap (h.comp (algebraMap R _)) _ = q
    rw [PrimeSpectrum.comap_comp_apply, IsLocalRing.comap_closedPoint h]
    ext1
    exact Localization.AtPrime.comap_maximalIdeal
  obtain ⟨χ, hχ, hVo⟩ := hext ((Algebra.ofId R K).comp g) W (hcl ▸ hy)
  have hχg : χ = (Algebra.ofId R W).comp g := by
    ext a
    have e := congrArg (fun φ : A →ₐ[R] K => φ a) hχ
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at e
    change algebraMap W K (χ a) = algebraMap W K (algebraMap R W (g a))
    rw [← IsScalarTower.algebraMap_apply]
    exact e
  have hmem := hVo (IsLocalRing.closedPoint W)
  rw [hχg] at hmem
  convert hmem using 1
  ext1
  change y.asIdeal = Ideal.comap (((algebraMap R W).comp (g : A →+* R))) (IsLocalRing.maximalIdeal W)
  rw [← Ideal.comap_comap]
  have hcl' := congrArg PrimeSpectrum.asIdeal hcl
  change Ideal.comap (algebraMap R W) (IsLocalRing.maximalIdeal W) = q.asIdeal at hcl'
  rw [hcl']
  exact hg

end Sections

theorem isIsoOver_abLocus_of_isModel : GlobalTheory.Published.RaynaudExtension → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.CubeTheorem → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime] (X Z : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (g : X ⟶ Z) (tZ : SAB H Z), GlobalTheory.IsNormalScheme X → ∀ (t₀ : SAB H (Sp (Kbar X))), Nonempty (SABMap t₀ tZ (genPt X ≫ g)) → IsOfType Dw t₀ → ∀ (U : AffOp X) (t : SAB H (Sp U.Bp)), Nonempty (SABMap t tZ (U.toX ≫ g)) → ∀ (GG : PDivGroup p U.Bp) (θ : TorsionMap t.G GG), IsModel (Kbar X) θ → θ.IsIsoOver (abLocus t.G) := by
  intro hR hD hC E _ _ _ H Dw p _ X Z _ _ g tZ hX t₀ m₀ hty U t m GG θ hθ n B _ _ hB
  obtain ⟨⟨Vo, hVo⟩, hgen⟩ := hθ n
  refine ⟨fun z z' h => (hVo B).injOn trivial trivial h, fun φ => ?_⟩
  have key : ∀ y : PrimeSpectrum (GG.A n), PrimeSpectrum.comap (algebraMap U.Bp (GG.A n)) y ∈ abLocus t.G →
      y ∈ (Vo : Set (Sp (GG.A n))) := by
    refine mem_of_extends (Kbar X) (Vo : Set (Sp (GG.A n))) _ ?_
    intro ψ V _ _ _ _ _ _ _ hV
    obtain ⟨z, hz⟩ := hgen.2 ψ
    obtain ⟨z', hz'⟩ := GlobalTheory.T.semiabelian_type_extends_normal_scheme hR hD hC E H Dw p X Z g tZ hX t₀ m₀ hty U t m V hV n z
    refine ⟨θ.pt n V z', ?_, fun x => (hVo V).mapsTo (Set.mem_univ z') ⟨x, rfl⟩⟩
    refine (θ.nat n V (Kbar X) (IsScalarTower.toAlgHom _ _ _) z' z (congrArg Subtype.val hz').symm).symm.trans ?_
    exact hz
  have hφ : Set.range (spMap (φ : GG.A n →+* B)) ⊆ (Vo : Set (Sp (GG.A n))) := by
    rintro _ ⟨b, rfl⟩
    apply key
    have e : (φ : GG.A n →+* B).comp (algebraMap U.Bp (GG.A n)) = algebraMap U.Bp B := φ.comp_algebraMap
    have hb := hB ⟨b, rfl⟩
    change PrimeSpectrum.comap (algebraMap U.Bp (GG.A n)) (PrimeSpectrum.comap (φ : GG.A n →+* B) b) ∈ abLocus t.G
    have e2 : PrimeSpectrum.comap (algebraMap U.Bp (GG.A n)) (PrimeSpectrum.comap (φ : GG.A n →+* B) b) =
        PrimeSpectrum.comap (algebraMap U.Bp B) b :=
      PrimeSpectrum.ext (by
        change Ideal.comap _ (Ideal.comap _ _) = Ideal.comap _ _
        rw [Ideal.comap_comap, e])
    rw [e2]
    exact hb
  obtain ⟨z, -, hz⟩ := (hVo B).surjOn hφ
  exact ⟨z, hz⟩

end GlobalTheory.GroupBplus.Aff
