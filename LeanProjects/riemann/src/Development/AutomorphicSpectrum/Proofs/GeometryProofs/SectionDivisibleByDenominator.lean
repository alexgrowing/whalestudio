import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionValueUniqueBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TopLeOfClosedPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeIdealExtensionLocalDomainStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GroupSchemeIntegralNoetherianStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleSectionDivisibleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPointValuationRingLiftStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicPointOverNumberFieldStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPointLineBundleUnitStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobsonClosedPointsToolsInt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Reg

instance locallyOfFiniteType_spInt (L : Type) [Field L] [NumberField L] :
    LocallyOfFiniteType (spMap (algebraMap ℤ (𝓞 L))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.Finite.finiteType (RingHom.finite_algebraMap.2 inferInstance)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {L : Type} [Field L] [NumberField L]

theorem isClosed_of_maximal (G : Over (Sp (𝓞 L))) [LocallyOfFiniteType G.hom] {W : G.left.Opens} (hW : IsAffineOpen W)
    (m : Ideal Γ(G.left, W)) [hm : m.IsMaximal] :
    IsClosed ({hW.fromSpec (⟨m, hm.isPrime⟩ : PrimeSpectrum Γ(G.left, W))} : Set G.left) := by
  have := (GlobalTheory.jacobson_closedPoints_tools_int G.left (G.hom ≫ spMap (algebraMap ℤ (𝓞 L)))).1
  refine isClosed_singleton_of_isLocallyClosed_singleton ?_
  have h1 : IsClosed ({(⟨m, hm.isPrime⟩ : PrimeSpectrum Γ(G.left, W))} : Set (PrimeSpectrum Γ(G.left, W))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hm
  have h2 := h1.isLocallyClosed.image (f := hW.fromSpec) hW.fromSpec.isOpenEmbedding.isInducing
    hW.fromSpec.isOpenEmbedding.isOpen_range.isLocallyClosed
  convert h2 using 1
  exact Set.image_singleton.symm

instance isDominant_spMap_field {K C : Type} [Field K] [Field C] (e : K →+* C) : IsDominant (spMap e) :=
  ⟨Function.Surjective.denseRange fun z => ⟨default, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩

theorem point_bound (D : PPData H L) (n : ℕ) (s : Out.H0 D.t.PP.L n) (d : 𝓞 L) (hd : d ≠ 0)
    (Hy : ∀ (K : Type) [Field K] [NumberField K] (c : 𝓞 L →+* K) (y : Over.mk (spMap c) ⟶ D.t.G) (N : ℕ) (T : K),
      TorsVal D.t.PP s y N T → IsIntegral ℤ (T / c d ^ (N ^ 2)))
    (i : D.t.PP.L.ι) (W : D.t.G.left.Opens) (hW : IsAffineOpen W)
    (hWU : W ≤ (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => (n : ℤ))).U (fun _ => i))
    (m : Ideal Γ(D.t.G.left, W)) (hm : m.IsMaximal) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (ψ : Γ(D.t.G.left, W) →+* O),
      (∀ b, b ∉ m → IsUnit (ψ b)) ∧ (∀ b ∈ m, ¬ IsUnit (ψ b)) ∧ Function.Injective (ψ.comp (sc D.t.G.hom W)) ∧
        ∃ c, ψ ((D.t.G.left.presheaf.map (homOfLE hWU).op).hom (s.f fun _ => i)) = ψ (sc D.t.G.hom W d) * c := by
  have hS := D.t.semi
  have := hS.smooth
  have := hS.separated
  let w : D.t.G.left := hW.fromSpec (⟨m, hm.isPrime⟩ : PrimeSpectrum Γ(D.t.G.left, W))
  have hwc : IsClosed ({w} : Set D.t.G.left) := isClosed_of_maximal D.t.G hW m
  have hwW : w ∈ W := by
    have : w ∈ Set.range hW.fromSpec := ⟨_, rfl⟩
    rwa [hW.range_fromSpec] at this
  have hmem : ∀ b : Γ(D.t.G.left, W), w ∈ D.t.G.left.basicOpen b ↔ b ∉ m := fun b => by
    have h1 : w ∈ D.t.G.left.basicOpen b ↔ (⟨m, hm.isPrime⟩ : PrimeSpectrum Γ(D.t.G.left, W)) ∈ hW.fromSpec ⁻¹ᵁ D.t.G.left.basicOpen b := Iff.rfl
    rw [h1, hW.fromSpec_preimage_basicOpen]
    rfl
  obtain ⟨N, O, ρ, y, hN, hyN, hyw, hρ⟩ := GlobalTheory.T.torsion_point_valuation_ring_lift L D.t.G hS w hwc
  let C := AlgebraicClosure L
  let yO : Sp O ⟶ D.t.G.left := y.left
  have hyO : yO ≫ D.t.G.hom = spMap ρ := Over.w y
  have hyw' : yO (IsLocalRing.closedPoint O) = w := hyw
  have htop : ⊤ ≤ yO ⁻¹ᵁ W := top_le_of_closedPoint _ (by change yO _ ∈ W; rw [hyw']; exact hwW)
  have hi : ⊤ ≤ yO ⁻¹ᵁ (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => (n : ℤ))).U (fun _ => i) :=
    fun x hx => hWU (htop hx)
  haveI : Algebra.IsAlgebraic ℚ C := Algebra.IsAlgebraic.trans ℚ L C
  haveI : FaithfulSMul O C := (faithfulSMul_iff_algebraMap_injective O C).2 Subtype.val_injective
  obtain ⟨K, _, _, e, x', hx⟩ := GlobalTheory.T.algebraic_point_over_number_field C D.t.G.left (D.t.G.hom ≫ spMap (algebraMap ℤ (𝓞 L)))
    (spMap (algebraMap O C) ≫ yO)
  obtain ⟨c', hc⟩ := Spec.map_surjective (x' ≫ D.t.G.hom)
  let c : 𝓞 L →+* K := c'.hom
  have hc' : spMap c = x' ≫ D.t.G.hom := hc
  let yK : Over.mk (spMap c) ⟶ D.t.G := Over.homMk x' hc'.symm
  have hb : spMap e ≫ spMap c = spMap (algebraMap O C) ≫ spMap ρ := by
    rw [hc', ← Category.assoc, hx, Category.assoc, hyO]
  let yC : Over.mk (spMap e ≫ spMap c) ⟶ D.t.G := Over.homMk (spMap e ≫ x') (by
    change (spMap e ≫ x') ≫ D.t.G.hom = spMap e ≫ spMap c
    rw [hc', Category.assoc])
  have hyC : yC.left = spMap (algebraMap O C) ≫ y.left := hx
  let v : Over.mk (spMap e ≫ spMap c) ⟶ Over.mk (spMap ρ) := Over.homMk (spMap (algebraMap O C)) hb.symm
  have hvy : v ≫ y = yC := Over.OverMorphism.ext hyC.symm
  have hyCN : yC ^ N = 1 := by rw [← hvy, ← MonObj.comp_pow, hyN, MonObj.comp_one]
  let u : Over.mk (spMap e ≫ spMap c) ⟶ Over.mk (spMap c) := Over.homMk (spMap e) rfl
  have huy : u ≫ yK = yC := Over.OverMorphism.ext rfl
  have hyKN : yK ^ N = 1 := by
    have h1 : u ≫ yK ^ N = u ≫ 1 := by rw [MonObj.comp_pow, huy, hyCN, MonObj.comp_one]
    have h2 : spMap e ≫ (yK ^ N).left = spMap e ≫ (1 : Over.mk (spMap c) ⟶ D.t.G).left := congrArg (·.left) h1
    refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp K) D.t.G.hom ((Over.w _).trans (Over.w _).symm) (spMap e) h2)
  obtain ⟨⟨T, hT, -⟩, hmap⟩ := GlobalTheory.T.torsion_value_unique_base_change E H L D n s K (spMap c) yK N hN hyKN
  have hC := hmap C e yC T rfl hT
  have hI := Hy K c yK N T hT
  obtain ⟨ε, hε⟩ := GlobalTheory.T.torsion_point_line_bundle_unit E H L D n s O C ρ y N hN hyN i hi _ hb yC hyC (e T) hC
  have hρi : Function.Injective ρ := fun a b hab => by
    have h1 := congrArg (Subtype.val) hab
    have h2 : algebraMap L C (a : L) = algebraMap L C (b : L) := by
      rw [← hρ, ← hρ]; exact h1
    exact RingOfIntegers.ext ((algebraMap L C).injective h2)
  let ψ : Γ(D.t.G.left, W) →+* O := valR yO W htop
  have hψd : ψ (sc D.t.G.hom W d) = ρ d := valR_sc yO D.t.G.hom ρ hyO W htop d
  have hψf : ψ ((D.t.G.left.presheaf.map (homOfLE hWU).op).hom (s.f fun _ => i)) =
      valR yO _ hi (s.f fun _ => i) := valR_res yO hWU htop hi _
  refine ⟨O, inferInstance, inferInstance, ψ, fun b hb' => ?_, fun b hb' hu => ?_, ?_, ?_⟩
  · exact (valR_isUnit_iff yO W htop b).2 (by rw [hyw']; exact (hmem b).2 hb')
  · have := (valR_isUnit_iff yO W htop b).1 hu
    rw [hyw'] at this
    exact (hmem b).1 this hb'
  · have : ψ.comp (sc D.t.G.hom W) = ρ := RingHom.ext fun a => valR_sc yO D.t.G.hom ρ hyO W htop a
    rw [this]; exact hρi
  · rw [hψf, hψd]
    set θ : O := valR yO _ hi (s.f fun _ => i) with hθ
    have he : e (c d) = algebraMap O C (ρ d) := by
      have h1 : Spec.map (CommRingCat.ofHom (e.comp c)) = Spec.map (CommRingCat.ofHom ((algebraMap O C).comp ρ)) := by
        rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp]
        exact hb
      have h2 : e.comp c = (algebraMap O C).comp ρ := by
        have := Spec.map_injective h1
        exact congrArg CommRingCat.Hom.hom this
      exact congrArg (· d) h2
    have hr0 : algebraMap O C (ρ d) ≠ 0 := by
      intro h0
      have : ρ d = 0 := (FaithfulSMul.algebraMap_injective O C) (by rw [h0, map_zero])
      exact hd (hρi (by rw [this, map_zero]))
    have hI' : IsIntegral ℤ (e T / e (c d) ^ (N ^ 2)) := by
      have h1 := hI.map e.toIntAlgHom
      have h2 : e.toIntAlgHom (T / c d ^ (N ^ 2)) = e T / e (c d) ^ (N ^ 2) := by
        change e _ = _
        simp [map_div₀, map_pow]
      rwa [h2] at h1
    rw [he, hε] at hI'
    let z : C := algebraMap O C θ / algebraMap O C (ρ d)
    have hz1 : IsIntegral O (z ^ (N ^ 2) * algebraMap O C ε) := by
      have h2 : algebraMap O C (θ ^ (N ^ 2) * ε) / algebraMap O C (ρ d) ^ (N ^ 2) = z ^ (N ^ 2) * algebraMap O C ε := by
        simp only [z, map_mul, map_pow, div_pow]; ring
      rw [h2] at hI'
      exact hI'.tower_top
    have hz2 : IsIntegral O (z ^ (N ^ 2)) := by
      have h3 : z ^ (N ^ 2) = (z ^ (N ^ 2) * algebraMap O C ε) * algebraMap O C (ε⁻¹ : Oˣ) := by
        rw [_root_.mul_assoc, ← map_mul]; simp
      rw [h3]
      exact hz1.mul isIntegral_algebraMap
    have hz3 : IsIntegral O z := IsIntegral.of_pow (by positivity) hz2
    obtain ⟨c₀, hc₀⟩ := IsIntegrallyClosed.isIntegral_iff.1 hz3
    refine ⟨c₀, (FaithfulSMul.algebraMap_injective O C) ?_⟩
    rw [map_mul, hc₀, mul_comm]
    exact (div_mul_cancel₀ _ hr0).symm

end GlobalTheory.CompanionTheory.Ar.Sl.Reg

namespace GlobalTheory.CompanionTheory.Ar.Sl.Reg

theorem section_dvd_of_torsVal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (n : ℕ) (s : Out.H0 D.t.PP.L n) (d : 𝓞 L), d ≠ 0 → (∀ (K : Type) [Field K] [NumberField K] (c : 𝓞 L →+* K) (y : Over.mk (spMap c) ⟶ D.t.G) (N : ℕ) (T : K), TorsVal D.t.PP s y N T → IsIntegral ℤ (T / c d ^ (N ^ 2))) → ∃ s' : Out.H0 D.t.PP.L n, ∀ j, s.f j = constFn D.t.G.hom _ d * s'.f j := by
  intro E _ _ _ H L _ _ D n s d hd Hy
  have hS := D.t.semi
  obtain ⟨hInt, hring⟩ := GlobalTheory.T.group_scheme_integral_noetherian L D.t.G hS
  haveI := hInt
  have hδ : sc D.t.G.hom ⊤ d ≠ 0 := by
    intro h0
    let e : Sp (𝓞 L) ⟶ D.t.G.left := η[D.t.G].left
    have he : e ≫ D.t.G.hom = spMap (RingHom.id (𝓞 L)) := by
      have : e ≫ D.t.G.hom = 𝟙 _ := Over.w η[D.t.G]
      rw [this]; simp [spMap]
    have := valR_sc e D.t.G.hom (RingHom.id _) he ⊤ (fun _ _ => trivial) d
    rw [h0, map_zero] at this
    exact hd this.symm
  obtain ⟨s', hs'⟩ := GlobalTheory.T.line_bundle_section_divisible D.t.G.left (𝓞 L) D.t.G.hom _ s d hδ (by
    intro j W hWU hW
    obtain ⟨i₀, rfl⟩ : ∃ i₀, j = fun _ => i₀ := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    by_cases hne : (W : Set D.t.G.left).Nonempty
    · obtain ⟨hNo, hft, hp⟩ := hring W hW
      haveI : Nonempty W := hne.to_subtype
      exact GlobalTheory.T.prime_ideal_extension_local_domain (𝓞 L) Γ(D.t.G.left, W) (sc D.t.G.hom W) hft hp _ d hd fun m hm =>
        point_bound D n s d hd Hy i₀ W hW hWU m hm
    · have hW0 : W = ⊥ := by
        ext x
        simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
        exact fun hx => hne ⟨x, hx⟩
      subst hW0
      haveI : Subsingleton Γ(D.t.G.left, ⊥) := inferInstance
      exact ⟨0, Subsingleton.elim _ _⟩)
  exact ⟨s', hs'⟩

end GlobalTheory.CompanionTheory.Ar.Sl.Reg
