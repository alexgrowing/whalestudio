import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.GenFibre

theorem isNoetherianRing_of_isInducing {A B : Type*} [CommRing A] [CommRing B] [IsNoetherianRing A]
    (f : A →+* B) (hi : Topology.IsInducing (PrimeSpectrum.comap f)) (hf : f.SurjectiveOnStalks) :
    IsNoetherianRing B := by
  refine (isNoetherianRing_iff_ideal_fg B).2 fun J => ?_
  have e : (J.comap f).map f = J := by
    refine le_antisymm Ideal.map_comap_le fun b hb => ?_
    by_contra hn
    have hne : ((J.comap f).map f).colon {b} ≠ ⊤ := fun h => hn (by
      have h1 : (1 : B) ∈ ((J.comap f).map f).colon {b} := h ▸ Submodule.mem_top
      simpa using Submodule.mem_colon_singleton.1 h1)
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨x, r, c, hc, hr, hx⟩ := RingHom.surjectiveOnStalks_iff_forall_maximal'.1 hf P hP b
    let p : PrimeSpectrum B := ⟨P, hP.isPrime⟩
    obtain ⟨U, hU, hUc⟩ := hi.isOpen_iff.1 (PrimeSpectrum.basicOpen c).isOpen
    have hpU : PrimeSpectrum.comap f p ∈ U := by
      have : p ∈ PrimeSpectrum.comap f ⁻¹' U := hUc ▸ hc
      exact this
    obtain ⟨_, ⟨a, rfl⟩, ha, haU⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpU hU
    have hac : PrimeSpectrum.basicOpen (f a) ≤ PrimeSpectrum.basicOpen c := fun q hq => by
      have : q ∈ PrimeSpectrum.comap f ⁻¹' U := haU hq
      exact hUc.subset this
    obtain ⟨n, hn⟩ := (PrimeSpectrum.basicOpen_le_basicOpen_iff _ _).1 hac
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hn
    have key : f (a ^ n * r) * b = f (a ^ n * x) := by
      rw [map_mul, map_mul, map_pow, ← hd]
      linear_combination d * hx
    have hmem : f (a ^ n * r) ∈ P := hle (Submodule.mem_colon_singleton.2 (by
      rw [smul_eq_mul, key]
      exact Ideal.mem_map_of_mem f (Ideal.mem_comap.2 (key ▸ J.mul_mem_left _ hb))))
    rw [map_mul, map_pow] at hmem
    rcases hP.isPrime.mem_or_mem hmem with h | h
    · exact ha (hP.isPrime.mem_of_pow_mem n h)
    · exact hr h
  rw [← e]
  exact Ideal.FG.map (IsNoetherian.noetherian _) f

theorem isLocallyNoetherian_of_isPreimmersion {W Z : Scheme.{0}} (j : W ⟶ Z) [IsPreimmersion j]
    [IsLocallyNoetherian Z] : IsLocallyNoetherian W := by
  have H (w : W) : ∃ V : W.affineOpens, w ∈ V.1 ∧ IsNoetherianRing Γ(W, V) := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hw, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (j w)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hwV, hVU⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
      (show w ∈ (j ⁻¹ᵁ U : Set W) from hw) (j ⁻¹ᵁ U).isOpen
    have hU' : IsAffineOpen U := hU
    have hV' : IsAffineOpen V := hV
    have e := IsAffineOpen.SpecMap_appLE_fromSpec j hU' hV' hVU
    have : IsPreimmersion (Spec.map (j.appLE U V hVU) ≫ hU'.fromSpec) := by
      rw [e]; infer_instance
    have h := (IsPreimmersion.SpecMap_iff _).1 (IsPreimmersion.of_comp (Spec.map (j.appLE U V hVU)) hU'.fromSpec)
    have : IsNoetherianRing Γ(Z, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    exact ⟨⟨V, hV⟩, hwV, isNoetherianRing_of_isInducing _ h.1.isInducing h.2⟩
  choose V hV hN using H
  exact isLocallyNoetherian_of_affine_cover (S := V)
    (top_le_iff.1 fun w _ => TopologicalSpace.Opens.mem_iSup.2 ⟨w, hV w⟩) hN

theorem isNormalScheme_of_flat_preimmersion {U X : Scheme.{0}} (j : U ⟶ X) [IsPreimmersion j] [Flat j]
    (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U := by
  intro x
  obtain ⟨h1, h2⟩ := h (j x)
  have hf : (j.stalkMap x).hom.Flat := Flat.stalkMap j x
  have hs : Function.Surjective (j.stalkMap x).hom := j.stalkMap_surjective x
  have hi : Function.Injective (j.stalkMap x).hom := by
    letI := (j.stalkMap x).hom.toAlgebra
    have : Module.Flat (X.presheaf.stalk (j x)) (U.presheaf.stalk x) := hf
    have : IsLocalHom (algebraMap (X.presheaf.stalk (j x)) (U.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (j.stalkMap x).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (j x))
      (B := U.presheaf.stalk x)
    exact FaithfulSMul.algebraMap_injective (X.presheaf.stalk (j x)) (U.presheaf.stalk x)
  let e := RingEquiv.ofBijective (j.stalkMap x).hom ⟨hi, hs⟩
  have h3 : IsDomain (U.presheaf.stalk x) := e.symm.toMulEquiv.isDomain _
  exact ⟨h3, IsIntegrallyClosed.of_equiv e⟩

theorem normal_genericFibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (N : Scheme.{0}) (g : N ⟶ Sp R),
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N → IsLocallyNoetherian N →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (pullback g (spMap (algebraMap R K))) ∧
      IsLocallyNoetherian (pullback g (spMap (algebraMap R K))) := by
  intro R K _ _ _ _ _ N g hN hL
  have hb : IsPreimmersion (spMap (algebraMap R K)) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have hbf : Flat (spMap (algebraMap R K)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))
  have : IsPreimmersion (pullback.fst g (spMap (algebraMap R K))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb
  have : Flat (pullback.fst g (spMap (algebraMap R K))) :=
    inferInstance
  exact ⟨isNormalScheme_of_flat_preimmersion (pullback.fst g (spMap (algebraMap R K))) hN, isLocallyNoetherian_of_isPreimmersion (pullback.fst g _)⟩

end GlobalTheory.GenFibre
