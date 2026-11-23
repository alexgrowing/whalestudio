import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomLocBijectiveGrSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomogeneousFamilySaturating
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexGradedModuleExactAtOfLargeDegree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGradedMapGlueD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCoboundaryOfPairsCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionCompatibleIteratedInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.XProdPowSmulMemRangeResIter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompatibleFamilyOfSingleton
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfEvEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsXProdPowSmulEqEv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SaturatedFgOfPowerTorsionKerCoker
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHomLocPiecesCompatible
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

open MvPolynomial in

theorem exists_finite_sub (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢]
    [DirectSum.Decomposition 𝒢]
    (h : ∀ i : ι, ∃ T : Finset G, ∀ y : G, ∃ k : ℕ,
      (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (T : Set G)) :
    ∃ K : Submodule (MvPolynomial ι R) G, K.IsHomogeneous 𝒢 ∧
      Module.Finite (MvPolynomial ι R) K ∧ ∀ (t : ℤ) (I : Finset ι), I.Nonempty →
        Function.Bijective (homLocMap (isGradedMap_subtype 𝒢 K) I t) := by
  obtain ⟨r, d, g, hg, hsat⟩ := exists_homogeneous_family_saturating ι R G 𝒢 h
  have hhom : (Submodule.span (MvPolynomial ι R) (Set.range g)).IsHomogeneous 𝒢 :=
    isHomogeneous_span_gr 𝒢 (by
      rintro _ ⟨l, rfl⟩
      exact ⟨d l, hg l⟩)
  refine ⟨_, hhom, Module.Finite.span_of_finite _ (Set.finite_range g), fun t I ⟨i, hi⟩ => ?_⟩
  letI := grSubDecomposition 𝒢 hhom
  exact homLocMap_bijective_of_X _ hi
    (fun m hm => ⟨0, by
      rw [(map_eq_zero_iff _ (Submodule.injective_subtype _)).1 hm, smul_zero]⟩)
    (fun y => by simpa using hsat i y) t

theorem pairs_of_cube {ι : Type} [LinearOrder ι] {A : Type} [CommRing A] (C : Cube.{0} ι A)
    (hpairs : ∀ c : ∀ i j : ι, C.obj {i, j}, (∀ i j k, Cube.res C (sub_triple_ij i j k) (c i j) +
      Cube.res C (sub_triple_jk i j k) (c j k) = Cube.res C (sub_triple_ik i j k) (c i k)) →
      ∃ b : ∀ i : ι, C.obj {i}, ∀ i j, c i j = Cube.res C (sub_pair_left i j) (b i) -
        Cube.res C (sub_pair_right i j) (b j))
    {P : Finset ι → Type} [∀ S, AddCommGroup (P S)] [∀ S, Module A (P S)]
    [∀ S, Module (MvPolynomial ι A) (P S)]
    (Qs : ∀ S, Submodule A (P S))
    (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S')
    (ψ : ∀ I : Finset ι, I.Nonempty → (C.obj I →ₗ[A] Qs I))
    (hb : ∀ I hI, Function.Bijective (ψ I hI))
    (hr : ∀ I J (hI : I.Nonempty) (hJ : J.Nonempty) (h : I ⊆ J) (z : C.obj I),
      (ψ J hJ (Cube.res C h z) : P J) = res I J h (ψ I hI z : P I))
    (c : ∀ i j : ι, P {i, j}) (hc : ∀ i j, c i j ∈ Qs {i, j})
    (hcoc : ∀ i j k, res {i, j} {i, j, k} (sub_triple_ij i j k) (c i j) +
      res {j, k} {i, j, k} (sub_triple_jk i j k) (c j k) =
        res {i, k} {i, j, k} (sub_triple_ik i j k) (c i k)) :
    ∃ b : ∀ i : ι, P {i}, (∀ i, b i ∈ Qs {i}) ∧
      ∀ i j, c i j = res {i} {i, j} (sub_pair_left i j) (b i) -
        res {j} {i, j} (sub_pair_right i j) (b j) := by
  have n2 (i j : ι) : ({i, j} : Finset ι).Nonempty := Finset.insert_nonempty _ _
  have n1 (i : ι) : ({i} : Finset ι).Nonempty := Finset.singleton_nonempty i
  have n3 (i j k : ι) : ({i, j, k} : Finset ι).Nonempty := Finset.insert_nonempty _ _
  choose c' hc' using fun i j => (hb {i, j} (n2 i j)).2 ⟨c i j, hc i j⟩
  have hv (i j : ι) : (ψ _ (n2 i j) (c' i j) : P {i, j}) = c i j := congrArg Subtype.val (hc' i j)
  obtain ⟨b', hb'⟩ := hpairs c' fun i j k => by
    refine (hb _ (n3 i j k)).1 (Subtype.ext ?_)
    rw [map_add, Submodule.coe_add, hr _ _ (n2 i j) (n3 i j k), hr _ _ (n2 j k) (n3 i j k),
      hr _ _ (n2 i k) (n3 i j k), hv, hv, hv, hcoc]
  refine ⟨fun i => ψ _ (n1 i) (b' i), fun i => (ψ _ (n1 i) (b' i)).2, fun i j => ?_⟩
  rw [← hv i j, hb' i j, map_sub, Submodule.coe_sub, hr _ _ (n1 i) (n2 i j),
    hr _ _ (n1 j) (n2 i j)]

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem serre_cech_pairs : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (A : Type) [CommRing A] [IsNoetherianRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module A (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] [∀ S, IsScalarTower A (MvPolynomial ι A) (P S)] (𝒢 : ∀ S, ℤ → Submodule A (P S)) [∀ S, PolyGradedSMul ι (𝒢 S)] [∀ S, DirectSum.Decomposition (𝒢 S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S S' (h : S ⊆ S'), IsGradedMap (𝒢 S) (𝒢 S') (res S S' h)) → (∀ S (h : S ⊆ S) a, res S S h a = a) → (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (i : ι) (S : Finset ι), i ∈ S → Function.Bijective fun m : P S => (MvPolynomial.X i : MvPolynomial ι A) • m) → (∀ (S : Finset ι) (j : ι) (a : P S), S.Nonempty → res S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • a = 0) → (∀ (S : Finset ι) (j : ι) (b : P (insert j S)), S.Nonempty → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • b ∈ LinearMap.range (res S (insert j S) (Finset.subset_insert j S))) → (∀ i : ι, ∃ s : Finset (P {i}), ∀ m : P {i}, ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι A) ^ k • m ∈ Submodule.span (MvPolynomial ι A) (s : Set (P {i}))) → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∀ c : ∀ i j : ι, P {i, j}, (∀ i j, c i j ∈ 𝒢 {i, j} t) → (∀ i j k, res {i, j} {i, j, k} (sub_triple_ij i j k) (c i j) + res {j, k} {i, j, k} (sub_triple_jk i j k) (c j k) = res {i, k} {i, j, k} (sub_triple_ik i j k) (c i k)) → ∃ b : ∀ i : ι, P {i}, (∀ i, b i ∈ 𝒢 {i} t) ∧ ∀ i j, c i j = res {i} {i, j} (sub_pair_left i j) (b i) - res {j} {i, j} (sub_pair_right i j) (b j) := by
  intro ι _ _ A _ _ P _ _ _ _ 𝒢 _ _ res hgr hid hcomp hbij hinj hsurj hfin
  have iI := GlobalTheory.CompanionTheory.FormalAlg.IterInj.iter_localisation_injective ι A P res hid hcomp hinj
  have iS := GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.xProd_pow_smul_mem_range_res_iter ι A P res hid hcomp hsurj
  have g1 := GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.exists_compatible_family_of_singleton ι A P res hid hcomp hinj hsurj
  have K1 := GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.smul_eq_zero_of_ev_eq_zero ι A P res hcomp iI
  have K2 := GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.exists_xProd_pow_smul_eq_ev ι A P res hcomp iS g1
  letI : DirectSum.Decomposition (glueGr res 𝒢) := glueDec 𝒢 hgr
  have sat : ∀ i : ι, ∃ T : Finset (glue res), ∀ y : glue res, ∃ k : ℕ,
      (MvPolynomial.X i : MvPolynomial ι A) ^ k • y ∈
        Submodule.span (MvPolynomial ι A) (T : Set (glue res)) := by
    intro i
    refine GlobalTheory.CompanionTheory.FormalAlg.Lift.SerreSat.saturated_fg_of_powerTorsion_ker_coker (MvPolynomial ι A) (MvPolynomial.X i) (glue res) (P {i})
      (ev res {i} (Finset.singleton_nonempty i)) (fun m hm => ?_) (fun f => ?_) (hfin i)
    · simpa [xProd] using K1 {i} _ m hm
    · simpa [xProd] using K2 {i} (Finset.singleton_nonempty i) f
  obtain ⟨K, hK, hKf, hb⟩ := exists_finite_sub ι A (glue res) (glueGr res 𝒢) sat
  letI := grSubDecomposition (glueGr res 𝒢) hK
  obtain ⟨t₀, ht₀⟩ := cubeComplex_grCube_exactAt_of_finite ι A K (grSub (glueGr res 𝒢) K) hKf
  refine ⟨t₀, fun t ht c hc hcoc => ?_⟩
  have hex := (cechComplex_exactAt_succ_iff _ 0).1
    ((cechComplex_exactAt_succ_iff_cube _ 0).2 (ht₀ t ht 2))
  obtain ⟨φ, hφb, hφr⟩ := GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.exists_homLoc_pieces_compatible ι A (glue res) (glueGr res 𝒢) P 𝒢 res (ev res)
    (isGradedMap_ev 𝒢 hgr) (fun I J hI hJ h m => res_ev hcomp hI hJ h m) hbij K1 K2 t
  refine pairs_of_cube (grCube ι (grSub (glueGr res 𝒢) K) t) (GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.exists_coboundary_of_pairs_cocycle ι A _ hex)
    (fun S => 𝒢 S t) res
    (fun I hI => φ I hI ∘ₗ homLocMap (isGradedMap_subtype _ K) I t)
    (fun I hI => (hφb I hI).comp (hb t I hI)) (fun I J hI hJ h z => ?_) c hc hcoc
  have e : homLocMap (isGradedMap_subtype (glueGr res 𝒢) K) J t (Cube.res _ h z) =
      homLocRes _ h t (homLocMap (isGradedMap_subtype (glueGr res 𝒢) K) I t z) :=
    homLocMap_homLocRes _ h t z
  exact (congrArg (fun w => ((φ J hJ w : 𝒢 J t) : P J)) e).trans (hφr I J hI hJ h _)

end GlobalTheory.CompanionTheory.FormalAlg.Lift
