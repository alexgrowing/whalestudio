import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedBaseChangeIffFibersStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOpenGeometricallyConnectedFibersStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem geometricallyConnected_descends_to_fg :
    ∀ (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V] [Algebra k V] (G : Over (Sp k))
      [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsProper G.hom →
      GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k V))) →
      ∃ R : Subalgebra k V, R.FG ∧
        GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k R))) := by
  intro k V _ _ _ _ G _ _ hs hp hV
  classical
  set U : Set (PrimeSpectrum k) := {x | GeometricallyConnected
      (pullback.snd G.hom (spMap (algebraMap k x.asIdeal.ResidueField)))} with hUdef
  have hU : IsOpen U := GlobalTheory.T.isOpen_geometricallyConnected_fibers k G hs hp
  have hVU : ∀ x ∈ Set.range (PrimeSpectrum.comap (algebraMap k V)), x ∈ U :=
    (GlobalTheory.T.geometricallyConnected_baseChange_iff_fibers k V G.left G.hom).1 hV
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1 hU.isClosed_compl
  have htop : Ideal.map (algebraMap k V) I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hx := hVU (PrimeSpectrum.comap (algebraMap k V) ⟨M, hM.isPrime⟩) ⟨_, rfl⟩
    have hx' : PrimeSpectrum.comap (algebraMap k V) ⟨M, hM.isPrime⟩ ∈ Uᶜ := by
      rw [hI, PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.comap_asIdeal]
      exact Ideal.map_le_iff_le_comap.1 hle
    exact hx' hx
  have h1 : (1 : V) ∈ Submodule.span V (algebraMap k V '' (I : Set k)) := by
    have h := (Ideal.eq_top_iff_one _).1 htop
    exact h
  obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.1 h1
  choose f hfI hfg using fun i => (g i).2
  let s : Finset V := Finset.univ.image c
  have hc : ∀ i, c i ∈ Algebra.adjoin k (s : Set V) := fun i =>
    Algebra.subset_adjoin (by simp [s])
  refine ⟨Algebra.adjoin k (s : Set V), Subalgebra.fg_adjoin_finset s, ?_⟩
  apply (GlobalTheory.T.geometricallyConnected_baseChange_iff_fibers k (Algebra.adjoin k (s : Set V)) G.left G.hom).2
  rintro x ⟨y, rfl⟩
  by_contra hx
  have hx' : PrimeSpectrum.comap (algebraMap k (Algebra.adjoin k (s : Set V))) y ∈ Uᶜ := hx
  rw [hI, PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.comap_asIdeal] at hx'
  have hmem : (∑ i, (⟨c i, hc i⟩ : Algebra.adjoin k (s : Set V)) *
      algebraMap k (Algebra.adjoin k (s : Set V)) (f i)) ∈ y.asIdeal :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hx' (hfI i))
  have hone : (∑ i, (⟨c i, hc i⟩ : Algebra.adjoin k (s : Set V)) *
      algebraMap k (Algebra.adjoin k (s : Set V)) (f i)) = 1 := by
    apply Subtype.ext
    have key : (Algebra.adjoin k (s : Set V)).val (∑ i, (⟨c i, hc i⟩ : Algebra.adjoin k (s : Set V)) *
        algebraMap k (Algebra.adjoin k (s : Set V)) (f i)) = ∑ i, c i • (g i : V) := by
      simp only [map_sum, map_mul, AlgHom.commutes, Subalgebra.coe_val, hfg, smul_eq_mul]
    exact key.trans (hsum.trans (by simp))
  exact y.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hone ▸ hmem))

end GlobalTheory.CompanionTheory.Ar.Approx
