import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinePolarisedMonomialPeriodsMonomialData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibresAbelianOfPsiUnitOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyBoundaryDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAbelianLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum.MonoAb

theorem exists_pos_of_ne_zero {X : Type} [AddCommGroup X] (d : LinearMap.BilinForm ℤ X)
    (hs : ∀ a b, d a b = d b a) (hn : ∀ a, 0 ≤ d a a) (h : d ≠ 0) : ∃ y, 0 < d y y := by
  by_contra hc
  push_neg at hc
  apply h
  ext a b
  have h1 := hc (a + b)
  have h2 : d a a = 0 := le_antisymm (hc a) (hn a)
  have h3 : d b b = 0 := le_antisymm (hc b) (hn b)
  have h4 := hn (a + b)
  have h5 : d (a + b) (a + b) = 0 := le_antisymm h1 h4
  simp only [map_add, LinearMap.add_apply, h2, h3, hs b a] at h5
  simp only [LinearMap.zero_apply]
  omega

end GlobalTheory.Mum.MonoAb

theorem GlobalTheory.Mum.abLocus_iff_of_monomialTau : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ Q : Data R, Q.IsPos (maximalIdeal R) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsMumPol Q G P → ∀ (m : ℕ) (t : Fin m → R) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), (∀ k, t k ∈ maximalIdeal R ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → (∀ k, δ k ≠ 0) → Q.IsMonomialTau t δ → ∀ p : Sp R, p ∈ abLocus G ↔ ∏ k, t k ∉ p.asIdeal := by
  intro R _ _ _ hR Q _ G _ _ P hM m t δ ht hsymm hnn hdef hne hmono p
  obtain ⟨R', _, _, _, ρ, r, D, e, hR', hinj, hfin, -, hr, href, hmon⟩ :=
    GlobalTheory.PolDeg.refine_monomial_of_polarised R Q m t δ hR hmono (fun k => (ht k).1) (fun k => (ht k).2)
      (fun k a b => hsymm k a b) hnn hdef
  obtain ⟨-, -, hG, -, hU⟩ := hM
  obtain ⟨G', _, _, π, -, A, U, hpb, -, -⟩ := hU R' ρ hR' hinj hfin D e href
  have hG' : IsSemiAbelian G' := GlobalTheory.SiegLoc.TraitOrd.isSemiAbelian_of_isGrpPullback hpb hG
  haveI : IsNoetherianRing R' := hR'.1

  obtain ⟨q, hq⟩ : ∃ q : Sp R', spMap ρ q = p := by
    letI := ρ.toAlgebra
    haveI : p.asIdeal.IsPrime := p.isPrime
    haveI : Module.Finite R R' := hfin
    obtain ⟨Q', -, hQ', hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal (⊥ : Ideal R') (by
      intro x hx
      have : ρ x = 0 := hx
      rw [show x = 0 from hinj (this.trans (map_zero ρ).symm)]
      exact p.asIdeal.zero_mem)
    exact ⟨⟨Q', hQ'⟩, PrimeSpectrum.ext hc⟩
  subst hq
  haveI : q.asIdeal.IsPrime := q.isPrime
  rw [abLocus_pullback abLocusOne hG hpb.1 q]
  have key : ∏ k, t k ∈ (spMap ρ q).asIdeal ↔ ∏ k, r k ∈ q.asIdeal := by
    show ρ (∏ k, t k) ∈ q.asIdeal ↔ _
    rw [map_prod, show (∏ k, ρ (t k)) = (∏ k, r k) ^ 2 by rw [← Finset.prod_pow]; simp only [hr]]
    exact ⟨fun h => q.isPrime.mem_of_pow_mem 2 h, fun h => Ideal.pow_mem_of_mem _ h 2 (by norm_num)⟩
  rw [key]
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := GlobalTheory.allSixLaws
  have ho : IsOpen (abLocus G') := GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian G' hG'
  constructor
  · intro hab hmem
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff).1 hmem
    obtain ⟨y, hy⟩ := GlobalTheory.Mum.MonoAb.exists_pos_of_ne_zero (δ k) (hsymm k) (hnn k) (hne k)
    obtain ⟨u, n, hn, hc⟩ := hmon (e.symm y)
    have hnk : 0 < n k := by
      have := hn k
      simp [pull] at this
      omega
    have hUo := GlobalTheory.PsiAbelian.psiUnitOn_abLocus h1 h2 h3 h4 h5 R' _ (GlobalTheory.SiegChart.isAdmissibleBase_of_completeNormalLocalCharZero hR') D A G' hG' U ho
      (e.symm y)
    refine GlobalTheory.PsiCoordLocal.not_mem_of_coord ho hab hUo hc ?_
    refine Ideal.mul_mem_left _ _ ?_
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ k))
      (Ideal.pow_mem_of_mem _ hk _ hnk)
  · intro hnot
    let W : (Sp R').Opens := ⟨{x | ∏ k, r k ∉ x.asIdeal}, (PrimeSpectrum.basicOpen (∏ k, r k)).isOpen⟩
    exact GlobalTheory.Mum.UnifFibre.fibres_abelian_of_psiUnitOn R' ⟨admissibleBase_of_completeNormalLocalCharZero hR', hR'.2.2.2⟩ D A G' hG' U W
      (fun y => hmon.psiUnitOn y fun x hx => hx) hnot
