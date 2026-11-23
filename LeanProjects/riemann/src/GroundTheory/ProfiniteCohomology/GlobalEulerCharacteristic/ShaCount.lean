import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.MemShaSubmoduleCohomologyAddEquivOfEquivIff
import GroundTheory.ProfiniteCohomology.PoitouTate.Deduction
import GroundTheory.ProfiniteCohomology.PoitouTate.BrauerInvZOfIsSepClosureCohomologyULiftIntAddEqu
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

universe u

noncomputable section

section PoitouTateCount

attribute [local instance 2000] Rep.hV2

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] {φ : ∀ v, Hv v →ₜ* G} [Fintype ι]
  {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) G} [IsDiscreteRep D]
  {t : compactCohomologyRes φ D 3 →+ ZMod n}
  {inv : ∀ v, cohomology (Rep.res (φ v).toMonoidHom D) 2 →+ QZ}

theorem natCard_cohomology_two_mul_of_poitouTate (P : PoitouTateDualityHypotheses φ D t inv)
    (M : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, n • m = 0) :
    Nat.card (cohomology M 2) * Nat.card (cohomology (dualRep D M) 0) =
      Nat.card (ptSha φ M 2) * ∏ v, Nat.card (cohomology (Rep.res (φ v).toMonoidHom M) 2) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, hex, hsurj⟩ := P.nineTerm M hM
  set F := (ptGlobalToLocal φ M 2).hom.toAddMonoidHom
  set Gm := ptLocalDualMap φ D M inv (show 2 + 0 = 2 from rfl)
  have : Finite D := finite_of_nonempty_addEquiv P.nonempty_addEquiv
  have hMD : ∀ f : dualRep D M, n • f = 0 :=
    nsmul_dualRep_eq_zero (nsmul_eq_zero_of_nonempty_addEquiv P.nonempty_addEquiv)
  have : Finite (dualRep D M) := finite_dualRep
  have : Finite (cohomology (dualRep D M) 0) := P.finite_cohomology (dualRep D M) hMD 0
  have h1 : Nat.card (cohomology M 2) = Nat.card F.range * Nat.card (ptSha φ M 2) := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (ptSha φ M 2)]
    congr 1
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange F).toEquiv
  have hker : Gm.ker = F.range := by
    ext y
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    exact hex y
  have h2 : Nat.card (∀ v, cohomology (Rep.res (φ v).toMonoidHom M) 2) =
      Nat.card (cohomology (dualRep D M) 0 →+ QZ) * Nat.card F.range := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup Gm.ker, ← hker]
    congr 1
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective Gm hsurj).toEquiv
  rw [Nat.card_pi, QZ.card_hom] at h2
  rw [h1, h2]
  ring

end PoitouTateCount

section GSPoitouTate

attribute [local instance 2000] Rep.hV2

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  {N : ℕ} [NeZero N] (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hK : Odd N ∨ IsTotallyComplex K.1)
  (H : ∀ p ∈ N.primeFactors, ∃ U₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
    CompactDualityHypotheses (gsFinFamily S ιs) (p ^ N.factorization p) (gsRoots S (p ^ N.factorization p))
      (gsCompactInv S ιs (p ^ N.factorization p) (odd_or_isTotallyComplex_of_dvd hK (Nat.ordProj_dvd N p))
        (subsingleton_cohomology_three_gsRoots S (mem_of_natCast_dvd_mem S hS (Nat.ordProj_dvd N p))
          (odd_or_isTotallyComplex_of_dvd hK (Nat.ordProj_dvd N p)))) U₀)
  (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
  (hM : ∀ m : M, N • m = 0)

omit [Fintype S] [NeZero N] in

instance isDiscreteRep_res_gsFinFamily_dualRep (v : S) :
    IsDiscreteRep (Rep.res (gsFinFamily S ιs v).toMonoidHom (dualRep (gsRoots S N) M)) :=
  isDiscreteRep_res_dualRep_of_finite (gsRoots S N) M (gsFinFamily S ιs v)

omit [Fintype S] in
include hS hM in

theorem natCard_gs_local_cohomology_two (v : S) :
    Nat.card (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom M) 2) =
      Nat.card (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (dualRep (gsRoots S N) M)) 0) := by
  have hD := nonempty_addEquiv_gsRoots_of_mem S hS
  have : Finite (gsRoots S N) := Finite.of_equiv _ hD.some.symm.toEquiv
  have : Finite (dualRep (gsRoots S N) M) := finite_dualRep
  have : Finite (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (dualRep (gsRoots S N) M)) 0) := by
    have : Finite (Rep.res (gsFinFamily S ιs v).toMonoidHom (dualRep (gsRoots S N) M)).ρ.invariants :=
      Subtype.finite (α := dualRep (gsRoots S N) M)
    exact Finite.of_equiv _ (H0Iso (Rep.res (gsFinFamily S ιs v).toMonoidHom
      (dualRep (gsRoots S N) M))).toLinearEquiv.toEquiv.symm
  rw [Nat.card_congr (Equiv.ofBijective _ (bijective_gsLocalPairing S ιs N hD M hM v (show 2 + 0 = 2 from rfl))),
    QZ.card_hom]

include H hM in

theorem natCard_gs_cohomology_two_mul :
    Nat.card (cohomology M 2) * Nat.card (cohomology (dualRep (gsRoots S N) M) 0) =
      Nat.card (ptSha (gsFinFamily S ιs) M 2) *
        ∏ v : S, Nat.card (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (dualRep (gsRoots S N) M)) 0) := by
  rw [natCard_cohomology_two_mul_of_poitouTate (gsPoitouTateDualityHypotheses S ιs hS hK H) M hM]
  congr 1
  exact Finset.prod_congr rfl fun v _ => natCard_gs_local_cohomology_two S ιs hS M hM v

end GSPoitouTate

end

end GroundTheory.ProfCoh
