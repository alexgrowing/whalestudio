import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.NatCardInvariantsEqOfAddEquiv
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

section Cards

variable {K : FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (M : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module.Finite (ZMod ℓ) M]

theorem finite_of_moduleFinite : Finite M := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  exact Module.finite_of_finite (ZMod ℓ)

variable [Finite M]

theorem finite_cohomology_two_int [Finite S] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal) :
    Finite (cohomology (intRep M) 2) := by
  have hℓ : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hcardM : Nat.card (intRep M) = ℓ ^ Module.finrank (ZMod ℓ) M := natCard_eq_pow_finrank_zmod ℓ M
  have hSM : ∀ v : HeightOneSpectrum (𝓞 K.1), ((Nat.card (intRep M) : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S := by
    intro v hv
    rw [hcardM, Nat.cast_pow] at hv
    by_contra h
    exact hℓS v h (v.isPrime.mem_of_pow_mem _ hv)
  exact finite_cohomology_gs K S (intRep M) hSM 2 le_rfl

theorem card_H2_integral_module [Finite S] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal) :
    Nat.card (cohomology (intRep M) 2) = ℓ ^ Module.finrank (ZMod ℓ) (cohomology M 2) := by
  haveI := finite_cohomology_two_int M hℓS
  haveI : Finite (cohomology M 2) := Finite.of_equiv _ (cohomologyIntEquiv M 2).symm.toEquiv
  rw [← Nat.card_congr (cohomologyIntEquiv M 2).toEquiv]
  exact natCard_eq_pow_finrank_zmod ℓ _

theorem card_H0_dual_module :
    Nat.card (cohomology (dualRep (gsRoots S ℓ) (intRep M)) 0) =
      ℓ ^ Module.finrank (ZMod ℓ) (dualRep (gsRootsZMod S ℓ) M).ρ.invariants := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  haveI : Finite (dualRep (gsRootsZMod S ℓ) M) := Module.finite_of_finite (ZMod ℓ)
  refine (Nat.card_congr (H0Iso (dualRep (gsRoots S ℓ) (intRep M))).toLinearEquiv.toEquiv).trans ?_
  exact (natCard_invariants_eq_of_addEquiv (dualRep (gsRoots S ℓ) (intRep M)).ρ
    (dualRep (gsRootsZMod S ℓ) M).ρ
    (dualIntEquiv (gsRoots S ℓ) (nsmul_galRootsOfUnity_eq_zero ℓ) M)
    (fun h f => dualIntEquiv_comm _ _ M h f)).trans (natCard_eq_pow_finrank_zmod ℓ _)

theorem card_H0_dual_local
    (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (v : S) :
    Nat.card (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (dualRep (gsRoots S ℓ) (intRep M))) 0) =
      ℓ ^ Module.finrank (ZMod ℓ) (Representation.invariants
          ((dualRep (gsRootsZMod S ℓ) M).ρ.comp (gsFinFamily S ιs v).toMonoidHom)) := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  haveI : Finite (dualRep (gsRootsZMod S ℓ) M) := Module.finite_of_finite (ZMod ℓ)
  refine (Nat.card_congr (H0Iso (Rep.res (gsFinFamily S ιs v).toMonoidHom
    (dualRep (gsRoots S ℓ) (intRep M)))).toLinearEquiv.toEquiv).trans ?_
  exact (natCard_invariants_eq_of_addEquiv
    (Rep.res (gsFinFamily S ιs v).toMonoidHom (dualRep (gsRoots S ℓ) (intRep M))).ρ
    ((dualRep (gsRootsZMod S ℓ) M).ρ.comp (gsFinFamily S ιs v).toMonoidHom)
    (dualIntEquiv (gsRoots S ℓ) (nsmul_galRootsOfUnity_eq_zero ℓ) M)
    (fun h f => dualIntEquiv_comm _ _ M _ f)).trans (natCard_eq_pow_finrank_zmod ℓ _)

theorem card_sha_int [Finite S] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :
    Nat.card (ptSha (gsFinFamily S ιs) (intRep M) 2) =
      ℓ ^ Module.finrank (ZMod ℓ) (shaSubmodule (gsFinFamily S ιs) M 2) := by
  haveI := finite_cohomology_two_int M hℓS
  haveI : Finite (cohomology M 2) := Finite.of_equiv _ (cohomologyIntEquiv M 2).symm.toEquiv
  have e : (shaSubmodule (gsFinFamily S ιs) M 2) ≃ (ptSha (gsFinFamily S ιs) (intRep M) 2) :=
    (cohomologyIntEquiv M 2).toEquiv.subtypeEquiv fun x => by
      rw [mem_ptSha_iff_mem_shaSubmodule]
      exact (mem_shaSubmodule_cohomologyAddEquivOfEquiv_iff _ (intRepEquiv M) (fun _ _ => rfl) 2 x).symm
  exact (Nat.card_congr e).symm.trans (natCard_eq_pow_finrank_zmod ℓ _)

end Cards

end PositivityTheory.Lit1.GEN.X
