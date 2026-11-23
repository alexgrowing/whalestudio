import Mathlib
import ReciprocityTheory.Hypotheses.GalCoh
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.Transport
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ExistsApplyEqOfMemDec
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.Inertia
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmp
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohField
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohTate
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsPrimeMemAsIdeal

open CategoryTheory MonoidalCategory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel NumberField IsDedekindDomain Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.Hypotheses₂

attribute [local instance 2000] Rep.hV2

theorem dualityFor_absGal (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (hK : FiniteDimensional ℚ_[p] K) (l : ℕ) [Fact l.Prime] (r : ℕ)
    (χ : (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) →* (ZMod (l ^ r))ˣ)
    (hχ : ∀ (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (ζ : PadicAlgCl p), ζ ^ (l ^ r) = 1 →
      σ ζ = ζ ^ ((χ σ : ZMod (l ^ r)).val))
    (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation (ZMod (l ^ r)) (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) M)
    (hrho : ContAction rho) : ReciprocityTheory.Neutral.Bridge.DualityFor χ rho hrho := by
  obtain ⟨hsep, _, _, hloc, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gcField p K hK
  have hl : (l ^ r : ℕ) ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ r) := ⟨hl⟩
  have : CharZero K := algebraRat.charZero K
  have hn : ((l ^ r : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hl
  obtain ⟨e⟩ := nonempty_addEquiv_galRootsOfUnity (K := K) (Ksep := PadicAlgCl p) hn
  have hD : ∀ (g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (m : ZMod (l ^ r)),
      e.symm ((χ g : ZMod (l ^ r)) * m) =
        (galRootsOfUnity.{0} K (PadicAlgCl p) (l ^ r)).ρ g (e.symm m) := by
    intro g m
    have key : ∀ x : Additive (rootsOfUnity (l ^ r) (PadicAlgCl p)),
        (galRootsOfUnity.{0} K (PadicAlgCl p) (l ^ r)).ρ g x =
          (χ g : ZMod (l ^ r)).val • x := by
      intro x
      rw [galRootsOfUnity_ρ_apply]
      apply Additive.toMul.injective
      rw [toMul_ofMul, toMul_nsmul]
      apply Subtype.ext
      apply Units.ext
      rw [coe_galRootsOfUnityHom_apply, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val]
      refine hχ g _ ?_
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 x.toMul.2, Units.val_one]
    refine Eq.trans ?_ (key _).symm
    refine Eq.trans ?_ (map_nsmul e.symm _ m)
    rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
  exact PositivityTheory.LocalTateOrthogonality.Gcoh.tate_core PositivityTheory.LocalTateOrthogonality.Gcoh.gcRep PositivityTheory.LocalTateOrthogonality.Gcoh.gc0
    PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 (galRootsOfUnity.{0} K (PadicAlgCl p) (l ^ r))
    (localDualityHypotheses hn)
    (fun A _ _ hA => finite_cohomology_galois_top K (PadicAlgCl p) hn A hA 1)
    χ e.symm hD M rho hrho

theorem localTateDuality : ReciprocityTheory.Gal.LocalTateDuality := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ A rho v _ hA hrho
  obtain ⟨p, hp, hpv⟩ := exists_prime_mem_asIdeal v
  haveI : Fact p.Prime := ⟨hp⟩
  have hval : A.valuation ((p : ℕ) : Ω) < 1 := by
    have := (hA ((p : ℕ) : 𝓞 F)).2 hpv
    simpa using this
  obtain ⟨ι, h⟩ := ReciprocityTheory.Neutral.Cmp.exists_compat F A hval
  let E : ReciprocityTheory.Neutral.Cmp.GK F ι ≃ₜ* Dec (F := F) A := ReciprocityTheory.Neutral.Cmp.equiv h
  let χ : Dec (F := F) A →* (ZMod (l ^ r))ˣ := (cycMod F Ω l r).comp (Dec (F := F) A).subtype
  have hχ : ∀ (σ : ReciprocityTheory.Neutral.Cmp.GK F ι) (ζ : PadicAlgCl p), ζ ^ (l ^ r) = 1 →
      σ ζ = ζ ^ (((χ.comp (E : ReciprocityTheory.Neutral.Cmp.GK F ι →* Dec (F := F) A)) σ :
        (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by
    intro σ ζ hζ
    have e1 := ReciprocityTheory.Neutral.Cmp.cycZ_res (F := F) ι l σ
    have e3 : (χ.comp (E : ReciprocityTheory.Neutral.Cmp.GK F ι →* Dec (F := F) A)) σ =
        Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom
          (cyclotomicCharacter (PadicAlgCl p) l (σ : PadicAlgCl p ≃+* PadicAlgCl p)) := by
      rw [← e1]
      rfl
    rw [e3]
    exact cyclotomicCharacter.spec (L := PadicAlgCl p) l (σ : PadicAlgCl p ≃+* PadicAlgCl p) ζ hζ
  have hD := dualityFor_absGal p (ReciprocityTheory.Neutral.Cmp.Kloc F ι)
    (ReciprocityTheory.Neutral.Cmp.finiteDimensional_Kloc ι) l r
    (χ.comp (E : ReciprocityTheory.Neutral.Cmp.GK F ι →* Dec (F := F) A)) hχ M
    (rho.comp (E : ReciprocityTheory.Neutral.Cmp.GK F ι →* Dec (F := F) A))
    (ReciprocityTheory.Neutral.Bridge.contAction_comp E hrho)
  exact ReciprocityTheory.Neutral.Bridge.DualityFor.of_comp E χ hrho hD

end GlobalTheory.CompanionTheory.Hypotheses₂
