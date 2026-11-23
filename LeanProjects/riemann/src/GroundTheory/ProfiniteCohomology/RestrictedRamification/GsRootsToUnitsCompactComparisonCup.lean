import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCupFormula
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCupGlobal
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsDiscreteRepResIntRepTrivGs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseClassIdele
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseKummerDelta
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory IsDedekindDomain NumberField GroundTheory.Global GroundTheory.GroupCoh GroundTheory.Global.IdeleGroup

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n] (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal)

omit [NeZero n] in
theorem linearMap_apply_add_apply {R M N P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] (f : M →ₗ[R] N →ₗ[R] P) (a b : M) (c : N) :
    f (a + b) c = f a c + f b c := by
  rw [map_add, LinearMap.add_apply]

set_option maxHeartbeats 1600000 in

theorem gsRootsToUnitsCompact_comparison_cup (h : gsUnitsCompact S ιs 1)
    (x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    (gsRootsToUnitsCompact S ιs n 3).hom ((gsRootsComparison S ιs n 3).hom
      (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n))
        (show 2 + 1 = 3 from rfl) ((gsRootsComparisonIso S ιs n hnS 2).inv.hom ((gsKummerCompactδ S ιs n hnS 1).hom h))
        x)) =
      compactCup (gsFinFamily S ιs) (gsPairingμ S n) (gsPairingμᵥ S ιs n) (gsPairingμ_hμ S ιs n)
        (show 1 + 1 + 1 = 2 + 1 from rfl) ((gsKummerCompactδ S ιs n hnS 1).hom h) x := by
  have ea := gsRootsComparison_compactCupRes S ιs n
    ((gsRootsComparisonIso S ιs n hnS 2).inv.hom ((gsKummerCompactδ S ιs n hnS 1).hom h)) x
  have ea' : (gsRootsComparison S ιs n 2).hom ((gsRootsComparisonIso S ιs n hnS 2).inv.hom
      ((gsKummerCompactδ S ιs n hnS 1).hom h)) = (gsKummerCompactδ S ιs n hnS 1).hom h :=
    hom_apply_hom_apply_of_comp_eq (gsRootsComparisonIso S ιs n hnS 2).inv_hom_id _
  have eb := compactCohomologyMap_compactCup (gsFinFamily S ιs) (A := gsRoots S n)
    (B := zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (C := gsRoots S n) (C' := galSUnitsMax K.1 ℚ̄ S)
    (Aᵥ := fun v => galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) (Cᵥ := fun v => galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) (C'ᵥ := fun v => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))
    (a := gsRootsOmegaMor S ιs n) (c := gsRootsOmegaMor S ιs n) (c' := gsSUnitsLocalMor S ιs)
    (gsZmodPairing S n) (gsZmodPairingᵥ S ιs n) (gsZmodPairing_hμ S ιs n)
    (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) n).f
    (fun v => (kummerSequence ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n).f)
    (fun v => (gsKummerLocalMap S ιs n v).comm₁₂) (gsPairingμ_hμ S ιs n) (show 1 + 1 + 1 = 2 + 1 from rfl)
    ((gsKummerCompactδ S ιs n hnS 1).hom h) x
  exact (congrArg (gsRootsToUnitsCompact S ιs n 3).hom (ea.trans (congrArg (fun w =>
    compactCup (gsFinFamily S ιs) (gsZmodPairing S n) (gsZmodPairingᵥ S ιs n) (gsZmodPairing_hμ S ιs n)
      (show 2 + 1 = 3 from rfl) w x) ea'))).trans eb

set_option maxHeartbeats 1600000 in

theorem gsRootsToUnitsCompact_cup_eq (ℓ k : ℕ) (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (d : GsUnitsDatum S) (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    ∃ W : cocycles (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2,
      (∀ g h, (Additive.toMul (cochainOf _ (cocycleι _ 2 W) ![g, h]) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) *
        (((Additive.toMul d.1 : sInvariantSubgroup (F := K.1) ℚ̄ S) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) ^
          bockInt (zmodCocycleHom z) g h)⁻¹ ∈ sUnitsMax K.1 ℚ̄ S) ∧
      (gsRootsToUnitsCompact S ιs n 3).hom ((gsRootsComparison S ιs n 3).hom
        (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n))
          (show 2 + 1 = 3 from rfl)
          ((gsRootsComparisonIso S ιs n hnS 2).inv.hom ((gsKummerCompactδ S ιs n hnS 1).hom (gsUnitsData S ιs d)))
          (cohomologyπ _ 1 z))) =
        (localToCompact (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) (fun v => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (gsSUnitsLocalMor S ιs) 2).hom
          (fun v => (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
              (gsUnitsLocalMor S ιs v) 2).hom (cohomologyπ _ 2 W) +
            cupPairing (mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (show 0 + 2 = 2 from rfl)
              ((H0Iso _).inv.hom (unitsToInvariants _ _ (d.2 v)))
              ((cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _) (𝟙 _) 2).hom
                ((δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom
                  (cohomologyπ _ 1 z)))) := by
  have ex := exists_gsUnitsData_cup_bock S ιs n ℓ k hℓ hnk hS (Additive.toMul d.1) z
  refine ⟨ex.choose, ex.choose_spec.1, ?_⟩
  have hd : gsUnitsData S ιs d = gsUnitsData S ιs (Additive.ofMul (Additive.toMul d.1), 0) +
      gsUnitsData S ιs (0, d.2) :=
    (congrArg (gsUnitsData S ιs) (Prod.ext (add_zero _).symm (zero_add _).symm)).trans (map_add _ _ _)
  have eloc := compactCup_localToCompact (gsFinFamily S ιs) (gsPairingU S)
    (fun v => mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (gsPairingU_hμ S ιs)
    (show 0 + 2 = 2 from rfl) (show 0 + 1 + 2 = 2 + 1 from rfl)
    (fun v => (H0Iso _).inv.hom (unitsToInvariants _ _ (d.2 v)))
    ((δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom (cohomologyπ _ 1 z))
  refine (gsRootsToUnitsCompact_comparison_cup S ιs n hnS (gsUnitsData S ιs d) (cohomologyπ _ 1 z)).trans
    ((gsKummerCompactδ_cup S ιs n hnS (gsUnitsData S ιs d) (cohomologyπ _ 1 z)).trans ?_)
  refine (congrArg (fun w => compactCup (gsFinFamily S ιs) (gsPairingU S)
      (fun v => mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (gsPairingU_hμ S ιs)
      (show 1 + (1 + 1) = 2 + 1 from rfl) w
      ((δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom (cohomologyπ _ 1 z)))
    hd).trans ((linearMap_apply_add_apply _ _ _ _).trans ?_)
  refine (congrArg₂ (· + ·) ex.choose_spec.2 ((congrArg (fun w => compactCup (gsFinFamily S ιs) (gsPairingU S)
      (fun v => mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (gsPairingU_hμ S ιs)
      (show 1 + (1 + 1) = 2 + 1 from rfl) w
      ((δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom (cohomologyπ _ 1 z)))
    (gsUnitsData_zero_local S ιs d.2)).trans eloc)).trans ?_
  exact (map_add _ _ _).symm

section Idele

variable [Fintype S] (hodd : Odd n ∨ IsTotallyComplex K.1)

omit [NeZero n] in
theorem prod_ofFinite_eq {M : Type*} [CommMonoid M] (f : S → M) :
    (letI := Fintype.ofFinite S; ∏ w : S, f w) = ∏ w : S, f w := by
  congr
  exact Subsingleton.elim _ _

omit [NeZero n] in

theorem sPresentation_fst (a : ∀ w : S, ((w : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)ˣ) :
    sPresentation S (a, 1) = ∏ w : S, SIdeleClassGroup.mk S (finiteEmbedding (w : HeightOneSpectrum (𝓞 K.1)) (a w)) := by
  rw [sPresentation_apply, toAdd_one, map_zero, toMul_zero, mul_one, placesIdele_apply, map_prod]
  exact prod_ofFinite_eq S _

set_option maxHeartbeats 1600000 in

theorem zmodToQZ_charEquiv_gsUnitsClass
    (χ : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n))) (d : GsUnitsDatum S) :
    zmodToQZ n (Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd χ (Additive.toMul (gsUnitsClass S d)))) =
      ∑ v : S, zmodToQZ n (Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd χ
        (SIdeleClassGroup.mk S (finiteEmbedding (v : HeightOneSpectrum (𝓞 K.1)) (Additive.toMul (d.2 v)))))) -
      divChar S hodd χ (divAbove S d.1) := by
  have e1 : Additive.toMul (gsUnitsClass S d) =
      sPresentation S (fun w => Additive.toMul (d.2 w), 1) *
        sPresentation S (1, Multiplicative.ofAdd (-divAbove S d.1)) :=
    (congrArg Additive.toMul (gsUnitsClass_apply S d)).trans
      ((congrArg (sPresentation S) (Prod.ext (mul_one _).symm (one_mul _).symm)).trans (map_mul _ _ _))
  set ψ := charEquiv ℚ̄ (Set.toFinite S) hodd χ with hψ
  have e2 : ψ (Additive.toMul (gsUnitsClass S d)) =
      (∏ w : S, ψ (SIdeleClassGroup.mk S (finiteEmbedding (w : HeightOneSpectrum (𝓞 K.1)) (Additive.toMul (d.2 w))))) *
        ψ (sPresentation S (1, Multiplicative.ofAdd (-divAbove S d.1))) :=
    (congrArg ψ e1).trans ((map_mul ψ _ _).trans (congrArg (· * _)
      ((congrArg ψ (sPresentation_fst S _)).trans (map_prod ψ _ _))))
  have e3 : zmodToQZ n (Multiplicative.toAdd (ψ (sPresentation S (1, Multiplicative.ofAdd (-divAbove S d.1))))) =
      -divChar S hodd χ (divAbove S d.1) :=
    (divChar_apply S hodd χ (-divAbove S d.1)).symm.trans (map_neg _ _)
  have e4 : zmodToQZ n (Multiplicative.toAdd (∏ w : S, ψ (SIdeleClassGroup.mk S
      (finiteEmbedding (w : HeightOneSpectrum (𝓞 K.1)) (Additive.toMul (d.2 w)))))) =
      ∑ w : S, zmodToQZ n (Multiplicative.toAdd (ψ (SIdeleClassGroup.mk S
        (finiteEmbedding (w : HeightOneSpectrum (𝓞 K.1)) (Additive.toMul (d.2 w)))))) :=
    (congrArg (zmodToQZ n) (toAdd_prod _ _)).trans (map_sum (zmodToQZ n) _ _)
  exact (congrArg (fun u => zmodToQZ n (Multiplicative.toAdd u)) e2).trans
    ((congrArg (zmodToQZ n) (toAdd_mul _ _)).trans ((map_add (zmodToQZ n) _ _).trans
      ((congrArg₂ (· + ·) e4 e3).trans (sub_eq_add_neg _ _).symm)))

end Idele

end

end GroundTheory.ProfCoh
