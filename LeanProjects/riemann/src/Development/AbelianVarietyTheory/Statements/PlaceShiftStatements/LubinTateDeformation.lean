import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalModule

noncomputable section

open PowerSeries

namespace GlobalTheory.FOM

def resRed (Ob R : Type*) [CommRing Ob] [IsLocalRing Ob] [CommRing R] [IsLocalRing R] [Algebra Ob R]
    [IsLocalHom (algebraMap Ob R)]
    (hb : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap Ob R))) :
    R →+* IsLocalRing.ResidueField Ob :=
  (RingEquiv.ofBijective _ hb).symm.toRingHom.comp (IsLocalRing.residue R)

def ModStarIso {O R : Type*} [CommRing O] [CommRing R] [Algebra O R] (m : Ideal R)
    (M N : FormalModule O R) : Prop :=
  ∃ u : PowerSeries R, IsStar m u ∧ IsModHom M N u

abbrev LTRing (Ob : Type*) [CommRing Ob] (h : ℕ) : Type _ := MvPowerSeries (Fin (h - 1)) Ob

def ltRed (Ob : Type*) [CommRing Ob] [IsLocalRing Ob] (h : ℕ) : LTRing Ob h →+* IsLocalRing.ResidueField Ob :=
  (IsLocalRing.residue Ob).comp MvPowerSeries.constantCoeff

def LubinTateDeformation : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
    (Ob : Type) [CommRing Ob] [IsDomain Ob] [IsDiscreteValuationRing Ob] [Algebra O Ob]
    [IsLocalHom (algebraMap O Ob)] [IsAdicComplete (IsLocalRing.maximalIdeal Ob) Ob]
    [IsAlgClosed (IsLocalRing.ResidueField Ob)] (ϖ : O), Irreducible ϖ → Irreducible (algebraMap O Ob ϖ) →
    ∀ (h : ℕ), 1 ≤ h → ∀ Gk : FormalModule O (IsLocalRing.ResidueField Ob),
      HasHeight ⊥ Gk ϖ (Nat.card (IsLocalRing.ResidueField O)) h →
      ∃ G : FormalModule O (LTRing Ob h), IsImage (ltRed Ob h) G Gk ∧
        ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
          [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Algebra Ob R] [Algebra O R] [IsScalarTower O Ob R]
          [IsLocalHom (algebraMap Ob R)] (hb : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap Ob R)))
          (D : FormalModule O R), IsImage (resRed Ob R hb) D Gk →
          ∃! φ : LTRing Ob h →ₐ[Ob] R, ∃ E : FormalModule O R, IsImage φ.toRingHom G E ∧
            ModStarIso (IsLocalRing.maximalIdeal R) E D

def IwahoriDeformation : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
    (Ob : Type) [CommRing Ob] [IsDomain Ob] [IsDiscreteValuationRing Ob] [Algebra O Ob]
    [IsLocalHom (algebraMap O Ob)] [IsAdicComplete (IsLocalRing.maximalIdeal Ob) Ob]
    [IsAlgClosed (IsLocalRing.ResidueField Ob)] (ϖ : O), Irreducible ϖ →
    ∀ (hϖ : Irreducible (algebraMap O Ob ϖ)) (h : ℕ) (hh : 1 ≤ h)
      (C0 : IsoChain (O := O) (⊥ : Ideal (IsLocalRing.ResidueField Ob)) ϖ (Nat.card (IsLocalRing.ResidueField O)) h),
      HasHeight ⊥ (C0.M 0) ϖ (Nat.card (IsLocalRing.ResidueField O)) h →
      ∃ U : IsoChain (O := O)
          (iwMax Ob h hh (algebraMap O Ob ϖ) ((IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit))
          ϖ (Nat.card (IsLocalRing.ResidueField O)) h,
        IsChainImage (iwRed Ob h hh (algebraMap O Ob ϖ) ((IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit)) U C0 ∧
        ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
          [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Algebra Ob R] [Algebra O R] [IsScalarTower O Ob R]
          [IsLocalHom (algebraMap Ob R)] (hb : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap Ob R)))
          (D : IsoChain (O := O) (IsLocalRing.maximalIdeal R) ϖ (Nat.card (IsLocalRing.ResidueField O)) h),
          IsChainImage (resRed Ob R hb) D C0 →
          ∃! φ : IwRing Ob h (algebraMap O Ob ϖ) →ₐ[Ob] R,
            ∃ E : IsoChain (O := O) (IsLocalRing.maximalIdeal R) ϖ (Nat.card (IsLocalRing.ResidueField O)) h,
              IsChainImage φ.toRingHom U E ∧ StarIso E D

end GlobalTheory.FOM
