import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.CntLocal
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LValEtaEqLValEtaF

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section DefsR

variable (D : Formalism.BasicNotions.D7)

def UPair {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') :
    Submodule D.host.E (VS D).V :=
  Submodule.span D.host.E (Set.range F0.fvec ∪ Set.range F'.fl.fvec)

def UUS {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') :
    Submodule (𝓞 D.host.E) (VS D).V :=
  XS D F0 ⊔ Submodule.span (𝓞 D.host.E) {F0.z} ⊔ XS D F'.fl ⊔ Submodule.span (𝓞 D.host.E) {F'.fl.z}

def MMg {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') :
    Submodule (𝓞 D.host.E) (VS D).V :=
  Submodule.span (𝓞 D.host.E)
    (Set.range F0.fvec ∪ Set.range fun b => ((gS D : D.host.E))⁻¹ • (F'.fl.fvec b - F0.fvec b))

def MMof {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') :
    Submodule (𝓞 D.host.E) (VS D).V :=
  ⨅ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E),
    haveI := P.isPrime
    if ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal then Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (MMg D F0 F')
    else Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UUS D F0 F')

def cOne (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K] : ℝ :=
  if hc : ∃ c : ℝ, 0 < c ∧ MassConst K F 1 c then hc.choose else 1

def cMass (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (j : ℕ) : ℝ :=
  cOne K F * ∏ i ∈ Finset.Icc 2 j, Formalism.HermitianLatticesTheory.massRatioRightSide K i

def IsGlueReps {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V)
    (M : Submodule (𝓞 K) V) (s : Finset (Submodule (𝓞 K) V)) : Prop :=
  (∀ Λ ∈ s, Λ ∈ GlueSet h U M) ∧
  (∀ Λ ∈ GlueSet h U M, ∃! Λ₁, Λ₁ ∈ s ∧ ∃ g ∈ isomFix h U, Formalism.HermitianLatticesTheory.gmap g Λ₁ = Λ) ∧
  (∀ Λ ∈ s, (stabFix h U Λ).Finite)

def cExpl {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : ℝ :=
  cMass D.host.E D.host.F (D.R.k - 1) *
    |(NumberField.discr D.host.F : ℝ)| ^ (-((2 * D.R.rS * (D.R.rS + 1) * (D.R.k - 1) : ℕ) : ℤ)) *
    (∏ i ∈ Finset.Icc D.R.k D.R.r, lValEtaF D.host.E D.host.F i) / Formalism.MainNotions.S.Cnt.massRows D F0 what₂

end DefsR

def HostDict : Prop :=
  ∀ D : Formalism.BasicNotions.D7, Formalism.HermitianLatticesTheory.IsCMUnram D.host.E ∧ IsFixF D.host.E D.host.F ∧ Nondeg (VS D).hT

def RatPair : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ Z : MatZ D, Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        ∃ F' : LFlag (VS D) D.R.rS (Tn u'), F'.zt = F'.fl.z ∧ ZhatL (lf D F0) F' = Z

def PerpDef : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (Z : MatZ D) (F' : LFlag (VS D) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        IsCompl (UPair D F0 F') (orthK (VS D).hT (UPair D F0 F')) ∧
        PosDefOn (VS D).hT (orthK (VS D).hT (UPair D F0 F')) ∧
        finrank D.host.E (UPair D F0 F') = D.R.m ∧
        finrank D.host.E (orthK (VS D).hT (UPair D F0 F')) = D.R.k - 1

def MMChar : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (Z : MatZ D) (F' : LFlag (VS D) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        IsLatIn (UPair D F0 F') (MMof D F0 F') ∧
        ∀ Λ : Submodule (𝓞 D.host.E) (VS D).V,
          (IsRowLat D F0 Λ ∧ F' ∈ EZ (Tn u') F0 Λ Z) ↔ Λ ∈ GlueSet (VS D).hT (UPair D F0 F') (MMof D F0 F')

def RowsGroupoid : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (Z : MatZ D) (F' : LFlag (VS D) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        ∀ s : Finset (Submodule (𝓞 D.host.E) (VS D).V),
          IsGlueReps (VS D).hT (UPair D F0 F') (MMof D F0 F') s →
          nu (Tn u') F0 what₂ Z * Formalism.MainNotions.S.Cnt.massRows D F0 what₂ =
            ∑ Λ ∈ s, ((Nat.card (stabFix (VS D).hT (UPair D F0 F') Λ) : ℕ) : ℝ)⁻¹

def DensAll : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) → ∀ (Z : MatZ D) (F' : LFlag (VS D) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        (Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') →
          (∀ p : PlF D, densP L δ ϖ (Tn u) (Tn u') Z p = alphaStd D.host.E p.asIdeal D.R.r /
            alphaStd D.host.E p.asIdeal (D.R.k - 1 - cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal)) ∧
          Multipliable (densP L δ ϖ (Tn u) (Tn u') Z)) ∧
        (¬ Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') → ∃ p : PlF D, densP L δ ϖ (Tn u) (Tn u') Z p = 0)

def NormMM : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (Z : MatZ D) (F' : LFlag (VS D) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') →
        nM D.host.F (VS D).hT (UPair D F0 F') (MMof D F0 F') =
          |(NumberField.discr D.host.F : ℝ)| ^ (-((2 * D.R.rS * (D.R.rS + 1) : ℕ) : ℤ)) * sqrtAbsNormOfScaledGram (Tn u) (Tn u') Z

def RowsMass : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
        Formalism.MainNotions.S.Cnt.massRows D F0 what₂ =
          cMass D.host.E D.host.F D.R.k * ((D.mem u).A.T : ℝ) ^ (D.R.k * finrank ℚ D.host.F) *
            ∏' 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal},
              (if (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ 𝔭.1 then
                1 - etaF D.host.E D.host.F 𝔭.1 ^ D.R.k * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(D.R.k : ℤ)) else 1)

def FormulaExplicit : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) → ∀ Z : MatZ D,
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
          nu (Tn u') F0 what₂ Z = cExpl D F0 what₂ * sqrtAbsNormOfScaledGram (Tn u) (Tn u') Z ^ (D.R.k - 1) *
            ∏' p, densP L δ ϖ (Tn u) (Tn u') Z p

end Formalism.L2.SG.Pf.Cnt
