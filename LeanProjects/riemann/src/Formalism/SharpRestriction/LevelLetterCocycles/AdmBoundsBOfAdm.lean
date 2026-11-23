import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def HypB (PD : PeriodData G Qp K₀ K B BdR) [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n)
    (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b w S η m : ℕ) (up : ZMod n → Bool)
    (size Mi hi : ZMod n → ℕ) : Prop :=
  11 ≤ PD.p ∧ TruncatedSeriesCountingBounds.HidaSetting PD W T₁ T₂ F b w S η m up size Mi hi ∧ 20 * w ≤ b ∧ 20 * η ≤ b ∧
    20 * S ≤ b ∧ ∃ i, ¬ TruncatedSeriesCountingBounds.Thick b η size i

def Alt (b η : ℕ) (up : ZMod n → Bool) (size : ZMod n → ℕ) : Prop :=
  ∀ i, up (i + 1) ≠ up i ∧
    ¬ (TruncatedSeriesCountingBounds.Thick b η size i ∧ TruncatedSeriesCountingBounds.Thick b η size (i + 1) ∧ TruncatedSeriesCountingBounds.Thick b η size (i + 2))

def One (b η R : ℕ) (up : ZMod n → Bool) (size : ZMod n → ℕ) : Prop :=
  (∀ i, up i = up 0) ∧ ∀ i, ¬ ∀ t : ℕ, t < R → TruncatedSeriesCountingBounds.Thick b η size (i + t)

def Sg (l b w S η : ℕ) (size : ZMod n → ℕ) : ℝ :=
  (TruncatedSeriesCountingBounds.hB b w S η size : ℝ) / (l : ℝ) ^ 2 + ((w : ℝ) + S + η) / l +
    Real.logb l (2 * (TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) + 1

def bandI (l b w S η : ℕ) (size : ZMod n → ℕ) (Cb : ℝ) : ℝ :=
  if TruncatedSeriesCountingBounds.Band l b S η size (Real.logb l (2 * (TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) Cb then 1 else 0

def arcOf [NeZero n] (b w S η : ℕ) (up : ZMod n → Bool) (size : ZMod n → ℕ) : ArcLiftingSetup.ArcP n where
  G₀ := w + S
  S := S
  η := η
  h := TruncatedSeriesCountingBounds.hB b w S η size
  j := 1
  ty := fun i => if up i then .up (size i) else .down (size i)
  cuts := Finset.univ.filter fun c => ¬ TruncatedSeriesCountingBounds.Thick b η size (c + 1)
  len := fun c => sInf {d : ℕ | 1 ≤ d ∧
    ¬ TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)}

def kapC (l : ℕ) (A : ArcLiftingSetup.ArcP n) (c : ZMod n) : ℕ :=
  A.len c + ∑ i ∈ (A.JS c).erase 0, (A.len c + 1 + padicValInt l i)

def ExpIn (PD : PeriodData G Qp K₀ K B BdR) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (Z : Finset (G → T₂.V)) (e : ℕ) : Prop :=
  ∀ c ∈ latticeFiniteCocycles PD T₂.L, ((PD.p : O) ^ e) • c ∈ F.ImF PD ⊔ Submodule.span O (Z : Set (G → T₂.V))

def ExtYCore (PD : PeriodData G Qp K₀ K B BdR) (W : LocWach PD LL O v n) : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ cc ∈ latticeFiniteCocycles PD T.L,
    ∃ (Y : LocLat G Qp LL O) (ι : LatHom T.L Y.L) (π : LatHom Y.L W.one.L),
      IsCrys PD Y.ρ ∧ Formalism.MainNotions.LiftingTheory.IsExtOf W ι π cc

end Core

structure AdmBoundsB (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CR CA CB CK : ℝ) : Prop where
  p2 : Formalism.MainNotions.DeltaInvariantLattices.P2 D HW F
  p3 : Formalism.MainNotions.DeltaInvariantLattices.P3 D HW F Cm
  p4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm
  p5 : Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F
  p9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F
  a2 : ArcLiftingSetup.adm2 D HW F CR CA CB CK
  a5 : ArcLiftingSetup.adm5 D HW F
  sP : ArcLiftingSetup.SaturationFrobeniusPullback D HW F
  kLev : ArcLiftingSetup.KillerLevL D.loc D.locA HW F
  kMod : ArcLiftingSetup.KillerModL D.loc D.locA HW F
  a9 : ArcLiftingSetup.adm9 D
  a10 : ArcLiftingSetup.adm10 D
  a11 : ArcLiftingSetup.adm11 D HW F
  a12 : ArcLiftingSetup.adm12 D HW F Cm
  a13 : ArcLiftingSetup.adm13 D HW F Cm
  a14 : ArcLiftingSetup.adm14 D HW F Cm
  a15 : ArcLiftingSetup.adm15 D

theorem admBoundsB_of_adm {D : D7} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW} {Cm : CmpOf D.loc D.locA HW F}
    {CR CA CB CK Ckap : ℝ} (h : ArcLiftingSetup.admitted D HW F Cm CR CA CB CK Ckap) : AdmBoundsB D HW F Cm CR CA CB CK :=
  ⟨fun l _ K s LL g => (h.1.1 l K s LL g).2.1, fun l _ K s LL g => (h.1.1 l K s LL g).2.2.1,
    fun l _ K s LL g => (h.1.1 l K s LL g).2.2.2.1, fun l _ K s LL g => (h.1.1 l K s LL g).2.2.2.2.1,
    fun l _ K s LL g => (h.1.1 l K s LL g).2.2.2.2.2.2.2.2.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1.2.2.1, h.2.2.2.2.1.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1⟩

end Formalism.MainNotions.N.Ln17
