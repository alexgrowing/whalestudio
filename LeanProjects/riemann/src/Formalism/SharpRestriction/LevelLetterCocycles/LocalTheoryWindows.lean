import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains

noncomputable section

open Classical

namespace Formalism.MainNotions.LocalTheoryWindows

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

inductive LT where
  | thin : LT
  | up (b : ℕ) : LT
  | down (b : ℕ) : LT
  deriving DecidableEq

def LT.thick : LT → Bool
  | .thin => false
  | _ => true

def LT.isUp : LT → Bool
  | .up _ => true
  | _ => false

def LT.isDown : LT → Bool
  | .down _ => true
  | _ => false

def LT.size : LT → ℕ
  | .thin => 0
  | .up b => b
  | .down b => b

def LT.win (G S η : ℕ) : LT → Set ℤ
  | .thin => Set.Icc (-(G : ℤ)) G
  | .up b => Set.Icc (b : ℤ) (b + S) ∪ Set.Icc (-(η : ℤ)) η
  | .down b => Set.Icc (-(b : ℤ) - S) (-(b : ℤ)) ∪ Set.Icc (-(η : ℤ)) η

def LT.ok (η : ℕ) : LT → Prop
  | .thin => True
  | .up b => η < b
  | .down b => η < b

def CutsOK (n j : ℕ) (ty : ZMod n → LT) (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ) : Prop :=
  cuts.Nonempty ∧ 1 ≤ j ∧
    (∀ c ∈ cuts, 1 ≤ arcLen c ∧ arcLen c ≤ n ∧ c - ((arcLen c : ℕ) : ZMod n) ∈ cuts ∧
      ∀ d : ℕ, 1 ≤ d → d < arcLen c → c - (d : ZMod n) ∉ cuts) ∧
    (∀ c ∈ cuts, j ≤ arcLen c) ∧
    (∀ c ∈ cuts, ∀ k : ℕ, 1 ≤ k → k ≤ j → ty (c + (k : ZMod n)) = LT.thin)

def thickLv {n : ℕ} (ty : ZMod n → LT) (arcLen : ZMod n → ℕ) (c : ZMod n) : Finset ℕ :=
  (Finset.range (arcLen c)).filter fun s => (ty (c - (s : ZMod n))).thick

def ro {n : ℕ} (ty : ZMod n → LT) (arcLen : ZMod n → ℕ) (c : ZMod n) : ℕ :=
  (thickLv ty arcLen c).card

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def WordOK {PD : PeriodData G Qp K₀ K B BdR} (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (S η G' σ : ℕ) (ty : ZMod n → LT) (arcLen : ZMod n → ℕ) (c : ZMod n) :
    Prop :=
  let l := PD.p
  let th := thickLv ty arcLen c
  (∀ s ∈ th, (ty (c - (s : ZMod n))).isDown) ∨
  (∀ s ∈ th, (ty (c - (s : ZMod n))).isUp) ∨
  (∃ g ∈ th, ∃ bD, ty (c - (g : ZMod n)) = LT.down bD ∧ (∀ s ∈ th, s ≤ g) ∧
    (∀ s ∈ th, s ≠ g → (ty (c - (s : ZMod n))).isUp) ∧
    ∑ s ∈ th.erase g, (ty (c - (s : ZMod n))).size * l ^ s < (bD + S) * l ^ g) ∨
  (∃ g ∈ th, ∃ bU, ty (c - (g : ZMod n)) = LT.up bU ∧ (∀ s ∈ th, s ≤ g) ∧
    (∀ s ∈ th, s ≠ g → (ty (c - (s : ZMod n))).isDown) ∧
    ∃ sA : ℕ, Formalism.MainNotions.LiftingTheory.Kills W F (c - (g : ZMod n)) (letπ ^ sA) ∧
      (sA + (l - 1) - 1) / (l - 1) + η + 2 * σ + 2 * (arcLen c - 1 - g) * G' + 1 ≤ bU)

def ArcAt (PD : PeriodData G Qp K₀ K B BdR) [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n)
    (C : ℝ) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p →
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), Formalism.MainNotions.LiftingTheory.Sur W F →
  ∀ (G' S η m h j : ℕ) (ty : ZMod n → LT) (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ)
    (Mi hi : ZMod n → ℕ),
    (∀ i, (ty i).ok η) →
    (∀ i, Formalism.MainNotions.TruncatedSeriesCountingBounds.JumpsAt W T₁ i ((ty i).win G' S η)) →
    (∀ i, (ty i).thick → Formalism.MainNotions.TruncatedSeriesCountingBounds.lowCount W T₂ i η ≤ m) →
    (∀ τ a, IsJumpV PD T₁.ρ τ a → |a| ≤ h) → (∀ τ a, IsJumpV PD T₂.ρ τ a → |a| ≤ h) →
    G' ≤ h → 1 ≤ h → (∀ i, (ty i).thick → (ty i).size + S ≤ h) →
    Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi hi →
    CutsOK n j ty cuts arcLen →
    let l := PD.p
    let M := 2 * h / (l - 1) + 1
    let σ : ℕ := ⌈(((2 * G' : ℕ) : ℝ) + (M : ℝ) / (l : ℝ) ^ (j - 1)) * l / ((l : ℝ) - 1) ^ 2 + 1⌉₊
    let roMax := cuts.sup (ro ty arcLen)
    let ellMax := cuts.sup arcLen
    ∀ rr : ℕ,
      (∀ c ∈ cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr) ∧
        ∀ (Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L),
          IsSESLat (Qp := Qp) ι π → IsCrys PD Y.ρ →
          Formalism.MainNotions.LiftingTheory.KillsΔ W π c (Formalism.MainNotions.LiftingTheory.lp W rr)) →
      (∀ c ∈ cuts, WordOK W F S η G' σ ty arcLen c) →
      ∃ (e κ : ℕ) (cls : Finset (LatticeCohomology T₂.L)),
        (κ : ℝ) ≤ C * (((G' : ℝ) + roMax * S + 1) * (ellMax + 1) + (roMax + 1) * Real.logb l h) ∧
        e ≤ 2 * rr + 6 * σ + 2 * κ + 2 * G' * ellMax + 1 ∧
        (↑cls : Set (LatticeCohomology T₂.L)) ⊆ (latticeFiniteCohomology PD T₂.L : Set (LatticeCohomology T₂.L)) ∧
        cls.card ≤ ∑ c ∈ cuts, m * ro ty arcLen c * (arcLen c + 1) ∧
        (∀ x ∈ latticeFiniteCohomology PD T₂.L, (((l : ℕ) : O) ^ e) • x ∈
          Submodule.span O (↑cls : Set (LatticeCohomology T₂.L)) ⊔ (latticeFiniteCohomology PD T₁.L).map F.H1map) ∧
        Formalism.MainNotions.TruncatedSeriesCountingBounds.ColLeR PD F (((n : ℝ) + 1) * finrank LL T₂.V * e +
          cls.card * Formalism.MainNotions.TruncatedSeriesCountingBounds.eLift W T₁ Mi hi)

end Core

section Lit

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {Bc BdR : Type} [CommRing Bc] [CommRing BdR] [Algebra Qp Bc] [Algebra K₀ Bc]
    [IsScalarTower Qp K₀ Bc] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

def H1fGeneratorBound (PD : PeriodData G Qp K₀ K Bc BdR) (LL O : Type) [Field LL] [Algebra Qp LL]
    [TopologicalSpace LL] [CommRing O] [Algebra O LL] : Prop :=
  Formalism.MainNotions.RamifiedCoefficientChains.H1fGeneratorBound PD LL O

end Lit

section Theory

def TheoremBLocal (Th : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (Th l)) (HW : HWOf Th)
    (F : FonOf Th A HW) (C : ℝ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL), K.1 ≤ MaximalUnramifiedExtension l →
    ∀ [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)],
      ArcAt ((Th l).PD K) ((HW l).W K 1 LL hG) C

def H1fGeneratorBoundAll (Th : LocTheory) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.H1fGeneratorBoundAll Th

end Theory

def Conclusion1 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := TheoremBLocal D.loc D.locA HW F C

def Conclusion2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := Formalism.MainNotions.TruncatedSeriesCountingBounds.Conclusion2 D HW F C

def adm1 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm

def adm2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CR CA CB CK : ℝ) : Prop := Formalism.MainNotions.LiftingTheory.aux₃ D HW F CR CA CB CK

def adm3 (D : D7) : Prop := Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D

def ArchimedeanSignatureMatching (D : D7) : Prop := Formalism.MainNotions.TruncatedSeriesCountingBounds.adm8 D

def adm5 (D : D7) : Prop := H1fGeneratorBoundAll D.loc

def adm6 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.adm2 D HW F

def adm7 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.adm17 D HW F

def adm8 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.adm18 D HW F

def adm9 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.adm19 D HW F

def adm10 (D : D7) : Prop := Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D

def adm11 (D : D7) : Prop := Formalism.MainNotions.TruncatedSeriesCountingBounds.adm16 D

def adm12 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.adm20 D HW F

def adm13 (D : D7) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.BlochKatoExtensionCriterion D.loc

def admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK : ℝ) : Prop :=
  adm1 D HW F Cm ∧ adm2 D HW F CR CA CB CK ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D HW F ∧ adm7 D HW F ∧
    adm8 D HW F ∧ adm9 D HW F ∧ adm10 D ∧ adm11 D ∧ adm12 D HW F ∧ adm13 D

def aux₃ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := Conclusion1 D HW F C ∧ Conclusion2 D HW F C

def Stmt (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (C CR CA CB CK : ℝ) : Prop :=
  admitted D HW F Cm CR CA CB CK → aux₃ D HW F C

def RealisationStatementAll : Prop :=
  ∀ CR CA CB CK : ℝ, ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    Stmt D HW F Cm C CR CA CB CK

end Formalism.MainNotions.LocalTheoryWindows
