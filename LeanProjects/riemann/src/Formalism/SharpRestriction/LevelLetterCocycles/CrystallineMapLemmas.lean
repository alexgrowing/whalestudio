import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

noncomputable section

open Classical

namespace Formalism.MainNotions.TruncatedSeriesCountingBounds

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def JumpsAt {PD : PeriodData G Qp K₀ K B BdR} (W : LocWach PD LL O v n)
    (T : LocLat G Qp LL O) (i : ZMod n) (Sset : Set ℤ) : Prop :=
  ∀ τ, Formalism.MainNotions.LiftingTheory.Over W τ i → JumpsInV PD T.ρ τ Sset

def lowCount {PD : PeriodData G Qp K₀ K B BdR} [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n)
    (T : LocLat G Qp LL O) (i : ZMod n) (η : ℕ) : ℤ :=
  ∑ τ ∈ Finset.univ.filter (fun τ => Formalism.MainNotions.LiftingTheory.Over W τ i),
    ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV PD T.ρ τ a

def ColLeR (PD : PeriodData G Qp K₀ K B BdR) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (x : ℝ) : Prop :=
  ∃ mm k : ℕ, F.col PD = mm ∧ lenOl PD (O := O) = k ∧ (mm : ℝ) ≤ x * k

def Thick (b η : ℕ) (size : ZMod n → ℕ) (i : ZMod n) : Prop := b ≤ size i ∧ size i ≤ b + η

def HidaSetting (PD : PeriodData G Qp K₀ K B BdR) [Fintype (K →ₐ[Qp] LL)]
    (W : LocWach PD LL O v n) (T₁ T₂ : LocLat G Qp LL O)
    (F : LatHom T₁.L T₂.L) (b w S η m : ℕ) (up : ZMod n → Bool) (size Mi hi : ZMod n → ℕ) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W ∧ Formalism.MainNotions.LiftingTheory.Sur W F ∧
  (∀ i, η < size i) ∧
  (∀ i, JumpsAt W T₁ i (if up i then
      Set.Icc (size i : ℤ) ((size i : ℤ) + S) ∪ Set.Icc (-(η : ℤ)) η
    else Set.Icc (-(size i : ℤ) - S) (-(size i : ℤ)) ∪ Set.Icc (-(η : ℤ)) η)) ∧
  (∀ i, lowCount W T₂ i η ≤ m) ∧
  (∀ i, ¬ Thick b η size i → size i ≤ w) ∧
  Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi hi

def WachLatticeMapSetting (PD : PeriodData G Qp K₀ K B BdR) [Fintype (K →ₐ[Qp] LL)]
    (W : LocWach PD LL O v n) (T₁ T₂ : LocLat G Qp LL O)
    (F : LatHom T₁.L T₂.L) (b w S η m : ℕ) (up : ZMod n → Bool) (size Mi hi : ZMod n → ℕ) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W ∧ Formalism.MainNotions.LiftingTheory.Sur W F ∧
  (∀ i, η < size i) ∧
  (∀ i, JumpsAt W T₁ i (if up i then
      Set.Icc (size i : ℤ) ((size i : ℤ) + S) ∪ Set.Icc (-(η : ℤ)) η
    else Set.Icc (-(size i : ℤ) - S) (-(size i : ℤ)) ∪ Set.Icc (-(η : ℤ)) η)) ∧
  (∀ i, Thick b η size i → lowCount W T₂ i η ≤ m) ∧
  (∀ i, ¬ Thick b η size i → size i ≤ w) ∧
  Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi hi

def eLift {PD : PeriodData G Qp K₀ K B BdR} (W : LocWach PD LL O v n) (T₁ : LocLat G Qp LL O)
    (Mi hi : ZMod n → ℕ) : ℕ :=
  Formalism.MainNotions.LiftingTheory.ePA PD.p (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi)
    (Formalism.MainNotions.LiftingTheory.jumpSet W T₁ (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi))

def hB (b w S η : ℕ) (size : ZMod n → ℕ) : ℕ :=
  if ∃ i, Thick b η size i then b + η + S else w + S

def Band (l b S η : ℕ) (size : ZMod n → ℕ) (lg C : ℝ) : Prop :=
  ∃ i, ¬ Thick b η size i ∧ (Thick b η size (i + 1) ∨ Thick b η size (i - 1)) ∧
    |(l : ℝ) * size i - b| ≤ C * ((l : ℝ) * η + (l : ℝ) * S + (b : ℝ) / l + size i + (l : ℝ) * lg)

def ThmB (PD : PeriodData G Qp K₀ K B BdR) [Fintype (K →ₐ[Qp] LL)]
    (W : LocWach PD LL O v n) (C : ℝ) : Prop :=
  11 ≤ PD.p →
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b w S η m : ℕ) (up : ZMod n → Bool)
    (size Mi hi : ZMod n → ℕ),
    HidaSetting PD W T₁ T₂ F b w S η m up size Mi hi →
    20 * w ≤ b → 20 * η ≤ b → 20 * S ≤ b →
    (∃ i, ¬ Thick b η size i) →
    let l : ℕ := PD.p
    let h : ℕ := hB b w S η size
    let lg : ℝ := Real.logb l (2 * (h : ℝ))
    let band : ℝ := if Band l b S η size lg C then 1 else 0
    let r : ℝ := finrank LL T₂.V
    let e' : ℝ := eLift W T₁ Mi hi
    ((∀ i, up (i + 1) ≠ up i ∧
        ¬ (Thick b η size i ∧ Thick b η size (i + 1) ∧ Thick b η size (i + 2))) →
      ColLeR PD F (C * ((n : ℝ) + 1) * r * ((h : ℝ) / (l : ℝ) ^ 2 + ((w : ℝ) + η) / l + S + 1 + lg +
        η * band) + C * n * m * e')) ∧
    (∀ R : ℕ, 1 ≤ R → (∀ i, up i = up 0) → (∀ i, ¬ ∀ t : ℕ, t < R → Thick b η size (i + t)) →
      ColLeR PD F (C * ((n : ℝ) + 1) * r * ((h : ℝ) / (l : ℝ) ^ 2 + ((w : ℝ) + η) / l +
        (R : ℝ) ^ 2 * (S + 1 + lg) + η * band) + C * n * m * (R : ℝ) ^ 2 * e'))

def Clusters (j : ℕ) (thick : ZMod n → Prop) : Prop :=
  ∀ t, thick t →
    (∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ thick (t - k)) ∨
    (∃ d : ℕ, 1 ≤ d ∧ d ≤ j ∧ thick (t - d) ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ d + j → k ≠ d → ¬ thick (t - k))

def CorA (PD : PeriodData G Qp K₀ K B BdR) [Fintype (K →ₐ[Qp] LL)]
    (W : LocWach PD LL O v n) (C : ℝ) : Prop :=
  11 ≤ PD.p →
  ∀ (j : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b w S η m : ℕ) (up : ZMod n → Bool)
    (size Mi hi : ZMod n → ℕ),
    WachLatticeMapSetting PD W T₁ T₂ F b w S η m up size Mi hi →
    1 ≤ j → 1 ≤ S → 1 ≤ η → 1 ≤ w → 1 ≤ b →
    let l : ℕ := PD.p
    let Gw : ℕ := w + S + η
    let h : ℕ := if ∃ i, Thick b η size i then b + η + S else max Gw 1
    C * ((j : ℝ) + 1) * ((Gw : ℝ) + 1) ≤ b → j + 1 ≤ n → Clusters j (Thick b η size) →
    ColLeR PD F (C * ((n : ℝ) + 1) * (finrank LL T₂.V : ℝ) *
        ((h : ℝ) / ((l : ℝ) - 1) ^ (j + 1) + ((Gw : ℝ) + 1) * ((j : ℝ) + 1) + Real.logb l h) +
      C * (Nat.card {i : ZMod n // Thick b η size i} : ℝ) * m * ((j : ℝ) + 1) * (eLift W T₁ Mi hi : ℝ))

end Core

def crisMap {Qp : Type} [Field Qp] (B : Type) [CommRing B] [Algebra Qp B] {LL : Type} [Field LL]
    [Algebra Qp LL] {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (f : V →ₗ[LL] V') :
    TensorProduct Qp V B →ₗ[LL] TensorProduct Qp V' B :=
  TensorProduct.AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B)

section Lit

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {Bc BdR : Type} [CommRing Bc] [CommRing BdR] [Algebra Qp Bc] [Algebra K₀ Bc] [IsScalarTower Qp K₀ Bc]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

def DcrisExactStrict [TopologicalSpace G] (PD : PeriodData G Qp K₀ K Bc BdR) (LL : Type) [Field LL]
    [Algebra Qp LL] [TopologicalSpace LL] : Prop :=
  Function.Bijective (algebraMap K₀ K) →
  ∀ (V₀ V₁ V₂ : Type) [AddCommGroup V₀] [Module LL V₀] [Module Qp V₀] [IsScalarTower Qp LL V₀]
    [FiniteDimensional LL V₀] [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁]
    [IsScalarTower Qp LL V₁] [FiniteDimensional LL V₁] [AddCommGroup V₂] [Module LL V₂]
    [Module Qp V₂] [IsScalarTower Qp LL V₂] [FiniteDimensional LL V₂]
    (ρ₀ : Representation LL G V₀) (ρ₁ : Representation LL G V₁) (ρ₂ : Representation LL G V₂)
    (ι : V₀ →ₗ[LL] V₁) (π : V₁ →ₗ[LL] V₂)
    [TopologicalSpace V₀] [IsModuleTopology LL V₀] [TopologicalSpace V₁] [IsModuleTopology LL V₁]
    [TopologicalSpace V₂] [IsModuleTopology LL V₂],
    (∀ x, Continuous fun g => ρ₀ g x) → (∀ x, Continuous fun g => ρ₁ g x) →
    (∀ x, Continuous fun g => ρ₂ g x) →
    (∀ g x, ι (ρ₀ g x) = ρ₁ g (ι x)) → (∀ g x, π (ρ₁ g x) = ρ₂ g (π x)) →
    Function.Injective ι → Function.Surjective π → LinearMap.range ι = LinearMap.ker π →
    IsCrys PD ρ₀ → IsCrys PD ρ₁ → IsCrys PD ρ₂ →
    (∀ y ∈ Dcris PD ρ₀, crisMap Bc ι y = 0 → y = 0) ∧
    (∀ x ∈ Dcris PD ρ₁, crisMap Bc π x = 0 → ∃ y ∈ Dcris PD ρ₀, crisMap Bc ι y = x) ∧
    (Dcris PD ρ₁).map (crisMap Bc π) = Dcris PD ρ₂ ∧
    (∀ a : ℤ, (FilCris PD ρ₁ a).map (crisMap Bc π) = FilCris PD ρ₂ a) ∧
    (∀ (a : ℤ), ∀ y ∈ Dcris PD ρ₀, crisMap Bc ι y ∈ FilCris PD ρ₁ a → y ∈ FilCris PD ρ₀ a)

def DdREqDcris [TopologicalSpace G] (PD : PeriodData G Qp K₀ K Bc BdR) (LL : Type) [Field LL]
    [Algebra Qp LL] [TopologicalSpace LL] : Prop :=
  Function.Bijective (algebraMap K₀ K) →
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V) [TopologicalSpace V] [IsModuleTopology LL V],
    (∀ x, Continuous fun g => ρ g x) → IsCrys PD ρ →
    (Dcris PD ρ).map (ιV PD (LL := LL) (V := V)) = DdR PD ρ ∧
    ∀ τ : K →ₐ[Qp] LL, FiniteDimensional LL ↥(DdRE PD ρ τ) ∧
      finrank LL ↥(DdRE PD ρ τ) = finrank LL V ∧
      ∀ a : ℤ, FildR PD ρ τ a =
        (FilCris PD ρ a ⊓ DcrisL PD ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))).map
          (ιV PD (LL := LL) (V := V))

def H1fGeneratorDRBound [TopologicalSpace G] (PD : PeriodData G Qp K₀ K Bc BdR) (LL O : Type) [Field LL]
    [Algebra Qp LL] [TopologicalSpace LL] [Fintype (K →ₐ[Qp] LL)] [CommRing O] [Algebra O LL] :
    Prop :=
  ∀ (T : LocLat G Qp LL O) [IsTopologicalAddGroup T.V], FiniteCohomologyGeneratorsBound PD T.L

end Lit

section Theory

def TheoremBLocal (LT : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (HW : HWOf LT) (F : FonOf LT A HW) (C : ℝ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL), K.1 ≤ MaximalUnramifiedExtension l →
    ∀ [NeZero (Module.finrank ℚ_[l] ↥(K0 K))] [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)],
      ThmB ((LT l).PD K) ((HW l).W K 1 LL hG) C

def CorollaryALocal (LT : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (HW : HWOf LT) (F : FonOf LT A HW) (C : ℝ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL), K.1 ≤ MaximalUnramifiedExtension l →
    ∀ [NeZero (Module.finrank ℚ_[l] ↥(K0 K))] [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)],
      CorA ((LT l).PD K) ((HW l).W K 1 LL hG) C

def BlochKatoDimensionLocal (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)],
    BlochKatoDim ((LT l).PD K) ↥LL.1

def DcrisExactStrictLocal (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), DcrisExactStrict ((LT l).PD K) ↥LL.1

def H1fGeneratorDRBoundAll (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)],
    H1fGeneratorDRBound ((LT l).PD K) ↥LL.1 ↥(OL LL)

def DdREqDcrisAll (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), DdREqDcris ((LT l).PD K) ↥LL.1

def FontaineDcrisInequality (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), FontaineLe ((LT l).PD K) ↥LL.1

end Theory

def Conclusion1 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := TheoremBLocal D.loc D.locA HW F C

def Conclusion2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := CorollaryALocal D.loc D.locA HW F C

def adm1 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm

def adm2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.ConclusionL D HW F

def adm3 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.ConclusionW D HW F

def ArchimedeanSignatureMatching (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := Formalism.MainNotions.LiftingTheory.WachAnnihilatorAll D HW F ∧ Formalism.MainNotions.LiftingTheory.WachResultConstant D HW F C

def adm5 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.ConclusionH D HW F

def adm6 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F

def adm7 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CA CB CK : ℝ) : Prop := Formalism.MainNotions.LiftingTheory.LiftTheoremAllCases D HW F CA CB CK

def adm8 (D : D7) : Prop := BlochKatoDimensionLocal D.loc

def adm9 (D : D7) : Prop := DcrisExactStrictLocal D.loc

def adm10 (D : D7) : Prop := H1fGeneratorDRBoundAll D.loc

def adm11 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.adm17 D HW F

def adm12 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.adm18 D HW F

def adm13 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.adm19 D HW F

def adm14 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.adm20 D HW F

def adm15 (D : D7) : Prop := DdREqDcrisAll D.loc

def adm16 (D : D7) : Prop := FontaineDcrisInequality D.loc

def admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (C CA CB CK : ℝ) : Prop :=
  adm1 D HW F Cm ∧ adm2 D HW F ∧ adm3 D HW F ∧ ArchimedeanSignatureMatching D HW F C ∧ adm5 D HW F ∧ adm6 D HW F ∧ adm7 D HW F CA CB CK ∧ adm8 D ∧ adm9 D ∧
    adm10 D ∧ adm11 D HW F ∧ adm12 D HW F ∧ adm13 D HW F ∧ adm14 D HW F ∧ adm15 D ∧ adm16 D

def Stmt (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (C₁ C₂ C CA CB CK : ℝ) : Prop :=
  admitted D HW F Cm C CA CB CK → Conclusion1 D HW F C₁ ∧ Conclusion2 D HW F C₂

end Formalism.MainNotions.TruncatedSeriesCountingBounds
