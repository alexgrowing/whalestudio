import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.WeaklyAdmissibleFiltrations.StatementPC
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

noncomputable section

namespace Formalism.MainNotions.ElementDenominator

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

section PartI

variable {l : ℕ} [Fact l.Prime]

def colLe (P : LocPrime l) (K LL : FinExt l) {T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)}
    (F : LatHom T₁.L T₂.L) (b : ℝ) : Prop :=
  ∃ m k : ℕ, F.col (P.PD K) = m ∧ lenOl (P.PD K) (O := ↥(OL LL)) = k ∧ (m : ℝ) ≤ b * k

def intersection_update_fsHerm_neg_one (K : FinExt l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL] (τ : ↥K.1 →ₐ[ℚ_[l]] LL) :
    ↥(K0 K) →ₐ[ℚ_[l]] LL :=
  τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)

def deep (up : Bool) (b S : ℕ) : Set ℤ :=
  if up then Set.Icc (b : ℤ) (b + S) else Set.Icc (-((b : ℤ) + S)) (-(b : ℤ))

def boundA (C : ℝ) (l n e r S η m h : ℕ) : ℝ :=
  C * ((n : ℝ) * e + 1) * r *
      ((e : ℝ) * h / l + (e : ℝ) * S + (e : ℝ) * Real.logb l h + 1 + η) +
    (n : ℝ) * e * (e + 1) * m * (C * ((h : ℝ) + 1))

def thmA (P : LocPrime l) (K LL : FinExt l) (C : ℝ) : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (r S η m h : ℕ)
    (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ),
    IsCrys (P.PD K) T₁.ρ → IsCrys (P.PD K) T₂.ρ → F.Onto →
    finrank ↥LL.1 T₂.V = r →
    (∀ τ, JumpsInV (P.PD K) T₁.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η)) →
    (∀ τ, η < b τ) →
    (∀ τ, ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV (P.PD K) T₂.ρ τ a ≤ m) →
    (∀ τ, JumpsInV (P.PD K) T₁.ρ τ (Set.Icc (-(h : ℤ)) h)) →
    (finrank ↥(K0 K) ↥K.1 = 2 ∨ ∀ τ τ', intersection_update_fsHerm_neg_one K τ = intersection_update_fsHerm_neg_one K τ' → up τ = up τ') →
    colLe P K LL F
      (boundA C l (finrank ℚ_[l] ↥(K0 K)) (finrank ↥(K0 K) ↥K.1) r S η m h)

end PartI

def TheoremBLocal (LT : LocTheory) (C : ℝ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → thmA (LT l) K LL C

def Conclusion1 (D : D7) (C : ℝ) : Prop := TheoremBLocal D.loc C

def H1fGeneratorBoundAll (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL →
    ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) [IsTopologicalAddGroup T.V],
      haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
      letI : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
      FiniteCohomologyGeneratorsBound ((LT l).PD K) T.L

def FontaineRegularity (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
    (FiniteDimensional ↥LL.1 ↥(Dcris ((LT l).PD K) T.ρ) ∧
      finrank ↥LL.1 ↥(Dcris ((LT l).PD K) T.ρ) ≤ finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 T.V) ∧
    ∀ τ, FiniteDimensional ↥LL.1 ↥(DdRE ((LT l).PD K) T.ρ τ) ∧
      finrank ↥LL.1 ↥(DdRE ((LT l).PD K) T.ρ τ) ≤ finrank ↥LL.1 T.V

def FontaineStrictExact (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l)
    (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
    IsSESLat (Qp := ℚ_[l]) ι π → IsCrys ((LT l).PD K) T₁.ρ →
    IsCrys ((LT l).PD K) T₀.ρ ∧ IsCrys ((LT l).PD K) T₂.ρ ∧
    ∀ τ a, multV ((LT l).PD K) T₁.ρ τ a =
      multV ((LT l).PD K) T₀.ρ τ a + multV ((LT l).PD K) T₂.ρ τ a

def CrystallineRestrictionToExtension (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K K' : FinExt l) (hKK : K'.1 ≤ K.1) (hle : GK K ≤ GK K')
    (LL : FinExt l) (T : LocLat ↥(GK K') ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((LT l).PD K') T.ρ →
    IsCrys ((LT l).PD K) (Formalism.MainNotions.LiftingTheory.resLoc (Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _) T).ρ ∧
    ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ),
      multV ((LT l).PD K) (Formalism.MainNotions.LiftingTheory.resLoc (Subgroup.inclusion hle)
        (continuous_subtype_val.subtype_mk _) T).ρ τ a =
      multV ((LT l).PD K') T.ρ (τ.comp (IntermediateField.inclusion hKK)) a

section Herr

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def IsUnitGen (W : LocWach PD LL O v n) (e : W.DD W.one) : Prop :=
  W.N W.one = Submodule.span (LetA O n) {e} ∧ W.φD W.one e = e ∧ ∀ g, W.γD W.one g e = e

def coreHerrExt (W : LocWach PD LL O v n) : Prop :=
  ∀ (T Tp : LocLat G Qp LL O) (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L),
    IsCrys PD T.ρ → IsCrys PD Tp.ρ →
    ∀ (c : G → T.V) (hc : c ∈ latticeCocycles T.L), Formalism.MainNotions.LiftingTheory.IsExtOf W ι π c →
    ∀ e : W.DD W.one, IsUnitGen W e →
    ∃ u : Oˣ, ∀ (x : W.DD Tp) (a : O), W.map π x = a • e →
      ∀ (y z : W.DD T) (h : (y, z) ∈ W.divisibleCocycles T),
        W.map ι y = W.φD Tp x - x → W.map ι z = W.γ Tp x - x →
        W.cl T ⟨(y, z), h⟩ = ((u : O) * a) •
          Formalism.MainNotions.DeltaInvariantLattices.res W.GKs T (Submodule.Quotient.mk (⟨c, hc⟩ : ↥(latticeCocycles T.L)) : LatticeCohomology T.L)

def coreHerrExtΔ (W : LocWach PD LL O v n) : Prop :=
  W.s = 1 → PD.p ≠ 2 →
  ∀ (T Tp : LocLat G Qp LL O) (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L),
    IsCrys PD T.ρ → IsCrys PD Tp.ρ →
    ∀ (c : G → T.V) (hc : c ∈ latticeCocycles T.L), Formalism.MainNotions.LiftingTheory.IsExtOf W ι π c →
    ∀ e : W.DD W.one, IsUnitGen W e →
    ∃ u : Oˣ, ∀ (x : W.DD Tp) (a : O), (∀ δ ∈ W.DelF, W.γD Tp δ x = x) → W.map π x = a • e →
      ∀ (y z : W.DD T) (h : (y, z) ∈ W.wachCocyclesDelta T),
        W.map ι y = W.φD Tp x - x → W.map ι z = W.γD Tp W.gamK x - x →
        W.clK T ⟨(y, z), h⟩ = ((u : O) * a) •
          (Submodule.Quotient.mk (⟨c, hc⟩ : ↥(latticeCocycles T.L)) : LatticeCohomology T.L)

end Herr

def HerrClassNaturalExtension (LT : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (HW : HWOf LT) (F : FonOf LT A HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    ((HW l).W K s LL h).ClNat ∧ Formalism.MainNotions.DeltaInvariantLattices.ClKNatG ((HW l).W K s LL h) ∧
      coreHerrExt ((HW l).W K s LL h) ∧ coreHerrExtΔ ((HW l).W K s LL h)

def adm1 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.deltaInvariantLatticeGlobal D HW F Cm

def adm2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.prop2 D HW F

def adm2b (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.adm20 D HW F

def adm2c (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.adm17 D HW F

def HerrClassMapsLocal (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := HerrClassNaturalExtension D.loc D.locA HW F

def adm3 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.lem3 D HW F

def ArchimedeanSignatureMatching (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CA CB CK : ℝ) : Prop := Formalism.MainNotions.LiftingTheory.LiftTheoremAllCases D HW F CA CB CK

def adm5 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.ConclusionW D HW F

def adm6 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.ConclusionL D HW F

def adm7 (D : D7) : Prop := H1fGeneratorBoundAll D.loc

def adm8 (D : D7) : Prop := FontaineRegularity D.loc

def adm11 (D : D7) : Prop := FontaineStrictExact D.loc

def adm12 (D : D7) : Prop := CrystallineRestrictionToExtension D.loc

def Adm1 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ) : Prop :=
  adm1 D HW F Cm ∧ adm2 D HW F ∧ adm2b D HW F ∧ adm2c D HW F ∧ HerrClassMapsLocal D HW F ∧ adm3 D HW F ∧ ArchimedeanSignatureMatching D HW F CA CB CK ∧ adm5 D HW F ∧ adm6 D HW F ∧
    adm7 D ∧ adm8 D ∧ adm11 D ∧ adm12 D

def IntegralityFromMetric (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK C : ℝ) : Prop := Adm1 D HW F Cm CA CB CK → Conclusion1 D C

def AbsoluteConstantFirstBound : Prop := ∀ CA CB CK : ℝ, ∃ C : ℝ, ∀ D : D7, ∀ HW : HWOf D.loc, ∀ F : FonOf D.loc D.locA HW, ∀ Cm : CmpOf D.loc D.locA HW F, IntegralityFromMetric D HW F Cm CA CB CK C

def qlExt (l : ℕ) [Fact l.Prime] : FinExt l := ⟨⊥, inferInstance⟩

def orbLen {G LL : Type} [Group G] [Field LL] (I : Subgroup G) (Fr : G) (χ : I →* LLˣ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ ∀ g h : I, (h : G) = (Fr ^ k)⁻¹ * g * Fr ^ k → χ h = χ g}

def rPrime {G LL : Type} [Group G] [Field LL] (I : Subgroup G) (Fr : G) (Sig : Finset (I →* LLˣ)) :
    ℕ :=
  (Sig ×ˢ Sig).sup fun p => orbLen I Fr (p.1 * p.2⁻¹)

section PartII

variable {l : ℕ} [Fact l.Prime]

def thmT {K₀' K' B BdR : Type} [Field K₀'] [Field K'] [Algebra ℚ_[l] K₀'] [Algebra ℚ_[l] K']
    [Algebra K₀' K'] [IsScalarTower ℚ_[l] K₀' K'] [CommRing B] [CommRing BdR] [Algebra ℚ_[l] B]
    [Algebra ↥(K0 (qlExt l)) B] [IsScalarTower ℚ_[l] ↥(K0 (qlExt l)) B] [Algebra K₀' B]
    [IsScalarTower ℚ_[l] K₀' B] [Algebra ℚ_[l] BdR] [Algebra ↥(K0 (qlExt l)) BdR]
    [Algebra ↥(qlExt l).1 BdR] [IsScalarTower ℚ_[l] ↥(qlExt l).1 BdR]
    [IsScalarTower ↥(K0 (qlExt l)) ↥(qlExt l).1 BdR] [IsScalarTower ℚ_[l] ↥(K0 (qlExt l)) BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower ℚ_[l] K' BdR] [IsScalarTower K₀' K' BdR]
    [IsScalarTower ℚ_[l] K₀' BdR]
    (PC : PotCrysData ↥(GK (qlExt l)) ℚ_[l] ↥(K0 (qlExt l)) ↥(qlExt l).1 K₀' K' B BdR)
    (LL : FinExt l) (C : ℕ) : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK (qlExt l)) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (N η H : ℕ)
    (U : Finset ℤ) (Sig : Finset (PC.Iner →* (↥LL.1)ˣ)) (Fr : ↥(GK (qlExt l))),
    PC.IsPotCrys T₁.ρ → PC.IsPotCrys T₂.ρ → F.Onto →
    PC.IsFrob Fr → FrobStable PC.Iner Fr Sig → 1 ∈ Sig → Sig.card ≤ N → 2 ≤ N →
    PC.InertiaThrough T₁.ρ Sig → PC.InertiaThrough T₂.ρ Sig →
    (∀ u ∈ U, -(η : ℤ) ≤ u ∧ u ≤ H) → (0 : ℤ) ∈ U → U.card ≤ N + 1 → 1 ≤ η → η < H →
    (∀ τ, JumpsInV PC.PD T₁.ρ τ (U : Set ℤ)) → (∀ τ, JumpsInV PC.PD T₂.ρ τ (U : Set ℤ)) →
    C * (H * N ^ 2 + N ^ 3) < l →
    4 * rPrime PC.Iner Fr Sig ≤ N ^ 2 ∧
      F.LiftF PC.PD (C * (N * rPrime PC.Iner Fr Sig + η * (N + rPrime PC.Iner Fr Sig)))

end PartII

def CorollaryALocal (LT : LocTheory) (C : ℕ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K' : FinExt l) (h : (qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal)
    (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (qlExt l))) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((LT l).PD (qlExt l)).actB g (algebraMap ↥(K0 K') (LT l).R.B c) =
        algebraMap ↥(K0 K') (LT l).R.B c')
    (LL : FinExt l), thmT (pc (LT l) h hN hF hS) LL C

def Conclusion2 (D : D7) (C : ℕ) : Prop := CorollaryALocal D.loc C

def CrysDRIntersectionQl (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (b : (LT l).R.B), ((LT l).PD K).φ b = b →
    ((LT l).PD K).ι b ∈ ((LT l).PD K).Fil 0 → ∃ c : ℚ_[l], algebraMap ℚ_[l] (LT l).R.B c = b

def adm10 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.adm20 D HW F

def adm13 (D : D7) : Prop := Formalism.MainNotions.LocalSituation.Conclusion5 D

def ArtinSchreierWittOnto : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (x : WCb l), ∃ y : WCb l, frobW l y - y = x

def Adm2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := adm10 D HW F ∧ adm13 D ∧ adm8 D ∧ adm11 D ∧ adm12 D ∧ ArtinSchreierWittOnto

def HodgeTateFromSandwich (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℕ) : Prop := Adm2 D HW F → Conclusion2 D C

def AbsoluteConstantSecondPart : Prop := ∃ C₀ : ℕ, ∀ C : ℕ, C₀ ≤ C → ∀ D : D7, ∀ HW : HWOf D.loc, ∀ F : FonOf D.loc D.locA HW, HodgeTateFromSandwich D HW F C

end Formalism.MainNotions.ElementDenominator
