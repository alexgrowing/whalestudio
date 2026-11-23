import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
import Formalism.HermitianLattices.StatementMass

noncomputable section

open ValuativeRel NumberField MeasureTheory
open scoped ENNReal

namespace Formalism.MainNotions.NonGenericAndKTwoTheorems

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NonGenericLocalBound (k r : ℕ) (C : ℝ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V),
      Module.finrank E V = k + 2 * r + 1 →
      ∀ P : LocNG.FPair H r, P.RelG (LocNG.theta M) → LocNG.NGAt k P C

def Conclusion1 (D : D7) (C : ℝ) : Prop := 4 * D.R.rS + 7 ≤ D.R.k → NonGenericLocalBound D.R.k D.R.rS C

section Hyps

variable (D : D7) (large₂ : SizeData₂ D)

def KTwoParameterConditions (Cl Cg CT : ℝ) : Prop :=
  Cl * (D.R.m : ℝ) ^ 6 * large₂.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k ∧
  (∀ i : Fin 2, ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (D.host.g i : ℝ) ∧ (D.host.g i : ℝ) ≤ large₂.sc.b ^ Cg) ∧
  (∀ (τ : D.what₂.Tau) (a c : Fin D.R.r), a ≠ c →
    Cl * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 < |lamS D.R (D.hc τ) a - lamS D.R (D.hc τ) c|) ∧
  Cl * Real.log D.host.rdE ≤ large₂.sc.L ∧
  Real.log (D.R.f : ℝ) ≤ (D.R.rS : ℝ) ^ 2 ∧
  (∀ u : D.what₂.Word, ((D.mem u).A.T : ℝ) ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ)) ∧
    Nat.Coprime (D.mem u).A.T (D.host.g 0 * D.host.g 1)) ∧
  Formalism.HermitianLatticesTheory.IsCMUnram D.host.E

def KTwoHypotheses (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ KTwoParameterConditions D large₂ Cl Cg CT

def TermsPP (u u' : D.what₂.Word) : Set (D.s.Term u u') := {t | D.s.Gterm t = 0 ∧ ¬ D.s.isId t}

def Kpp (u u' : D.what₂.Word) : D.s.Cu u' →L[ℂ] D.s.Cu u := KOf D.s u u' {t | D.s.Gterm t = 0 ∧ ¬ D.s.isId t}

def Conclusion2 (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ u : D.what₂.Word,
    Summable (fun t : TermsPP D u u => D.s.aTerm u u t.1) ∧
    hsNormSq (Kpp D u u) ≤ (D.duS u : ℝ) * Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k))

def PointsLemma (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ u u' : D.what₂.Word, u ≠ u' →
    ∀ t : D.s.Term u u', D.s.Gterm t = 0 → D.s.aTerm u u' t = 0

end Hyps

section Terms

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D)

def adm1 (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop := Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ (u u' : D.what₂.Word) (Φ : Set (D.s.Term u u')),
  IsSat D Φ → Summable (fun p : pairsIn D.s Φ => ‖D.s.pval p.1‖) →
    hsNormSq (KOf D.s u u' Φ) ≤
      (∏ i : Fin 2, (1 + 3 / (D.host.g i : ℝ))) ^ D.R.f * gaG D * (∑' p : pairsIn D.s Φ, D.s.pval p.1).re

def adm2 (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop := Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ u u' : D.what₂.Word, KExpansion D.s u u' ∧ KAbsConv D.s u u'

def adm3 (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop := Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  (∀ (u : D.what₂.Word) (t : D.s.Term u u),
    ((∀ j, Xflag (X.fl' t) j = Xflag (X.fl t) j) ∧ Xplus (X.fl' t) = Xplus (X.fl t)) → D.s.relevant t → D.s.isId t) ∧
  ∀ u : D.what₂.Word, IdCellDiag D.s u

def ArchimedeanSignatureMatching (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop := Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), ¬ D.s.relevant t → D.s.aTerm u u' t = 0

def adm5 (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop := Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), D.s.Gterm t ≠ 0 →
    Dl (X.fl t).fl (X.fl' t).fl (D.R.rS + 1) ≠ 0 ∧
    (Dl (X.fl t).fl (X.fl' t).fl D.R.rS ≠ 0 → ∀ τ, 0 < (embS D τ (Gval (X.fl t) (X.fl' t))).re)

def adm6 (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop := Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), D.s.relevant t →
    ∀ (j : ℕ) (hj : j ≤ D.R.rS + 1), Dl (X.fl t).fl (X.fl' t).fl j ≠ 0 →
      ∃ p : Point D.host.E j,
        IsInCell ((ZhatOM (ZhatL (X.fl t) (X.fl' t))).submatrix (Fin.castLE hj) (Fin.castLE hj)) p

end Terms

def adm7 : Prop :=
  ∀ (k : ℕ) (u u' : Fin k → ℝ) (H H' : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (ρ : Matrix (Fin k) (Fin k) ℂ → (H' →L[ℂ] H')),
    IsHCTypeU k u π → IsHCTypeU k u' ρ → u ≠ u' →
    ∀ P : H' →L[ℂ] H, (∀ h ∈ UJset (allPos k), P.comp (ρ h) = (π h).comp P) → P = 0

section Size

variable (D : D7) (large₂ : SizeData₂ D)

def hNC (τ : D.what₂.Tau) : ℝ :=
  sInf {x | ∃ a b, epsSH D.R a ≠ epsSH D.R b ∧ x = |lamD D τ a - lamD D τ b|}

def CloudNodeShape (τ : D.what₂.Tau) (Cq bv : ℝ) : Prop :=
  Cq * (D.R.r : ℝ) ^ 7 ≤ bv ∧
  (∀ l, 1 ≤ l → l ≤ D.R.k - 1 → 0 ≤ vOne D τ l ∧ vOne D τ l ≤ bv / 8) ∧
  ∀ j, 1 ≤ j → j ≤ D.R.m → bv ≤ bOne D τ j ∧ bOne D τ j ≤ 2 * bv

def q0 (τ : D.what₂.Tau) (cq Cq : ℝ) : ℝ :=
  min (cq * hNC D τ * (D.R.m : ℝ) ^ (-(1 / 2 : ℝ))) (4 * (D.s.Del : ℝ)) / Cq

def adm8 (C' Cl Cg cb Cu cT CT C0 Cθ C1 cq Cq CH : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ (τ : D.what₂.Tau) (u : D.what₂.Word) (bv : ℝ), CloudNodeShape D τ Cq bv →
  ∀ θ, normWin D large₂ Cθ θ → ∀ W, GoodW D τ u u θ W → ∀ A : LocS W, GoodS D (lamD D τ) A →
    IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) A.σ A.v0 →
    ∀ q : ℕ, (q : ℝ) ≤ C1 * D.R.k * D.R.rS → (D.R.m : ℝ) * q ≤ q0 D τ cq Cq →
      (D.R.m : ℝ) * q ≤ bv / (Cq * (D.R.r : ℝ) ^ 4) →
    ∀ la : ℝ, 0 < la →
      ∫⁻ x, Set.indicator {x | ∃ a : Fin (D.R.rS + 1), la * large₂.sc.b ^ (CH * (D.R.m : ℝ)) ≤
              max (lA D.R.k D.R.rS W.z (Matrix.of x) a) (lA D.R.k D.R.rS W.z (Matrix.of x) a)⁻¹}
            (fun x => (‖A.Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2) x ∂W.νS ≤
        ENNReal.ofReal (2 * (D.R.m : ℝ) * la ^ (-(2 * (q : ℝ)))) * l2SG W.νS A.Φ

end Size

section Mass

def IntegrationByPartsAlt (D : D7) : Prop :=
  ∀ (j : ℕ), 3 ≤ j →
    ∀ (V V' : Type) [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
      [IsScalarTower (𝓞 D.host.E) D.host.E V] [AddCommGroup V'] [Module D.host.E V']
      [Module (𝓞 D.host.E) V'] [IsScalarTower (𝓞 D.host.E) D.host.E V']
      (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E) (h' : V' →ₗ⋆[D.host.E] V' →ₗ[D.host.E] D.host.E)
      (L : Submodule (𝓞 D.host.E) V) (L' : Submodule (𝓞 D.host.E) V'),
      h.IsSymm → h'.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h L j → Formalism.HermitianLatticesTheory.IsOrthoLattice h' L' (j - 1) →
      Formalism.HermitianLatticesTheory.mass h L / Formalism.HermitianLatticesTheory.mass h' L' = Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E j

def LogThetaIdentity (D : D7) : Prop :=
  ∀ i : ℕ, 2 ≤ i →
    |Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E i)| ≤ (D.R.f : ℝ) * Real.log (riemannZeta (i : ℂ)).re

def RankTwoMassHypothesis (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 C : ℝ) : Prop :=
  KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ (V : Type) [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
    [IsScalarTower (𝓞 D.host.E) D.host.E V]
    (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E) (L : Submodule (𝓞 D.host.E) V),
    h.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h L 2 →
      Formalism.HermitianLatticesTheory.mass h L ≤ (large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ C

def MassPairedLatticeBound (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 C : ℝ) : Prop :=
  (∀ (V V' : Type) [AddCommGroup V] [Module D.host.E V] [FiniteDimensional D.host.E V] [Module (𝓞 D.host.E) V]
      [IsScalarTower (𝓞 D.host.E) D.host.E V] [AddCommGroup V'] [Module D.host.E V'] [Module (𝓞 D.host.E) V']
      [IsScalarTower (𝓞 D.host.E) D.host.E V']
      (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E) (h' : V' →ₗ⋆[D.host.E] V' →ₗ[D.host.E] D.host.E)
      (M : Submodule (𝓞 D.host.E) V) (L' : Submodule (𝓞 D.host.E) V'),
      h.IsSymm → IsPosDef h → Module.finrank D.host.E V = 1 → Submodule.IsLattice D.host.E M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
      h'.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h' L' 1 →
        Formalism.HermitianLatticesTheory.mass h M = Formalism.HermitianLatticesTheory.mass h' L') ∧
  (KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0 →
    ∀ (V' : Type) [AddCommGroup V'] [Module D.host.E V'] [Module (𝓞 D.host.E) V'] [IsScalarTower (𝓞 D.host.E) D.host.E V']
      (h' : V' →ₗ⋆[D.host.E] V' →ₗ[D.host.E] D.host.E) (L' : Submodule (𝓞 D.host.E) V'),
      h'.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h' L' 1 →
        Formalism.HermitianLatticesTheory.mass h' L' ≤ (large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ C)

def DefiniteComplementMassVolumes (D : D7) (Gv : GaugeVol D) : Prop :=
  ∀ (j : ℕ) (Y U : Submodule D.host.E (hS D).V), 2 ≤ j → Module.finrank D.host.E Y = j → U ≤ Wb D →
    Y = Wb D ⊓ orth (hS D) U → (∀ τ : D.host.E →+* ℂ, ∀ y ∈ Y, y ≠ 0 → 0 < nrm (hS D) τ y) →
    Gv.vol Y = Gv.volUni j

end Mass

section L3

variable (D : D7)

def PlaneWaveLetters : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module D.host.E V] [FiniteDimensional D.host.E V]
    [Module (𝓞 D.host.E) V] [IsScalarTower (𝓞 D.host.E) D.host.E V]
    (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E), h.IsSymm → IsPosDef h →
    ∀ M : Submodule (𝓞 D.host.E) V, Submodule.IsLattice D.host.E M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ de : ℕ, latDetH h M = de → ∀ e : ℕ, DiscGen h M e →
      Formalism.HermitianLatticesTheory.mass h M * levelIdx h M de =
        massU D.host.E (finrank D.host.E V) * (de : ℝ) ^ (finrank D.host.E V) *
          ∏ᶠ p : PrimesOver D.host.F de,
            thP (finrank D.host.E V) (eP h M p.1) (eta₃ D.host.F D.host.E p.1) (Ideal.absNorm p.1) ∧
      (∀ p : Ideal (𝓞 D.host.F), p.IsMaximal →
        thP (finrank D.host.E V) (eP h M p) (eta₃ D.host.F D.host.E p) (Ideal.absNorm p) ≤ (2 : ℝ) ^ e) ∧
      Formalism.HermitianLatticesTheory.mass h M ≤ massU D.host.E (finrank D.host.E V) * (de : ℝ) ^ (finrank D.host.E V) *
        (2 : ℝ) ^ (e * omegaF D.host.F de)

def PlaneWaveIsometry : Prop :=
  ∀ u : D.what₂.Word, (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ s : Finset (LatV D), IsRowReps D F0 s →
    massRows D F0 s = massS D D.R.k * ((Tu D u : ℝ) ^ D.R.k - 1) ^ D.R.f ∧
    ∀ Λ : LatV D, IsRowLat D F0 Λ →
      Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ (lf D F0)) = massRows D F0 s / ((Tu D u : ℝ) - 1) ^ D.R.f ∧
      massS D D.R.k * NT D u ^ (D.R.k - 1) ≤ Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ (lf D F0))

end L3

def minkM (N : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (N + 2)).filter Nat.Prime, p ^ (∑ j ∈ Finset.range (N + 1), N / (p ^ j * (p - 1)))

def adm11 : Prop :=
  ∀ (N : ℕ) (G : Subgroup (GL (Fin N) ℤ)), Finite G → Nat.card G ∣ minkM N

section Packet

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (Gv : GaugeVol D)

def admitted (C' Cl Cg cb Cu cT CT C0 Cθ C1 cq Cq CH CM : ℝ) : Prop :=
  adm1 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ adm2 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ adm3 D large₂ X C' Cl Cg cb Cu cT CT C0 ∧
    ArchimedeanSignatureMatching D large₂ C' Cl Cg cb Cu cT CT C0 ∧ adm5 D large₂ X C' Cl Cg cb Cu cT CT C0 ∧ adm6 D large₂ X C' Cl Cg cb Cu cT CT C0 ∧ adm7 ∧
    adm8 D large₂ C' Cl Cg cb Cu cT CT C0 Cθ C1 cq Cq CH ∧
    IntegrationByPartsAlt D ∧ LogThetaIdentity D ∧ RankTwoMassHypothesis D large₂ C' Cl Cg cb Cu cT CT C0 CM ∧ DefiniteComplementMassVolumes D Gv ∧
    PlaneWaveLetters D ∧ PlaneWaveIsometry D ∧ adm11 ∧ MassPairedLatticeBound D large₂ C' Cl Cg cb Cu cT CT C0 CM

def NonGenericLocalBoundOfLargeRank (CN : ℝ) : Prop := Conclusion1 D CN

def NonIdentityTermSummabilityOfAdmissible (C' Cl Cg cb Cu cT CT C0 Cθ C1 cq Cq CH CM : ℝ) : Prop :=
  admitted D large₂ X Gv C' Cl Cg cb Cu cT CT C0 Cθ C1 cq Cq CH CM →
    Conclusion2 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ PointsLemma D large₂ C' Cl Cg cb Cu cT CT C0

def Stmt (CN C' Cl Cg cb Cu cT CT C0 Cθ C1 cq Cq CH CM : ℝ) : Prop :=
  NonGenericLocalBoundOfLargeRank D CN ∧ NonIdentityTermSummabilityOfAdmissible D large₂ X Gv C' Cl Cg cb Cu cT CT C0 Cθ C1 cq Cq CH CM

end Packet

section Family

variable {eps : ℝ} (Fm : FamP eps) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Gv : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, GaugeVol (Fm.D x i))

def Conclusion1Family (CN : ℝ) : Prop := ∀ x (i : Fm.Ix x), Conclusion1 (Fm.D x i) CN

def Conclusion2Family : Prop := ∀ Cg cb Cu cT CT C0 : ℝ,
  OwnEv Fm fun C' Cl x i => Conclusion2 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0

def Conclusion3Family : Prop := ∀ Cg cb Cu cT CT C0 : ℝ,
  OwnEv Fm fun C' Cl x i => PointsLemma (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0

def admF1 : Prop := ∀ Cg cb Cu cT CT C0 : ℝ,
  OwnEv Fm fun C' Cl x i => adm1 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0
def admF2 : Prop := ∀ Cg cb Cu cT CT C0 : ℝ,
  OwnEv Fm fun C' Cl x i => adm2 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0
def admF3 : Prop := ∀ Cg cb Cu cT CT C0 : ℝ,
  OwnEv Fm fun C' Cl x i => ∀ hx : Fm.x1 < x, adm3 (Fm.D x i) (Fm.L x i) (At x hx i) C' Cl Cg cb Cu cT CT C0
def admF4 : Prop := ∀ Cg cb Cu cT CT C0 : ℝ,
  OwnEv Fm fun C' Cl x i => ArchimedeanSignatureMatching (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0
def admF5 : Prop := ∀ Cg cb Cu cT CT C0 : ℝ,
  OwnEv Fm fun C' Cl x i => ∀ hx : Fm.x1 < x, adm5 (Fm.D x i) (Fm.L x i) (At x hx i) C' Cl Cg cb Cu cT CT C0
def admF6 : Prop := ∀ Cg cb Cu cT CT C0 : ℝ,
  OwnEv Fm fun C' Cl x i => ∀ hx : Fm.x1 < x, adm6 (Fm.D x i) (Fm.L x i) (At x hx i) C' Cl Cg cb Cu cT CT C0

def admF8 : Prop := ∀ Cg cb Cu cT CT C0 Cθ : ℝ, ∃ cq Cq CH : ℝ, 0 < cq ∧ 0 < Cq ∧ ∀ C1 : ℝ,
  OwnEv Fm fun C' Cl x i => adm8 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cθ C1 cq Cq CH

def FamilyMassFirstHypothesis : Prop := ∀ x (i : Fm.Ix x), IntegrationByPartsAlt (Fm.D x i)
def FamilyMassSecondHypothesis : Prop := ∀ x (i : Fm.Ix x), LogThetaIdentity (Fm.D x i)

def FamilyRankTwoMassHyp : Prop := ∀ Cg cb Cu cT CT C0 : ℝ, ∃ CM : ℝ,
  OwnEv Fm fun C' Cl x i => RankTwoMassHypothesis (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 CM

def FamilyMassLatticeBound : Prop := ∀ Cg cb Cu cT CT C0 : ℝ, ∃ CM : ℝ,
  OwnEv Fm fun C' Cl x i => MassPairedLatticeBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 CM

def FamilyComplementMassVolumes : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), DefiniteComplementMassVolumes (Fm.D x i) (Gv x hx i)
def FamilyRowsExist : Prop := ∀ x (i : Fm.Ix x), PlaneWaveLetters (Fm.D x i)

def FamilyWeylDimensionVandermondeQuotient : Prop := ∀ x, Fm.x1 < x → ∀ (i : Fm.Ix x), PlaneWaveIsometry (Fm.D x i)

def AdmF : Prop :=
  admF1 Fm ∧ admF2 Fm ∧ admF3 Fm At ∧ admF4 Fm ∧ admF5 Fm At ∧ admF6 Fm At ∧ adm7 ∧ admF8 Fm ∧
    FamilyMassFirstHypothesis Fm ∧ FamilyMassSecondHypothesis Fm ∧ FamilyRankTwoMassHyp Fm ∧ FamilyComplementMassVolumes Fm Gv ∧ FamilyRowsExist Fm ∧ FamilyWeylDimensionVandermondeQuotient Fm ∧ adm11 ∧ FamilyMassLatticeBound Fm

def FamilyNonGenericLocalBound (CN : ℝ) : Prop := Conclusion1Family Fm CN

def FamilyNonIdentityTermSummability : Prop := Conclusion2Family Fm ∧ Conclusion3Family Fm

def FamilyNonIdentityTermSummabilityOfAdmissible : Prop := AdmF Fm At Gv → FamilyNonIdentityTermSummability Fm

def OrbitValuationBound (CN : ℝ) : Prop := Conclusion1Family Fm CN ∧ FamilyNonIdentityTermSummability Fm

def KudlaFamilyStatement (CN : ℝ) : Prop := FamilyNonGenericLocalBound Fm CN ∧ FamilyNonIdentityTermSummabilityOfAdmissible Fm At Gv

end Family

end Formalism.MainNotions.NonGenericAndKTwoTheorems

end
