import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.OneSquareClosed

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.PairingDivisionLocalBalance (wt HtLe)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL IsValChar beta)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair)

namespace GlobalTheory.SqTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev GP := ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}, GridData Lc sc → T → ℝ → ℝ → ℝ → Prop

structure Rec {D : D7} (large₂ : SizeData₂ D) : Prop where

  size : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂

  host : HostHyp D

  hF : D.host.F = maximalRealSubfield D.host.E

  dlog : |large₂.logDerivativeAtOne| ≤ large₂.sc.x ^ large₂.sc.eps

def GBig (Q : GP) : Prop :=
  ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ C0 x₀ : ℝ, ∀ C, C0 ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → Rec large₂ →
    ∀ (T : Type) (Lc : LevCh D T) (μ₀ : T), Lc.Is μ₀ → ∀ G : GridData Lc ⟨1, CF, large₂.sc.b⟩, Q G μ₀ C large₂.sc.x large₂.sc.b

section Objects

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc)

def bTH (D : D7) (C x b : ℝ) : ℝ := C * D.R.f * b * (Real.log b + Real.log x)

def fam (μ₀ : T) (i j : Fin D.R.m) : Option Bool → HChar D.host.E
  | none => nuH G μ₀ i j
  | some c => nuH G μ₀ i j * delOf Lc c

open Classical in

def twPl (t : T) : Finset (HeightOneSpectrum (𝓞 D.host.E)) := (locPl G t).filter fun w => w ∉ G.pl.W0

def Qn (t : T) : ℕ := ∏ w ∈ twPl G t, Ideal.absNorm w.asIdeal

def modT (t : T) : Ideal (𝓞 D.host.E) := SqNum.condE G.pl * ∏ w ∈ twPl G t, w.asIdeal

def e0 (D : D7) (i j : ℕ) : ℕ := (botBig D i j - botSmall D i j) / 2

def h0 (D : D7) (i j : ℕ) : ℕ := (botBig D i j + botSmall D i j) / 2

def pp (D : D7) (j : ℕ) : ℕ := (D.R.m - (j + 1)) / 2

def qq (D : D7) (j : ℕ) : ℕ := (D.R.m - j) / 2

def eTop (D : D7) (i j : ℕ) : ℕ := (rankV D (i + 1) (j + 1) - rankV D i j) / 2

def ThA (μ₀ : T) (μ : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL → T) : Prop :=
  ∀ w, μ w ≠ μ₀ → (Qn G (μ w) : 𝓞 D.what₂.LL) ∉ w.asIdeal ∧ ∀ l : ℕ, l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal →
    ∀ (i j : Fin D.R.m) (s : ℕ) (Λ Λd : ℂ → ℂ) (z : D.what₂.LL), 1 ≤ s → s ≤ halfRank D i j → IsHeckeL (nuH G (μ w) i j) Λ →
      IsHeckeL (nuH G μ₀ i j * Lc.C.delAt l) Λd → D.what₂.embLL z * Λd s = Λ s →
        (vw w z : ℝ) ≤ (vw w (l : D.what₂.LL) : ℝ) / (l : ℝ) ^ 2

end Objects

def FieldDat : Prop := GBig fun {D} _ _ _ G _ _ _ _ =>
  ∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (condF G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ

def LNe : Prop := GBig fun {D} _ _ _ G μ₀ _ _ _ => ∀ i j : Fin D.R.m,
  (∀ t, ∃ Λ, IsHeckeL (nuH G t i j) Λ ∧ ∀ s : ℤ, 1 - (e0 D i j : ℤ) ≤ s → s ≤ halfRank D i j → Λ s ≠ 0) ∧
    ∀ c, ∃ Λ, IsHeckeL (fam G μ₀ i j c) Λ ∧ ∀ s : ℕ, 1 ≤ s → Λ s ≠ 0

def TorEx : Prop := GBig fun {D} _ _ {sc} G μ₀ _ _ _ => ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j → ∀ c,
  ∃ x, IsTor G i j s (fam G μ₀ i j c) x ∧ x ≠ 0 ∧ (∀ Λ, IsHeckeL (fam G μ₀ i j c) Λ → x = Λ s) ∧
    ∀ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ → IsAlgebraic ℚ (beta D.host.E D.host.d s (kap D sc.cGap i j s) Λ x)

def DenEx : Prop := GBig fun {D} _ _ _ G _ _ _ _ => ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
  ∃ n, IsDenom G i j s n ∧ {l | l.Prime ∧ n l ≠ 0}.Finite

def DenSum : Prop := GBig fun {D} _ _ _ G _ C x b => ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
  ∀ n, IsDenom G i j s n → ∀ S : Finset ℕ, (∀ l ∈ S, l.Prime) → (∀ l ∈ S, 0 ≤ n l) ∧ ∑ l ∈ S, n l * Real.log l ≤ bTH D C x b

def LBound : Prop := GBig fun {D} _ _ {sc} G _ C x b => ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
  ∀ (π : Equiv.Perm D.what₂.Tau) (χ : HChar D.host.E) (Λ : ℂ → ℂ),
    IsValChar (cmPhi D) s (kap D sc.cGap i j s ∘ π) (condF G.pl) ∅ χ → IsHeckeL χ Λ → Real.log ‖Λ s‖ ≤ bTH D C x b

def BetaArch : Prop := GBig fun {D} _ _ {sc} G μ₀ C x b => ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
  ∀ c y Λ, IsTor G i j s (fam G μ₀ i j c) y → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ →
    Real.log |(((minpoly ℚ (beta D.host.E D.host.d s (kap D sc.cGap i j s) Λ y)).coeff 0 : ℚ) : ℝ)| ≤
      (minpoly ℚ (beta D.host.E D.host.d s (kap D sc.cGap i j s) Λ y)).natDegree * (12 * bTH D C x b)

def ThbSt : Prop := GBig fun {D} _ _ _ G μ₀ C x b => ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
  ∀ zd g, IsTorVal G μ₀ i j s zd g → HtLe g (1 : D.what₂.LL) (bTH D C x b) ∧ ∀ c, zd c ≠ 0 ∧ HtLe g (zd c) (bTH D C x b)

def BotEx : Prop := GBig fun {D} _ _ _ G μ₀ _ _ _ => ∃ δ t0 : ℂ, ∀ ij : Fin D.R.m × Fin D.R.m,
  ∃ P P' : Pair D ⊤ δ t0 (levQ G.pl), IsBottom G μ₀ ij.1 ij.2 (SqNum.condE G.pl) P P'

def BotExT : Prop := GBig fun {D} _ _ _ G _ _ _ _ => ∀ (δ t0 : ℂ) (Q : ℕ) (_ : Pair D ⊤ δ t0 Q) (t) (i j : Fin D.R.m),
  ∃ P P' : Pair D ⊤ δ t0 (levQ G.pl * Qn G t), IsBottom G t i j (modT G t) P P'

def BotSmall : Prop := GBig fun {D} _ _ {sc} G μ₀ _ _ _ => GlobalTheory.NormSum.GoodLevel D (levQ G.pl) ∧ twPl G μ₀ = ∅ ∧
  ∀ (δ t0 : ℂ) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q) t (i j : Fin D.R.m) 𝔪, IsBottom G t i j 𝔪 P P' →
    P.Small (bigN D) (maxWt D sc.cGap) ∧ P'.Small (bigN D) (maxWt D sc.cGap)

def NormBig : Prop := GBig fun {D} _ _ _ G _ _ _ _ => ∀ (δ t0 : ℂ) (i j : Fin D.R.m), ∃ A : ℂ, A ≠ 0 ∧
  ∀ t (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q) (Λ : ℂ → ℂ), IsBottom G t i j (modT G t) P P' → IsHeckeL (nuH G t i j) Λ →
    (P.norm : ℂ) = A * ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ s

def NormSmall : Prop := GBig fun {D} _ _ _ G _ _ _ _ => ∀ (δ t0 : ℂ) (i j : Fin D.R.m), ∃ A : ℂ, A ≠ 0 ∧
  ∀ t (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q) (Λ : ℂ → ℂ), IsBottom G t i j (modT G t) P P' → IsHeckeL (nuH G t i j) Λ →
    (P'.norm : ℂ) = A * ∏ s ∈ Icc (1 + (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ s

def BotNe : Prop := GBig fun {D} _ _ _ G μ₀ _ _ _ => ∀ (δ t0 : ℂ) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q) (i j : Fin D.R.m),
  IsBottom G μ₀ i j (SqNum.condE G.pl) P P' → (∃ h T, P.coord h T ≠ 0) ∧ ∃ h T, P'.coord h T ≠ 0

def TriEx : Prop := GBig fun {D} T _ _ G _ _ _ _ => ∀ W : G.Weil, IsStdChar D W.ψ (-1) → ∀ i j : Fin D.R.m,
  ∃ (A A' WW : HSp D) (X : Tri T A A' WW) (c0 : T → ℂ), IsBottomTri W i j X ∧ X.IsConst W.ψ W.θ c0

def Tower : Prop := GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ) (ρ : RealMatch W),
  IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) (c c₀ : ℂ) (A A' WW : HSp D) (X : Tri T A A' WW)
    (c0 : T → ℂ) (Λ Λ₀ : ℂ → ℂ), SquareNonzero W S.B ρ t i j → IsSquareConst W S.B ρ t i j c → SquareNonzero W S.B ρ μ₀ i j →
    IsSquareConst W S.B ρ μ₀ i j c₀ → IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 → IsHeckeL (nuH G t i j) Λ →
    IsHeckeL (nuH G μ₀ i j) Λ₀ → ∃ u : Fin (pp D j + qq D j) → ℂ,
      (∀ k, GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (u k) 1) ∧
      ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧
        c / c₀ * ∏ k ∈ range (qq D j), Λ (eTop D i j + k + 1 : ℕ) / Λ₀ (eTop D i j + k + 1 : ℕ) =
          D.what₂.embLL ζ * (∏ k, u k) * (c0 t / c0 μ₀) *
            ∏ k ∈ range (pp D j), Λ (eTop D i j + qq D j - k : ℕ) / Λ₀ (eTop D i j + qq D j - k : ℕ)

def BotConst : Prop := GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ),
  IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) (A A' WW : HSp D) (X : Tri T A A' WW)
    (c0 : T → ℂ) (δ t0 : ℂ) (P₀ P₀' : Pair D ⊤ δ t0 (levQ G.pl)) (P P' : Pair D ⊤ δ t0 (levQ G.pl * Qn G t)) (z z' : D.what₂.LL)
    (C' : ℝ) (dl : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL → ℝ), IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 →
    IsBottom G μ₀ i j (SqNum.condE G.pl) P₀ P₀' → IsBottom G t i j (modT G t) P P' → D.what₂.embLL z = (P.norm : ℂ) →
    D.what₂.embLL z' = (P₀'.norm : ℂ) → z ≠ 0 → z' ≠ 0 → IsIntExp G C' dl →
    ∃ γ : D.what₂.LL, γ ≠ 0 ∧ c0 μ₀ ≠ 0 ∧ D.what₂.embLL γ * c0 μ₀ = c0 t ∧ ∀ w : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL,
      (Qn G t : 𝓞 D.what₂.LL) ∉ w.asIdeal → (vw w γ : ℝ) ≤ vw w z + vw w z' + 6 * dl w

def Refl : Prop := GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ →
  ∀ (i j : Fin D.R.m) (t : T) (Λ Λ₀ : ℂ → ℂ), IsHeckeL (nuH G t i j) Λ → IsHeckeL (nuH G μ₀ i j) Λ₀ →
    ∀ s : ℤ, 1 - (e0 D i j : ℤ) ≤ s → s ≤ 0 → ∃ Ep : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) Ep ∧
      Λ s * Λ₀ ((1 - s : ℤ) : ℂ) = D.what₂.embLL Ep * (Λ ((1 - s : ℤ) : ℂ) * Λ₀ s)

def RhoLow : Prop := GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
  ∀ (t : T) (Λ Λ₀ : ℂ → ℂ) (z : D.what₂.LL) zd g n, IsHeckeL (nuH G t i j) Λ → IsHeckeL (nuH G μ₀ i j) Λ₀ →
    D.what₂.embLL z * Λ₀ s = Λ s → IsTorVal G μ₀ i j s zd g → IsDenom G i j s n →
    ∀ (w : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → (Qn G t : 𝓞 D.what₂.LL) ∉ w.asIdeal →
      -(n l * (vw w (l : D.what₂.LL) : ℝ)) ≤ ((vw w z + g w : ℤ) : ℝ)

def OneSqSt : Prop := GBig fun {D} _ _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ) (ρ : RealMatch W),
  IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (C' : ℝ) μ rq zA zA' zT zTd gT ch N0 Sd Se dl Bw, ThA G μ₀ μ →
    IsSqOf W S.B ρ C' μ₀ μ rq zA zA' zT zTd gT ch N0 Sd Se dl Bw → ∀ w ij, rq (μ w) ij ≠ 0 ∧
      (vw w (rq (μ w) ij) : ℝ) ≤ |(vw w (zA ij) : ℝ)| + |(vw w (zA' ij) : ℝ)| +
        4 * (∑ s ∈ Icc (1 : ℤ) (halfRank D ij.1 ij.2), (|((vw w (zT ij s) + gT ij s w : ℤ) : ℝ)| +
          |((vw w (zTd ij (ch w) s) + gT ij s w : ℤ) : ℝ)|)) +
        5 * (∑ s ∈ Icc (1 : ℤ) (halfRank D ij.1 ij.2), wt Sd (N0 ij s) w) +
        (2 * halfRank D ij.1 ij.2 : ℕ) * wt Se (fun l => 1 / (l : ℝ) ^ 2) w + 6 * dl w +
        (D.R.m - 1 - ij.2 : ℕ) * (2 * ∑ q ∈ G.pl.S0, (condExp G.pl q : ℝ) * (vw w (Ideal.absNorm q.asIdeal : D.what₂.LL) : ℝ))

end GlobalTheory.SqTop

end
