import Mathlib
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

@[reducible] def recFields (D : D7) : Fields where
  F := D.host.F
  E := D.host.E
  K := D.what₂.LL
  starE := D.host.cmStar
  Tau := D.what₂.Tau
  deTau := Classical.decEq _
  emb τ := D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)

@[reducible] def recPrimes {D : D7} (EX : ErrX D) : Primes (recFields D) where
  cond := D.host.QS * D.host.q * D.host.d
  g := D.host.g
  piG := EX.piG
  Word := D.what₂.Word
  deWord := Classical.decEq _
  T u := (D.mem u).A.T
  piT := EX.piT

def recWts {D : D7} (EX : ErrX D) : Wts (recFields D) (recPrimes EX).Word D.R where
  row τ := RowPar.of (D.hc τ)
  hc := D.hcW
  tops := topsOf D.host D.eTau

def recSeam (D : D7) : Seam D (recFields D) where
  iE := RingEquiv.refl _
  iT := Equiv.refl _
  σ₀ := D.what₂.embLL

def badS (D : D7) : Set ℕ :=
  hostS D.host.q D.host.d (D.host.g 0) (D.host.g 1)
    ((Set.range fun u : D.what₂.Word => (D.mem u).A.T) ∪ (D.host.small : Set ℕ))

theorem T_mem_badS (D : D7) (u : D.what₂.Word) : (D.mem u).A.T ∈ badS D := Or.inr (Or.inl ⟨u, rfl⟩)

theorem small_mem_badS (D : D7) (l : ℕ) (h : l ∈ D.host.small) : l ∈ badS D := Or.inr (Or.inr (Finset.mem_coe.2 h))

theorem g_mem_badS (D : D7) (i : Fin 2) : D.host.g i ∈ badS D := Or.inl (by fin_cases i <;> simp)

abbrev Twist (D : D7) : Type := Tup (recFields D).F (recFields D).E (recFields D).K (badS D)

def recGlob (D : D7) (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) : ChGlob (recFields D) D.R.m where
  σ₀ := D.what₂.embLL
  xi0 := D.host.xi0
  mu0 := mu0

def HostTie {D : D7} (EX : ErrX D) : Prop :=
  D.host.ccK = ⊤ ∧ GL3Theta.InducedCMType D ∧ GL3Theta.HostFieldConditions D ∧ (recFields D).AbelianUnramifiedExtensionConditions ∧ (recPrimes EX).Ok

def CharTie {D : D7} {EX : ErrX D} (Ch : Chars (recFields D) (recPrimes EX) D.R.m)
    (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) (eta : Formalism.L2.Host.HChar D.host.E)
    (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  Ch.Ok ∧ Ch.Tied D.what₂.embLL (fun j τ => (D.hc τ).e j) mu0 eta ∧ Ch.WeilTied D.what₂.embLL D.host.xi0 ∧
    IsSel (recFields D) sel

def AnTie (D : D7) (δ : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) : Prop :=
  TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ ∧ TaylorLogMetric.IsChi D χ ∧ IsDgen D cD

def SizeAt (D : D7) (i : Fin 2) : Prop :=
  2 * D.R.f * D.R.N D.R.m + 1 < D.host.g i ∧
    ∀ u : D.what₂.Word, ∀ j ∈ LiftErrorLocal.lifts D,
      2 * LiftErrorLocal.Dpi D u j + 2 < (D.host.g i : ℝ) ∧ LiftErrorLocal.Dpi D u j + (D.R.N D.R.m : ℝ) < (D.host.g i : ℝ)

def TwistTie {D : D7} (Dx : DivX D) (μ : D.what₂.Tup) (ξ : Twist D) : Prop :=
  ((Dx.Qp μ : Set ℕ) = QprimeN (ξ : Chr (recFields D).F (recFields D).E (recFields D).K)) ∧ (μ = D.what₂.mu0 → ξ = 1)

open Classical in

def JetsRatDeg {X : Fields} (A : Amb X) (a b : ℕ) (Sb : Finset (HeightOneSpectrum (𝓞 X.E))) (M : ℕ) (deg : X.Tau → ℤ) : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b),
    InRange Sb M c N N' x → ∀ e : DVar X.Tau a b →₀ ℕ,
      (∀ τ, ((∑ k ∈ e.support.filter (fun k => k.1 = τ), e k : ℕ) : ℤ) = deg τ) →
      ∃ y : X.K, A.σ₀ y = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sb N N' c x) e

section Ties

variable {D : D7} {EX : ErrX D} (Ch : Chars (recFields D) (recPrimes EX) D.R.m)
  (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))

def FieldTie (A : Amb (recFields D)) (ξ : Twist D) (cst : LocCst (recFields D) (rowSG (recPrimes EX) sel ξ))
    (u : D.what₂.Word) : Prop :=
  ∀ i < D.R.m, JetsRatDeg A (D.R.N i) (D.R.N (i + 1)) (Sall (Pr := recPrimes EX) sel ξ u)
    (cAof sel ξ cst * cBof sel ξ cst u) (fun τ => ∑ a, ((recWts EX).nuW u (i + 1) τ).w a)

def ColTie (u : D.what₂.Word) (eM : (D.div.Nu u).V ≃ₗ[D.what₂.LL] MramV (recWts EX) Ch u) : Prop :=
  ∀ x, x ∈ DV.MramL D u ↔ eM x ∈ Formalism.L2.Col.MramL (recWts EX) Ch u

def RowTie (μ : D.what₂.Tup) (ξ : Twist D)
    (jA : MtildeV (recWts EX) Ch sel ξ (rPsymF Ch) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ) : Prop :=
  (∀ s : Finset (MtildeV (recWts EX) Ch sel ξ (rPsymF Ch)),
      LinearIndependent D.what₂.LL (fun x : s => (x : MtildeV (recWts EX) Ch sel ξ (rPsymF Ch))) →
      LinearIndependent ℂ (fun x : s => jA x)) ∧
    Submodule.span ℂ (Set.range jA) = ⊤ ∧
    (∀ v ∈ (D.what₂.Mtilde μ).gen, v ∈ Set.range jA) ∧
    ∀ x, x ∈ MtildeL (recWts EX) Ch sel ξ (rPsymF Ch) ↔ ∃ c : D.what₂.Amb μ → 𝓞 D.what₂.LL,
      jA x = ∑ v ∈ (D.what₂.Mtilde μ).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v

def PerTie (u : D.what₂.Word) (μ : D.what₂.Tup) (ξ : Twist D)
    (hP : (mtildeGSD (recWts EX) Ch sel ξ (rPsymF Ch)).Ok)
    (col : MfV (recWts EX) Ch u →ₗ[D.what₂.LL] (evGSD (recWts EX) Ch sel ξ (rPsymF Ch) u).EqFun)
    (eM : (D.div.Nu u).V ≃ₗ[D.what₂.LL] MramV (recWts EX) Ch u)
    (jA : MtildeV (recWts EX) Ch sel ξ (rPsymF Ch) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ) : Prop :=
  ∀ φ x, D.what₂.perCol u μ (D.jN u φ) (jA x) =
    D.what₂.embLL (PtilE (recWts EX) Ch sel ξ (rPsymF Ch) hP u (col (eM φ : MfV (recWts EX) Ch u)) x)

def ChainTie (Dx : DivX D) (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) (A : Amb (recFields D))
    (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  ∃ (ξ : Twist D) (cst : LocCst (recFields D) (rowSG (recPrimes EX) sel ξ))
    (I : ChIdx (recFields D) (recPrimes EX) D.R (QE sel (ξ : Chr (recFields D).F (recFields D).E (recFields D).K)))
    (hI : I.Ok Ch sel ξ cst (recGlob D mu0) (D.R.m - 2))
    (b : I.β (D.R.m - 2 + 1)) (hY : YbHyp (R := D.R) sel ξ cst I u (D.R.m - 2) b)
    (hK : KerEquivC (recWts EX) Ch sel ξ cst I A u (D.R.m - 2) b hY (rPsymF Ch))
    (hF : ∀ j, (chF (recWts EX) sel ξ I u j).Ok)
    (hP : (mtildeGSD (recWts EX) Ch sel ξ (rPsymF Ch)).Ok)
    (eM : (D.div.Nu u).V ≃ₗ[D.what₂.LL] MramV (recWts EX) Ch u)
    (jA : MtildeV (recWts EX) Ch sel ξ (rPsymF Ch) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ),
    cst.sharp = true ∧ TwistTie Dx μ ξ ∧ FieldTie sel A ξ cst u ∧ ColTie Ch u eM ∧ RowTie Ch sel μ ξ jA ∧
      PerTie Ch sel u μ ξ hP (colMu (recWts EX) Ch sel ξ cst I A u (D.R.m - 2) b hY (rPsymF Ch) hK hF hI) eM jA

end Ties

def BoundAt {D : D7} (L : SizeData₂ D) (EX : ErrX D) (C1 : ℝ) (i : Fin 2) (w : LiftErrorLocal.Pl D) (u : D.what₂.Word)
    (μ : D.what₂.Tup) : Prop :=
  ∀ φ ∈ DV.MramL D u, ∀ F ∈ (D.what₂.Mtilde μ).carrier, ∃ y : D.what₂.LL,
    D.what₂.embLL y = D.what₂.perCol u μ (D.jN u φ) F ∧
      (y = 0 ∨ -(∑ j ∈ LiftErrorLocal.lifts D, vNN EX i u j w) - C1 * LiftErrorLocal.errC D L ≤ LiftErrorLocal.vG D w y)

def periodBound_at (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D)
    (Ch : Chars (recFields D) (recPrimes EX) D.R.m)
    (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) (eta : Formalism.L2.Host.HChar D.host.E)
    (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
    {δ : ℂ} (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (C1 : ℝ) : Prop :=
  HostTie EX → CharTie Ch mu0 eta sel → AnTie D δ χ cD →
    ∀ (i : Fin 2), SizeAt D i → ∀ w : LiftErrorLocal.Pl D, LiftErrorLocal.Over D i w →
      ∀ u : D.what₂.Word, D.what₂.places.resChar w ≠ (D.mem u).A.T →
        ∀ μ : D.what₂.Tup, D.host.g i ∉ Dx.Qp μ →
          ChainTie Ch sel Dx mu0 (ambOf (recSeam D) B χ cD) u μ → BoundAt L EX C1 i w u μ

theorem recSeam_emb (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    (recSeam D).σ₀ ((recFields D).emb τ x) = TaylorLogMetric.embT D ((recSeam D).iT τ) ((recSeam D).iE x) := by
  have h := RingHom.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ : D.R.GG) x)
  exact h

theorem recWts_row {D : D7} (EX : ErrX D) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    RowPar.of ((recWts EX).hc u τ) = (recWts EX).row τ := by
  show RowPar.of (D.hcW u τ) = RowPar.of (D.hc τ)
  simp only [RowPar.of, D.hcW_v, D.hcW_b, D.hcW_e]

end GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound
