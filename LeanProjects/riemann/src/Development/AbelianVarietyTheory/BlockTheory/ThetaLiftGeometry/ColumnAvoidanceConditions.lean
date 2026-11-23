import Mathlib
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ColumnAvoidanceConditions

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV

@[reducible] def fieldsOf (D : D7) : Fields where
  F := D.host.F
  E := D.host.E
  K := D.what₂.LL
  starE := D.host.cmStar
  Tau := D.what₂.Tau
  deTau := Classical.decEq _
  emb τ := D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)

@[reducible] def primesOf (D : D7) (EX : ErrX D) : Primes (fieldsOf D) where
  cond := D.host.QS * D.host.q * D.host.d
  g := D.host.g
  piG := EX.piG
  Word := D.what₂.Word
  ftWord := D.wordFin
  deWord := Classical.decEq _
  T u := (D.mem u).A.T
  piT := EX.piT

def wtsOf (D : D7) (EX : ErrX D) : Wts (fieldsOf D) (primesOf D EX).Word D.R where
  row τ := RowPar.of (D.hc τ)
  hc := D.hcW
  tops := topsOf D.host D.eTau

def seamOf (D : D7) : Seam D (fieldsOf D) where
  iE := RingEquiv.refl _
  iT := Equiv.refl _
  σ₀ := D.what₂.embLL

def globOf (D : D7) (m0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) : ChGlob (fieldsOf D) D.R.m where
  σ₀ := D.what₂.embLL
  xi0 := D.host.xi0
  mu0 := m0

example (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : (fieldsOf D).emb τ x = tauLL D τ x := rfl

example (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    (seamOf D).σ₀ ((fieldsOf D).emb τ x) = TaylorLogMetric.embT D ((seamOf D).iT τ) ((seamOf D).iE x) :=
  DFunLike.congr_fun D.embE_φ₀ _

section Ties

variable (D : D7) (Dx : DivX D) (EX : ErrX D) (Ch : Chars (fieldsOf D) (primesOf D EX) D.R.m)
  (m0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E)
  (sel : HeightOneSpectrum (𝓞 (fieldsOf D).F) → HeightOneSpectrum (𝓞 (fieldsOf D).E))

def HostTie : Prop := GL3Theta.InducedCMType D ∧ GL3Theta.HostFieldConditions D ∧ D.host.ccK = ⊤

def PrimeTie : Prop := (primesOf D EX).Ok ∧ (primesOf D EX).PiGCong

def CharTie : Prop :=
  Ch.Ok ∧ ∃ eta : Formalism.L2.Host.HChar D.host.E, Ch.Tied D.what₂.embLL (fun j τ => (D.hc τ).e j) m0 eta

def ThetaTie (δ : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) : Prop :=
  TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D ⊤ δ ∧ TaylorLogMetric.IsChi D χ ∧ IsDgen D cD

def RangeG (i : Fin 2) (u : D.what₂.Word) : Prop :=
  2 * D.R.f * D.R.N D.R.m + 1 < D.host.g i ∧
  (∀ j ∈ LiftErrorLocal.lifts D, 2 * LiftErrorLocal.Dpi D u j + 2 < (D.host.g i : ℝ)) ∧
  ∀ j, j ≤ D.R.m → ∀ τ, ((wtsOf D EX).lamTrue u j τ).spread < (D.host.g i : ℤ)

def AvoidTie (i : Fin 2) (u : D.what₂.Word) (S : Set ℕ) : Prop :=
  (∀ l ∈ D.host.small, l ∈ S) ∧ D.host.q ∈ S ∧ D.host.d ∈ S ∧ D.host.g (1 - i) ∈ S ∧ (D.mem u).A.T ∈ S

variable {S : Set ℕ} (ξ : Tup (fieldsOf D).F (fieldsOf D).E (fieldsOf D).K S)

def TupTie (μ : D.what₂.Tup) : Prop :=
  (μ = D.what₂.mu0 → ξ = 1) ∧
    (Dx.Qp μ : Set ℕ) = QprimeN (ξ : Chr (fieldsOf D).F (fieldsOf D).E (fieldsOf D).K)

def FieldTie (cst : LocCst (fieldsOf D) (rowSG (primesOf D EX) sel ξ)) (A : Amb (fieldsOf D)) (u : D.what₂.Word) : Prop :=
  letI := (fieldsOf D).starE
  ∀ s, s < D.R.m →
    ∀ (N : Submodule (𝓞 (fieldsOf D).E) (Sp (fieldsOf D).E (D.R.N s)))
      (N' : Submodule (𝓞 (fieldsOf D).E) (Sp (fieldsOf D).E (D.R.N (s + 1))))
      (x : HomE (fieldsOf D).E (D.R.N s) (D.R.N (s + 1))),
      InRange (Sall (Pr := primesOf D EX) sel ξ u) (cAof sel ξ cst * cBof sel ξ cst u) (cBof sel ξ cst u) N N' x →
      ∀ n : DVar (fieldsOf D).Tau (D.R.N s) (D.R.N (s + 1)) →₀ ℕ,
        (∀ τ, (∑ b, ∑ a, (n (τ, b, a) : ℤ)) = ∑ r, ((wtsOf D EX).nuW u (s + 1) τ).w r) →
        ∃ k : D.what₂.LL, A.σ₀ k = (A.chiF _ _ N N')⁻¹ *
          jetC A.cD (A.thInd (Sall (Pr := primesOf D EX) sel ξ u) N N' (cBof sel ξ cst u) x) n

def ColTie (u : D.what₂.Word) (κ : ((D.fm u).lat 0).V ≃ₗ[D.what₂.LL] MfV (wtsOf D EX) Ch u) : Prop :=
  (∀ x, x ∈ ((D.fm u).lat 0).L ↔ κ x ∈ MfL (wtsOf D EX) Ch u) ∧
    ∀ x, x ∈ (D.fm u).ramSub ↔ κ x ∈ MramV (wtsOf D EX) Ch u

def RowTie (μ : D.what₂.Tup)
    (ι : MtildeV (wtsOf D EX) Ch sel ξ (rPsymF Ch) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ) : Prop :=
  (∀ (n : ℕ) (v : Fin n → MtildeV (wtsOf D EX) Ch sel ξ (rPsymF Ch)), LinearIndependent D.what₂.LL v →
    LinearIndependent ℂ (fun a => ι (v a))) ∧
  Submodule.span ℂ (Set.range ι) = ⊤ ∧
  (∀ x ∈ (D.what₂.Mtilde μ).gen, x ∈ Set.range ι) ∧
  ∀ F, F ∈ MtildeL (wtsOf D EX) Ch sel ξ (rPsymF Ch) ↔ ∃ c : D.what₂.Amb μ → 𝓞 D.what₂.LL,
    ι F = ∑ v ∈ (D.what₂.Mtilde μ).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v

def PerTie (u : D.what₂.Word) (μ : D.what₂.Tup) (hP : (mtildeGSD (wtsOf D EX) Ch sel ξ (rPsymF Ch)).Ok)
    (col : MfV (wtsOf D EX) Ch u →ₗ[D.what₂.LL] (evGSD (wtsOf D EX) Ch sel ξ (rPsymF Ch) u).EqFun)
    (κ : ((D.fm u).lat 0).V ≃ₗ[D.what₂.LL] MfV (wtsOf D EX) Ch u)
    (ι : MtildeV (wtsOf D EX) Ch sel ξ (rPsymF Ch) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ) : Prop :=
  ∀ (φ : (D.div.Nu u).V) (F : MtildeV (wtsOf D EX) Ch sel ξ (rPsymF Ch)),
    D.what₂.perCol u μ (D.jN u φ) (ι F) =
      D.what₂.embLL (PtilE (wtsOf D EX) Ch sel ξ (rPsymF Ch) hP u (col (κ (D.nuIn u φ))) F)

def ChainTie (A : Amb (fieldsOf D)) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  ∃ (cst : LocCst (fieldsOf D) (rowSG (primesOf D EX) sel ξ))
    (Lx : ChIdx (fieldsOf D) (primesOf D EX) D.R (QE sel (ξ : Chr (fieldsOf D).F (fieldsOf D).E (fieldsOf D).K)))
    (m2 : ℕ) (b : Lx.β (m2 + 1)) (hY : YbHyp (R := D.R) sel ξ cst Lx u m2 b)
    (hL : Lx.Ok Ch sel ξ cst (globOf D m0) m2)
    (hF : ∀ j, (chF (wtsOf D EX) sel ξ Lx u j).Ok)
    (hK : KerEquivC (wtsOf D EX) Ch sel ξ cst Lx A u m2 b hY (rPsymF Ch))
    (hP : (mtildeGSD (wtsOf D EX) Ch sel ξ (rPsymF Ch)).Ok)
    (κ : ((D.fm u).lat 0).V ≃ₗ[D.what₂.LL] MfV (wtsOf D EX) Ch u)
    (ι : MtildeV (wtsOf D EX) Ch sel ξ (rPsymF Ch) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ),
    cst.sharp = true ∧ FieldTie D EX sel ξ cst A u ∧ ColTie D EX Ch u κ ∧ RowTie D EX Ch sel ξ μ ι ∧
      PerTie D EX Ch sel ξ u μ hP (colMu (wtsOf D EX) Ch sel ξ cst Lx A u m2 b hY (rPsymF Ch) hK hF hL) κ ι

end Ties

def Bound (D : D7) (L : SizeData₂ D) (EX : ErrX D) (C1 : ℝ) (i : Fin 2) (w : LiftErrorLocal.Pl D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  ∀ φ ∈ DV.MramL D u, ∀ F ∈ (D.what₂.Mtilde μ).carrier,
    ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u μ (D.jN u φ) F ∧
      (y = 0 ∨ -(∑ j ∈ LiftErrorLocal.lifts D, vNN EX i u j w) - C1 * LiftErrorLocal.errC D L ≤ LiftErrorLocal.vG D w y)

def ColPeriodAt (D : D7) (Dx : DivX D) (L : SizeData₂ D) (EX : ErrX D)
    (Ch : Chars (fieldsOf D) (primesOf D EX) D.R.m) (m0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E)
    (sel : HeightOneSpectrum (𝓞 (fieldsOf D).F) → HeightOneSpectrum (𝓞 (fieldsOf D).E))
    (δ : ℂ) (B : Base D ⊤ δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (C1 : ℝ) : Prop :=
  HostTie D → PrimeTie D EX → CharTie D EX Ch m0 → IsSel (fieldsOf D) sel → ThetaTie D δ χ cD →
  ∀ (i : Fin 2) (w : LiftErrorLocal.Pl D), LiftErrorLocal.Over D i w → ∀ u : D.what₂.Word, D.what₂.places.resChar w ≠ (D.mem u).A.T →
    RangeG D EX i u →
    ∀ μ : D.what₂.Tup, D.host.g i ∉ Dx.Qp μ →
    ∀ (S : Set ℕ) (ξ : Tup (fieldsOf D).F (fieldsOf D).E (fieldsOf D).K S), AvoidTie D i u S → TupTie D Dx ξ μ →
      ChainTie D EX Ch m0 sel ξ (ambOf (seamOf D) B χ cD) u μ →
      Bound D L EX C1 i w u μ

example (D : D7) (L : SizeData₂ D) (EX : ErrX D) (C1 C2 : ℝ) (h : LiftErrorLocal.PropositionCLatticeBound D L EX C1 C2) (i : Fin 2) (w : LiftErrorLocal.Pl D)
    (hw : LiftErrorLocal.Over D i w) (u : D.what₂.Word) (hT : D.what₂.places.resChar w ≠ (D.mem u).A.T) (μ : D.what₂.Tup) :
    Bound D L EX C1 i w u μ := h.1 i w hw u hT μ

end GlobalTheory.IndefiniteRowSideFullHecke.ColumnAvoidanceConditions

end
