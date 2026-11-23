import Mathlib
import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.BadPrimesPeriodBound

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConjugateFieldBounds

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist HostTie CharTie FieldTie)

section Chain

variable {K : Type} [Field K] [NumberField K] [StarRing K] (Q : KerChain K)

def clsNum (i : ℕ) : ℕ :=
  if i ≤ Q.n then ⨆ b : (Q.F i).β, Nat.card ((Q.F i).mem b).Cl
  else if i = Q.n + 1 then Nat.card Q.S.Cl else Nat.card Q.S₁.Cl

def idxNum (i : ℕ) : ℕ :=
  if i ≤ Q.n then Fintype.card (Q.F i).β
  else if i = Q.n + 1 then ⨆ c : Q.S.Cl, (Q.Y.ys (Q.S.outSec.rep c)).ncard else 1

def FactorBounds (v : InfinitePlace K) (c : ℕ → ℝ) : Prop :=
  (∀ i < Q.n, ∀ φ : (Q.F i).Forms,
    (famIpAt (Q.F (i + 1)) (Q.hF (i + 1)) v (Q.step i φ) (Q.step i φ)).re ≤
      Real.exp (c (i + 1)) * (famIpAt (Q.F i) (Q.hF i) v φ φ).re) ∧
  ∀ φ : (Q.F Q.n).Forms,
    (Q.S₁.ipAt Q.hS₁ v (Q.cpl φ) (Q.cpl φ)).re ≤
      Real.exp (c (Q.n + 1) + c (Q.n + 2)) * (famIpAt (Q.F Q.n) (Q.hF Q.n) v φ φ).re

end Chain

section Numbers

variable {D : D7} (large₂ : SizeData₂ D) (EX : ErrX D)

def nuRows (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (i : Fin (D.R.N D.R.m)) : ℝ :=
  if h : i.1 < D.R.N (j - 1) then ((((recWts EX).nuW u j τ).w ⟨i.1, h⟩ : ℤ) : ℝ) else 0

def scalK (D : D7) (CK : ℝ) (u : D.what₂.Word) : ℝ :=
  CK * D.R.f * (D.R.m : ℝ) ^ 2 * (D.R.N D.R.m : ℝ) ^ 2 *
    Real.log ((D.host.g 0 : ℝ) * D.host.g 1 * (D.mem u).A.T)

def boundB (C : ℝ) (u : D.what₂.Word) (j : ℕ) : ℝ :=
  Formalism.DimensionVariation.sizeB (nuRows EX u) large₂.logOm D.R.f D.R.m (D.R.N D.R.m) large₂.sc.L large₂.La C j

def boundA (C : ℝ) (u : D.what₂.Word) : ℝ :=
  -(∑ t : D.host.TT, (large₂.aT t : ℝ) * Real.log ((D.mem u).A.T : ℝ)) +
    C * ((D.host.TT.card : ℝ) * large₂.sc.b' * D.R.N D.R.m + D.R.f * (D.R.m * large₂.etaSz + large₂.Sc) * D.R.N D.R.m +
      D.R.f * (D.R.N D.R.m : ℝ) ^ 2) * large₂.La

end Numbers

def ConjField (D : D7) (δ : ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] (c : D.what₂.Tau → M)
    (t : (M →ₐ[ℚ] ℂ) → ℂ) : Prop :=
  (∀ x : D.what₂.LL, D.what₂.embLL x ∈ M) ∧ TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D D.host.ccK δ) M ∧
    (∀ τ, TaylorLogMetric.ellT D M τ = Submodule.span (𝓞 M) {c τ}) ∧
    ∀ ρ, GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D D.host.ccK δ)) (t ρ)

section Emb

variable {D : D7} {δ : ℂ} {M : IntermediateField ℚ ℂ} [NumberField M] {c : D.what₂.Tau → M} {t : (M →ₐ[ℚ] ℂ) → ℂ}

def ConjField.under (h : ConjField D δ M c t) (ρ : M →ₐ[ℚ] ℂ) : D.what₂.LL →+* ℂ :=
  (ρ : M →+* ℂ).comp (D.what₂.embLL.codRestrict M h.1)

variable (δ c) in

def logOmAt (τ : D.what₂.Tau) (ρ : M →ₐ[ℚ] ℂ) : ℝ := -TaylorLogMetric.logMet M (TaylorLogMetric.lamOf D D.host.ccK δ) ρ (c τ)

variable (D δ t) in

def logTh0At (ρ : M →ₐ[ℚ] ℂ) : ℝ :=
  Real.log (GL3Theta.normSq1 (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D D.host.ccK δ))
    (GL3Theta.th0 (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D D.host.ccK δ)) (t ρ)))

variable (δ c t) in

def sizeAt (EX : ErrX D) (CK : ℝ) (u : D.what₂.Word) (Q : KerChain D.what₂.LL) (j : ℕ) (ρ : M →ₐ[ℚ] ℂ) : ℝ :=
  Formalism.DimensionVariation.liftedMapLogSize (nuRows EX u) (fun l => (D.R.N (l - 1) : ℝ) * D.R.N l) (fun _ _ => scalK D CK u) (logOmAt δ c) (logTh0At D δ t)
            (fun l => Real.log (clsNum Q (l - 1))) (fun l => Real.log (clsNum Q l)) D.host.v j ρ +
    Real.log ((idxNum Q (j - 1) : ℝ) * idxNum Q j)

end Emb

def ParamHyp {D : D7} (large₂ : SizeData₂ D) (EX : ErrX D) (Cs : ℝ) : Prop :=
  Nonempty (ParameterChoice' D large₂) ∧ placeRankTwoOne.Sizes D large₂ Cs ∧ Formalism.L2.Col.Sizes (recPrimes EX) (recWts EX) large₂.sc.a

section Stmt

variable {D : D7} (large₂ : SizeData₂ D) {EX : ErrX D} (Ch : Chars (recFields D) (recPrimes EX) D.R.m)
  (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E)
  (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))

def KernelNorms (CK C : ℝ) : Prop :=
  ∀ (δ : ℂ) (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ → TaylorLogMetric.IsChi D χ →
  ∀ (M : IntermediateField ℚ ℂ) [NumberField M] (c : D.what₂.Tau → M) (t : (M →ₐ[ℚ] ℂ) → ℂ) (hM : ConjField D δ M c t)
    (u : D.what₂.Word) (cst : LocCst (recFields D) (rowSG (recPrimes EX) sel (1 : Twist D)))
    (I : ChIdx (recFields D) (recPrimes EX) D.R (QE sel ((1 : Twist D) : Chr (recFields D).F (recFields D).E (recFields D).K)))
    (b : I.β (D.R.m - 2 + 1)) (hY : YbHyp (R := D.R) sel (1 : Twist D) cst I u (D.R.m - 2) b)
    (hK : KerEquivC (recWts EX) Ch sel (1 : Twist D) cst I (ambOf (recSeam D) B χ fun τ => (c τ : ℂ)) u (D.R.m - 2) b hY (rPsymF Ch))
    (hF : ∀ j, (chF (recWts EX) sel (1 : Twist D) I u j).Ok)
    (hE : (evGSD (recWts EX) Ch sel (1 : Twist D) (rPsymF Ch) u).Ok),
    I.Ok Ch sel (1 : Twist D) cst (recGlob D mu0) (D.R.m - 2) → cst.sharp = true →
    FieldTie sel (ambOf (recSeam D) B χ fun τ => (c τ : ℂ)) (1 : Twist D) cst u →
    let Q : KerChain D.what₂.LL := KerChain.ofCol (recWts EX) Ch sel (1 : Twist D) cst I
      (chKerC (recWts EX) Ch sel (1 : Twist D) cst I (ambOf (recSeam D) B χ fun τ => (c τ : ℂ)) u (D.R.m - 2) b hY (rPsymF Ch) hK) hF hE
    (∀ ρ : M →ₐ[ℚ] ℂ, FactorBounds Q (InfinitePlace.mk (hM.under ρ)) fun j => sizeAt δ c t EX CK u Q j ρ) ∧
      ∀ j, 1 ≤ j → j ≤ D.R.m →
        (∑ ρ : M →ₐ[ℚ] ℂ, sizeAt δ c t EX CK u Q j ρ) / (Module.finrank ℚ M : ℝ) ≤ boundB large₂ EX C u j

def PeriodNorm (C : ℝ) : Prop :=
  ∀ (u : D.what₂.Word) (hP : (mtildeGSD (recWts EX) Ch sel (1 : Twist D) (rPsymF Ch)).Ok)
    (hE : (evGSD (recWts EX) Ch sel (1 : Twist D) (rPsymF Ch) u).Ok)
    (Xg : Finset (G0 (recFields D).E (recPrimes EX).vGs D.R.r → (recFields D).K)) (s : D.what₂.LL →+* ℂ)
    (ψ : (evGSD (recWts EX) Ch sel (1 : Twist D) (rPsymF Ch) u).EqFun)
    (F : V0X (recWts EX) Ch sel (1 : Twist D) Xg (rPsymF Ch)),
    ‖s (PtilFF (recWts EX) Ch sel (1 : Twist D) (rPsymF Ch) hP u ψ.1 F.1.1)‖ ^ 2 ≤
      Real.exp (boundA large₂ C u) *
        ((evGSD (recWts EX) Ch sel (1 : Twist D) (rPsymF Ch) u).ipAt hE (InfinitePlace.mk s) ψ.1 ψ.1).re *
        ((mtildeGSD (recWts EX) Ch sel (1 : Twist D) (rPsymF Ch)).ipAt hP (InfinitePlace.mk s) F.1.1 F.1.1).re

end Stmt

def ColumnNormsAt (Cs CK C : ℝ) (D : D7) (large₂ : SizeData₂ D) (EX : ErrX D) : Prop :=
  ∀ (Ch : Chars (recFields D) (recPrimes EX) D.R.m) (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E)
    (eta : Formalism.L2.Host.HChar D.host.E) (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E)),
    HostTie EX → CharTie Ch mu0 eta sel → ParamHyp large₂ EX Cs → KernelNorms large₂ Ch mu0 sel CK C ∧ PeriodNorm large₂ Ch sel C

def ColumnNorms : Prop :=
  ∀ Cs : ℝ, ∃ CK C : ℝ, 0 ≤ CK ∧ 0 ≤ C ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (EX : ErrX D), ColumnNormsAt Cs CK C D large₂ EX

example (M : IntermediateField ℚ ℂ) [NumberField M] :
    Fintype.card (M →ₐ[ℚ] ℂ) = Module.finrank ℚ M ∧ 0 < Module.finrank ℚ M :=
  ⟨AlgHom.card ℚ M ℂ, Module.finrank_pos⟩

open Formalism.L2.DIV.Inst Formalism.L2.Indef.Examples₂ in

example (v : InfinitePlace K3) : FactorBounds (ptQ 0 (fun _ => 1) 1 1) v fun _ => 0 := by
  refine ⟨fun i hi => absurd hi (Nat.not_lt_zero i), fun φ => ?_⟩
  rw [ptInF_eta φ, pt_cpl]
  have h1 := pt_ipAt pt_ok v ((1 * 1 : K3) • fun _ : Fin 1 => (φ () : Unit → K3) ())
  have h2 := pt_famIpAt v (fun _ : Fin 1 => (φ () : Unit → K3) ())
  refine le_of_eq ?_
  refine (congrArg Complex.re h1).trans ?_
  refine Eq.trans ?_ (congrArg (fun z : ℂ => Real.exp (0 + 0) * z.re) h2).symm
  simp

open Formalism.L2.DIV.Inst Formalism.L2.Indef.Examples₂ in

example (v : InfinitePlace K3) : ¬ FactorBounds (ptQ 0 (fun _ => 1) 2 1) v fun _ => 0 := by
  intro h
  have h0 := h.2 (ptInF fun _ => 1)
  rw [pt_cpl] at h0
  have h1 := congrArg Complex.re (pt_ipAt pt_ok v ((1 * 2 : K3) • fun _ : Fin 1 => (1 : K3)))
  have h2 := congrArg (fun z : ℂ => Real.exp (0 + 0) * z.re) (pt_famIpAt v (fun _ : Fin 1 => 1))
  have h3 := h1.symm.le.trans (h0.trans h2.le)
  simp only [Complex.ofReal_re, Pi.smul_apply, smul_eq_mul, mul_one, one_mul, map_ofNat, map_one, add_zero, Real.exp_zero] at h3
  norm_num at h3

end GlobalTheory.IndefiniteRowSideFullHecke.ConjugateFieldBounds
