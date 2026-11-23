import Mathlib
import Formalism.LocalToGlobal.Divisibility.LinkDIVL2R3Col

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions Formalism.L2.Col

section ConcreteCol3

variable {X : Fields} {Pr : Primes X} {Rk : Ranks} {W : Wts X Pr.Word Rk} {Ch : Chars X Pr Rk.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {Sg : Set ℕ}
  {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

theorem linkDIV_L2R3_rec [IsTotallyComplex X.K] (A3 : FamIn3 X.K G Pl0 I0 Ty T m) {s : ℕ} (hOk : A3.fam3.Ok3 s)
    (hsep : A3.fam3.TypesSep3) (P0 : Subgroup G) (ψ0 : P0 →* X.Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* X.Kˣ) (hX : X.Ok)
    {P : LevFam X.E X.K Rk.r Pr.vGs} (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs Rk.r → X.K)) {m2 : ℕ} {Gc : ChGlob X Rk.m}
    (mu : A3.fam3.base3.Tup → Tup X.F X.E X.K Sg) (cst : ∀ t, LocCst X (rowSG Pr sel (mu t)))
    (L : ∀ t, ChIdx X Pr Rk (QE sel (mu t : Chr X.F X.E X.K))) (hL : ∀ t, (L t).Ok Ch sel (mu t) (cst t) Gc m2)
    (hP : ∀ t, (mtildeGSD W Ch sel (mu t) P).Ok) (Mem : Type) (wd : Mem → Pr.Word) (b : ∀ t, Mem → (L t).β (m2 + 1))
    (hY : ∀ t x, YbHyp (R := Rk) sel (mu t) (cst t) (L t) (wd x) m2 (b t x))
    (Am : Formalism.L2.Ker.Amb X) (hK : ∀ t x, Formalism.L2.Ker.KerEquivC W Ch sel (mu t) (cst t) (L t) Am (wd x) m2 (b t x) (hY t x) P)
    (hF : ∀ t x j, (chF W sel (mu t) (L t) (wd x) j).Ok) (hE : ∀ x, (evGSD W Ch sel (mu A3.fam3.base3.μ0) P (wd x)).Ok)
    (ev : ∀ (Zs : DefSub A3.fam3.amb3) t, (Fin ((A3.side3 P1 ψ1 Zs).nV t) → X.K) →ₗ[X.K] V0X W Ch sel (mu t) Xg P)
    (Sp : ∀ Zs : DefSub A3.fam3.amb3,
      SPer (colFace hX (A3.side3 P1 ψ1 Zs) Xg mu cst L hL hP Mem wd b hY (kerRec mu cst L wd b hY Am hK) hF (ev Zs)))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (cf : ConvFace A3.fam3.base3) (C CH : ℝ)
    (Pk : IndefPkgR A3.fam3.amb3
      (Formalism.IndefR.Cx.faceOf3 A3 P0 ψ0 P1 ψ1
        (fun Zs => colFace hX (A3.side3 P1 ψ1 Zs) Xg mu cst L hL hP Mem wd b hY (kerRec mu cst L wd b hY Am hK) hF (ev Zs)) Sp Zsc)
      cf C CH)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (R : RecNums A3.fam3.base3.J Pl) (x : Mem)
    (Nu : Submodule (𝓞 X.K) (Fin (ramDim W Ch hX (wd x)) → X.K)) (sg : HeightOneSpectrum (𝓞 X.K) → ℝ)
    (I : DivInputsR Pk.core R x Nu sg)
    (hQ : ChainTie I.ch (memQ (A := kerRec mu cst L wd b hY Am hK) (hF := hF) hE (x := x))) (h0 : FirstCols hE hQ) :
    DivClausesR Pk.core R x Nu sg ∧
      (∀ y : Fin (I.ch.c 0) → X.K,
        hQ.coL ((chainMat I.ch.Kj ⟨(memQ (A := kerRec mu cst L wd b hY Am hK) (hF := hF) hE (x := x)).n + 1, by have := hQ.hmm; omega⟩).mulVec y) =
          Formalism.L2.Ker.colMu W Ch sel (mu A3.fam3.base3.μ0) (cst A3.fam3.base3.μ0) (L A3.fam3.base3.μ0) Am (wd x) m2 (b A3.fam3.base3.μ0 x)
            (hY A3.fam3.base3.μ0 x) P (hK A3.fam3.base3.μ0 x) (hF A3.fam3.base3.μ0 x) (hL A3.fam3.base3.μ0)
            (colOfCoord W Ch hX (wd x) fun i => y (Fin.cast I.ch.c0.symm i))) ∧
      ∀ (φ : Fin (ramDim W Ch hX (wd x)) → X.K) (F : Fin ((A3.side3 P1 ψ1 Pk.Zs).nV A3.fam3.base3.μ0) → X.K),
        I.ch.PtL ((chainMat I.ch.Kj (Fin.last I.ch.mm)).mulVec fun i => φ (Fin.cast I.ch.c0 i)) F =
          colPerL (hP A3.fam3.base3.μ0) Xg (wd x) (ev Pk.Zs A3.fam3.base3.μ0)
            (Formalism.L2.Ker.colMu W Ch sel (mu A3.fam3.base3.μ0) (cst A3.fam3.base3.μ0) (L A3.fam3.base3.μ0) Am (wd x) m2 (b A3.fam3.base3.μ0 x)
              (hY A3.fam3.base3.μ0 x) P (hK A3.fam3.base3.μ0 x) (hF A3.fam3.base3.μ0 x) (hL A3.fam3.base3.μ0) (colOfCoord W Ch hX (wd x) φ)) F :=
  ⟨divClausesR_of (A3.side_well_formed hOk P0 ψ0 Pk.Zs Pk.stable Pk.inBlock hsep)
    (A3.side_well_formed hOk P1 ψ1 Pk.Zs Pk.stable Pk.inBlock hsep) Pk.core R x Nu sg I, FirstCols.chain hE h0, fun φ F => (I.ch.fact φ F).symm⟩

end ConcreteCol3

end Formalism.L2.DIV
