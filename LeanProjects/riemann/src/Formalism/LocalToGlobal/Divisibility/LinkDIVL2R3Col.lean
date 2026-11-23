import Mathlib
import Formalism.LocalToGlobal.Divisibility.ConstantGeTwentyEight
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
import Formalism.LocalToGlobal.IndefiniteReal.FaceOf3

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.Indef

section Face

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem linkDIV_L2R_face [IsTotallyComplex K] {Bs : DefBase K} {A : DefAmb Bs} {fc : DefSub A → DefFace Bs} {cf : ConvFace Bs} {C CH : ℝ}
    (Pk : IndefPkgR A fc cf C CH) (wf0 : (fc Pk.Zs).Df0.WF) (wf1 : (fc Pk.Zs).Df1.WF)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (R : RecNums Bs.J Pl) (u : (fc Pk.Zs).Dc.Mem)
    (Nu : Submodule (𝓞 K) (Fin ((fc Pk.Zs).Dc.a u) → K)) (sg : HeightOneSpectrum (𝓞 K) → ℝ)
    (I : DivInputsR Pk.core R u Nu sg) : DivClausesR Pk.core R u Nu sg :=
  divClausesR_of wf0 wf1 Pk.core R u Nu sg I

end Face

section Fam3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

theorem linkDIV_L2R3 [IsTotallyComplex K] (A3 : FamIn3 K G Pl0 I0 Ty T m) {s : ℕ} (hOk : A3.fam3.Ok3 s)
    (hsep : A3.fam3.TypesSep3) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (cf : ConvFace A3.fam3.base3) (C CH : ℝ)
    (Pk : IndefPkgR A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) cf C CH)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (R : RecNums A3.fam3.base3.J Pl) (u : (Dc Pk.Zs).Mem)
    (Nu : Submodule (𝓞 K) (Fin ((Dc Pk.Zs).a u) → K)) (sg : HeightOneSpectrum (𝓞 K) → ℝ)
    (I : DivInputsR Pk.core R u Nu sg) : DivClausesR Pk.core R u Nu sg :=
  divClausesR_of (A3.side_well_formed hOk P0 ψ0 Pk.Zs Pk.stable Pk.inBlock hsep)
    (A3.side_well_formed hOk P1 ψ1 Pk.Zs Pk.stable Pk.inBlock hsep) Pk.core R u Nu sg I

end Fam3

section Col3

variable {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
  (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
  (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
  (trIv : Fin R.m → (Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K)

theorem linkDIV_L2R3_col (hH : ColHyp3 W Ch sel v0 TU Xg S0) (hI : (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).TrISep)
    (P0 P1 : Col.LevFam X.E X.K R.r Pr.vGs)
    (Dc : ∀ Zs : DefSub (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).amb3,
      DefCols ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).side3 P1.grp P1.chr Zs))
    (Sp : ∀ Zs : DefSub (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).amb3, SPer (Dc Zs))
    (Zsc : DefSub (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).amb3 → IndefScale (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).base3)
    (cf : ConvFace (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).base3) (C CH : ℝ)
    (Pk : IndefPkgR (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).amb3
      (Formalism.IndefR.Cx.faceOf3 (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv) P0.grp P0.chr P1.grp P1.chr Dc Sp Zsc) cf C CH)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (Rn : RecNums (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).base3.J Pl)
    (u : (Dc Pk.Zs).Mem) (Nu : Submodule (𝓞 X.K) (Fin ((Dc Pk.Zs).a u) → X.K)) (sg : HeightOneSpectrum (𝓞 X.K) → ℝ)
    (I : DivInputsR Pk.core Rn u Nu sg) : DivClausesR Pk.core Rn u Nu sg :=
  haveI : IsTotallyComplex X.K := hX.cplxK
  divClausesR_of (colSide3_WF W Ch sel hX v0 TU Xg S0 xiVal trIv hH hI P0 Pk.Zs Pk.stable Pk.inBlock)
    (colSide3_WF W Ch sel hX v0 TU Xg S0 xiVal trIv hH hI P1 Pk.Zs Pk.stable Pk.inBlock) Pk.core Rn u Nu sg I

end Col3

end Formalism.L2.DIV
