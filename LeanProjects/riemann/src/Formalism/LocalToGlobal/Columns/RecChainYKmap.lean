import Formalism.LocalToGlobal.Columns.RecChainYUnfPol
import Formalism.LocalToGlobal.Columns.RecordFS

open NumberField IsDedekindDomain Module Matrix MvPolynomial

noncomputable section

namespace Formalism.L2.Col.Sc

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker Formalism.L2.Col

section Charts

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

abbrev SecY (u : Pr.Word) (m2 : ℕ) : Type := ∀ j b, ((Formalism.L2.Col.chFY W sel mu cst L u m2 j).mem b).Sec

@[reducible] def chFY (u : Pr.Word) (m2 : ℕ) (sec : SecY W sel mu cst L u m2) (j : ℕ) : GFamS X.K :=
  { toGFam := Formalism.L2.Col.chFY W sel mu cst L u m2 j, sec := sec j }

variable {W sel mu cst L}

def ptYc {u : Pr.Word} {m2 : ℕ} {sec : SecY W sel mu cst L u m2} {j : ℕ} (c : (chFY W sel mu cst L u m2 sec j).Cl) : ChPt (R := R) sel mu u j :=
  (((chFY W sel mu cst L u m2 sec j).sec c.1).rep c.2).1.1

def ybY {u : Pr.Word} {m2 : ℕ} {sec : SecY W sel mu cst L u m2} {j : ℕ} (c : (chFY W sel mu cst L u m2 sec j).Cl) : Set (Sp X.E (R.N j)) :=
  (((chFY W sel mu cst L u m2 sec j).sec c.1).rep c.2).1.2

def XiY {u : Pr.Word} {m2 : ℕ} {sec : SecY W sel mu cst L u m2} (i : ℕ) (c : (chFY W sel mu cst L u m2 sec i).Cl) (c' : (chFY W sel mu cst L u m2 sec (i + 1)).Cl)
    (x : HomE X.E (R.N i) (R.N (i + 1))) : X.K :=
  if i < m2 then XiEntry Ch sel mu cst L i c.1 c'.1 (ptYc c) (ptYc c') x
  else if i = m2 then XiCpl1 Ch sel mu cst L i c.1 (ptYc c) (ptYc c') (ybY c') x
  else if i = m2 + 1 then XiTop Ch sel mu cst i (ptYc c) (ybY c) (ptYc c') x
  else 0

def thY (Am : Amb X) {u : Pr.Word} {m2 : ℕ} {sec : SecY W sel mu cst L u m2} (i : ℕ) (c : (chFY W sel mu cst L u m2 sec i).Cl) (c' : (chFY W sel mu cst L u m2 sec (i + 1)).Cl) :
    VCx X.Tau (R.N i) (R.N (i + 1)) → ℂ :=
  Am.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (ptYc c).deco.1.N (ptYc c').deco.1.N (XiY Ch i c c')

def kerYc (Am : Amb X) {u : Pr.Word} {m2 : ℕ} {sec : SecY W sel mu cst L u m2} (i : ℕ) (c : (chFY W sel mu cst L u m2 sec i).Cl) (c' : (chFY W sel mu cst L u m2 sec (i + 1)).Cl) :
    VV X.K (W.lamTrue u i) →ₗ[X.K] VV X.K (W.lamTrue u (i + 1)) :=
  kerOf (stepC W Ch sel mu cst Am u i (W.lamTrue u (i + 1))) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u)
    (ptYc c).deco.1.N (frsF sel mu (ptYc c)) (ptYc c').deco.1.N (frsF sel mu (ptYc c')) (XiY Ch i c c')

def rhoY (σ₀ : X.K →+* ℂ) (Am : Amb X) {u : Pr.Word} {m2 : ℕ} {sec : SecY W sel mu cst L u m2} (i : ℕ) (c : (chFY W sel mu cst L u m2 sec i).Cl) : ℂ :=
  σ₀ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) (ptYc c).deco.1.N (frsF sel mu (ptYc c))) *
    (Am.chiF (R.N i) (R.N (i + 1)) (ptYc c).deco.1.N (stdLat X.E (R.N (i + 1))))⁻¹

def rhoY' (σ₀ : X.K →+* ℂ) (Am : Amb X) {u : Pr.Word} {m2 : ℕ} {sec : SecY W sel mu cst L u m2} (i : ℕ) (c' : (chFY W sel mu cst L u m2 sec (i + 1)).Cl) : ℂ :=
  (σ₀ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) (ptYc c').deco.1.N (frsF sel mu (ptYc c'))))⁻¹ *
    (Am.chiF (R.N i) (R.N (i + 1)) (stdLat X.E (R.N i)) (ptYc c').deco.1.N)⁻¹

def RhoYUnit (σ₀ : X.K →+* ℂ) (Am : Amb X) (u : Pr.Word) (m2 : ℕ) (sec : SecY W sel mu cst L u m2) : Prop :=
  (∀ i, i < R.m → ∀ c : (chFY W sel mu cst L u m2 sec i).Cl, ‖rhoY Ch σ₀ Am i c‖ = 1) ∧
    ∀ i, i < R.m → ∀ c' : (chFY W sel mu cst L u m2 sec (i + 1)).Cl, ‖rhoY' Ch σ₀ Am i c'‖ = 1

def ChainArgF.ofChKer (σ₀ : X.K →+* ℂ) (Am : Amb X) (u : Pr.Word) (m2 : ℕ) (sec : SecY W sel mu cst L u m2) (hU : RhoYUnit (W := W) (cst := cst) (L := L) Ch σ₀ Am u m2 sec) :
    ChainArgF R (fun i => (chFY W sel mu cst L u m2 sec i).toGFam) σ₀ where
  rhoDet := rhoY Ch σ₀ Am
  rhoDet' := rhoY' Ch σ₀ Am
  rho_norm := hU.1
  rho'_norm := hU.2
  unf i c c' := unfTh σ₀ Am.cD (thY Ch Am i c c')

def recChainY (σ₀ : X.K →+* ℂ) (Am : Amb X) (u : Pr.Word) (m2 : ℕ) (sec : SecY W sel mu cst L u m2) (hU : RhoYUnit (W := W) (cst := cst) (L := L) Ch σ₀ Am u m2 sec)
    (hF : ∀ j, (chFY W sel mu cst L u m2 sec j).Ok) (D : ℕ) (hD : 0 < D)
    (hdvd : ∀ j, j ≤ R.m → ∀ c : (chFY W sel mu cst L u m2 sec j).Cl, Nat.card (FamStabS (chFY W sel mu cst L u m2 sec j) c) ∣ D) :
    ColumnChain R X.Tau (W.hc u) :=
  recChainFS (W.hc u) (chFY W sel mu cst L u m2 sec) hF σ₀ D hD hdvd (ChainArgF.ofChKer Ch σ₀ Am u m2 sec hU)

variable {Ch}

end Charts

end Formalism.L2.Col.Sc
