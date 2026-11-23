import Formalism.LocalToGlobal.Columns.RecChainUnfOne
import Formalism.LocalToGlobal.Columns.ChainInstY

open NumberField IsDedekindDomain Module Matrix MvPolynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker

section Charts

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

open Classical in

def cplAt (u : Pr.Word) (m2 j : ℕ) (b : L.β j) : Cpl ((chF W sel mu L u j).mem b) where
  Yb := Set (Sp X.E (R.N j))
  actY :=
    { smul := fun g Y => (fun v => g.1.1 v) '' Y
      one_smul := fun Y => Set.image_id Y
      mul_smul := fun g h Y => (Set.image_image (fun v => g.1.1 v) (fun v => h.1.1 v) Y).symm }
  ys p := if j = m2 + 1 then ybSet sel mu cst p.deco.1.N else {Set.univ}
  fin p := by
    split_ifs
    · exact ybSet_finite sel mu cst _ p.deco.2.lat.fg
    · exact Set.finite_singleton _
  equiv g p Y := by
    split_ifs
    · exact ybSet_gmap sel mu cst p.deco.1.N g.1.1 Y
    · show (fun v => g.1.1 v) '' Y = Set.univ ↔ Y = Set.univ
      constructor
      · intro h
        have h2 : (fun v => g.1.1 v) '' Y = (fun v => g.1.1 v) '' Set.univ := by
          rw [h, Set.image_univ]
          exact (g.1.1.surjective.range_eq).symm
        exact g.1.1.injective.image_injective h2
      · rintro rfl
        rw [Set.image_univ]
        exact g.1.1.surjective.range_eq

@[reducible] def chFY (u : Pr.Word) (m2 j : ℕ) : GFam X.K where
  β := L.β j
  V := (colValF W sel mu u j).V
  ιV := VVIdx (colValF W sel mu u j).lam
  bV := (colValF W sel mu u j).bV
  pair := (colValF W sel mu u j).pair
  G b := FrmG (L.levG j b) (L.levQ j b)
  D b := (cplAt W sel mu cst L u m2 j b).Pts
  actD b := (cplGSD (cplAt W sel mu cst L u m2 j b)).actD
  ρ b := frmRho (colValF W sel mu u j) (L.levG j b) (L.levQ j b)
  Nab _ p := (colValF W sel mu u j).Nab p.1.1
  Del _ p := (colValF W sel mu u j).Del p.1.1

variable {W sel mu cst L}

def ptYc {u : Pr.Word} {m2 j : ℕ} (c : (chFY W sel mu cst L u m2 j).Cl) : ChPt (R := R) sel mu u j :=
  (((chFY W sel mu cst L u m2 j).mem c.1).outSec.rep c.2).1.1

def ybY {u : Pr.Word} {m2 j : ℕ} (c : (chFY W sel mu cst L u m2 j).Cl) : Set (Sp X.E (R.N j)) :=
  (((chFY W sel mu cst L u m2 j).mem c.1).outSec.rep c.2).1.2

def XiY {u : Pr.Word} {m2 : ℕ} (i : ℕ) (c : (chFY W sel mu cst L u m2 i).Cl) (c' : (chFY W sel mu cst L u m2 (i + 1)).Cl)
    (x : HomE X.E (R.N i) (R.N (i + 1))) : X.K :=
  if i < m2 then XiEntry Ch sel mu cst L i c.1 c'.1 (ptYc c) (ptYc c') x
  else if i = m2 then XiCpl1 Ch sel mu cst L i c.1 (ptYc c) (ptYc c') (ybY c') x
  else if i = m2 + 1 then XiTop Ch sel mu cst i (ptYc c) (ybY c) (ptYc c') x
  else 0

def thY (Am : Amb X) {u : Pr.Word} {m2 : ℕ} (i : ℕ) (c : (chFY W sel mu cst L u m2 i).Cl) (c' : (chFY W sel mu cst L u m2 (i + 1)).Cl) :
    VCx X.Tau (R.N i) (R.N (i + 1)) → ℂ :=
  Am.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (ptYc c).deco.1.N (ptYc c').deco.1.N (XiY Ch i c c')

def kerYc (Am : Amb X) {u : Pr.Word} {m2 : ℕ} (i : ℕ) (c : (chFY W sel mu cst L u m2 i).Cl) (c' : (chFY W sel mu cst L u m2 (i + 1)).Cl) :
    VV X.K (W.lamTrue u i) →ₗ[X.K] VV X.K (W.lamTrue u (i + 1)) :=
  kerOf (stepC W Ch sel mu cst Am u i (W.lamTrue u (i + 1))) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u)
    (ptYc c).deco.1.N (frsF sel mu (ptYc c)) (ptYc c').deco.1.N (frsF sel mu (ptYc c')) (XiY Ch i c c')

def rhoY (σ₀ : X.K →+* ℂ) (Am : Amb X) {u : Pr.Word} {m2 : ℕ} (i : ℕ) (c : (chFY W sel mu cst L u m2 i).Cl) : ℂ :=
  σ₀ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) (ptYc c).deco.1.N (frsF sel mu (ptYc c))) *
    (Am.chiF (R.N i) (R.N (i + 1)) (ptYc c).deco.1.N (stdLat X.E (R.N (i + 1))))⁻¹

def rhoY' (σ₀ : X.K →+* ℂ) (Am : Amb X) {u : Pr.Word} {m2 : ℕ} (i : ℕ) (c' : (chFY W sel mu cst L u m2 (i + 1)).Cl) : ℂ :=
  (σ₀ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) (ptYc c').deco.1.N (frsF sel mu (ptYc c'))))⁻¹ *
    (Am.chiF (R.N i) (R.N (i + 1)) (stdLat X.E (R.N i)) (ptYc c').deco.1.N)⁻¹

def RhoYUnit (σ₀ : X.K →+* ℂ) (Am : Amb X) (u : Pr.Word) (m2 : ℕ) : Prop :=
  (∀ i, i < R.m → ∀ c : (chFY W sel mu cst L u m2 i).Cl, ‖rhoY Ch σ₀ Am i c‖ = 1) ∧
    ∀ i, i < R.m → ∀ c' : (chFY W sel mu cst L u m2 (i + 1)).Cl, ‖rhoY' Ch σ₀ Am i c'‖ = 1

def _root_.Formalism.L2.Ker.Amb.ChiSplit (Am : Amb X) (a b : ℕ) : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
    Am.chiF a b N N' = Am.chiF a b N (stdLat X.E b) * Am.chiF a b (stdLat X.E a) N'

def ChainArgF.ofChKer (σ₀ : X.K →+* ℂ) (Am : Amb X) (u : Pr.Word) (m2 : ℕ) (hU : RhoYUnit (W := W) (cst := cst) (L := L) Ch σ₀ Am u m2) :
    ChainArgF R (chFY W sel mu cst L u m2) σ₀ where
  rhoDet := rhoY Ch σ₀ Am
  rhoDet' := rhoY' Ch σ₀ Am
  rho_norm := hU.1
  rho'_norm := hU.2
  unf i c c' := unfTh σ₀ Am.cD (thY Ch Am i c c')

def recChainY (σ₀ : X.K →+* ℂ) (Am : Amb X) (u : Pr.Word) (m2 : ℕ) (hU : RhoYUnit (W := W) (cst := cst) (L := L) Ch σ₀ Am u m2)
    (hF : ∀ j, (chFY W sel mu cst L u m2 j).Ok) (D : ℕ) (hD : 0 < D)
    (hdvd : ∀ j, j ≤ R.m → ∀ c : (chFY W sel mu cst L u m2 j).Cl, Nat.card (FamStab (chFY W sel mu cst L u m2 j) c) ∣ D) :
    ColumnChain R X.Tau (W.hc u) :=
  recChainF (W.hc u) (chFY W sel mu cst L u m2) hF σ₀ D hD hdvd (ChainArgF.ofChKer Ch σ₀ Am u m2 hU)

variable {Ch}

end Charts

end Formalism.L2.Col
