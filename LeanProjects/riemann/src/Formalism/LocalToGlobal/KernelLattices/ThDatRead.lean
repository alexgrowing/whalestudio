import Mathlib
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.ColInst
import Formalism.LocalToGlobal.KernelLattices.MatrixKernelDiamondCommutation

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H

open Classical in

def cutDat {X : Fields} {a b : ℕ} (σ : X.K →+* ℂ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (cA : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a))
    (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → X.K) (x : HomE X.E a b) : ℂ :=
  if x ∈ divLat cA (homAt S N N') then σ (Ξ x) else 0

def ThDatCut : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a))
    (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → X.K), A.LaHyp a b S → IsSdLat N → IsSdLat N' → 0 < cA → 0 < cB →
    (∀ x ∈ divLat cA (homAt S N N'), ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x) →
      A.thDat S cA cB N N' Ξ =
        thC (X.embC A.σ₀) A.δ A.d A.sc A.AA S N N' (cA * cB) (cutDat A.σ₀ S cA N N' Ξ) (A.e a b N N')

def ThDatThC : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a))
    (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → X.K), A.LaHyp a b S → IsSdLat N → IsSdLat N' → 0 < cA → 0 < cB →
    (∀ x ∈ divLat cA (homAt S N N'), ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x) →
    (∀ x, x ∉ divLat cA (homAt S N N') → Ξ x = 0) →
      A.thDat S cA cB N N' Ξ =
        thC (X.embC A.σ₀) A.δ A.d A.sc A.AA S N N' (cA * cB) (fun x => A.σ₀ (Ξ x)) (A.e a b N N')

def ThDatRead : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r : KerRead C X) (s : Seam D X) (A : Amb X)
    (i : ℕ) (c : C.cls i) (c' : C.cls (i + 1)) (cA cB : ℕ) (Ξ : HomE X.E (D.R.N i) (D.R.N (i + 1)) → X.K),
    A.LaHyp (D.R.N i) (D.R.N (i + 1)) r.SS → IsSdLat (r.N i c) → IsSdLat (r.N (i + 1) c') → 0 < cA → 0 < cB → r.lev = cA * cB →
    (∀ x, r.Xi i c c' x = A.σ₀ (Ξ x)) →
    (∀ x ∈ divLat cA (homAt r.SS (r.N i c) (r.N (i + 1) c')), ∀ y ∈ mulLat cB (homAt r.SS (r.N i c) (r.N (i + 1) c')), Ξ (x + y) = Ξ x) →
    (∀ x, x ∉ divLat cA (homAt r.SS (r.N i c) (r.N (i + 1) c')) → Ξ x = 0) →
      s.push (A.thDat r.SS cA cB (r.N i c) (r.N (i + 1) c') Ξ) = r.Th s A i c c'

def ThDatReadNat : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r : KerRead C X) (s : Seam D X)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (i : ℕ) (c : C.cls i) (c' : C.cls (i + 1)) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E (D.R.N i))) (N' : Submodule (𝓞 X.E) (Sp X.E (D.R.N (i + 1))))
    (Ξ : HomE X.E (D.R.N i) (D.R.N (i + 1)) → X.K),
    (ambOf s B χ cD : Amb X).LaHyp (D.R.N i) (D.R.N (i + 1)) S → IsSdLat N → IsSdLat N' → 0 < cA → 0 < cB →
    r.SS = S → r.lev = cA * cB → r.N i c = N → r.N (i + 1) c' = N' → (∀ x, r.Xi i c c' x = s.σ₀ (Ξ x)) →
    (∀ x ∈ divLat cA (homAt S N N'), ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x) →
    (∀ x, x ∉ divLat cA (homAt S N N') → Ξ x = 0) →
      s.push ((ambOf s B χ cD : Amb X).thDat S cA cB N N' Ξ) = r.Th s (ambOf s B χ cD) i c c'

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

def ThDatEntry : Prop :=
  ∀ (A : Amb X) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ) (al : L.β i) (be : L.β (i + 1))
    (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1)),
    Pr.Ok → 0 < Pr.T u → L.Ok Ch sel mu cst G m2 → i < m2 → A.LaHyp (R.N i) (R.N (i + 1)) (Sall sel mu u) →
      A.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N p'.deco.1.N (XiEntry Ch sel mu cst L i al be p p') =
        thEntry Ch sel mu cst L (X.embC A.σ₀) A.σ₀ A.δ A.d A.sc A.AA i al be p p' (A.e _ _ p.deco.1.N p'.deco.1.N)

def ThDatCpl1 : Prop :=
  ∀ (A : Amb X) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (al : L.β m2)
    (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))),
    Pr.Ok → 0 < Pr.T u → L.Ok Ch sel mu cst G m2 → A.LaHyp (R.N m2) (R.N (m2 + 1)) (Sall sel mu u) →
      A.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p₀.deco.1.N p.deco.1.N (XiCpl1 Ch sel mu cst L m2 al p₀ p Y) =
        thCpl1 Ch sel mu cst L (X.embC A.σ₀) A.σ₀ A.δ A.d A.sc A.AA m2 al p₀ p Y (A.e _ _ p₀.deco.1.N p.deco.1.N)

def XiCpl2Adm {u : Pr.Word} (m2 : ℕ) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (dd : RowPt Pr R sel mu) : Prop :=
  (∀ x ∈ divLat (cAof sel mu cst) (homAt (Sall sel mu u) p.deco.1.N (tilQ sel mu u dd).1.N),
    ∀ y ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N (tilQ sel mu u dd).1.N),
      XiCpl2 Ch sel mu cst m2 p Y dd (x + y) = XiCpl2 Ch sel mu cst m2 p Y dd x) ∧
  ∀ x, x ∉ divLat (cAof sel mu cst) (homAt (Sall sel mu u) p.deco.1.N (tilQ sel mu u dd).1.N) → XiCpl2 Ch sel mu cst m2 p Y dd x = 0

def ThDatCpl2 : Prop :=
  ∀ (A : Amb X) (m2 : ℕ) (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (dd : RowPt Pr R sel mu),
    0 < Pr.T u → XiCpl2Adm Ch sel mu cst m2 p Y dd → A.LaHyp (R.N (m2 + 1)) (R.N R.m) (Sall sel mu u) →
      A.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (tilQ sel mu u dd).1.N (XiCpl2 Ch sel mu cst m2 p Y dd) =
        thCpl2 Ch sel mu cst (X.embC A.σ₀) A.σ₀ A.δ A.d A.sc A.AA m2 p Y dd (A.e _ _ p.deco.1.N (tilQ sel mu u dd).1.N)

def XiCpl2AdmOf : Prop :=
  ∀ (m2 : ℕ) (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (dd : RowPt Pr R sel mu),
    Pr.Ok → cst.Ok → R.m = m2 + 2 → (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) → PosT sel mu u → Y ∈ ybSet sel mu cst p.deco.1.N →
      XiCpl2Adm Ch sel mu cst m2 p Y dd

def ThDatCpl2Of : Prop :=
  ∀ (A : Amb X) (m2 : ℕ) (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (dd : RowPt Pr R sel mu),
    Pr.Ok → 0 < Pr.T u → cst.Ok → R.m = m2 + 2 → (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) → PosT sel mu u → Y ∈ ybSet sel mu cst p.deco.1.N →
    A.LaHyp (R.N (m2 + 1)) (R.N R.m) (Sall sel mu u) →
      A.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (tilQ sel mu u dd).1.N (XiCpl2 Ch sel mu cst m2 p Y dd) =
        thCpl2 Ch sel mu cst (X.embC A.σ₀) A.σ₀ A.δ A.d A.sc A.AA m2 p Y dd (A.e _ _ p.deco.1.N (tilQ sel mu u dd).1.N)

end Chain

def ReadThDat : Prop :=
  ∀ (D : D7) (X : Fields) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (r : KerRead C X) (s : Seam D X) (A : Amb X)
    (Pr : Primes X) (Ch : Chars X Pr D.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr D.R (QE sel (mu : Chr X.F X.E X.K)))
    (G : ChGlob X D.R.m) (v : Pr.Word) (m2 : ℕ), r.IsChain Ch sel mu cst L A.σ₀ v m2 → Pr.Ok → 0 < Pr.T v → L.Ok Ch sel mu cst G m2 →
    (∀ i, i ≤ m2 → A.LaHyp (D.R.N i) (D.R.N (i + 1)) (Sall sel mu v)) →
    ∃ (pt : ∀ i, i ≤ m2 + 1 → C.cls i → ChPt (R := D.R) sel mu v i) (ix : ∀ i, i ≤ m2 → C.cls i → L.β i)
      (yb : C.cls (m2 + 1) → Set (Sp X.E (D.R.N (m2 + 1)))) (row : C.cls (m2 + 1 + 1) → Option (RowPt Pr D.R sel mu)),
      (∀ i (hi : i ≤ m2 + 1) c, r.N i c = (pt i hi c).deco.1.N) ∧
      (∀ c', yb c' ∈ ybSet sel mu cst (pt (m2 + 1) le_rfl c').deco.1.N) ∧
      (∀ i (hi : i < m2) c c', r.Th s A i c c' = s.push (A.thDat (Sall sel mu v) (cAof sel mu cst) (cBof sel mu cst v)
        (pt i (by omega) c).deco.1.N (pt (i + 1) (by omega) c').deco.1.N
        (XiEntry Ch sel mu cst L i (ix i hi.le c) (ix (i + 1) hi c') (pt i (by omega) c) (pt (i + 1) (by omega) c')))) ∧
      (∀ c c', r.Th s A m2 c c' = s.push (A.thDat (Sall sel mu v) (cAof sel mu cst) (cBof sel mu cst v)
        (pt m2 (Nat.le_succ _) c).deco.1.N (pt (m2 + 1) le_rfl c').deco.1.N
        (XiCpl1 Ch sel mu cst L m2 (ix m2 le_rfl c) (pt m2 (Nat.le_succ _) c) (pt (m2 + 1) le_rfl c') (yb c')))) ∧
      (∀ c' d, row c' = some d → HEq (r.N (m2 + 1 + 1) c') (tilQ sel mu v d).1.N) ∧
      (∀ c c' d, row c' = some d → HEq (r.Xi (m2 + 1) c c') fun x => A.σ₀ (XiCpl2 Ch sel mu cst m2 (pt (m2 + 1) le_rfl c) (yb c) d x)) ∧
      (∀ i, i ≤ m2 + 1 → ∀ c, r.pin i c) ∧ ∀ c', r.pin (m2 + 1 + 1) c' ↔ ∃ d, row c' = some d

end Formalism.L2.Ker
