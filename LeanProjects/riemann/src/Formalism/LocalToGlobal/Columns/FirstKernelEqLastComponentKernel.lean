import Formalism.LocalToGlobal.Columns.GFamEv
import Formalism.LocalToGlobal.Columns.StabMapRLInjective
import Formalism.LocalToGlobal.Columns.RefLevChFstSurjective
import Formalism.LocalToGlobal.Columns.RecChainYUnfPol
import Mathlib

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Defs

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (m2 : ℕ) (al : ∀ j, j ≤ m2 + 1 → L.β j) (Am : Amb X) (u : Pr.Word)

variable {W Λ u} in

def rcol1To (kk : ∀ i, ClsKer (stepGSD W Λ u i) (stepGSD W Λ u (i + 1))) (hX : X.Ok) :
    ∀ j, (stepGSD W Λ u 0).EqFun →ₗ[X.K] (stepGSD W Λ u j).EqFun
  | 0 => LinearMap.id
  | j + 1 => (kk j).op (stepOk W Λ hX u j) ∘ₗ rcol1To kk hX j

def rcol1Start (h0 : Λ 0 = colLev Ch 0) : MfV W Ch u →ₗ[X.K] (stepGSD W Λ u 0).EqFun where
  toFun φ := ⟨φ.1, show φ.1 ∈ (formGSD (colVal W u 0 (Pr.vT u) Pr.vGs) (Λ 0)).EqFun by rw [h0]; exact φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def OneYbKer : Prop :=
  ∀ (a : L.β m2) (q₀ : ChPt (R := R) sel mu u m2) (q : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))),
    Y ∈ ybSet sel mu cst q.deco.1.N → Y ≠ q.deco.1.y0 R.k → cp1K W Ch sel mu cst L (chTh W Ch sel mu cst Am u m2) a q₀ q Y = 0

include hQ in
theorem rcol_rowSG_eq : Pr.vGs = rowSG Pr sel mu := by
  classical
  unfold rowSG uSG
  rw [hQ, Finset.union_empty]

def rcolRow {n : ℕ} (d : DecoSet X.E n ∅ Pr.vGs) : DecoSet X.E n ∅ (rowSG Pr sel mu) := rcol_rowSG_eq sel mu hQ ▸ d

def basisCoordinatesModPlace (Pr : Primes X) (R : Ranks) (n : ℕ) : ∀ w : Pr.vGs, Fin n → 𝓞 X.E ⧸ w.1.asIdeal := fun w => Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) n R.k

end Defs

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {hQ : QE sel (mu : Chr X.F X.E X.K) = ∅} {m2 : ℕ} {al : ∀ j, j ≤ m2 + 1 → L.β j} {Am : Amb X} {u : Pr.Word}
  (hX : X.Ok) {Gc : ChGlob X R.m} (hL : L.Ok Ch sel mu cst Gc m2) (h0 : Λ 0 = colLev Ch 0)
  (hΛ : ∀ j, j ≤ m2 + 1 → ∀ b : L.β j, L.levG j b = Λ j) (h1 : ∀ j, j ≤ m2 + 1 → ∀ b b' : L.β j, b = b')
  (hE : XiEquiv W Λ Ch sel mu cst Am u (refXi1 Ch sel mu cst L hQ m2 al u))
  {b₁ : L.β (m2 + 1)} {hY : YbHyp (R := R) sel mu cst L u m2 b₁} {P : LevFam X.E X.K R.r Pr.vGs}
  (hK : KerEquivC W Ch sel mu cst L Am u m2 b₁ hY P) (hF : ∀ j, (chF W sel mu L u j).Ok)
  (φ : MfV W Ch u)

abbrev rcol1Rec (j : ℕ) : (stepGSD W Λ u j).EqFun := rcol1To (xiKK hE) hX j (rcol1Start W Λ Ch u h0 φ)

end Main

end Formalism.L2.Col
