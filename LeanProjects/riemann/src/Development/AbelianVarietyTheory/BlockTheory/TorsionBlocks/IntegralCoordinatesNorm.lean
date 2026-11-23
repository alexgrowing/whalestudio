import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.IntegralLeaf.LeafINTFree
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.ArchimedeanLeaf.LeafARCHFree

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts (NonArchimedeanDefectBound ArchimedeanHeightBound)

namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralCoordinatesNorm

def del_vw {K : Type} [Field K] [NumberField K] (S : Finset ℕ) (del_vp : ℕ → ℝ) (w : Formalism.PairingDivisionLocalBalance.Pl K) : ℝ :=
  ∑ l ∈ S, del_vp l * (Formalism.DivisionValues.vw w (l : K) : ℝ)

def bInt (C : ℝ) (f N : ℕ) (B L : ℝ) (Q : ℕ) : ℝ :=
  C * f * (2 * (N : ℝ)) * Real.log ((f : ℝ) * (2 * (N : ℝ))) + C * f * (2 * (N : ℝ)) * B * L +
    C * f * (2 * (N : ℝ)) ^ 2 * B * Real.log Q

def bArch (C : ℝ) (f N : ℕ) (B L : ℝ) (Q : ℕ) : ℝ :=
  C * f * (2 * (N : ℝ)) * B * (L + Real.log (B * (2 * (N : ℝ)))) +
    C * f * (N : ℝ) ^ 2 * (L + Real.log ((f : ℝ) * (2 * (N : ℝ)) * B)) + C * (N : ℝ) ^ 2 * Real.log Q

def Curve (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) : Prop :=
  Crv D cc δ ∧ GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0

def IsNorm (D : D7) (A : Set (Ideal (𝓞 D.host.K))) (N : ℕ) (B : ℝ) (Q : ℕ) (x : ℂ) : Prop :=
  ∃ cc ∈ A, ∃ δ t0 : ℂ, Curve D cc δ t0 ∧ ∃ P : Pair D cc δ t0 Q, P.Small N B ∧ x = (P.norm : ℂ)

def Sizes (D : D7) (N : ℕ) (B L : ℝ) (Q : ℕ) : Prop :=
  1 ≤ N ∧ 1 ≤ B ∧ GoodLevel D Q ∧ Real.log D.host.rdE ≤ L

def Del (S : Finset ℕ) (del_vp : ℕ → ℝ) (b : ℝ) : Prop :=
  (∀ l ∈ S, l.Prime) ∧ (∀ l, 0 ≤ del_vp l) ∧ (∀ l, l ∉ S → del_vp l = 0) ∧ ∑ l ∈ S, del_vp l * Real.log l ≤ b

def NormsInt (D : D7) (A : Set (Ideal (𝓞 D.host.K))) (N : ℕ) (B : ℝ) (Q : ℕ) (S : Finset ℕ) (del_vp : ℕ → ℝ) (b : ℝ) :
    Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (emb : K →+* ℂ) (ι : Type) (zA zA' : ι → K),
    (∀ ij, IsNorm D A N B Q (emb (zA ij)) ∧ IsNorm D A N B Q (emb (zA' ij))) →
    (∀ ij, zA ij ≠ 0 ∧ zA' ij ≠ 0) →
    NonArchimedeanDefectBound (del_vw S del_vp) zA zA' b

def IntOver (D : D7) {N : ℕ} (l : ℕ) (h : GA D N) : Prop :=
  ∃ k ∈ intG D N, TrivAt D l ((h * k⁻¹ : GA D N) : GL (Fin N) (AE D))

def CoordsInt (D : D7) (A : Set (Ideal (𝓞 D.host.K))) (N : ℕ) (B : ℝ) (Q : ℕ) (del_vp : ℕ → ℝ) : Prop :=
  ∀ cc ∈ A, ∀ δ t0 : ℂ, Curve D cc δ t0 → ∀ (l : ℕ) [Fact l.Prime], Nat.Coprime (Ideal.absNorm cc) l →
    ∀ Q' : ℕ, GoodLevel D Q' → Nat.Coprime Q' l → ∀ P : Pair D cc δ t0 (Q * Q'), P.Small N B →
      (∀ h : GA D P.d, ∃ γ ∈ ratG D P.d, ∃ j ∈ P.J, IntOver D l (γ * h * j)) ∧
      (∀ h : GA D P.d, gam D P.J h ≠ 0 ∧ (padicValNat l (gam D P.J h) : ℝ) ≤ del_vp l) ∧
      ∀ h : GA D P.d, IntOver D l h → ∀ T, ∃ hz : P.coord h T ∈ Qbar,
        ∀ lam : Qbar →+* ℂ_[l], ‖lam ⟨P.coord h T, hz⟩‖ ≤ (l : ℝ) ^ del_vp l

def IntUnder (H : D7 → Prop) (A : ∀ D : D7, Set (Ideal (𝓞 D.host.K))) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ D : D7, H D → ∀ (N : ℕ) (B L : ℝ) (Q : ℕ), Sizes D N B L Q →
    ∃ (S : Finset ℕ) (del_vp : ℕ → ℝ), Del S del_vp (bInt C (fF D) N B L Q) ∧
      NormsInt D (A D) N B Q S del_vp (bInt C (fF D) N B L Q)

def IntFullUnder (H : D7 → Prop) (A : ∀ D : D7, Set (Ideal (𝓞 D.host.K))) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ D : D7, H D → ∀ (N : ℕ) (B L : ℝ) (Q : ℕ), Sizes D N B L Q →
    ∃ (S : Finset ℕ) (del_vp : ℕ → ℝ), Del S del_vp (bInt C (fF D) N B L Q) ∧
      CoordsInt D (A D) N B Q del_vp ∧ NormsInt D (A D) N B Q S del_vp (bInt C (fF D) N B L Q)

def ArchUnder (H : D7 → Prop) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ D : D7, H D → ∀ (N : ℕ) (B L : ℝ) (Q : ℕ), Sizes D N B L Q →
    Real.log D.host.d ≤ L → |logDerivativeAtOne D| ≤ L →
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (emb : K →+* ℂ) (ι : Type) (zA zA' : ι → K),
      (∀ ij, IsNorm D Set.univ N B Q (emb (zA ij)) ∧ IsNorm D Set.univ N B Q (emb (zA' ij))) →
      ArchimedeanHeightBound zA zA' (bArch C (fF D) N B L Q)

def INT : Prop := IntUnder (fun _ => True) (fun _ => {⊤})

def INTFull : Prop := IntFullUnder (fun _ => True) (fun _ => {⊤})

def INTAll : Prop := IntUnder (fun _ => True) (fun _ => Set.univ)

def ARCH : Prop := ArchUnder (fun _ => True)

def NormAlg : Prop :=
  ∀ (D : D7) (N : ℕ) (B : ℝ) (Q : ℕ) (x : ℂ), GoodLevel D Q → IsNorm D Set.univ N B Q x → x ∈ Qbar

def IntArch : Prop := INT ∧ ARCH

theorem IntUnder.mono {H H' : D7 → Prop} {A A' : ∀ D : D7, Set (Ideal (𝓞 D.host.K))} (hH : ∀ D, H' D → H D)
    (hA : ∀ D, A' D ⊆ A D) (h : IntUnder H A) : IntUnder H' A' := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, fun D hD N B L Q hs => ?_⟩
  obtain ⟨S, dl, h1, h2⟩ := h D (hH D hD) N B L Q hs
  refine ⟨S, dl, h1, fun K _ _ emb ι zA zA' hn hz => h2 K emb ι zA zA' (fun ij => ?_) hz⟩
  obtain ⟨⟨c, hc, r⟩, ⟨c', hc', r'⟩⟩ := hn ij
  exact ⟨⟨c, hA D hc, r⟩, ⟨c', hA D hc', r'⟩⟩

theorem ArchUnder.mono {H H' : D7 → Prop} (hH : ∀ D, H' D → H D) (h : ArchUnder H) : ArchUnder H' := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C, hC, fun D hD => h D (hH D hD)⟩

end GlobalTheory.IndefiniteRowSideFullHecke.IntegralCoordinatesNorm
