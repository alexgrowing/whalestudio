import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult

namespace GlobalTheory.IndefiniteRowSideFullHecke.CharacterMatchingGaps

def Gap (D : D7) : Prop :=
  ∀ (τ : D.what₂.Tau) (n : ℕ), n + 1 < D.R.r →
    (D.R.r : ℚ) ≤ Formalism.L2.NTheta.lamAt (D.hc τ) n - Formalism.L2.NTheta.lamAt (D.hc τ) (n + 1)

def finS (D : D7) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  primesOf ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F)

abbrev EigSys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

def EEc (P : LevelP R.Pg D.R.r ℂ) (c : EigSys D) : Submodule ℂ (MMap (R.MY 0)) :=
  partDual R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) (finS D) c ⊓ R.EEat P

def Wc' (i : Fin D.R.m) (P : LevelP R.Pg D.R.r ℂ) (c : EigSys D) : Submodule ℂ (MMap (R.MW i (sg0 D A))) :=
  partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P)) (finS D) c ⊓
    R.Wat i (sg0 D A) P

def MatchAt (P P' : LevelP R.Pg D.R.r ℂ) : Prop :=
  ∀ (i : Fin D.R.m) (c : EigSys D),
    FiniteDimensional ℂ (EEc R P c) ∧ FiniteDimensional ℂ (Wc' R i P' c) ∧
      Module.finrank ℂ (EEc R P c) = Module.finrank ℂ (Wc' R i P' c)

def MatchAll : Prop :=
  MatchAt R R.triv R.triv ∧ ∀ b : Bool, MatchAt R (R.levR F b) (R.levL F b (sg0 D A))

end

def PartsMatch : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    Gap D → GlobalTheory.GLq.ESerTie D → R.toLevCh.Is A.μ0 → R.IsGrp F → IsInfFam R.θ → MatchAll R F

def PartsMatchChar : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    Gap D → GlobalTheory.GLq.ESerTie D → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsChain → R.IsThP → R.IsScal F →
      MatchAll R F

theorem PartsMatch.char (h : PartsMatch) : PartsMatchChar :=
  fun D G _ _ Pl0 T A Ks _ _ _ R F hg he hl hG _ hM _ _ _ => h D G Pl0 T A Ks R F hg he hl hG hM.inf

theorem mem_finS (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    v ∈ finS D ↔ ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  unfold finS
  rw [mem_primesOf]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  exact_mod_cast mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

end GlobalTheory.IndefiniteRowSideFullHecke.CharacterMatchingGaps

end
