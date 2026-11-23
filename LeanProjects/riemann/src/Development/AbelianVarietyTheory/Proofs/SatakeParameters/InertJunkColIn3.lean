import Mathlib
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotGoodGenericSign

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory.Hk3

theorem inertJunk_iff {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {m : ℕ}
    (A3 : FamIn3 K G Pl0 I0 (List ℕ) T m) :
    InertJunk A3 ↔
      ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨
          ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧
        ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨
          ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) :=
  ⟨fun h => ⟨fun t k => h.R t k.1 k.2, fun j t k => h.L j t k.1 k.2⟩,
    fun h => ⟨fun t Q s => h.1 t (Q, s), fun j t Q s => h.2 j t (Q, s)⟩⟩

theorem inertJunk_colIn3 {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
    (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
    (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
    (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
    (trIv : Fin R.m → (Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) :
    InertJunk (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv) :=
  FamModel.inertJunk_col W Ch sel hX v0 TU Xg S0 xiVal trIv

end GlobalTheory.Hk3
