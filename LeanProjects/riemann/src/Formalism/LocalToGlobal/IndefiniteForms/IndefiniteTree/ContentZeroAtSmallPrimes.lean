import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCondPf

open Module NumberField IsDedekindDomain

namespace Formalism.L2.Indef.Tree.DepthCond

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}

theorem content_zero_at_small_primes (N : IndefNum Bs) (O : OnObj S P c) (Nd : NumDatum) (ι : Bs.J → ℕ)
    (hPg : LeafPage O) (tF : ContentEqualsDatumContent N Nd ι) (tP : TiePrimes O Nd) :
    ∀ w : HeightOneSpectrum (𝓞 K), plc w ∈ O.sm → ∀ j, N.F0 w j = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hg1t, hg2t, -, -, -⟩ := hPg
  obtain ⟨hg1, hg2, -, -, hsm⟩ := tP
  intro w h2 j
  rw [tF w j]
  show Nd.FjP (ι j) (plc w) = 0
  apply (content_prime_condition_holds Nd (ι j) (plc w)).2.1
  · rw [← hg1]; exact fun h => hg1t (h ▸ h2)
  · rw [← hg2]; exact fun h => hg2t (h ▸ h2)
  · exact Or.inl (hsm ▸ h2)

end Formalism.L2.Indef.Tree.DepthCond
