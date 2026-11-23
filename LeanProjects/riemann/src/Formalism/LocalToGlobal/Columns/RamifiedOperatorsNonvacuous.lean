import Mathlib
import Formalism.LocalToGlobal.Columns.KernelArgumentHypothesisScalar
import Formalism.LocalToGlobal.Columns.BtExistsSmulLeOfFg
import Formalism.LocalToGlobal.Columns.AtTOwedV
import Formalism.LocalToGlobal.Columns.AtTOwedC
import Formalism.LocalToGlobal.Columns.LocWLemmas
import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Formalism.LocalToGlobal.Columns.Inputs
import Formalism.GL3MeanSquares.PrimeOrderRamificationResults
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
  {V' : Type} [AddCommGroup V'] [Module K V']

end Gen

section LemC

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end LemC

section Det

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Det

section T5

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

variable [Nonempty X.Tau]

end T5

section Nab

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Nab

section Col

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}

theorem list_prod_intertwines {K : Type} [Field K] {V V' ι : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    (k : V →ₗ[K] V') (A : ι → Module.End K V) (A' : ι → Module.End K V') (c : ι → K)
    (h : ∀ i, (A' i).comp k = c i • k.comp (A i)) (l : List ι) :
    ((l.map A').prod).comp k = (l.map c).prod • k.comp (l.map A).prod := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, one_smul]; rfl
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    have e1 : (A' i * (l.map A').prod).comp k = (A' i).comp (((l.map A').prod).comp k) := rfl
    rw [e1, ih, LinearMap.comp_smul, ← LinearMap.comp_assoc, h i, LinearMap.smul_comp, smul_smul, mul_comm (l.map c).prod]
    rfl

theorem KernelArgumentHypothesisScalar.prod {u : Pr.Word} {kk : KerArg W Ch u} {c : ℕ → {P // P ∈ Pr.vT u} → X.Kˣ} (h : KernelArgumentHypothesisScalar kk c) (w : HeightOneSpectrum (𝓞 X.K))
    (j : ℕ) (hj : j < R.m) :
    (UprodC W Ch u (j + 1) w).comp (kk j) = ((cProdC W c w j : X.Kˣ) : X.K) • (kk j).comp (UprodC W Ch u j w) := by
  have := list_prod_intertwines (kk j) (fun P => UOp W Ch u j P) (fun P => UOp W Ch u (j + 1) P) (fun P => ((c j P : X.Kˣ) : X.K))
    (fun P => h j hj P) (VVTc W u w).toList
  unfold UprodC cProdC
  rw [this, Units.coe_prod, Finset.prod_map_toList]

end Col

section NonDeg

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

theorem VVTc_nonempty (hPr : Pr.Ok) {u : Pr.Word} {w : HeightOneSpectrum (𝓞 X.K)} (hw : seenC Pr u w) (ht : W.tops.Nonempty) :
    (VVTc W u w).Nonempty := by
  obtain ⟨τ, hτ⟩ := ht
  exact ⟨⟨pullW τ w, (seenC_iff hPr u w).1 hw τ⟩, (mem_VVTc W u w _).2 ⟨τ, by rw [topsP_of_seenC W hPr u w hw]; exact hτ, rfl⟩⟩

end NonDeg

section AutomorphicFormsHyp

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end AutomorphicFormsHyp

section Price

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Price

section Vals

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

end Vals

namespace GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

end GSD

section ValsCol

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end ValsCol

end Formalism.L2.Col
