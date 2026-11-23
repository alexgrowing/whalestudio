import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LenCob
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_cyclotomic_block_cocycles_le_sha : ∀ (D : D7) (i : D.nd.Loc) (c : ℕ) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) 1)), C ≤ Z1 (WKG (chiRatO D.nd i c)) → 2 ≤ c → c ≤ D.R.t → (∀ f ∈ C, ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), locFun i (chiRatO D.nd i c) w hw f ∈ BD (Br.locLat D.nbr i w hw (chiRatO D.nd i c))) → (∀ v, v ∉ placesOver D.host.E (D.nd.l i) → resIne i C v = ⊥) → Module.length (D.nd.O i) ↥C ≤ lenCob i (chiRatO D.nd i c) (C) + lenQ i ((D.nd.l i : ℕ) : D.nd.O i) * Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) ((c - 1 : ℕ) : ℤ) := by
  first | exact @GlobalTheory.Cut.ShaBound.main | exact GlobalTheory.Cut.ShaBound.main | (intros; apply GlobalTheory.Cut.ShaBound.main <;> assumption)
