import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf Formalism.MainNotions.PairedCharacterCondition
open scoped TensorProduct

namespace GlobalTheory.PendOf.CenKey

theorem stable (D : D7) (i : D.nd.Loc) (h : OnMtPreservesTypeV D) (c : MonoidAlgebra ℂ (G0g D.nd))
    (s : Set (D.naut.AV i)) (F : D.what₂.Mt (D.nd.mu i) (D.nd.j i))
    (hF : F ∈ ⨆ P ∈ s, D.naut.typeV i P) :
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c F ∈ ⨆ P ∈ s, D.naut.typeV i P := by
  have : (⨆ P ∈ s, D.naut.typeV i P) ≤
      (⨆ P ∈ s, D.naut.typeV i P).comap (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c) := by
    refine iSup₂_le fun P hP G hG => ?_
    exact le_biSup (D.naut.typeV i) hP (h i P c G hG)
  exact this hF

theorem phi_mem (D : D7) (i : D.nd.Loc) (S : Sec D i)
    (u : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) :
    S.Φ u ∈ ⨆ P ∈ {P | D.naut.ptV i P ≠ none}, D.naut.typeV i P := by
  have hu : u ∈ ⨆ x, heckeEig (D.nd.T i) (D.nd.act i) x := by
    rw [Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.EigSpan_holds D.nd i]; exact Submodule.mem_top
  induction hu using Submodule.iSup_induction' with
  | mem x u hu =>
    have hle : typeSum D i (some x) ≤ ⨆ P ∈ {P | D.naut.ptV i P ≠ none}, D.naut.typeV i P := by
      refine iSup₂_le fun P hP => ?_
      have hP' : D.naut.ptV i P = some x := hP
      exact le_biSup (D.naut.typeV i)
        (show P ∈ {P | D.naut.ptV i P ≠ none} from by simp [hP'])
    exact hle (S.eig x u hu)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb

theorem phi_onMt : ∀ (D : D7) (i : D.nd.Loc) (S : Sec D i), OnMtPreservesTypeV D →
    ∀ (c : MonoidAlgebra ℂ (G0g D.nd)) (x y : D.what₂.MtL (D.nd.mu i) (D.nd.j i)),
    D.what₂.jMt _ _ y = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (D.what₂.jMt _ _ x) →
    S.Φ (D.nd.prMt i y) = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (S.Φ (D.nd.prMt i x)) := by
  intro D i S h c x y hxy
  have hd : Disjoint (⨆ P ∈ {P | D.naut.ptV i P ≠ none}, D.naut.typeV i P)
      (⨆ P ∈ {P | D.naut.ptV i P = none}, D.naut.typeV i P) :=
    (D.naut.typeV_indep i).disjoint_biSup_biSup
      (Set.disjoint_left.2 fun P h1 h2 => h1 h2)
  have h1 := Submodule.sub_mem _ (phi_mem D i S (D.nd.prMt i y))
    (stable D i h c _ _ (phi_mem D i S (D.nd.prMt i x)))
  have h2 := Submodule.sub_mem _ (stable D i h c {P | D.naut.ptV i P = none} _ (S.split x)) (S.split y)
  have e : D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (D.what₂.jMt _ _ x - S.Φ (D.nd.prMt i x)) -
      (D.what₂.jMt _ _ y - S.Φ (D.nd.prMt i y)) =
      S.Φ (D.nd.prMt i y) - D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (S.Φ (D.nd.prMt i x)) := by
    rw [map_sub, hxy]; abel
  rw [e] at h2
  exact sub_eq_zero.1 (Submodule.disjoint_def.1 hd _ h1 h2)

end GlobalTheory.PendOf.CenKey
