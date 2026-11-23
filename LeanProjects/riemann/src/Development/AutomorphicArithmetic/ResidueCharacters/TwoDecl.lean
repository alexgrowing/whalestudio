import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Development.AutomorphicArithmetic.ResidueCharacters.TwoRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimeImpliesPlacesSplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CmHalfTypePlacesMeetConjugatePairsAndCount
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitPlacesDeclarationSplitRowPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatePlaces

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes
open GlobalTheory.SplitRowProbe GlobalTheory.SplitType GlobalTheory.SplitDecl

namespace UpperTheory.N.Two

theorem columns_xor (D : D7) (i : D.nd.Loc) (h2 : D.nd.l i = 2) (s : Bool) :
    ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ w', IsConjPl D.host w w' →
      Xor' (w ∈ columns (N := D.nd) D.nbr i s) (w' ∈ columns (N := D.nd) D.nbr i s) := by
  intro w hw w' h
  have hw' := GlobalTheory.SplitCount.mem_placesOver_of_conj D.host hw h
  have n1 := GlobalTheory.SplitRowProbe.not_both_columns D i w hw
  have n2 := GlobalTheory.SplitRowProbe.not_both_columns D i w' hw'
  rcases Two.place_type_conj D i h2 w w' hw hw' h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases s
  · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h1, h3⟩⟩
  · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h3, h2⟩⟩
  · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h2, h3⟩⟩
  · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h3, h1⟩⟩

theorem decl_split (D : D7) (i : D.nd.Loc) (h2 : D.nd.l i = 2) (ep : Bool) :
    (∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc ep) ∧ EmbeddingTypes.ambTypeD (D := D) i ep := by
  have hl : D.nd.l i ≠ 0 := (D.nd.lPrime i).out.ne_zero
  have hx := columns_xor D i h2 ep
  refine ⟨⟨decl D i hl ep, ?_, ?_⟩, ?_⟩
  · intro v hv
    rw [mem_col, plTypeUe_iff]
    exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hv, hv, h⟩⟩
  · intro v
    rw [mem_row]
    constructor
    · rintro ⟨hv, hnc⟩
      obtain ⟨v', hv', hc⟩ := GlobalTheory.SplitPlaces.exists_conjPl D.host _ v hv
      have hv'c : v' ∈ columns (N := D.nd) D.nbr i ep := by
        rcases hx v hv v' hc with h | h
        · exact absurd h.1 hnc
        · exact h.1
      exact ⟨v', (mem_col D i hl ep v').2 ⟨hv', hv'c⟩, GlobalTheory.Proof.ConjugatePlaces.isConjPl_symm hc⟩
    · rintro ⟨u, hu, hc⟩
      obtain ⟨hu, huc⟩ := (mem_col D i hl ep u).1 hu
      refine ⟨GlobalTheory.SplitCount.mem_placesOver_of_conj D.host hu hc, fun hvc => ?_⟩
      rcases hx u hu v hc with h | h
      · exact h.2 hvc
      · exact h.2 huc
  · intro u hu hU w hw hc τ₀ hτ
    have hnb : ∀ v hv τ, ¬ (EmbIn (N := D.nd) D.nbr i true v hv τ ∧ EmbIn (N := D.nd) D.nbr i false v hv τ) := by
      rintro v hv τ ⟨a, b⟩
      rcases embIn_xor D i v hv τ with h | h
      · exact h.2 b
      · exact h.2 a
    have hUin : ∀ τ, EmbIn (N := D.nd) D.nbr i ep u hu τ := fun τ => (embTypeUe_iff ep τ).1 (hU τ)
    have hwin : EmbIn (N := D.nd) D.nbr i ep w hw τ₀ := (embTypeUe_iff ep τ₀).1 hτ
    rcases Two.place_type_conj D i h2 u w hu hw hc with ⟨hpu, hpw⟩ | ⟨hpu, hpw⟩ <;> cases ep
    · obtain ⟨τ⟩ := hpu.1
      exact hnb u hu τ ⟨hpu.2 τ, hUin τ⟩
    · exact hnb w hw τ₀ ⟨hwin, hpw.2 τ₀⟩
    · exact hnb w hw τ₀ ⟨hpw.2 τ₀, hwin⟩
    · obtain ⟨τ⟩ := hpu.1
      exact hnb u hu τ ⟨hUin τ, hpu.2 τ⟩

end UpperTheory.N.Two

end
