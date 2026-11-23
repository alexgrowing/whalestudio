import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimeImpliesPlacesSplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimePlaceCmTypeConjugate
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CmHalfTypePlacesMeetConjugatePairsAndCount
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitPlacesDeclarationSplitRowPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatePlaces

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes
open GlobalTheory.SplitRowProbe GlobalTheory.SplitType GlobalTheory.SplitDecl

namespace UpperTheory.N

theorem place_type_conj (D : D7) (i : D.nd.Loc) (h2 : D.nd.l i ≠ 2) (hj : jacobiSym (-(D.host.d : ℤ)) (D.nd.l i) = 1)
    (w w' : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (hw' : w' ∈ placesOver D.host.E (D.nd.l i)) (hc : IsConjPl D.host w w') :
    (PlIn (N := D.nd) D.nbr i true w hw ∧ PlIn (N := D.nd) D.nbr i false w' hw') ∨
      (PlIn (N := D.nd) D.nbr i false w hw ∧ PlIn (N := D.nd) D.nbr i true w' hw') := by
  obtain ⟨s, hs, hn⟩ := exists_sqrt (D.nd.l i) D.host.d h2 hj
  obtain ⟨s₀, hs₀, h₀⟩ := exists_root
    ((algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).comp (algebraMap ℤ_[D.nd.l i] (D.nd.O i))) hs
    (map_sqrt_sq D.host ((D.nd.embK i).comp D.embE))
  have hs0 : s₀ ^ 2 = -(D.host.d : ℤ_[D.nd.l i]) := by rcases hs₀ with rfl | rfl <;> simp [hs]
  have hn0 : ‖2 * s₀‖ = 1 := by rcases hs₀ with rfl | rfl <;> simpa using hn
  have hne : s₀ ≠ -s₀ := fun e => by
    rw [show 2 * s₀ = 0 by linear_combination e] at hn0
    simp at hn0
  have key : ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.nd.l i)),
      ∃ t : ℤ_[D.nd.l i], algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
        (D.nbr i v hv).j (algebraMap D.host.E D.nd.Om (D.host.sqd)) ∧
        ((t = s₀ ∧ PlIn (N := D.nd) D.nbr i true v hv) ∨ (t = -s₀ ∧ PlIn (N := D.nd) D.nbr i false v hv)) := by
    intro v hv
    obtain ⟨t, ht, h⟩ := exists_root
      ((algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i))).comp PadicInt.Coe.ringHom) hs0
      (map_sqrt_sq D.host ((D.nbr i v hv).j.comp (algebraMap D.host.E D.nd.Om)))
    refine ⟨t, h, ?_⟩
    rcases ht with ht | ht
    · refine Or.inl ⟨ht, nonempty_emb D i v hv, fun τ => ?_⟩
      rcases embIn_xor D i v hv τ with e | e
      · exact e.1
      · exact absurd (ht.symm.trans ((root_of_embIn D i v hv h₀ h τ).2 e.1)) hne
    · refine Or.inr ⟨ht, nonempty_emb D i v hv, fun τ => ?_⟩
      rcases embIn_xor D i v hv τ with e | e
      · exact absurd (((root_of_embIn D i v hv h₀ h τ).1 e.1).symm.trans ht) hne
      · exact e.1
  obtain ⟨t, ht, h⟩ := key w hw
  obtain ⟨t', ht', h'⟩ := key w' hw'
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rcases h' with ⟨e, h'⟩ | ⟨e, h'⟩
  · exact (root_ne D i w w' hw hw' hc hn0 ht (e ▸ ht')).elim
  · exact Or.inl ⟨h, h'⟩
  · exact Or.inr ⟨h, h'⟩
  · exact (root_ne D i w w' hw hw' hc (by simpa using hn0) ht (e ▸ ht')).elim

theorem columns_xor (D : D7) (i : D.nd.Loc) (h2 : D.nd.l i ≠ 2) (hj : jacobiSym (-(D.host.d : ℤ)) (D.nd.l i) = 1) (s : Bool) :
    ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ w', IsConjPl D.host w w' →
      Xor' (w ∈ columns (N := D.nd) D.nbr i s) (w' ∈ columns (N := D.nd) D.nbr i s) := by
  intro w hw w' h
  have hw' := GlobalTheory.SplitCount.mem_placesOver_of_conj D.host hw h
  have n1 := GlobalTheory.SplitRowProbe.not_both_columns D i w hw
  have n2 := GlobalTheory.SplitRowProbe.not_both_columns D i w' hw'
  rcases place_type_conj D i h2 hj w w' hw hw' h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases s
  · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h1, h3⟩⟩
  · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h3, h2⟩⟩
  · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h2, h3⟩⟩
  · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h3, h1⟩⟩

theorem decl_split (D : D7) (i : D.nd.Loc) (h2 : D.nd.l i ≠ 2) (hj : jacobiSym (-(D.host.d : ℤ)) (D.nd.l i) = 1) (ep : Bool) :
    (∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc ep) ∧ EmbeddingTypes.ambTypeD (D := D) i ep := by
  have hl : D.nd.l i ≠ 0 := (D.nd.lPrime i).out.ne_zero
  have hx := columns_xor D i h2 hj ep
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
    rcases place_type_conj D i h2 hj u w hu hw hc with ⟨hpu, hpw⟩ | ⟨hpu, hpw⟩ <;> cases ep
    · obtain ⟨τ⟩ := hpu.1
      exact hnb u hu τ ⟨hpu.2 τ, hUin τ⟩
    · exact hnb w hw τ₀ ⟨hwin, hpw.2 τ₀⟩
    · exact hnb w hw τ₀ ⟨hpw.2 τ₀, hwin⟩
    · obtain ⟨τ⟩ := hpu.1
      exact hnb u hu τ ⟨hUin τ, hpu.2 τ⟩

end UpperTheory.N

end
