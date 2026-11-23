import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.SplitOutPlace

set_option maxHeartbeats 1000000 in

theorem not_mem_gPl_qPl : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C) (Pl : PlSide D) (M : MtFam D) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec Pl M C big X T) (i : X.nd.Loc) (w : PlE D.host) (s : SplitPlace D.host.E), SplitOut X.nd i w → IsConjPl D.host w s.w → s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩) := by
  intro D cf C tp Pl M big X T Sp i w s hso hc hmem
  obtain ⟨-, hl, hS, hQ⟩ := hso

  have hp : ∀ (w' : PlE D.host), NG.OverPl w' s.v → ∀ p : ℕ, w' ∈ placesOver D.host.E p →
      w ∈ placesOver D.host.E p := by
    intro w' hover p hp
    have h1 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        w'.asIdeal := by rw [map_natCast]; exact hp
    have h2 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
      rw [← hover]; exact h1
    have h3 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        s.w.asIdeal := by
      rw [← Ideal.mem_comap, s.w_under]; exact h2
    rw [map_natCast] at h3
    exact (hc (p : 𝓞 D.host.E) (p : 𝓞 D.host.E) (by simp)).2 h3
  have hi : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i) := (X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  have hg : s.v ∉ gPl D := by
    rintro ⟨w', hover, k, hk⟩
    apply hS
    refine (X.nd.S_def i w).2 ⟨?_, hl⟩
    have hw := hp w' hover _ hk
    fin_cases k
    · exact Or.inl hw
    · exact Or.inr (Or.inl hw)
  rcases hmem with hm | hm
  · exact hg hm
  obtain ⟨w', hover, hw'⟩ := GlobalTheory.FitHecke.qPl_sub tp (X.nd.w i) (X.nd.w_tw i)
    ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩ hm
  rcases hw' with hCQ | hpd
  · apply hQ
    rw [← Sp.Qc_eq (X.nd.j i) (X.nd.w i)] at hCQ
    have hsw : s.w ∈ Sp.B.Qc (X.nd.j i) (X.nd.w i) :=
      Sp.B.Qc_over (X.nd.j i) (X.nd.w i) w' s.w hCQ ⟨s.v, hover, s.w_under⟩
    rw [Sp.Q_eq _ _ i hi]
    exact Sp.B.Qc_conj (X.nd.j i) (X.nd.w i) w s.w hsw hc
  · apply hS
    refine (X.nd.S_def i w).2 ⟨?_, hl⟩
    rw [X.nd.w_l i] at hpd
    exact Or.inr (Or.inr (hp w' hover _ hpd))

end GlobalTheory.SplitOutPlace
