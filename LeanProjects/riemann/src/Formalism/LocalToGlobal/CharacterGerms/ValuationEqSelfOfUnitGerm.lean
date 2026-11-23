import Formalism.LocalToGlobal.CharacterGerms.GermLiftSelfSt

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

namespace VP

theorem cc_mvExp' {σ : Type} (h : MvPowerSeries σ C) : MvPowerSeries.constantCoeff (mvExp h) = 1 := by
  show (∑ k ∈ Finset.range ((0 : σ →₀ ℕ).degree + 1), MvPowerSeries.coeff 0 (h ^ k) / (k.factorial : C)) = 1
  simp

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o))

theorem pullback_two_var_mul (F G : PS C 2 dd) : pull2 Y p (F * G) = pull2 Y p F * pull2 Y p G := by
  unfold pull2
  exact linPull_mul _ _ F G

theorem pullback_two_var_prod {ι : Type} (s : Finset ι) (F : ι → PS C 2 dd) :
    pull2 Y p (∏ i ∈ s, F i) = ∏ i ∈ s, pull2 Y p (F i) := by
  unfold pull2
  exact linPull_prod _ _ s F

theorem pullback_two_var_one : pull2 Y p (1 : PS C 2 dd) = 1 := by
  have h := pullback_two_var_prod Y p (∅ : Finset Unit) (fun _ => (1 : PS C 2 dd))
  simpa using h

theorem pullS_exp {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) (E : PS C 1 dd) (hE : MvPowerSeries.constantCoeff E = 1) :
    pullS Y p pl (∏ b : Fin n, ev (n := n) ![pt C dd b] E) =
      ∏ ρ : Fin N, rowOf ρ (pull2 Y p (∏ col : Fin 2, ev (n := 2) ![pt C dd col] E)) := by
  have hprod : pullS Y p pl (∏ b : Fin n, ev (n := n) ![pt C dd b] E) =
      ∏ b : Fin n, pullS Y p pl (ev (n := n) ![pt C dd b] E) := by
    unfold pullS
    exact linPull_prod _ _ _ _
  rw [hprod]
  have hoff : ∀ b ∈ (Finset.univ : Finset (Fin n)), b ∉ Finset.univ.map pl →
      pullS Y p pl (ev (n := n) ![pt C dd b] E) = 1 := by
    intro b _ hb
    have hb' : b ∉ Set.range pl := by simpa using hb
    rw [pullS_off (b := b) (hb := hb'), hE, map_one]
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.map pl)) hoff, Finset.prod_map,
    Fintype.prod_prod_type]
  simp_rw [pullS_col]
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [pullback_two_var_prod, rowOf_prod]

end VP

theorem valuation_eq_self_of_unit_germ (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
    (Ls : LetSys C dd) (n : ℕ) (h2 : UnitSelfSt Y p) (h3 : GermLiftSelfSt Y p H) : ValEqSelfSt Y p H Ls n := by
  intro hs N pl P hP Po hQ kind hk S t ht gr hg
  obtain ⟨U, hUi, hU0, hU⟩ := h2 hs
  obtain ⟨U', hU'i, hUU⟩ := VP.intInv hUi hU0
  choose G hGi hG using fun (o : Orb) (ρ : Fin N) => h3 hs o (S o) (t o) (ht o) (gr o ρ) (hg o ρ)
  obtain ⟨co, hco, hQe⟩ := hQ
  refine ⟨∏ ρ, ev (n := n) ![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] (U' * ∏ o, G o ρ), ?_, ?_⟩
  · refine VP.IntS_prod _ fun ρ _ => ?_
    unfold ev
    refine IntS.subst (VP.cc_ptPl pl ρ) (fun q => ?_) (hU'i.mul (VP.IntS_prod _ fun o _ => hGi o ρ))
    obtain ⟨g, i⟩ := q
    fin_cases g <;> exact VP.IntS_X _
  · have hk0 : MvPowerSeries.constantCoeff ((Y.k : C) • Y.B.hL C Y.h Y.w0) = 0 := VP.cc_smul _ (VP.cc_hL Y)
    have hE1 : MvPowerSeries.constantCoeff (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)) = 1 := by
      rw [VP.expS_eq _ hk0, VP.cc_mvExp']
    have hrow : ∀ ρ : Fin N,
        rowOf ρ (pull2 Y p (U' * ∏ o, G o ρ)) *
          rowOf ρ (pull2 Y p (∏ col : Fin 2, ev (n := 2) ![pt C dd col]
            (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)))) =
        ∏ o, MvPowerSeries.rename (VP.eAll (I := IS I0) N o)
          (rowCopy ρ (gr o ρ) * mvExp (rowCopy ρ (Y.rawSelf (p o)).hRow)) := by
      intro ρ
      rw [← VP.rowOf_mul, hU, VP.pullback_two_var_mul, VP.pullback_two_var_prod]
      have e2 : (pull2 Y p U' * ∏ o, pull2 Y p (G o ρ)) *
          (pull2 Y p U * ∏ o, toAllS (I := IS I0) o (mvExp (Y.rawSelf (p o)).hRow)) =
          ∏ o, toAllS (I := IS I0) o (gr o ρ * mvExp (Y.rawSelf (p o)).hRow) := by
        have e3 : pull2 Y p U' * pull2 Y p U = 1 := by rw [← VP.pullback_two_var_mul, hUU, VP.pullback_two_var_one]
        calc (pull2 Y p U' * ∏ o, pull2 Y p (G o ρ)) *
              (pull2 Y p U * ∏ o, toAllS (I := IS I0) o (mvExp (Y.rawSelf (p o)).hRow))
            = (pull2 Y p U' * pull2 Y p U) *
                ((∏ o, pull2 Y p (G o ρ)) * ∏ o, toAllS (I := IS I0) o (mvExp (Y.rawSelf (p o)).hRow)) := by ring
          _ = ∏ o, toAllS (I := IS I0) o (gr o ρ * mvExp (Y.rawSelf (p o)).hRow) := by
              rw [e3, one_mul, ← Finset.prod_mul_distrib]
              exact Finset.prod_congr rfl fun o _ => by rw [hG o ρ, VP.toAllS_mul]
      rw [e2, VP.rowOf_prod]
      exact Finset.prod_congr rfl fun o _ => by rw [VP.rowOf_toAllS, VP.rowCopy_mul_exp]
    have hser : pullS Y p pl ((∏ ρ, ev (n := n) ![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] (U' * ∏ o, G o ρ)) *
        FB.expS C ((Y.k : C) • ∑ b : Fin n, ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0))) =
        ∏ o, MvPowerSeries.rename (VP.eAll (I := IS I0) N o)
          (∏ ρ, (rowCopy ρ (gr o ρ) * mvExp (rowCopy ρ (Y.rawSelf (p o)).hRow))) := by
      have hpl : ∀ ρ : Fin N, VP.linPull Y (MS Y p pl)
          (ev (n := n) ![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] (U' * ∏ o, G o ρ)) =
          rowOf ρ (pull2 Y p (U' * ∏ o, G o ρ)) := fun ρ => VP.pullS_plane Y p pl ρ _
      rw [VP.expS_copies, show pullS Y p pl (_ * _) = _ from VP.linPull_mul Y _ _ _,
        show VP.linPull Y (MS Y p pl) (∏ b : Fin n, _) = _ from VP.pullS_exp Y p pl _ hE1,
        VP.linPull_prod, Finset.prod_congr rfl fun ρ _ => hpl ρ,
        ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun ρ _ => hrow ρ, Finset.prod_comm]
      exact Finset.prod_congr rfl fun o _ => (map_prod _ _ _).symm
    unfold FBChart.nab nabValN
    rw [VP.logCoordG Y (MS Y p pl) (Ls.cp n) (Ls.uv n) P co
      (fun ℓ hℓ b i => VP.hco_of_img Y p pl (Ls.cp n) (Ls.uv n) ℓ (co ℓ) (hco ℓ hℓ) b i), ← hQe]
    rw [show VP.linPull Y (MS Y p pl) _ = _ from hser, VP.jet_orb]
    exact Finset.prod_congr rfl fun o _ =>
      leaf_holds C V d (fun _ => I0 o) (Fin 2 × Fin dd) (Y.rawSelf (p o)) (H o) N (Po o) (kind o) (hk o) (gr o)

end Formalism.L2.FormalSeriesBounds
