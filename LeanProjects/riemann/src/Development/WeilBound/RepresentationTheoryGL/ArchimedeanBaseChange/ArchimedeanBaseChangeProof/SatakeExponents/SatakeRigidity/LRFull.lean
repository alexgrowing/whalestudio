import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.StFull
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.One

namespace PositivityTheory.Rg.BcB.F.Rig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem rfull_finite_under_eq (u : HeightOneSpectrum (𝓞 E)) :
    {w : HeightOneSpectrum (𝓞 E) |
      w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E))}.Finite := by
  have hm : (u.under (𝓞 (maximalRealSubfield E))).asIdeal.IsMaximal := (u.under _).isMaximal
  refine (Set.Finite.preimage (f := HeightOneSpectrum.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h)
    (IsDedekindDomain.primesOver_finite (u.under (𝓞 (maximalRealSubfield E))).asIdeal (𝓞 E))).subset ?_
  intro w hw
  exact ⟨w.isPrime, ⟨by rw [← hw]; rfl⟩⟩

theorem rfull_eventually_sat (D : Pre E n) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, D.Sat w B := by
  have h : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
      ∀ i, GlobalTheory.LGrp.IsSpherical (D.σ i w).ρ (GlobalTheory.LFun.KGL w (D.N i)) :=
    Filter.eventually_all.2 fun i =>
      (GlobalTheory.SpehPair.eventually_spherical (D.discrete i)).mono fun w hw => hw _ (D.loc i w)
  refine h.mono fun w hw => ?_
  choose b hb using fun i =>
    GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible (D.σ i w).smooth (D.σ i w).irred (hw i)
  exact ⟨∑ i, b i, b, fun i => ⟨hw i, hb i⟩, rfl⟩

theorem rfull_bcParam_map_inv (n : ℕ) (α : Fin (n / 2) → ℂˣ) :
    (GlobalTheory.LGrp.bcParam n α).map (·⁻¹) = GlobalTheory.LGrp.bcParam n α := by
  simp only [GlobalTheory.LGrp.bcParam, Multiset.map_add, Multiset.map_map, Function.comp_def, inv_inv,
    Multiset.map_replicate, inv_one]
  rw [add_comm (Multiset.map _ _) (Multiset.map _ _)]

theorem rFullSat : RFullSat := by
  intro hU hI hS E _ _ _ hE n π hπ D D' hD hD'
  filter_upwards [hU E n π hπ, hS E n π hπ D D' hD.1.2 hD'.1.2] with w hu hsp
  by_cases hw : IsSplitAt w
  · exact hsp hw
  · obtain ⟨s, ϖ, q, α, hs, hinv, hα⟩ := hI E hE n π hπ w hw hu
    obtain ⟨B, hB, hBα⟩ := hD.2 w hu hw
    obtain ⟨B', hB', hBα'⟩ := hD'.2 w hu hw
    refine ⟨B, hB, ?_⟩
    rw [hBα s ϖ q hs hinv α hα, ← hBα' s ϖ q hs hinv α hα]
    exact hB'

theorem rFullTheta : RFullTheta := by
  intro hU hI hC E _ _ _ hE n π hπ D hD
  have hbad : {u : HeightOneSpectrum (𝓞 E) |
      ¬ ((∃ B, D.Sat u B) ∧ (IsSplitAt u → D.SplitAt π u))}.Finite := by
    refine ((Filter.eventually_cofinite.1 (rfull_eventually_sat D)).union hD.1.2).subset ?_
    intro u hu
    by_cases h1 : ∃ B, D.Sat u B
    · right
      by_contra h2
      exact hu ⟨h1, fun hs => by_contra fun h3 => h2 ⟨hs, h3⟩⟩
    · left
      exact h1
  have hconj : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ u, ConjPl w u →
      (∃ B, D.Sat u B) ∧ (IsSplitAt u → D.SplitAt π u) := by
    rw [Filter.eventually_cofinite]
    refine (hbad.biUnion fun u _ => rfull_finite_under_eq u).subset ?_
    intro w hw
    have hw' : ¬ ∀ u, ConjPl w u → (∃ B, D.Sat u B) ∧ (IsSplitAt u → D.SplitAt π u) := hw
    obtain ⟨u, hu⟩ := not_forall.1 hw'
    obtain ⟨hc, hu'⟩ := Classical.not_imp.1 hu
    exact Set.mem_biUnion hu' hc.1.symm
  have hsp0 : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ¬ (IsSplitAt w ∧ ¬ D.SplitAt π w) :=
    Filter.eventually_cofinite.2 (hD.1.2.subset fun x hx => not_not.1 hx)
  filter_upwards [hU E n π hπ, rfull_eventually_sat D, hconj, hsp0]
    with w hu hs hc hsp
  by_cases hw : IsSplitAt w
  · obtain ⟨B, hB⟩ := hs
    refine ⟨B, hB, fun u hwu => ?_⟩
    obtain ⟨⟨B', hB'⟩, hsu⟩ := hc u hwu
    have hus : IsSplitAt u := ⟨w, (hwu.2.resolve_right (not_not_intro hw)).symm, hwu.1.symm⟩
    have hsw : D.SplitAt π w := by
      by_contra h
      exact hsp ⟨hw, h⟩
    have e := hC E n π hπ D w u hw hwu hu hsw (hsu hus) B B' hB hB'
    rw [← e]
    exact hB'
  · obtain ⟨s, ϖ, q, α, hs', hinv, hα⟩ := hI E hE n π hπ w hw hu
    obtain ⟨B, hB, hBα⟩ := hD.2 w hu hw
    refine ⟨B, hB, fun u hwu => ?_⟩
    have hu' : u = w := by
      by_contra hne
      exact hw ⟨u, hne, hwu.1⟩
    subst hu'
    have e := hBα s ϖ q hs' hinv α hα
    rw [e, rfull_bcParam_map_inv, ← e]
    exact hB

end PositivityTheory.Rg.BcB.F.Rig

end
