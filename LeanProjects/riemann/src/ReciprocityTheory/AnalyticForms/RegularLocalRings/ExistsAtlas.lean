import ReciprocityTheory.AnalyticForms.RegularLocalRings.IsOpenAlt
import ReciprocityTheory.AnalyticForms.RegularLocalRings.AnChart
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.RegularLocalRings.AtlasA

namespace ReciprocityTheory.AnForm.R

open MvPolynomial ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def AlgRes.IsGoodAtlas {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : AlgRes ι P D e)
    (A : FinHolAtlas e R.M) : Prop :=
      (∀ i (h : MvPolynomial (Fin (R.amb i)) ℂ),
        A.HoloOn (R.src i) fun x => eval (R.coord i x) h) ∧
      ∀ i, ∀ x ∈ R.src i, ∀ (r : Fin e → MvPolynomial (Fin (R.amb i)) ℂ),
        Ideal.span (Set.range fun l => algebraMap _ (locRing (R.ideal i) (R.coord i x)) (r l)) =
          Ideal.map (algebraMap _ (locRing (R.ideal i) (R.coord i x))) (ptIdeal (R.coord i x)) →
        ∀ O : Set R.M, IsOpen O → x ∈ O →
          ∃ ψ : OpenPartialHomeomorph R.M (Fin e → ℂ), IsCompatChart A ψ ∧ x ∈ ψ.source ∧
            ψ.source ⊆ O ∩ R.src i ∧ ∀ y ∈ ψ.source, ψ y = evalFam r (R.coord i y)

theorem AlgRes.exists_atlas {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : AlgRes ι P D e) :
    ∃ A : FinHolAtlas e R.M, R.IsGoodAtlas A := by
  have hloc : ∀ x : R.M, ∃ ψ : OpenPartialHomeomorph R.M (Fin e → ℂ),
      R.GoodChart ψ ∧ x ∈ ψ.source := by
    intro x
    obtain ⟨i, hx⟩ := R.cover x
    obtain ⟨ψ, hψ, hxψ, -⟩ := R.exists_goodChart i x hx (R.sncAt i x hx).r
      (R.sncAt i x hx).span_eq Set.univ isOpen_univ trivial
    exact ⟨ψ, hψ, hxψ⟩
  choose ψ hψ hxψ using hloc
  obtain ⟨t, -, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set R.M)).elim_nhds_subcover
    (fun x => (ψ x).source) (fun x _ => (ψ x).open_source.mem_nhds (hxψ x))
  let A : FinHolAtlas e R.M :=
    { n := t.card
      chart := fun j => ψ (t.equivFin.symm j).1
      cover := fun x => by
        obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
        exact ⟨t.equivFin ⟨z, hz⟩, by simpa using hxz⟩
      holo := fun j k => by
        obtain ⟨ik, hsk, ⟨rk, hrk⟩, -⟩ := hψ (t.equivFin.symm k).1
        exact R.analyticOnNhd_comp_symm (hψ _) _ _ (ψ (t.equivFin.symm k).1).open_source ik hsk
          rk hrk }
  have hgood : ∀ j, R.GoodChart (A.chart j) := fun j => hψ _
  refine ⟨A, fun i h j => ?_, fun i x hx r hr O hO hxO => ?_⟩
  · obtain ⟨i', hs, -, g, hg, hgc⟩ := hgood j
    rintro w ⟨hw, hwi⟩
    exact R.analyticAt_coord_symm hs hg hgc i h hw hwi
  · obtain ⟨φ, hφ, hxφ, hsub, hform⟩ := R.exists_goodChart i x hx r hr O hO hxO
    refine ⟨φ, fun j => ⟨?_, ?_⟩, hxφ, hsub, hform⟩
    · exact R.analyticOnNhd_comp_symm (hgood j) φ φ.source φ.open_source i
        (fun y hy => (hsub hy).2) r hform
    · obtain ⟨ij, hsj, ⟨rj, hrj⟩, -⟩ := hgood j
      exact R.analyticOnNhd_comp_symm hφ _ _ (A.chart j).open_source ij hsj rj hrj

end ReciprocityTheory.AnForm.R
