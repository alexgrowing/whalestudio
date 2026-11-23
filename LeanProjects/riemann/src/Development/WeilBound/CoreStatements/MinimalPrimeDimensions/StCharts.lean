import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.GenIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinateNearGenericPoint

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.Cartier

namespace ChowFormHeightComparison₂.CF.H

variable {R : Type} [CommRing R] {Z : Scheme.{0}} {B : LB Z} {m : ℕ} {p : Z ⟶ Sp R} {s : Fin m → B.Sec}

theorem eval₂_coords_eq_zero (hB : B.IsLB) {σ : R →+* ℂ} (y : CxPts p σ) {q : MvPolynomial (Fin m) R}
    (hq : q ∈ ptIdeal p s (under y)) : eval₂ σ (coords p σ hB s y) q = 0 := by
  have hy0 : y ∈ ptsIn p σ (B.U (pick hB y)) := mem_pick hB y
  have hz : under y ∈ B.U (pick hB y) := mem_ptsIn.mp hy0
  let ψ := Z.descResidueField (Scheme.stalkClosedPointTo (y : Sp ℂ ⟶ Z))
  have hev : ∀ f : Γ(Z, B.U (pick hB y)),
      ψ.hom ((Z.evaluation (B.U (pick hB y)) (under y) hz).hom f) = ev p σ (B.U (pick hB y)) f y := by
    intro f
    have hv := congrArg (fun g => g.hom f)
      (Points.germ_stalkClosedPointTo_eq_valMap (C := ℂ) (y : Sp ℂ ⟶ Z) (B.U (pick hB y)) hy0)
    rw [ev_eq hy0, evHom]
    refine Eq.trans ?_ hv
    rfl
  have hmem : q ∈ RingHom.ker (coneHom p s (under y) (pick hB y) hz) := by
    have h := hq
    simp only [ptIdeal, Submodule.mem_iInf] at h
    exact h _ hz
  have hΦ : eval₂Hom σ (coords p σ hB s y) = (Polynomial.evalRingHom 1).comp
      ((Polynomial.mapRingHom ψ.hom).comp (coneHom p s (under y) (pick hB y) hz)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [coneHom, RingHom.comp_apply, eval₂Hom_C, Polynomial.coe_mapRingHom, Polynomial.map_C,
        Polynomial.coe_evalRingHom, Polynomial.eval_C]
      erw [hev, ev_algX hy0]
    · intro k
      simp only [coneHom, RingHom.comp_apply, eval₂Hom_X', Polynomial.coe_mapRingHom, Polynomial.map_mul,
        Polynomial.map_X, Polynomial.map_C, Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_C, one_mul]
      erw [hev]
      rfl
  have he : eval₂ σ (coords p σ hB s y) q = eval₂Hom σ (coords p σ hB s y) q := rfl
  rw [he, hΦ, RingHom.comp_apply, RingHom.comp_apply, RingHom.mem_ker.mp hmem, map_zero, map_zero]

theorem exists_form (h1 : StPts) [IsIntegral Z] [NoetherianSpace Z] (hE : Emb p s) (U : Z.Opens)
    (hU : genericPoint Z ∈ U) : ∃ (n : ℕ) (q : MvPolynomial (Fin m) R), q.IsHomogeneous n ∧
      q ∉ ptIdeal p s (genericPoint Z) ∧ ∀ z, z ∉ U → q ∈ ptIdeal p s z := by
  obtain ⟨hprime, hspec, -, -⟩ := h1 R Z p B m s hE
  let C : Closeds Z := ⟨(U : Set Z)ᶜ, U.isOpen.isClosed_compl⟩
  obtain ⟨S, hirr, hSC⟩ := NoetherianSpace.exists_finset_irreducible C
  have hg0 : ∀ k : S, ∃ g : Z, IsGenericPoint g (k : Set Z) := fun k => QuasiSober.sober (hirr k) k.1.isClosed
  choose g hg using hg0
  have hr0 : ∀ k : S, ∃ (d : ℕ) (r : MvPolynomial (Fin m) R), r.IsHomogeneous d ∧ r ∈ ptIdeal p s (g k) ∧
      r ∉ ptIdeal p s (genericPoint Z) := by
    intro k
    have hk : (k : Set Z) ⊆ (U : Set Z)ᶜ := by
      intro z hz
      have h' : z ∈ (C : Set Z) := by
        rw [hSC]
        exact (Finset.le_sup (f := id) k.2) hz
      exact h'
    have hnot : ¬ ptIdeal p s (g k) ≤ ptIdeal p s (genericPoint Z) := by
      intro hle
      have hm : genericPoint Z ∈ closure ({g k} : Set Z) := specializes_iff_mem_closure.mp ((hspec _ _).mpr hle)
      have hcl : closure ({g k} : Set Z) = (k : Set Z) := hg k
      rw [hcl] at hm
      exact hk hm hU
    obtain ⟨f, hf, hfn⟩ := Set.not_subset.mp hnot
    have hex : ∃ d, homogeneousComponent d f ∉ ptIdeal p s (genericPoint Z) := by
      by_contra hcon
      push_neg at hcon
      apply hfn
      rw [← MvPolynomial.sum_homogeneousComponent f]
      exact Ideal.sum_mem _ fun d _ => hcon d
    obtain ⟨d, hd⟩ := hex
    exact ⟨d, _, homogeneousComponent_isHomogeneous d f, (hprime (g k)).isHomog f hf d, hd⟩
  choose d r hr using hr0
  refine ⟨∑ k, d k, ∏ k, r k, IsHomogeneous.prod _ _ _ fun k _ => (hr k).1, ?_, ?_⟩
  · intro hmem
    obtain ⟨k, -, hk⟩ := ((hprime _).isPrime.prod_mem_iff).mp hmem
    exact (hr k).2.2 hk
  · intro z hz
    have hzC : z ∈ (C : Set Z) := hz
    rw [hSC, Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion] at hzC
    simp only [Set.mem_iUnion] at hzC
    obtain ⟨k, hkS, hzk⟩ := hzC
    have hle := (hspec (g ⟨k, hkS⟩) z).mp ((hg ⟨k, hkS⟩).specializes hzk)
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ _)) (hle (hr ⟨k, hkS⟩).2.1)

end ChowFormHeightComparison₂.CF.H

open ChowFormHeightComparison₂.CF.H in

theorem ChowFormHeightComparison₂.CF.stCharts (h1 : ChowFormHeightComparison₂.CF.StPts) : ChowFormHeightComparison₂.CF.StCharts := by
  intro K _ _ Z _ p B m s e hE hX
  have := hX.isNoetherian
  obtain ⟨U, x, hU, hg, hx⟩ := GlobalTheory.GenericEtale.exists_etale_coords hX
  obtain ⟨n, q, h₁, h₂, h₃⟩ := exists_form h1 hE U hg
  refine ⟨n, q, h₁, h₂, fun σ y hy => ?_⟩
  have hy' : y ∈ ptsIn p σ U := mem_ptsIn.2 (by_contra fun h => hy (eval₂_coords_eq_zero hE.isLB y (h₃ _ h)))
  obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hU x hx hy'
  exact ⟨c, hc⟩
