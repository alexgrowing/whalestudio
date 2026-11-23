import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetMap

theorem isFPt_comp {R : Type} [CommRing R] {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [GrpObj G']
    {κ : Type} {y : Fam G κ} (hy : IsFPt y) (f : G ⟶ G') (hf : η[G] ≫ f = η[G']) :
    IsFPt (fun m => y m ≫ f : Fam G' κ) := by
  refine ⟨fun m => ?_, fun m => ?_⟩
  · show spMap _ ≫ y (m + 1) ≫ f = y m ≫ f
    rw [← Category.assoc, hy.1 m]
  · show spMap _ ≫ y m ≫ f = 1
    rw [← Category.assoc, hy.2 m, Hom.one_def, Hom.one_def, Category.assoc, hf]

theorem mapSt (hJ : JetAlgSt) (hR : RepSt) : MapSt := by
  intro R _ G _ G' _ d x x' hx hx' f hf
  obtain ⟨hex, -, hfp, -, hsub⟩ := hR R G d x hx (Fin 1 × Fin d)
  obtain ⟨-, hco', -, -, hsub'⟩ := hR R G' d x' hx' (Fin 1 × Fin d)
  obtain ⟨y₀, hy₀, -⟩ := hex (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R (n := 1) d 0) (gp_pt 0)
  obtain ⟨φ, hφ, hu⟩ := hco' _ (isFPt_comp (hfp _ _ hy₀) f hf)
  refine ⟨φ, ⟨hφ.1, fun n a y hy => ?_⟩, fun φ' hφ' => ?_⟩
  · have hb : ∀ p : Fin 1 × Fin d, constantCoeff ((![a] : Fin 1 → Pt R n d) p.1 p.2) = 0 :=
      fun p => single_point_zero_constant (a := a) hy.1 p.1 p.2
    have hψ := fun m => ((hJ R (Fin n × Fin d)).2.2.2.2 (Fin 1 × Fin d) _ hb m).1
    choose ψ hψ using hψ
    have h1 := hsub (Fin n × Fin d) _ ψ hb hψ _ _ hy₀
    have h2 := hsub' (Fin n × Fin d) _ ψ hb hψ _ _ hφ
    have h1' : Rep x a (fun m => spMap (ψ m) ≫ y₀ m) := by
      have := gt_comp1_pt a hy.1
      rw [← this]
      exact h1
    have e : y = fun m => spMap (ψ m) ≫ y₀ m :=
      ((hR R G d x hx (Fin n × Fin d)).1 a hy.1).unique hy h1'
    subst e
    simp only [Category.assoc]
    exact h2
  · have := hφ'.2 1 _ _ hy₀
    rw [gt_comp1_pt_right] at this
    exact hu _ this

theorem toJet_one_eq_sum {R : Type} [CommRing R] {κ : Type} [Fintype κ] (g : MvPowerSeries κ R)
    (hg : constantCoeff g = 0) :
    toJet 1 g = ∑ p, coeff (Finsupp.single p 1) g • zR (R := R) 1 p := by
  classical
  have h : truncTotal (1 + 1) g = ∑ p, coeff (Finsupp.single p 1) g • (MvPolynomial.X p : MvPolynomial κ R) := by
    ext e
    rw [coeff_truncTotal_eq_ite, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_X', smul_eq_mul, mul_ite, _root_.mul_one, mul_zero]
    by_cases he : ∃ p, Finsupp.single p 1 = e
    · obtain ⟨p, rfl⟩ := he
      rw [if_pos (by simp), Finset.sum_eq_single p (fun q _ hq => if_neg fun h =>
        hq (Finsupp.single_left_injective one_ne_zero h)) (by simp), if_pos rfl]
    · rw [Finset.sum_eq_zero fun p _ => if_neg fun h => he ⟨p, h⟩]
      split_ifs with hd
      · have h0 : e.degree = 0 := by
          by_contra h0
          have h1 : e.degree = 1 := by omega
          have : e ∈ Set.range (fun a : κ => Finsupp.single a 1) := by
            rw [Finsupp.range_single_one]; exact h1
          exact he this
        rw [(Finsupp.degree_eq_zero_iff e).1 h0]
        simpa using hg
      · rfl
  unfold toJet
  rw [h]
  exact (map_sum (Ideal.Quotient.mkₐ R _) _ _).trans
    (Finset.sum_congr rfl fun p _ => map_smul (Ideal.Quotient.mkₐ R _) _ _)

theorem dLinSt (hR : RepSt) : DLinSt := by
  intro R _ G _ G' _ d x x' hx hx' f φ hφ w hw hw'
  obtain ⟨y₀, hy₀, -⟩ := (hR R G d x hx (Fin 1 × Fin d)).1
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R (n := 1) d 0) (gp_pt 0)
  have h' := hφ.2 1 _ _ hy₀
  rw [gt_comp1_pt_right] at h'
  obtain ⟨ψ₀, hψ₀, e₀⟩ := hy₀.2 1
  obtain ⟨ψ', hψ', e'⟩ := h'.2 1
  set c := tcoord hx w hw with hc
  let l : JetR R (Fin 1 × Fin d) 1 →ₐ[R] DualNumber R :=
    jetLift R (RingHom.ker (fstD R)) kerD_sq (fun p => TrivSqZeroExt.inr (c p.2)) (fun _ => inr_mem_kerD _)
  have hl : ∀ p, l (zR 1 p) = TrivSqZeroExt.inr (c p.2) := fun p => jetLift_zR _ _ _ _ p
  have e1 : l.comp ψ₀ = dualLift c := jet_ext fun j => by
    rw [AlgHom.comp_apply, hψ₀, dualLift_zR]
    exact (congrArg l (toJet_X 1 _)).trans (hl _)
  have e2 : l.comp ψ' = dualLift ((dLin φ).mulVec c) := jet_ext fun j => by
    rw [AlgHom.comp_apply, hψ', dualLift_zR, toJet_one_eq_sum _ (hφ.1 j), map_sum]
    simp only [map_smul, hl, ← TrivSqZeroExt.inr_smul, smul_eq_mul]
    rw [← TrivSqZeroExt.inr_sum, Fintype.sum_prod_type, Fin.sum_univ_one]
    rfl
  apply tcoord_eq
  have e'' : y₀ 1 ≫ f = spMap ψ' ≫ x' 1 := e'
  rw [← e2, ← spMap_comp, Category.assoc, ← e'', e₀, ← Category.assoc, ← Category.assoc, spMap_comp, e1,
    ← tcoord_spec hx w hw]

theorem mapSt_and_dLinSt : JetAlgSt → RepSt → MapSt ∧ DLinSt :=
  fun hJ hR => ⟨mapSt hJ hR, dLinSt hR⟩

end GlobalTheory.JetMap
