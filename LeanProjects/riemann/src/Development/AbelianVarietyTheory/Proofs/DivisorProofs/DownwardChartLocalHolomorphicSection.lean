import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessRelFnB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfWeightLocPot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviAtLinearCombinationPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentMapContinuousSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralMultipleExtensionStatement
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpaCHessComp
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst
import ReciprocityTheory.L2DbarEstimates.LeviForms.DetUpdateColEq
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O

open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.Cover

theorem valR_app_comp {R : Type} [CommRing R] {X Y : Scheme.{0}} (x : Sp R ⟶ Y) (g : Y ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ g ⁻¹ᵁ U) (f : Γ(X, U)) : valR x (g ⁻¹ᵁ U) ((g.app U).hom f) = valR (x ≫ g) U f := by
  rw [ZH.CrdCalc.valR_eq x _ h, ZH.CrdCalc.valR_eq (x ≫ g) U h]
  rfl

theorem differentiableOn_chart_of_isDown : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (e : ℕ) (M : Man e) (I : ManIs M Y) (ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts V.p σ → M.X (ε σ)), V.IsDown I ε π → ∀ (σ : 𝓞 F →+* ℂ) (c : AlgChart V.p σ e) (y : CxPts V.p σ), y ∈ c.e.source → ∀ (j : Fin (M.A (ε σ)).n), π σ y ∈ ((M.A (ε σ)).chart j).source → ∃ U : Set (ReciprocityTheory.L2DbarEstimates.V e), IsOpen U ∧ c.e y ∈ U ∧ U ⊆ c.e.target ∧ (∀ v ∈ U, π σ (c.e.symm v) ∈ ((M.A (ε σ)).chart j).source) ∧ DifferentiableOn ℂ (fun v => FinChart.toV e (((M.A (ε σ)).chart j) (π σ (c.e.symm v)))) U := by
  intro F _ _ Y V e M I ε π hD σ c y hy j hj
  obtain ⟨c', hc⟩ := I.alg (ε σ) j
  have hcont : Continuous (π σ) := (isDown_continuous_surjective F Y V e M I ε π hD σ).1
  have hsrc : ∀ z, π σ z ∈ ((M.A (ε σ)).chart j).source ↔ I.pt (ε σ) (π σ z) ∈ c'.e.source := by
    intro z; rw [hc, Homeomorph.transOpenPartialHomeomorph_source]; rfl
  have happ : ∀ z, FinChart.toV e (((M.A (ε σ)).chart j) (π σ z)) = c'.e (I.pt (ε σ) (π σ z)) := by
    intro z; rw [hc, Homeomorph.transOpenPartialHomeomorph_apply]; rfl
  obtain ⟨w₀, hw₀j, hw₀π⟩ := (hD σ).2 y
  have hy' : I.pt (ε σ) (π σ y) ∈ c'.e.source := (hsrc y).1 hj
  have hx : w₀ (IsLocalRing.closedPoint ℂ) ∈ V.π ⁻¹ᵁ c'.U := by
    have := mem_ptsIn.1 (c'.source_subset hy')
    rw [← hw₀π] at this
    exact this
  obtain ⟨W', hW', hxW', n, g', hn, hg'⟩ := T.exists_integral_multiple_extension F V.X V.G V.p (V.π ≫ Y.str) V.j V.pb
    (V.π ⁻¹ᵁ c'.U) _ hx (Fin e) (fun b => (V.π.app c'.U).hom (c'.x b))
  have key : ∀ z : CxPts V.p σ, z ∈ ptsIn V.p σ W' → I.pt (ε σ) (π σ z) ∈ c'.e.source → ∀ b,
      c'.e (I.pt (ε σ) (π σ z)) b = (n : ℂ)⁻¹ * ev V.p σ W' (g' b) z := by
    intro z hz hz' b
    obtain ⟨w, hwj, hwπ⟩ := (hD σ).2 z
    have hz1 : ⊤ ≤ w ⁻¹ᵁ V.j ⁻¹ᵁ W' := by
      have : ⊤ ≤ z.1 ⁻¹ᵁ W' := hz
      rw [← hwj] at this; exact this
    have hz2 : ⊤ ≤ w ⁻¹ᵁ V.π ⁻¹ᵁ c'.U := hz1.trans (w.preimage_mono hW')
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    rw [c'.apply_eq _ hz' b, eq_inv_mul_iff_mul_eq₀ hn']
    show (n : ℂ) * valR (I.pt (ε σ) (π σ z)).1 c'.U (c'.x b) = valR z.1 W' (g' b)
    rw [← hwπ, ← hwj, ← valR_app_comp w V.π c'.U hz2, ← valR_app_comp w V.j W' hz1, ← hg' b,
      ZH.CrdCalc.valR_eq w _ hz1, map_mul, map_natCast, ← ZH.CrdCalc.valR_eq w _ hz1]
    congr 1
    exact (Points.valR_res w hW' hz1 _).symm
  refine ⟨c.e.target ∩ c.e.symm ⁻¹' (ptsIn V.p σ W' ∩ (π σ) ⁻¹' ((M.A (ε σ)).chart j).source),
    c.e.isOpen_inter_preimage_symm ((isOpen_ptsIn W').inter
      (((M.A (ε σ)).chart j).open_source.preimage hcont)),
    ⟨c.e.map_source hy, ?_⟩, Set.inter_subset_left, fun v hv => hv.2.2, ?_⟩
  · rw [Set.mem_preimage, c.e.left_inv hy]
    refine ⟨mem_ptsIn.2 ?_, hj⟩
    rw [← hw₀j]
    exact hxW'
  · rw [differentiableOn_euclidean]
    intro b
    have hd := ((c.holo W' (g' b)).mono
      (Set.inter_subset_inter_right _ (Set.preimage_mono
        (Set.inter_subset_left (t := (π σ) ⁻¹' ((M.A (ε σ)).chart j).source))))).const_mul ((n : ℂ)⁻¹)
    refine hd.congr fun v hv => ?_
    simp only [happ]
    exact key _ hv.2.1 ((hsrc _).1 hv.2.2) b

end GlobalTheory.Mean4O.Cover
