import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatementOfDegreeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreUniformisationAppellHumbertUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFibreIsoUniversalGroupFramedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearLiftPreservingAppellHumbertForm
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.FlatDegreeCompare

open Limits MonoidalCategory CartesianMonoidalCategory MonObj in

private theorem isTangent_of_isTanAt_sab {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {t' : SAB H (Sp S)} (m : SABMap t' Xo.univ.t x)
    (w : epsR S ⟶ t'.G) (h : IsTanAt x (w.left ≫ m.φ)) : IsTangent w := by
  have hw : w.left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) := Over.w w
  have one : η[t'.G].left ≫ m.φ = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by
    have e1 : (1 : Over.mk x ⟶ Xo.univ.t.G).left = x ≫ η[Xo.univ.t.G].left := by
      show (toUnit _ ≫ η[Xo.univ.t.G]).left = _
      simp
    rw [e1]
    have := m.cm.e_comm
    rw [m.base] at this
    exact this
  apply m.cart.1.hom_ext
  · rw [Category.assoc]; exact h.2.trans one.symm
  · have a : η[t'.G].left ≫ t'.G.hom = 𝟙 _ := Over.w η[t'.G]
    rw [Category.assoc, hw, a, GlobalTheory.spMap_comp_spMap]
    have : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
      ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]
    exact Spec.map_id _

theorem UpperTheory.tangent_vectors_at_frame_point_independent :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), 1 ≤ Dw.p + Dw.q → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (ρ : E →+* ℂ) (v : Fin (Dw.mult ρ) → (epsR K ⟶ t₀.G)), (∀ i, (v i).left ≫ m1.φ = y.u ρ i) → ∀ (σ : K →+* ℂ) (N : ℝ), EigenvectorLieDegree.IsArchSq t₀.G t₀.PP.L v σ N → ∀ (φ : K →ₐ[c.F] CAt (σ.comp (algebraMap c.F K))), (∀ a, toC (φ a) = σ a) → ∀ (z : FrPt Xo c (CAt (σ.comp (algebraMap c.F K)))), FrMap φ y z → ∀ (k : (U (σ.comp (algebraMap c.F K))).Comp) (w : ((U (σ.comp (algebraMap c.F K))).X k).dom) (W : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnfAt (U (σ.comp (algebraMap c.F K))) k w) (Wu : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnitAt W), z.x = ((U (σ.comp (algebraMap c.F K))).un k w).x → ∀ (C : Fin (Dw.mult ρ) → Fin (Dw.mult ρ) → CAt (σ.comp (algebraMap c.F K))), (∀ i, IsCombAt ((U (σ.comp (algebraMap c.F K))).un k w).x (((U (σ.comp (algebraMap c.F K))).un k w).u ρ) (C i) (z.u ρ i)) → N = (Matrix.of fun i j : Fin (Dw.mult ρ) => (Real.pi : ℂ) * hermForm Wu.Hm (∑ l, toC (C j l) • Pi.single (W.e.symm ⟨ρ, l⟩) (1 : ℂ)) (∑ l, toC (C i l) • Pi.single (W.e.symm ⟨ρ, l⟩) (1 : ℂ))).det.re := by
  intro E _ _ _ H Dw l Xo c r U hpos K _ _ _ y t₀ m1 ρ v hv σ N hN φ hφ z hz k w W Wu hzx C hC
  obtain ⟨A, _, ψ, g, u, Hm, χ, v', Wc, hψ, hAH, hvec, -, hN⟩ := hN
  obtain ⟨T, m, u', χ', hA', hw'⟩ := GlobalTheory.T.exists_fibre_uniformisation_appellHumbert_unit E H Dw l Xo c r _ _ hpos k w W Wu ρ z hzx C hC
  choose w' hw'1 hw'2 using hw'
  have hφσ : (φ.toRingHom : K →+* ℂ) = σ := RingHom.ext hφ
  have hbase : z.x = spMap σ ≫ y.x := by rw [hz.1, hφσ]; rfl
  have hχ := (hψ.comp m1.cart).congr hbase.symm rfl
  obtain ⟨e, he, hfl⟩ := grpPullback_iso hχ m.cart
  let f : A ⟶ T.pol.A := e.hom
  haveI hf : IsMonHom f := he
  have hfl' : f.left ≫ m.φ = ψ ≫ m1.φ := hfl
  have hLA := pull_isLB t₀.PP.isLB ψ
  have hLB : LBIso (T.pol.L.pull f.left) (t₀.PP.L.pull ψ) := by
    obtain ⟨wT, hwT, -⟩ := m.lin
    obtain ⟨w1', hw1', -⟩ := m1.lin
    have hT : LBIso T.t.PP.L (Xo.univ.t.PP.L.pull m.φ) := ⟨wT, hwT⟩
    have h1 : LBIso t₀.PP.L (Xo.univ.t.PP.L.pull m1.φ) := ⟨w1', hw1'⟩
    have hT2 := GlobalTheory.CM.EllComp.lbIso_pull_comp hT.symm f.left
    rw [hfl'] at hT2
    have h3 := GlobalTheory.CM.EllComp.lbIso_pull_comp h1.symm ψ
    exact LBIso.trans (pull_isLB T.t.PP.isLB f.left) (pull_isLB Xo.univ.t.PP.isLB _) hLA hT2.symm h3
  have htan : ∀ i, IsTangent (v' i) := fun i => GlobalTheory.IsVecOver.isTangent hψ (hvec i).1
    (isTangent_of_isTanAt_sab m1 (v i) (by rw [hv i]; exact y.tan ρ i))
  have hvw : ∀ i, v' i ≫ f = w' i := fun i => by
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · rw [hw'1, hz.2.1, ← hv i, hφσ]
      change ((v' i).left ≫ f.left) ≫ m.φ = _
      rw [Category.assoc, hfl', ← Category.assoc, (hvec i).1, Category.assoc]
      rfl
    · exact (Over.w (v' i ≫ f)).trans (Over.w (w' i)).symm
  obtain ⟨-, -, -, -, h1, h2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all T.pol W.g u' Wu.Hm χ' hA'
  obtain ⟨F, hF, -⟩ := GlobalTheory.T.existsUnique_linearLift_of_holomorphic_abelianVariety T.pol.A T.pol.isAb T.pol.L W.g g u' h1 h2 (fun z => u.ex z ≫ f)
    (fun z w => by simp only [u.ex_add]; exact MonObj.mul_comp _ _ f) (GlobalTheory.HomLinear.isHolTo_ex_comp u f)
  have hH : ∀ x x', hermForm Wu.Hm (F x) (F x') = hermForm Hm x x' := fun x x' => by
    have := GlobalTheory.hermForm_pull_eq_of_lbIso_pow A T.pol.A _ T.pol.L hLA T.pol.isLB g W.g u u' Hm χ Wu.Hm χ' hAH hA' f F hF
      1 1 (GlobalTheory.lbIso_lbPow hLB 1) x x'
    simpa using this
  have hFW : ∀ i, F (Wc i) = ∑ l, toC (C i l) • Pi.single (W.e.symm ⟨ρ, l⟩) (1 : ℂ) := fun i => by
    have hd := GlobalTheory.HomLinear.isDiff_comp u u' f F hF (htan i) (hvec i).2
    have ht := GlobalTheory.HomLinear.isTangent_comp f (htan i)
    rw [hvw i] at hd ht
    obtain ⟨_, -, hw⟩ := h1 (w' i) ht
    exact (hw _ hd).trans (hw _ (hw'2 i)).symm
  have hre := congrArg Complex.re hN
  rw [Complex.ofReal_re, ← Matrix.det_transpose] at hre
  rw [hre]
  congr 2
  ext i j
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  rw [← hFW, ← hFW, hH]
  rfl
