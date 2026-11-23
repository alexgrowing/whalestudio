import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatementOfDegreeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameTangentVectorsOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFramesDifferByUnit
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SabMapCancelAndCompOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.FlatDegreeCompare

section Helpers

open MonoidalCategory CartesianMonoidalCategory MonObj Matrix

private theorem isTan_iff {V : Type} [CommRing V] {G : Over (Sp V)} [GrpObj G] (w : epsOver V V ⟶ G) :
    IsTan w ↔ IsTangent (R := V) w := by
  have h1 : (1 : ptOver V V ⟶ G).left = η[G].left := by
    have e : (1 : ptOver V V ⟶ G) = CartesianMonoidalCategory.toUnit _ ≫ η[G] := rfl
    rw [e, Over.comp_left]
    have e2 : (CartesianMonoidalCategory.toUnit (ptOver V V)).left = 𝟙 (Sp V) := by
      have := Over.w (CartesianMonoidalCategory.toUnit (ptOver V V))
      exact ((Category.comp_id _).symm.trans this).trans (Spec.map_id _)
    rw [e2]
    exact Category.id_comp _
  unfold IsTan IsTangent
  rw [h1]

private theorem eig_of_comb {K O : Type} [CommRing K] [CommRing O] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A]
    (act : OAct O A) (a : O) (s : K) {m : ℕ} {x : Fin m → (epsR K ⟶ A)} (ht : ∀ i, IsTangent (x i))
    (he : ∀ i, (x i ≫ act.act a).left = spMap (epsScaleR s) ≫ (x i).left) {c : Fin m → K} {w : epsR K ⟶ A}
    (hc : IsLieComb c x w) : (w ≫ act.act a).left = spMap (epsScaleR s) ≫ w.left := by
  let y : Fin m → GlobalTheory.Serre.Lie act := fun i => GlobalTheory.Serre.Lie.mk act (x i) (ht i)
  have hy : ∀ i, a • y i = s • y i := fun i => GlobalTheory.Serre.Lie.ext (Over.OverMorphism.ext (he i))
  obtain rfl := (GlobalTheory.Serre.Lie.isLieComb_iff c y w).1 hc
  have : a • ∑ i, c i • y i = s • ∑ i, c i • y i := by
    rw [Finset.smul_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_comm a, hy, smul_comm]
  exact congrArg (fun z : GlobalTheory.Serre.Lie act => z.hom.left) this

private theorem tangent_ext {V K : Type} [CommRing V] [IsLocalRing V] [CommRing K] {f : V →+* K}
    (hf : Function.Injective f) {G : Over (Sp V)} [GrpObj G] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A]
    {φ : A.left ⟶ G.left} (hG : IsSemiAbelian G) (hφ : IsGrpPullback A G (spMap f) φ) {w w₀ : epsR V ⟶ G}
    (hw : IsTangent w) (hw₀ : IsTangent w₀) {w' : epsR K ⟶ A} (o : GlobalTheory.IsVecOver f φ w w')
    (o₀ : GlobalTheory.IsVecOver f φ w₀ w') : w = w₀ := by
  have := hG.comm
  obtain ⟨n, e, e', -, he, he', h, -⟩ := exists_frame (m := 0) (x := Fin.elim0) hG hφ (fun i => i.elim0)
  obtain ⟨p, hp, -⟩ := he.2 w hw
  obtain ⟨q, hq, -⟩ := he.2 w₀ hw₀
  have := (Indep.of_basis he').2 _ _ w' ((GlobalTheory.lieComb_baseChange _ _ _ G A φ hφ n e w p e' w' h hp).1 o)
    ((GlobalTheory.lieComb_baseChange _ _ _ G A φ hφ n e w₀ q e' w' h hq).1 o₀)
  obtain rfl : p = q := funext fun j => hf (congrFun this j)
  exact ((GlobalTheory.LieComb.lieComb_algebra _ G n e he.1).1 p).unique hp hq

private theorem eig_descend {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {V K : Type} [CommRing V] [IsLocalRing V] [CommRing K] {f : V →+* K}
    (hf : Function.Injective f) {G : SAB H (Sp V)} {t : SAB H (Sp K)} (m : SABMap t G (spMap f))
    {w : epsR V ⟶ G.G} (hw : IsTangent w) {w' : epsR K ⟶ t.G} (o : GlobalTheory.IsVecOver f m.φ w w') (a : 𝓞 E) (z : V)
    (he : (w' ≫ t.act.act a).left = spMap (epsScaleR (f z)) ≫ w'.left) :
    (w ≫ G.act.act a).left = spMap (epsScaleR z) ≫ w.left := by
  have := t.semi.comm
  have := G.semi.comm
  have := G.act.hom a
  let y : GlobalTheory.Serre.Lie G.act := GlobalTheory.Serre.Lie.mk G.act w hw
  have key : w ≫ G.act.act a = (z • y).hom := by
    refine tangent_ext hf G.semi m.cart (GlobalTheory.CM.DiffCoord.isTangent_comp_hom _ hw) (GlobalTheory.Serre.Lie.isTangent _)
      (w' := w' ≫ t.act.act a) ?_ ?_
    · unfold GlobalTheory.IsVecOver at o ⊢
      rw [Over.comp_left, Over.comp_left, Category.assoc]
      refine (congrArg (w'.left ≫ ·) (m.act a)).trans ?_
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ _) o
    · unfold GlobalTheory.IsVecOver at o ⊢
      rw [he, Category.assoc]
      refine (congrArg (spMap (epsScaleR (f z)) ≫ ·) o).trans ?_
      show _ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ spMap (epsScaleR z) ≫ w.left
      rw [← Category.assoc, ← Category.assoc, GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂]
      congr 2
      exact (GlobalTheory.IntLie.dualMap_epsMul f z).symm
  rw [key]
  rfl

private theorem eq_exp_of_log {x : WithZero (Multiplicative ℤ)} (hx : x ≠ 0) {n : ℤ} (h : WithZero.log x = n) :
    x = WithZero.exp n := by
  rw [← h, WithZero.exp_log hx]

end Helpers

theorem UpperTheory.tangent_vectors_reduction_prime :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (ρ : E →+* ℂ) (v : Fin (Dw.mult ρ) → (epsR K ⟶ t₀.G)), (∀ i, (v i).left ≫ m1.φ = y.u ρ i) → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr) (e : ℕ), 0 < e → (∀ z : K, vV T.V (iK z) = (e : ℤ) * vAdd 𝔓 z) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (td : Ix Dw → T.Frˣ) (y' : FrPt Xo c T.Fr), FrBor td yT y' → Formalism.L2.Pj.Integral T (iK.comp (algebraMap c.F K)) y' → EigenvectorLieDegree.IsLocOrd t₀.G v 𝔓 (-(vV T.V (∏ i : Fin (Dw.mult ρ), (td (some ⟨ρ, i⟩) : T.Fr)) : ℝ) / (e : ℝ)) := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y t₀ m1 ρ v hv 𝔓 T iK e he hval
  letI := (iK.comp (algebraMap c.F K)).toAlgebra
  intro yT hmap td y' hbor hint
  obtain ⟨G, t', m1', m2', ⟨ub, hubt, -, hubu, hl⟩, -⟩ := hint
  have := t'.semi.comm
  have := G.semi.comm
  have hx1 : yT.x = spMap iK ≫ y.x := hmap.1
  have hx2 : y'.x = yT.x := hbor.1
  obtain ⟨n', hn'⟩ := (GlobalTheory.sabMap_cancel_and_comp_over E H _ _ _ _ _ _ _ _ (spMap iK) m1 m1' (hx2.trans hx1)).1
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  choose v' hv' _ using fun i => GlobalTheory.existsUnique_isVecOver (f := iK) n'.cart.1 (v i)
  let u : Fin (Dw.mult ρ) → (epsR T.V ⟶ G.G) := ub ρ
  choose u' hu' huu using fun i => GlobalTheory.existsUnique_isVecOver (f := algebraMap T.V T.Fr) m2'.cart.1 (u i)
  have hvy : ∀ i, (v' i).left ≫ m1'.φ = yT.u ρ i := fun i => by
    rw [← hn', ← Category.assoc]
    refine (congrArg (· ≫ m1.φ) (hv' i)).trans ?_
    rw [Category.assoc, hv i]
    exact (hmap.2.1 ρ i).symm
  have huy : ∀ i, (u' i).left ≫ m1'.φ = y'.u ρ i := fun i => by
    obtain ⟨z, hz1, hz2⟩ := hl ρ i
    have : z = (u' i).left := by
      apply m2'.cart.1.hom_ext
      · exact hz2.trans (hu' i).symm
      · apply GlobalTheory.IntLie.spMap_frac_cancel (V := T.V)
        rw [Category.assoc, Category.assoc, ← m2'.cart.1.w, ← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ _) (hz2.trans (hu' i).symm)
    rw [← this, hz1]
  have hvt : ∀ i, IsTangent (v' i) := fun i =>
    (GlobalTheory.KSExist.FrameLift.tan_iff m1'.cart (v' i)).1 (by
      have := yT.tan ρ i
      rw [← hvy, ← hx2] at this
      exact this)
  have hve : ∀ i (a : 𝓞 E), (v' i ≫ t'.act.act a).left =
      spMap (epsScaleR (iK (algebraMap c.F K (embK c ρ a)))) ≫ (v' i).left := fun i a => by
    have h := (GlobalTheory.KSExist.FrameLift.eig_iff m1'.cart (m1'.act a) (v' i) (iK (algebraMap c.F K (embK c ρ a)))).1 (by
      have := yT.eig ρ i a
      rw [← hvy] at this
      exact this)
    rw [h]
    rfl
  choose C hCd hCl hCc using hbor.2.1 ρ
  let C' : Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) T.Fr := C
  have hC : ∀ i, IsLieComb (C' i) v' (u' i) := fun i =>
    GlobalTheory.KSExist.FrameLift.isLieComb_of_isCombAt m1'.cart v' _ _ (by
      have := hCc i
      rw [← huy, ← funext hvy, ← hx2] at this
      exact this)
  have hdet : C'.det = ∏ i : Fin (Dw.mult ρ), (td (some ⟨ρ, i⟩) : T.Fr) := by
    rw [Matrix.det_of_lowerTriangular C' (fun a b hab => hCl a b hab)]
    exact Finset.prod_congr rfl fun i _ => hCd i
  have hne : C'.det ≠ 0 := by
    rw [hdet]
    exact Finset.prod_ne_zero_iff.2 fun i _ => Units.ne_zero _
  have hut : ∀ i, IsTangent (u i) := fun i => (isTan_iff _).1 (hubt ρ i)
  refine ⟨T.V, T.Fr, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, iK, e, G.G, inferInstance, t'.G, inferInstance, m2'.φ, n'.φ, v', u, u', C'⁻¹,
    -vV T.V C'.det, he, fun z => ?_, G.semi, m2'.cart, n'.cart, hv', fun i => ⟨hut i, hu' i, _, hC i⟩,
    fun w w' hw hw' ⟨b, hb⟩ => ?_, fun i => ?_, ?_, by rw [hdet]; push_cast; rfl⟩
  · rcases eq_or_ne z 0 with rfl | hz
    · simp [he.ne']
    · have h0 : 𝔓.valuation K z ≠ 0 := by simpa using hz
      have h1 : valV T.V (iK z) ≠ 0 := valV_ne_zero ((map_ne_zero iK).2 hz)
      have h2 := hval z
      simp only [vV, vAdd] at h2
      refine (eq_exp_of_log h1 (n := (e : ℤ) * WithZero.log (𝔓.valuation K z)) (by linarith)).trans ?_
      rw [← nsmul_eq_mul, WithZero.exp_nsmul, WithZero.exp_log h0]
  · refine hubu ρ w ((isTan_iff _).2 hw) fun a z hz => ?_
    refine eig_descend hinj m2' hw hw' a z ?_
    rw [hz]
    exact eig_of_comb t'.act a _ hvt (fun i => hve i a) hb
  · rw [comb_comb hvt hC]
    have : Matrix.vecMul (C'⁻¹ i) C' = Pi.single i 1 := by
      have := congrFun (Matrix.nonsing_inv_mul C' hne.isUnit) i
      exact this.trans (by ext j; simp [Matrix.one_apply, Pi.single_apply, eq_comm])
    rw [this]
    exact (GlobalTheory.LieComb.lieComb_algebra _ _ _ v' hvt).2.2.2.1 i
  · rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀, neg_neg, vV, WithZero.exp_neg,
      WithZero.exp_log (valV_ne_zero hne)]
    rfl
