import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameChangeIntegralInvertibleMatrix
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NonemptyLift
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsModelChartGenericPointComponentStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TieBaseChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFrPtTie
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FramedPointIntegralIntegralCellAnyModelStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieBasisCoordinatesBijectiveTangent
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsCombAtIffCoordinateCombination
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsEigenvectorIffLieBasisCoordinates
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartFiniteType
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralPivotDecomposition

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.Reg.GenInt

section Sec

variable {X Y : Scheme.{0}}

def mulSec {L : LB X} (r : Γ(X, ⊤)) (s : LB.Sec L) : LB.Sec L where
  f i := resG X le_top r * s.f i
  compat i j := by
    have e : ∀ (U : X.Opens) (h : L.U i ⊓ L.U j ≤ U),
        (X.presheaf.map (homOfLE h).op).hom (resG X (le_top : U ≤ ⊤) r) = resG X le_top r := fun U h => by
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
    rw [map_mul, map_mul, s.compat i j, e, e, mul_left_comm]

theorem res_res {U V : X.Opens} (h : V ≤ U) (r : Γ(X, ⊤)) :
    (X.presheaf.map (homOfLE h).op).hom (resG X (le_top : U ≤ ⊤) r) = resG X le_top r := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem appLE_res (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (r : Γ(X, ⊤)) :
    (f.appLE U V h).hom (resG X le_top r) = resG Y le_top (f.appTop.hom r) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  rfl

theorem isoMaps_mul {L M : LB X} {w : LB.Iso L M} {s : LB.Sec L} {s' : LB.Sec M} (h : IsoMaps w s s')
    (r : Γ(X, ⊤)) : IsoMaps w (mulSec r s) (mulSec r s') := by
  intro i k
  have := h i k
  simp only [mulSec, map_mul, res_res]
  rw [this, mul_left_comm]

theorem pullSec_mul {L : LB X} {f : Y ⟶ X} {s : LB.Sec L} {s' : LB.Sec (L.pull f)} (h : PullSec f s s')
    (r : Γ(X, ⊤)) : PullSec f (mulSec r s) (mulSec (f.appTop.hom r) s') := by
  intro j hj
  simp only [mulSec, map_mul, appLE_res]
  rw [h j hj]

theorem appTop_toΓ {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (a : A) :
    (spMap φ).appTop.hom (toΓ A a) = toΓ B (φ a) := by
  have := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  exact this.symm

end Sec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem integral_scal (T : CDVR) (io : c.F →+* T.Fr) : letI := io.toAlgebra
    ∀ (y : FrPt Xo c T.Fr) (a : T.Vˣ) (s' : LB.Sec (PPx y.x))
      (hg : ∀ s'' : LB.Sec (PPx y.x), ∃! b : T.Fr, ∀ i, s''.f i = scal y.x b i * s'.f i),
      (∀ i, s'.f i = scal y.x (algebraMap T.V T.Fr a) i * y.s.f i) → Integral T io y →
      Integral T io { y with s := s', gen := hg } := by
  let _ := io.toAlgebra
  intro y a s' hg hs h
  obtain ⟨G, t', m1, m2, hu, θ, hθ, w1, w2, σ, s1, θ2, r1, r2, i1, i2, hp, hl⟩ := h
  have hc : m2.φ.appTop.hom (G.G.hom.appTop.hom (toΓ T.V a)) =
      t'.G.hom.appTop.hom (toΓ T.Fr (algebraMap T.V T.Fr a)) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, m2.cart.1.w, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply]
    exact congrArg _ (appTop_toΓ _ _)
  refine ⟨G, t', m1, m2, hu, mulSec (G.G.hom.appTop.hom (toΓ T.V a)) θ, fun τ => ?_, w1, w2, _, _, _, r1, r2,
    isoMaps_mul i1 _, isoMaps_mul i2 _, pullSec_mul hp _, ?_⟩
  · obtain ⟨b, hb, hbu⟩ := hθ τ
    have key : ∀ (d : T.V) i, resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V d)) *
        (mulSec (G.G.hom.appTop.hom (toΓ T.V a)) θ).f i =
        resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V (d * a))) * θ.f i := fun d i => by
      simp only [mulSec, map_mul, _root_.mul_assoc]
    refine ⟨b * ↑a⁻¹, fun i => ?_, fun d hd => ?_⟩
    · rw [key, Units.inv_mul_cancel_right]; exact hb i
    · rw [← hbu (d * a) fun i => by rw [← key]; exact hd i, Units.mul_inv_cancel_right]
  · intro g e1 e2 j hj
    have e3 := hl g e1 e2 j hj
    show resG _ le_top _ * s1.f j = (g.appLE _ _ hj).hom (s'.f _)
    refine Eq.symm ((congrArg _ (hs _)).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ e3.symm)))
    refine (appLE_res g _ _ hj _).trans (congrArg _ ?_)
    rw [hc, ← e2, Scheme.Hom.comp_appTop]
    rfl

theorem integral_chg (T : CDVR) (io : c.F →+* T.Fr) : letI := io.toAlgebra
    ∀ (y y' : FrPt Xo c T.Fr) (k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V) (a : T.Vˣ),
      (∀ τ, IsUnit (k τ).det) → FrChg (fun τ => (k τ).map (algebraMap T.V T.Fr)) (algebraMap T.V T.Fr a) y y' →
      Integral T io y → Integral T io y' := by
  let _ := io.toAlgebra
  intro y y' k a hk ⟨hx, hu, pm, h1, h2, h3⟩ hy
  have hk' : ∀ τ, IsUnit (k τ).transpose.det := fun τ => by rw [Matrix.det_transpose]; exact hk τ
  have hK : ∀ τ, IsUnit ((k τ).transpose.map (algebraMap T.V T.Fr)).det := fun τ => by
    have e : ((k τ).transpose.map (algebraMap T.V T.Fr)).det = algebraMap T.V T.Fr (k τ).transpose.det :=
      (RingHom.map_det _ _).symm
    rw [e]
    exact (hk' τ).map _
  have hr := GlobalTheory.IntRebase.integral_reb T io y hy (fun τ => (k τ).transpose) hk' hK
  obtain ⟨zx, zo, zu, zt, ze, zb, zs, zg⟩ := y'
  simp only at hx
  subst hx
  have eu : zu = (GlobalTheory.IntRebase.rebase₂ y _ hK).u := by
    funext τ i
    exact Formalism.L2.PjFree.isCombAt_unique (hu τ i)
      ((GlobalTheory.IntRebase.isCombAtG_iff Xo.univ.t y.x (fun j => GlobalTheory.IntRebase.ovT (t := Xo.univ.t) (y.tan τ j)) _ _).2 rfl)
  subst eu
  have ep : pm = 𝟙 _ := by
    apply pullback.hom_ext
    · refine h2.trans ?_
      simp only [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id, Category.id_comp]
      rfl
    · exact h1.trans (Category.id_comp _).symm
  subst ep
  refine integral_scal T io (GlobalTheory.IntRebase.rebase₂ y _ hK) a zs zg (fun i => ?_) hr
  exact (h3 i le_rfl).symm.trans (GlobalTheory.IntRebase.id_appLE_apply _ _ _ _)

theorem exists_factor {A V F : Type} [CommRing A] [CommRing V] [CommRing F] (i : V →+* F) (hi : Function.Injective i)
    (g : A →+* F) (hg : ∀ a, g a ∈ i.range) : ∃ g₀ : A →+* V, i.comp g₀ = g := by
  let e : V ≃+* i.range := RingEquiv.ofBijective i.rangeRestrict
    ⟨fun x y h => hi (congrArg Subtype.val h), i.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (g.codRestrict i.range hg), RingHom.ext fun a => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply (g.codRestrict i.range hg a))

theorem int_mem_range {K V F : Type} [Field K] [CommRing V] [IsDomain V] [IsIntegrallyClosed V] [Field F] [Algebra V F]
    [IsFractionRing V F] (io : K →+* F) (o : 𝓞 K) : io (algebraMap (𝓞 K) K o) ∈ (algebraMap V F).range := by
  have h1 : IsIntegral ℤ (io (algebraMap (𝓞 K) K o)) :=
    (RingOfIntegers.isIntegral_coe o).map io.toIntAlgHom
  have h2 : IsIntegral V (io (algebraMap (𝓞 K) K o)) := h1.tower_top
  exact IsIntegrallyClosed.isIntegral_iff.1 h2

theorem isUnit_of_vV (T : CDVR) (v : T.V) (h0 : algebraMap T.V T.Fr v ≠ 0) (h : vV T.V (algebraMap T.V T.Fr v) = 0) :
    IsUnit v := by
  have h1 : vV T.V (1 : T.Fr) = 0 := by simp [vV]
  have h2 := vV_mul (V := T.V) h0 (inv_ne_zero h0)
  rw [mul_inv_cancel₀ h0, h1, h, zero_add] at h2
  obtain ⟨w, hw⟩ := Formalism.L2.PjFree.mem_range_of_vV_nonneg (V := T.V) h2.le
  refine IsUnit.of_mul_eq_one w (IsFractionRing.injective T.V T.Fr ?_)
  rw [map_mul, hw, mul_inv_cancel₀ h0, map_one]

theorem exists_tie_cell (hT : Out.SecTwistSt) {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
    (M : MChart Y) {R : Type} [Field R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (y : FrPt Xo c R)
    (Λ : M.Lift f y.x) : ∃ (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n)
      (u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) R) (y₀ : FrPt Xo c R),
      (∀ τ, InCell (ix τ) (u τ)) ∧ y₀.x = y.x ∧ M.Comparison₂ f u y₀ := by
  obtain ⟨b1, b2, b3⟩ := GlobalTheory.Reg.vec_bijective E H Dw l Xo c O β Y M R f y.x Λ
  have bc := GlobalTheory.Reg.VecComb.isCombAt_iff_vec E H Dw l Xo c O β Y M R f y.x Λ
  have be := GlobalTheory.Reg.isEigAt_iff_eig E H Dw l Xo c O β Y M R f y.x Λ
  choose cv hcv using fun τ i => (b3 _ (y.tan τ i)).exists
  let g : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) R := fun τ => Matrix.of fun j i => cv τ i j
  have hg : ∀ τ a, (g τ).mulVec a = ∑ i, a i • cv τ i := fun τ a => by
    funext j
    simp [g, Matrix.mulVec, dotProduct, Finset.sum_apply, _root_.mul_comm]
  have hE : ∀ τ a, M.Eig f τ ((g τ).mulVec a) := fun τ a r => by
    rw [hg, Matrix.mulVec_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, (be τ _ _ (hcv τ i)).1 (y.eig τ i) r, smul_comm]
  have hB : ∀ τ v, M.Eig f τ v → ∃! a : Fin (Dw.mult τ) → R, (g τ).mulVec a = v := fun τ v hv => by
    obtain ⟨w, hw, -⟩ := b1 v
    obtain ⟨a, ha, hau⟩ := y.basis τ w (b2 v w hw) ((be τ v w hw).2 hv)
    refine ⟨a, ?_, fun a' ha' => hau a' ((bc _ _ _ a' w (hcv τ)).2 ?_)⟩
    · show (g τ).mulVec a = v
      rw [hg]
      exact (b3 w (b2 v w hw)).unique ((bc _ _ _ a w (hcv τ)).1 ha) hw
    · rw [← hg, ha']; exact hw
  have hli : ∀ τ, LinearIndependent R (g τ).transpose := fun τ => by
    exact Matrix.mulVec_injective_iff.1 fun a a' h => (hB τ _ (hE τ a')).unique h rfl
  choose ix u b _ h0 h1 hb hd hub using fun τ =>
    GlobalTheory.exists_integral_pivot_decomposition R ⊤ _ _ (g τ) (hli τ)
  have hdet : ∀ τ, IsUnit (b τ).det := fun τ => by
    rw [Matrix.det_of_upperTriangular (hb τ)]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hd τ i).isUnit
  have hu : ∀ τ a, (u τ).mulVec a = (g τ).mulVec ((b τ)⁻¹.mulVec a) := fun τ a => by
    rw [hub, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hdet τ), Matrix.mul_one]
  obtain ⟨y₀, hx, ht⟩ := GlobalTheory.Reg.exists_frPt_tie hT E H Dw l Xo c O β Y M R f y.x Λ u (fun τ i => by
      have e : (fun j => u τ j i) = (u τ).mulVec (Pi.single i 1) := by
        funext j; simp
      rw [e, hu]; exact hE τ _) (fun τ v hv => by
      obtain ⟨a, ha, hau⟩ := hB τ v hv
      refine ⟨(b τ).mulVec a, ?_, fun a' ha' => ?_⟩
      · show (u τ).mulVec ((b τ).mulVec a) = v
        rw [Matrix.mulVec_mulVec, ← hub]; exact ha
      · rw [← hau ((b τ)⁻¹.mulVec a') (by rw [← ha', hu]), Matrix.mulVec_mulVec,
          Matrix.mul_nonsing_inv _ (hdet τ), Matrix.one_mulVec])
  exact ⟨ix, u, y₀, fun τ => ⟨h0 τ, h1 τ⟩, hx, ht⟩

theorem exists_finset_of_lift (hT : Out.SecTwistSt) (hbc : FrBC Xo c) {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}
    (M : MChart Y) {R : Type} [Field R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (y : FrPt Xo c R)
    (Λ : M.Lift f y.x) : ∃ S : Finset R, (∀ s ∈ S, s ≠ 0) ∧ ∀ (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra
      ∀ ψ : R →ₐ[c.F] T.Fr, (∀ s ∈ S, vV T.V (ψ s) = 0) → ∀ z : FrPt Xo c T.Fr, FrMap ψ y z → Integral T io z := by
  classical
  obtain ⟨ix, u, y₀, hcell, hx, ht⟩ := exists_tie_cell hT M f y Λ
  obtain ⟨k, a, hk, hchg⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c R y₀ y).1 hx.symm
  obtain ⟨α, hα, hfin, -⟩ := (GlobalTheory.ModelPoints.model_points_charts E H Dw l Xo c _ _ Y).2.2 M.U M.hU
  have hfα : f.comp α = (algebraMap c.F R).comp (algebraMap (𝓞 c.F) c.F) := by
    have e : spMap (f.comp α) = spMap ((algebraMap c.F R).comp (algebraMap (𝓞 c.F) c.F)) := by
      rw [← Formalism.L2.PjFree.spMap_comp', ← Formalism.L2.PjFree.spMap_comp', ← hα, ← Category.assoc, ← Λ.xF_j,
        Category.assoc, Y.j_s, ← Category.assoc, Λ.xF_snd]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  let _ := α.toAlgebra
  obtain ⟨G, hG⟩ := hfin.out
  let S₀ : Finset R := G.image f ∪
    Finset.univ.biUnion (fun τ : E →+* ℂ => Finset.univ.image fun p : Fin M.n × Fin (Dw.mult τ) => u τ p.1 p.2) ∪
    Finset.univ.biUnion (fun τ : E →+* ℂ =>
      Finset.univ.image fun p : Fin (Dw.mult τ) × Fin (Dw.mult τ) => k τ p.1 p.2) ∪
    Finset.univ.image (fun τ : E →+* ℂ => (k τ).det) ∪ {(a : R)}
  refine ⟨S₀.filter (· ≠ 0), fun s hs => (Finset.mem_filter.1 hs).2, fun T io => ?_⟩
  let _ := io.toAlgebra
  intro ψ hψ z hz
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  have hin : ∀ s ∈ S₀, ∃ v, algebraMap T.V T.Fr v = ψ s := fun s hs => by
    by_cases h0 : s = 0
    · exact ⟨0, by rw [h0, map_zero, map_zero]⟩
    · exact Formalism.L2.PjFree.mem_range_of_vV_nonneg (hψ s (Finset.mem_filter.2 ⟨hs, h0⟩)).ge
  have hun : ∀ s ∈ S₀, IsUnit s → ∀ v, algebraMap T.V T.Fr v = ψ s → IsUnit v := fun s hs h0 v hv =>
    isUnit_of_vV T v (by rw [hv]; exact (h0.map ψ).ne_zero)
      (by rw [hv]; exact hψ s (Finset.mem_filter.2 ⟨hs, h0.ne_zero⟩))
  obtain ⟨f₀, hf₀⟩ := exists_factor (algebraMap T.V T.Fr) hinj (ψ.toRingHom.comp f) fun r => by
    have hr : r ∈ Algebra.adjoin (𝓞 c.F) (G : Set Γ(Y.X, M.U)) := hG ▸ Algebra.mem_top
    induction hr using Algebra.adjoin_induction with
    | mem x hx => exact hin (f x) (by simp only [S₀, Finset.mem_union]; exact .inl (.inl (.inl (.inl
        (Finset.mem_image_of_mem f hx)))))
    | algebraMap o =>
      have e : (ψ.toRingHom.comp f) (algebraMap (𝓞 c.F) _ o) = io (algebraMap (𝓞 c.F) c.F o) :=
        (congrArg ψ (RingHom.congr_fun hfα o)).trans (ψ.commutes _)
      rw [e]; exact int_mem_range io o
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  choose u₀ hu₀ using fun τ j i => hin (u τ j i) (by
    simp only [S₀, Finset.mem_union, Finset.mem_biUnion]
    exact .inl (.inl (.inl (.inr ⟨τ, Finset.mem_univ _, Finset.mem_image.2 ⟨(j, i), Finset.mem_univ _, rfl⟩⟩))))
  choose k₀ hk₀ using fun τ j i => hin (k τ j i) (by
    simp only [S₀, Finset.mem_union, Finset.mem_biUnion]
    exact .inl (.inl (.inr ⟨τ, Finset.mem_univ _, Finset.mem_image.2 ⟨(j, i), Finset.mem_univ _, rfl⟩⟩)))
  have ha : (a : R) ∈ S₀ := by simp [S₀]
  obtain ⟨a₀, ha₀⟩ := hin a ha
  obtain ⟨a₁, rfl⟩ := hun a ha a.isUnit a₀ ha₀
  have eu : (fun τ => (Matrix.of (u₀ τ)).map (algebraMap T.V T.Fr)) = fun τ => (u τ).map ψ :=
    funext fun τ => Matrix.ext fun j i => hu₀ τ j i
  have ek : ∀ τ, (Matrix.of (k₀ τ)).map (algebraMap T.V T.Fr) = (k τ).map ψ :=
    fun τ => Matrix.ext fun j i => hk₀ τ j i
  obtain ⟨z₀, hz₀⟩ := hbc R T.Fr ψ y₀
  have ht₀ := GlobalTheory.Reg.MChart.tie_baseChange E H Dw l Xo c _ _ Y M R T.Fr f ψ u y₀ z₀ ht hz₀
  rw [← hf₀, ← eu] at ht₀
  have hi₀ : Integral T io z₀ := GlobalTheory.T.framedPoint_integral_integralCell_anyModel hT E H Dw l Xo c _ _ Y M T io f₀ ix (fun τ => Matrix.of (u₀ τ))
    (fun τ => ⟨fun i j hij => hinj ((hu₀ τ _ _).trans (by rw [(hcell τ).1 i j hij, map_zero, map_zero])),
      fun i => hinj ((hu₀ τ _ _).trans (by rw [(hcell τ).2 i, map_one, map_one]))⟩) z₀ ht₀
  have hc := (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c R T.Fr ψ y₀ y z₀ z k a hchg hz₀).1 hz
  refine integral_chg T io z₀ z (fun τ => Matrix.of (k₀ τ)) a₁ (fun τ => ?_) ?_ hi₀
  · refine hun (k τ).det ?_ (hk τ) _ ?_
    · simp only [S₀, Finset.mem_union]
      exact .inl (.inr (Finset.mem_image_of_mem _ (Finset.mem_univ τ)))
    · rw [RingHom.map_det, RingHom.mapMatrix_apply, ek]
      exact (ψ.toRingHom.map_det (k τ)).symm
  · rw [funext ek, ha₀]
    exact hc

theorem genFr_integral : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FrBC Xo c → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (h : GenFrEx Xo c) (Z : Comp Xo c), ∃ S : Finset (Om Z), (∀ s ∈ S, s ≠ 0) ∧ ∀ (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ ψ : Om Z →ₐ[c.F] T.Fr, (∀ s ∈ S, vV T.V (ψ s) = 0) → ∀ z : FrPt Xo c T.Fr, FrMap ψ (genFr h Z) z → Integral T io z := by
  intro hT E _ _ _ H Dw l Xo c hbc Y h Z
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_modelChart_genericPoint_component hT E H Dw l Xo c Y Z
  let xF : Sp (Om Z) ⟶ Xo.XF c := spMap (algebraMap (kap Z) (Om Z)) ≫ genSp Z
  have hpt : ∀ p, genSp Z p = genPt Z := fun p => Scheme.fromSpecResidueField_apply _ p
  obtain ⟨f, hf, -⟩ := GlobalTheory.ModelPoints.existsUnique_chartHom M.hU (Om Z) (xF ≫ Y.j) (by
    show Y.j (genSp Z _) ∈ M.U
    rw [hpt]; exact hM)
  have hs : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F (Om Z)) := by
    have e : genSp Z ≫ strK = spMap (algebraMap c.F (kap Z)) := (Spec.map_preimage _).symm
    rw [IsScalarTower.algebraMap_eq c.F (kap Z) (Om Z), ← Formalism.L2.PjFree.spMap_comp', ← e]
    exact Category.assoc _ _ _
  obtain ⟨Λ⟩ := GlobalTheory.Reg.MChart.nonempty_lift E H Dw l Xo c _ _ Y M (Om Z) f xF hs hf.symm
  have ex : xF ≫ pullback.fst _ _ = (genFr h Z).x := (Category.assoc _ _ _).trans (isGenFr_genFr h Z).1.symm
  rw [ex] at Λ
  exact exists_finset_of_lift hT hbc M f (genFr h Z) Λ

end GlobalTheory.Reg.GenInt
