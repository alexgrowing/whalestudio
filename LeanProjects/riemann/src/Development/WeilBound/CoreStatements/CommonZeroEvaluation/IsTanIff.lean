import Mathlib
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.CombComb
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.ExistsLeftInv
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjEmbRtOfNe
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrPullbackSemiabelianStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartFiniteType
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

noncomputable section

namespace ModelDimension.Near

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
  {R R' : Type} [CommRing R] [CommRing R']

theorem tanY_gt [Algebra c.F R] (y : FrPt Xo c R) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    GT Y.t.G (Small.ptY Y y) (Small.tanY Y y τ i) :=
  gt_push Y.m.cart (gt_pull Y.m0.cart (Small.tanF_hom Y y τ i) (by
    have e : Small.tanF Y y τ i ≫ Y.m0.cm.F = y.u τ i := Small.tanF_φ Y y τ i
    rw [e, Small.ptF_fst]
    exact y.tan τ i))

theorem ptF_bor [Algebra c.F R] {t : Ix Dw → Rˣ} {y y' : FrPt Xo c R} (h : FrBor t y y') :
    Small.ptF y' = Small.ptF y := by
  apply pullback.hom_ext
  · rw [Small.ptF_fst, Small.ptF_fst, h.1]
  · rw [Small.ptF_snd, Small.ptF_snd]

theorem ptY_bor [Algebra c.F R] {t : Ix Dw → Rˣ} {y y' : FrPt Xo c R} (h : FrBor t y y') :
    Small.ptY Y y' = Small.ptY Y y := by
  rw [Small.ptY, Small.ptY, ptF_bor h]

theorem tanY_bor [Algebra c.F R] {t : Ix Dw → Rˣ} {y y' : FrPt Xo c R} (h : FrBor t y y') (τ : E →+* ℂ) :
    ∃ C : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R, C.BlockTriangular id ∧ (∀ i, C i i = t (some ⟨τ, i⟩)) ∧
      ∀ i, GC Y.t.G (Small.ptY Y y) (Small.tanY Y y τ) (fun j => C j i) (Small.tanY Y y' τ i) := by
  choose cf h1 h2 h3 using h.2.1 τ
  refine ⟨Matrix.of fun j i => cf i j, fun j i hij => h2 i j hij, h1, fun i => ?_⟩
  refine gc_push Y.m.cart (gc_pull Y.m0.cart (Small.tanF_hom Y y τ) (by rw [Small.tanF_hom, ptF_bor h]) ?_)
  have e : ∀ (y : FrPt Xo c R) i, Small.tanF Y y τ i ≫ Y.m0.cm.F = y.u τ i := fun y i => Small.tanF_φ Y y τ i
  simp only [e, Small.ptF_fst]
  exact h3 i

variable {U : Y.X.Opens} (hU : IsAffineOpen U) {n : ℕ} (v₀ : Fin n → (Sp (DualNumber Γ(Y.X, U)) ⟶ Y.t.G.left))

def IsChart : Prop :=
  ∀ (R' : Type) [CommRing R'] (f : Γ(Y.X, U) →+* R') (G' : Over (Sp R')) [GrpObj G'] (φ : G'.left ⟶ Y.t.G.left),
    IsGrpPullback G' Y.t.G (spMap f ≫ hU.fromSpec) φ →
      ∃ v' : Fin n → (epsR R' ⟶ G'), (∀ j, (v' j).left ≫ φ = spMap (dualMapR f) ≫ v₀ j) ∧ IsLieBasis v'

def Crd (f : Γ(Y.X, U) →+* R) (cv : Fin n → R) (w : Sp (DualNumber R) ⟶ Y.t.G.left) : Prop :=
  GC Y.t.G (spMap f ≫ hU.fromSpec) (fun j => spMap (dualMapR f) ≫ v₀ j) cv w

variable {Y hU v₀}

theorem IsChart.isBas (hC : IsChart Y hU v₀) (f : Γ(Y.X, U) →+* R) :
    IsBas Y.t.G (spMap f ≫ hU.fromSpec) (fun j => spMap (dualMapR f) ≫ v₀ j) := by
  obtain ⟨t, ⟨m⟩⟩ := (GlobalTheory.ModelPoints.model_points_charts E H Dw l Xo c O β Y).2.1 (Sp R) (spMap f ≫ hU.fromSpec)
  obtain ⟨v, hv, hb⟩ := hC R f t.G m.φ m.cart
  exact ⟨t.G, inferInstance, inferInstance, m.φ, m.cart, v, hv, hb⟩

theorem Crd.bc (ψ : R →+* R') {f : Γ(Y.X, U) →+* R} {cv : Fin n → R} {w : Sp (DualNumber R) ⟶ Y.t.G.left}
    (h : Crd Y hU v₀ f cv w) : Crd Y hU v₀ (ψ.comp f) (fun j => ψ (cv j)) (spMap (dualMapR ψ) ≫ w) := by
  have h1 := gc_bc ψ h
  have e : dualMapR (ψ.comp f) = (dualMapR ψ).comp (dualMapR f) := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [dualMapR]
  unfold Crd
  rw [e, spMap_comp, spMap_comp, Category.assoc]
  simpa only [Category.assoc] using h1

theorem IsChart.crd_bor (hC : IsChart Y hU v₀) [Algebra c.F R] {t : Ix Dw → Rˣ} {y y' : FrPt Xo c R}
    (h : FrBor t y y') (τ : E →+* ℂ) :
    ∃ C : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R, C.BlockTriangular id ∧ (∀ i, C i i = t (some ⟨τ, i⟩)) ∧
      ∀ (f : Γ(Y.X, U) →+* R), Small.ptY Y y = spMap f ≫ hU.fromSpec →
        ∀ (g u : Matrix (Fin n) (Fin (Dw.mult τ)) R), (∀ i, Crd Y hU v₀ f (fun j => g j i) (Small.tanY Y y τ i)) →
          (∀ i, Crd Y hU v₀ f (fun j => u j i) (Small.tanY Y y' τ i)) → g * C = u := by
  obtain ⟨C, h1, h2, h3⟩ := tanY_bor Y h τ
  refine ⟨C, h1, h2, fun f hf g u hg hu => ?_⟩
  rw [hf] at h3
  ext j i
  exact congrFun ((hC.isBas f).unique ((hC.isBas f).comb hg (h3 i)) (hu i)) j

theorem isTan_iff {A : Over (Sp R)} [GrpObj A] (w : epsR R ⟶ A) : IsTan (V := R) (R := R) w ↔ IsTangent w := by
  have e : (1 : ptOver R R ⟶ A).left = η[A].left := by
    show spMap (RingHom.id R) ≫ η[A].left = _
    have : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp]
  unfold IsTan IsTangent
  rw [e]

theorem IsChart.integral (hExt : GlobalTheory.Published.SemiAbelianHomExtension) (hC : IsChart Y hU v₀) {T : CDVR}
    {io : c.F →+* T.Fr} (y : IntFr Xo c T io) (f₀ : Γ(Y.X, U) →+* T.V)
    (hf : letI := io.toAlgebra; Small.ptY Y y.1 = spMap ((algebraMap T.V T.Fr).comp f₀) ≫ hU.fromSpec)
    (τ : E →+* ℂ) :
    letI := io.toAlgebra
    ∃ u : Matrix (Fin n) (Fin (Dw.mult τ)) T.V, Prim u ∧
      ∀ i, Crd Y hU v₀ ((algebraMap T.V T.Fr).comp f₀) (fun j => algebraMap T.V T.Fr (u j i))
        (Small.tanY Y y.1 τ i) := by
  letI := io.toAlgebra
  obtain ⟨G, t', m1, m2, ⟨ub, htan, heig, hbasis, hlift⟩, -⟩ := y.2.2
  have wa : m1.φ ≫ Xo.univ.t.G.hom = (t'.G.hom ≫ Small.ptF y.1) ≫ pullback.fst _ _ := by
    rw [m1.cart.1.w, Category.assoc, Small.ptF_fst]
  let a : t'.G.left ⟶ Y.oF.t.G.left := Y.m0.cart.1.lift m1.φ (t'.G.hom ≫ Small.ptF y.1) wa
  have ha1 : a ≫ Y.m0.toSABMap.φ = m1.φ := IsPullback.lift_fst _ _ _ _
  have ha2 : a ≫ Y.oF.t.G.hom = t'.G.hom ≫ Small.ptF y.1 := IsPullback.lift_snd _ _ _ _
  have gpa : IsGrpPullback t'.G Y.oF.t.G (Small.ptF y.1) a :=
    IsGrpPullback.cancel Y.m0.cart (m1.cart.congr (Small.ptF_fst y.1).symm ha1.symm) ha2
  have hg : Small.ptY Y y.1 = spMap (algebraMap T.V T.Fr) ≫ spMap f₀ ≫ hU.fromSpec := by
    rw [hf, spMap_comp, Category.assoc]
  have gpY : IsGrpPullback t'.G Y.t.G (spMap (algebraMap T.V T.Fr) ≫ spMap f₀ ≫ hU.fromSpec) (a ≫ Y.m.φ) :=
    (gpa.comp Y.m.cart).congr hg rfl
  have acta : ∀ r, (t'.act.act r).left ≫ a = a ≫ (Y.oF.t.act.act r).left := by
    intro r
    apply Y.m0.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, ha1, Y.m0.act r, ← Category.assoc, ha1, m1.act r]
    · rw [Category.assoc, Category.assoc, ha2, Over.w (Y.oF.t.act.act r), ha2, ← Category.assoc,
        Over.w (t'.act.act r)]
  obtain ⟨Ψ, hΨ, hm2, -⟩ := GlobalTheory.T.complete_dvr_pullback_semiabelian E H hExt Y.X Y.t T (spMap f₀ ≫ hU.fromSpec) G t' m2 (a ≫ Y.m.φ) gpY
    (fun r => by rw [← Category.assoc, acta r, Category.assoc, Y.m.act r, Category.assoc])
  obtain ⟨v, hv, hb⟩ := hC T.V f₀ G.G Ψ hΨ
  obtain ⟨u, hu, hp⟩ := exists_prim hb
    (I := {q : 𝓞 E × T.V // algebraMap T.V T.Fr q.2 = io (embK c τ q.1)})
    (fun q => G.act.act q.1.1) (fun q => G.act.hom _) (fun q => q.1.2) (ub τ)
    (fun i => (isTan_iff _).1 (htan τ i)) (fun i q => heig τ i _ _ q.2)
    (fun w hw he => hbasis τ w ((isTan_iff _).2 hw) fun a z hz => he ⟨(a, z), hz⟩)
  refine ⟨u, hp, fun i => ?_⟩
  have h1 : Crd Y hU v₀ f₀ (fun j => u j i) ((ub τ i).left ≫ Ψ) := by
    have := (gc_iff hΨ _ _ _).1 (hu i)
    simp only [hv] at this
    exact this
  have h2 := h1.bc (algebraMap T.V T.Fr)
  obtain ⟨u', hu1, hu2⟩ := hlift τ i
  have hbase := GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.base_eq T G t' m2 _ u' hu2
  have e : u' ≫ a = Small.tanF Y y.1 τ i := by
    apply Small.eq_tanF
    · rw [Category.assoc, ha1, hu1]
    · rw [Category.assoc, ha2, ← Category.assoc, hbase]
  have e2 : Small.tanY Y y.1 τ i = spMap (dualMapR (algebraMap T.V T.Fr)) ≫ (ub τ i).left ≫ Ψ := by
    rw [Small.tanY, ← e, Category.assoc, ← hm2, ← Category.assoc, hu2, Category.assoc]
    rfl
  rw [e2]
  exact h2

end ModelDimension.Near
