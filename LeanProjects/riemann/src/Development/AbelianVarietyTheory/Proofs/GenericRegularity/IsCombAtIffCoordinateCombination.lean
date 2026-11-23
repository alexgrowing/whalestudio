import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec

noncomputable section

namespace GlobalTheory.Reg.VecComb

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {M : MChart Y}
  {R : Type} [CommRing R]

theorem comb_unique {x : Sp R ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)} {a : Fin m → R}
    {w w' : Sp (DualNumber R) ⟶ Xo.univ.t.G.left} (h : IsCombAt x v a w) (h' : IsCombAt x v a w') : w = w' := by
  obtain ⟨u, hu1, hu2⟩ := h
  obtain ⟨u', hu1', hu2'⟩ := h'
  have e : u = u' := funext fun i => Over.OverMorphism.ext ((hu1 i).trans (hu1' i).symm)
  rw [← hu2, ← hu2', e]

theorem comb_exists {x : Sp R ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)}
    (hv : ∀ j, v j ≫ Xo.univ.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) (a : Fin m → R) :
    ∃ w, IsCombAt x v a w := by
  refine ⟨_, fun i => Over.homMk (spMap (epsMul (a i)) ≫ v i) ?_, fun i => rfl, rfl⟩
  show (spMap (epsMul (a i)) ≫ v i) ≫ Xo.univ.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x
  have e : (epsMul (a i)).comp (algebraMap R (DualNumber R)) = algebraMap R (DualNumber R) :=
    RingHom.ext fun r => by simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  rw [Category.assoc, hv i, ← Category.assoc, ← spMap_comp, e]

variable [Algebra c.F R] {f : Γ(Y.X, M.U) →+* R} {x : Sp R ⟶ Xo.X}

theorem exists_frame (Λ : M.Lift f x) : ∃ V : Fin M.n → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left),
    (∀ j, IsTanAt x (V j)) ∧ ∀ cv w, Λ.Vec cv w ↔ IsCombAt x V cv w := by
  obtain ⟨v', hv1, ⟨htan, -⟩, -⟩ := M.lie R f Λ.t' Λ.m2
  have p1 : IsGrpPullback Λ.t'.G Xo.univ.t.G x Λ.m1.φ := Λ.m1.2
  have p2 : IsGrpPullback Λ.t'.G Y.t.G (spMap f ≫ M.hU.fromSpec) Λ.m2.φ := Λ.m2.2
  refine ⟨fun j => (v' j).left ≫ Λ.m1.φ, fun j => ?_, fun cv w => ?_⟩
  · unfold IsTanAt
    constructor
    · rw [Category.assoc, p1.1.w, ← Category.assoc, Over.w (v' j)]
      rfl
    · exact (Chart.tan_push p1 (v' j)).1 (htan j)
  · unfold MChart.Lift.Vec IsCombAt
    constructor
    · rintro ⟨v'', u', hv'', hc, hw⟩
      have e : v'' = v' := funext fun j => Chart.inj_over p2 ((hv'' j).trans (hv1 j).symm)
      rw [e] at hc
      obtain ⟨u, hu1, hu2⟩ := (Chart.comb_push p1 cv v' u').1 hc
      exact ⟨u, fun i => hu1 i, hu2.trans hw⟩
    · rintro ⟨u, hu1, hu2⟩
      have hw : w ≫ Xo.univ.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x := by
        rw [← hu2]
        exact Over.w (List.ofFn u).prod
      let u' : epsR R ⟶ Λ.t'.G :=
        Over.homMk (p1.1.lift w (spMap (algebraMap R (DualNumber R))) hw) (p1.1.lift_snd _ _ _)
      have hl : u'.left ≫ Λ.m1.φ = w := p1.1.lift_fst _ _ _
      exact ⟨v', u', hv1, (Chart.comb_push p1 cv v' u').2 ⟨u, fun i => hu1 i, hu2.trans hl.symm⟩, hl⟩

theorem isCombAt_iff_vec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ (m : ℕ) (cv : Fin m → Fin M.n → R) (w : Fin m → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)) (a : Fin m → R) (w' : Sp (DualNumber R) ⟶ Xo.univ.t.G.left), (∀ i, Λ.Vec (cv i) (w i)) → (IsCombAt x w a w' ↔ Λ.Vec (∑ i, a i • cv i) w') := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ m cv w a w' hw
  obtain ⟨V, hV, hVec⟩ := exists_frame Λ
  have hwc : ∀ i, IsCombAt x V (cv i) (w i) := fun i => (hVec _ _).1 (hw i)
  have e : (∑ i, a i • cv i) = (Matrix.of fun j i => cv i j).mulVec a := by
    funext j
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have key : ∀ w'', IsCombAt x w a w'' → IsCombAt x V (∑ i, a i • cv i) w'' := by
    intro w'' h
    rw [e]
    exact GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo R x V hV w _ a w'' (fun i => hwc i) h
  have hov : ∀ {k : Fin M.n → R} {w0}, IsCombAt x V k w0 →
      w0 ≫ Xo.univ.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x := by
    rintro k w0 ⟨u, -, hu⟩
    rw [← hu]
    exact Over.w (List.ofFn u).prod
  rw [hVec]
  constructor
  · exact key w'
  · intro h
    obtain ⟨w'', h''⟩ := comb_exists (fun i => hov (hwc i)) a
    exact comb_unique (key w'' h'') h ▸ h''

end GlobalTheory.Reg.VecComb
