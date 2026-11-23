import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SqMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientLineBundleGauge
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjointRelationGeneratorCorrStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermJetLiftStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermFunPf

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.UAxis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdTr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

section Prod

variable {U : Type} [CommGroup U]

theorem prod_cube (h : ULift.{0} (Finset (Fin 2)) → U) :
    ∏ I, h I ^ cε 2 I = h ⟨∅⟩ * (h ⟨{0}⟩)⁻¹ * (h ⟨{1}⟩)⁻¹ * h ⟨{0, 1}⟩ := by
  have e : ∏ I, h I ^ cε 2 I = ∏ I : Finset (Fin 2), h ⟨I⟩ ^ cε 2 ⟨I⟩ :=
    Fintype.prod_equiv Equiv.ulift _ _ (fun _ => rfl)
  have u : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [e, u, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  simp [cε, _root_.mul_assoc, zpow_neg]

end Prod

section Psum

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (A B : T ⟶ G)

theorem psum_nil : psum G ![A, B] ∅ = 1 := by
  have f : (List.finRange 2).filter (· ∈ (∅ : Finset (Fin 2))) = [] := by decide
  unfold psum
  rw [f]
  rfl

theorem psum_fst : psum G ![A, B] {0} = A := by
  have f : (List.finRange 2).filter (· ∈ ({0} : Finset (Fin 2))) = [0] := by decide
  unfold psum
  rw [f]
  exact _root_.mul_one A

theorem psum_snd : psum G ![A, B] {1} = B := by
  have f : (List.finRange 2).filter (· ∈ ({1} : Finset (Fin 2))) = [1] := by decide
  unfold psum
  rw [f]
  exact _root_.mul_one B

theorem psum_both : psum G ![A, B] {0, 1} = A * B := by
  have f : (List.finRange 2).filter (· ∈ ({0, 1} : Finset (Fin 2))) = [0, 1] := by decide
  unfold psum
  rw [f]
  exact congrArg (A * ·) (_root_.mul_one B)

end Psum

section Fib

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {k : Type} [Field k] (x : Sp k ⟶ X)

theorem one_left {S : Scheme.{0}} (G : Over S) [GrpObj G] (T : Over S) : (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  rw [Hom.one_def]
  simp

theorem one_fst (T : Over (Sp k)) :
    (1 : T ⟶ GF t x).left ≫ pullback.fst t.G.hom x = (1 : Over.mk (T.hom ≫ x) ⟶ t.G).left :=
  congrArg (fun z => z.left) (map_one (pushHom (isGrpPullback_pullback t.G x) T))

theorem one_map {T : Over (Sp k)} (c : t.G ⟶ t.G) [IsMonHom c] :
    (1 : T ⟶ GF t x) ≫ (Over.pullback x).map c = 1 := by
  apply fib_ext
  have A : ((Over.pullback x).map c).left ≫ pullback.fst t.G.hom x = pullback.fst t.G.hom x ≫ c.left :=
    pullback.lift_fst _ _ _
  rw [Over.comp_left, Category.assoc, A, ← Category.assoc, one_fst, ← Over.comp_left, MonObj.one_comp]

theorem adF_inl {T : Over (Sp k)} (P R : T ⟶ GF t x) (a : 𝓞 E) (I : ULift.{0} (Finset (Fin 2))) :
    (lift P R).left ≫ adF t x a (Sum.inl I) =
      (psum (GF t x) ![P, R ≫ (Over.pullback x).map (t.act.act (H.bar a))] I.down).left := by
  show (lift P R).left ≫ (sqPt t x (psum t.G ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)] I.down)).left = _
  rw [sqPt_psum, ← Over.comp_left, comp_psum]
  refine congrArg (fun z => (psum (GF t x) z I.down).left) (funext fun i => ?_)
  fin_cases i
  · simp [sqPt_fst]
  · simp [sqPt_comp, sqPt_snd]

theorem adF_inr {T : Over (Sp k)} (P R : T ⟶ GF t x) (a : 𝓞 E) (I : ULift.{0} (Finset (Fin 2))) :
    (lift P R).left ≫ adF t x a (Sum.inr I) =
      (psum (GF t x) ![P ≫ (Over.pullback x).map (t.act.act a), R] I.down).left := by
  show (lift P R).left ≫ (sqPt t x (psum t.G ![fst t.G t.G ≫ t.act.act a, snd t.G t.G] I.down)).left = _
  rw [sqPt_psum, ← Over.comp_left, comp_psum]
  refine congrArg (fun z => (psum (GF t x) z I.down).left) (funext fun i => ?_)
  fin_cases i
  · simp [sqPt_comp, sqPt_fst]
  · simp [sqPt_snd]

end Fib

section Vals

variable {X Y F Y' Z : Scheme.{0}} {L : LB X} {M : LB Y} {f : F ⟶ X} {g : F ⟶ Y}

theorem appTop_eq_one (r : Z ⟶ Y') (u : Γ(Y', ⊤)ˣ) (h : ∀ z, gm r z ⊤ u = 1) : r.appTop.hom u.val = 1 := by
  refine fn_ext (V := ⊤) fun z hz => ?_
  have e : gs (𝟙 Z) z ⊤ (r.appTop.hom u.val) = gs (𝟙 Z ≫ r) z ⊤ u.val := gs_pull (𝟙 Z) r z ⊤ trivial u.val
  rw [e, Category.id_comp, gs_unit r z ⊤ trivial, h z, gs_eq (𝟙 Z) z ⊤ trivial, map_one, map_one]
  rfl

theorem tr_one {K : Type} [Fintype K] (hL : L.IsLB) (hM : M.IsLB) {w : LB.Iso (L.pull f) (M.pull g)}
    {φ : K → (Y' ⟶ F)} {φL : K → (Y' ⟶ X)} {φM : K → (Y' ⟶ Y)} {ε : K → ℤ} {c : LB.Gen (LB.LinComb L φL ε)}
    {b : LB.Gen (LB.LinComb M φM ε)} {u : Γ(Y', ⊤)ˣ} (hT : Tr w φ φL φM ε c b u) (r : Z ⟶ Y')
    (hc : ∀ z JL, Good L z JL → val c r z JL = 1) (hb : ∀ z JM, Good M z JM → val b r z JM = 1)
    (hp : ∀ z JL JM, ∏ k, wv w (r ≫ φ k) z JL JM ^ ε k = 1) : r.appTop.hom u.val = 1 :=
  appTop_eq_one r u fun z => by
    choose JL hJL using fun χ : Z ⟶ X => exists_chart hL (χ z)
    choose JM hJM using fun χ : Z ⟶ Y => exists_chart hM (χ z)
    have e := hT Z r z JL JM hJL hJM
    rw [hc z JL hJL, hp, hb z JM hJM, _root_.mul_one, _root_.mul_one] at e
    exact e.symm

theorem val_pull_one {Y₀ Y₁ Y₂ : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ}
    (c : LB.Gen (LB.LinComb L φ ε)) (s : Y₁ ⟶ Y₀) (ρ : Y₂ ⟶ Y₀)
    (h : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε c ρ) (LB.oneGen L)) (r : Z ⟶ Y₁) (q : Z ⟶ Y₂)
    (e : r ≫ s = q ≫ ρ) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) : val (LB.pullGen L φ ε c s) r z J = 1 := by
  rw [val_pull hJ, e, ← val_pull hJ, val_corr hJ h, val_one]

end Vals

section Pairs

variable {U : Type} [CommGroup U] {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S}
  {F : Scheme.{0}}

theorem prod_left (W : (T.left ⟶ G.left) → U) (B : T ⟶ G) :
    ∏ I : ULift.{0} (Finset (Fin 2)), W (psum G ![1, B] I.down).left ^ cε 2 I = 1 := by
  rw [prod_cube (fun I => W (psum G ![1, B] I.down).left)]
  simp only [psum_nil, psum_fst, psum_snd, psum_both, _root_.one_mul]
  simp

theorem prod_right (W : (T.left ⟶ G.left) → U) (A : T ⟶ G) :
    ∏ I : ULift.{0} (Finset (Fin 2)), W (psum G ![A, 1] I.down).left ^ cε 2 I = 1 := by
  rw [prod_cube (fun I => W (psum G ![A, 1] I.down).left)]
  simp only [psum_nil, psum_fst, psum_snd, psum_both, _root_.mul_one]
  simp [mul_comm]

end Pairs

section Fib2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {k : Type} [Field k] (x : Sp k ⟶ X)

theorem prod_ad {U : Type} [CommGroup U] {T : Over (Sp k)} (P R : T ⟶ GF t x) (a : 𝓞 E) (W : (T.left ⟶ (GF t x).left) → U)
    (h₀ : ∏ I : ULift.{0} (Finset (Fin 2)), W (psum (GF t x) ![P, R ≫ (Over.pullback x).map (t.act.act (H.bar a))] I.down).left ^ cε 2 I = 1)
    (h₁ : ∏ I : ULift.{0} (Finset (Fin 2)), W (psum (GF t x) ![P ≫ (Over.pullback x).map (t.act.act a), R] I.down).left ^ cε 2 I = 1) :
    ∏ i : ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)), W ((lift P R).left ≫ adF t x a i) ^ (Sum.elim (cε 2) (fun I => -cε 2 I) i) = 1 := by
  have e₀ := adF_inl t x P R a
  have e₁ := adF_inr t x P R a
  have A : ∏ I : ULift.{0} (Finset (Fin 2)), W ((lift P R).left ≫ adF t x a (Sum.inl I)) ^ cε 2 I = 1 :=
    (Finset.prod_congr rfl fun I _ => congrArg (fun z => W z ^ cε 2 I) (e₀ I)).trans h₀
  have B : ∏ I : ULift.{0} (Finset (Fin 2)), W ((lift P R).left ≫ adF t x a (Sum.inr I)) ^ cε 2 I = 1 :=
    (Finset.prod_congr rfl fun I _ => congrArg (fun z => W z ^ cε 2 I) (e₁ I)).trans h₁
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rw [A, B, inv_one, _root_.mul_one]

theorem adjoint_product_first_axis {U : Type} [CommGroup U] {T : Over (Sp k)} (R : T ⟶ GF t x) (a : 𝓞 E)
    (W : (T.left ⟶ (GF t x).left) → U) :
    ∏ i : ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)), W ((lift 1 R).left ≫ adF t x a i) ^ (Sum.elim (cε 2) (fun I => -cε 2 I) i) = 1 := by
  haveI := t.act.hom a
  refine prod_ad t x 1 R a W (prod_left _ W _) ?_
  rw [one_map]
  exact prod_left _ W _

theorem adjoint_product_second_axis {U : Type} [CommGroup U] {T : Over (Sp k)} (P : T ⟶ GF t x) (a : 𝓞 E)
    (W : (T.left ⟶ (GF t x).left) → U) :
    ∏ i : ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)), W ((lift P 1).left ≫ adF t x a i) ^ (Sum.elim (cε 2) (fun I => -cε 2 I) i) = 1 := by
  haveI := t.act.hom (H.bar a)
  refine prod_ad t x P 1 a W ?_ (prod_right _ W _)
  rw [one_map]
  exact prod_right _ W _

theorem left_first_axis_lift {T : Over (Sp k)} (P : T ⟶ GF t x) : P.left ≫ ax0 t x = (lift 1 P).left := by
  rw [ax0, ← Over.comp_left, comp_lift, Category.comp_id, MonObj.comp_one]

theorem left_second_axis_lift {T : Over (Sp k)} (P : T ⟶ GF t x) : P.left ≫ ax1 t x = (lift P 1).left := by
  rw [ax1, ← Over.comp_left, comp_lift, Category.comp_id, MonObj.comp_one]

theorem lift_sq {R : Type} [CommRing R] [Algebra k R] (P Q : overAt (𝟙 (Sp k)) R ⟶ GF t x) (p q : overAt x R ⟶ t.G)
    (hp : P.left ≫ pullback.fst t.G.hom x = p.left) (hq : Q.left ≫ pullback.fst t.G.hom x = q.left) :
    (lift P Q).left ≫ sqMap t x = (lift p q).left := by
  apply pullback.hom_ext
  · show ((lift P Q).left ≫ sqMap t x) ≫ (fst t.G t.G).left = (lift p q).left ≫ (fst t.G t.G).left
    rw [sqMap, Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, ← hp]
    show (lift P Q).left ≫ (fst (GF t x) (GF t x)).left ≫ pullback.fst t.G.hom x = _
    rw [← Category.assoc, ← Over.comp_left, lift_fst]
  · show ((lift P Q).left ≫ sqMap t x) ≫ (snd t.G t.G).left = (lift p q).left ≫ (snd t.G t.G).left
    rw [sqMap, Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, ← hq]
    show (lift P Q).left ≫ (snd (GF t x) (GF t x)).left ≫ pullback.fst t.G.hom x = _
    rw [← Category.assoc, ← Over.comp_left, lift_snd]

theorem lift_qq {t : SAB H X} {x : Sp k ⟶ X} (Q : AbQuot t x) {T : Over (Sp k)} (P R : T ⟶ GF t x) :
    (lift P R).left ≫ qq Q = (lift (P ≫ Q.q) (R ≫ Q.q)).left := by
  rw [qq, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc]

theorem one_fst' {R : Type} [CommRing R] [Algebra k R] :
    (1 : overAt (𝟙 (Sp k)) R ⟶ GF t x).left ≫ pullback.fst t.G.hom x = (1 : overAt x R ⟶ t.G).left := by
  rw [one_fst, one_left, one_left]
  simp

theorem fibPt_fst {R : Type} [CommRing R] [Algebra k R] (y : overAt x R ⟶ t.G) :
    (fibPt t x y).left ≫ pullback.fst t.G.hom x = y.left :=
  pullback.lift_fst _ _ _

end Fib2

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)]

theorem eq_one_of_jets (hs : ∀ a : 𝓞 E, star a = H.bar a) {X : Scheme.{0}} (t : SAB H X) {k : Type} [Field k]
    [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) {d : ℕ} (g : GermAt t x d)
    (xk : ∀ m, Sp (Jet k (Fin 1 × Fin d) m) ⟶ pullback t.G.hom x) (hx : ∀ m, xk m = (fibPt t x (g.x m)).left)
    (f : Γ(pullback t.G.hom x, ⊤)) (h : ∀ m, (xk m).appTop.hom f = 1) : f = 1 := by
  obtain ⟨hI, -, -, T⟩ := GlobalTheory.T.formal_germ_jet_lift E H hs X t k p x d g xk
    (fun m => by rw [hx]; exact fibPt_fst t x (g.x m))
    (fun m => by rw [hx]; exact (pullback.lift_snd _ _ _).trans (Category.comp_id _))
  haveI := hI
  obtain ⟨F, hF, h0, -⟩ := @T ⊤ (fun m => le_rfl) ⟨⟨Classical.arbitrary _, trivial⟩⟩ (f - 1)
  have hz : F = 0 := Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.psJet_inj fun m => Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.toΓ_injective _ (by
    have z : psJet m (0 : MvPowerSeries (Fin 1 × Fin d) k) = 0 := by simp [psJet, psTrunc]
    rw [← hF m, z, map_zero]
    have e : ((xk m).appLE ⊤ ⊤ (le_rfl : (⊤ : (Sp (Jet k (Fin 1 × Fin d) m)).Opens) ≤ xk m ⁻¹ᵁ ⊤)).hom (f - 1) =
        (xk m).appTop.hom (f - 1) := by
      simp only [Scheme.Hom.appLE, homOfLE_refl, op_id, CategoryTheory.Functor.map_id, map_sub, map_one]
      first | rfl | (erw [Category.comp_id]; rfl)
    rw [e, map_sub, map_one, h m, sub_self])
  exact sub_eq_zero.1 (h0 hz)

end Main

theorem unit_one_on_axes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ (w : LB.Iso (t.PP.L.pull (pullback.fst t.G.hom x)) (Q.tB.PP.L.pull Q.q.left)), w.IsGen → ∀ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) → (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) → ∀ (a : 𝓞 E) (wL : AdTy t a) (wB : AdTy Q.tB a), wL.IsGen → wB.IsGen → AdRel t x d g.x g.B.A.act g.B.ad g.e a wL → AdRel Q.tB (𝟙 (Sp k)) d' gB.x gB.B.A.act gB.B.ad gB.e a wB → ∀ u : Γ((GF t x ⊗ GF t x).left, ⊤)ˣ, Tr w (adF t x a) (fun i => sqMap t x ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i) (fun i => qq Q ≫ Sum.elim (cφG Q.tB ![fst Q.tB.G Q.tB.G, snd Q.tB.G Q.tB.G ≫ Q.tB.act.act (H.bar a)]) (cφG Q.tB ![fst Q.tB.G Q.tB.G ≫ Q.tB.act.act a, snd Q.tB.G Q.tB.G]) i) (Sum.elim (cε 2) fun I => -cε 2 I) (LB.pullGen t.PP.L _ _ wL (sqMap t x)) (LB.pullGen Q.tB.PP.L _ _ wB (qq Q)) u → (ax0 t x).appTop.hom u.val = 1 ∧ (ax1 t x).appTop.hom u.val = 1 := by
  intro E _ _ _ H _ hs X t k _ _ p _ _ x Q d d' g gB w hw Qs hQ0 hQ a wL wB hL hB hR hRB u hT
  haveI := Q.q_hom
  have cL := GlobalTheory.T.adjoint_relation_generator_corr E H hs X t k x d g a wL hL hR
  have cB := GlobalTheory.T.adjoint_relation_generator_corr E H hs (Sp k) Q.tB k (𝟙 (Sp k)) d' gB a wB hB hRB
  have hLB := t.PP.isLB
  have hMB := Q.tB.PP.isLB
  constructor
  · refine eq_one_of_jets H hs t p x g (fun m => (fibPt t x (g.x m)).left) (fun _ => rfl) _ fun m => ?_
    have e := tr_one hLB hMB hT (lift 1 (fibPt t x (g.x m))).left
      (fun z JL hJ => val_pull_one wL (sqMap t x) (lift 1 (g.x m)).left (cL m).1 _ (𝟙 _)
        (by rw [lift_sq t x 1 _ 1 (g.x m) (one_fst' t x) (fibPt_fst t x _), Category.id_comp]) hJ)
      (fun z JM hJ => val_pull_one wB (qq Q) (lift 1 (gB.x m)).left (cB m).1 _ (homAt (𝟙 (Sp k)) (sub1 Qs m)).left
        (by rw [lift_qq, MonObj.one_comp, hQ m, ← Over.comp_left, comp_lift, MonObj.comp_one]) hJ)
      (fun z JL JM => adjoint_product_first_axis t x _ a (fun ψ => wv w ψ z JL JM))
    rw [← left_first_axis_lift, Scheme.Hom.comp_appTop] at e
    exact e
  · refine eq_one_of_jets H hs t p x g (fun m => (fibPt t x (g.x m)).left) (fun _ => rfl) _ fun m => ?_
    have e := tr_one hLB hMB hT (lift (fibPt t x (g.x m)) 1).left
      (fun z JL hJ => val_pull_one wL (sqMap t x) (lift (g.x m) 1).left (cL m).2 _ (𝟙 _)
        (by rw [lift_sq t x _ 1 (g.x m) 1 (fibPt_fst t x _) (one_fst' t x), Category.id_comp]) hJ)
      (fun z JM hJ => val_pull_one wB (qq Q) (lift (gB.x m) 1).left (cB m).2 _ (homAt (𝟙 (Sp k)) (sub1 Qs m)).left
        (by rw [lift_qq, MonObj.one_comp, hQ m, ← Over.comp_left, comp_lift, MonObj.comp_one]) hJ)
      (fun z JL JM => adjoint_product_second_axis t x _ a (fun ψ => wv w ψ z JL JM))
    rw [← left_second_axis_lift, Scheme.Hom.comp_appTop] at e
    exact e

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.UAxis
