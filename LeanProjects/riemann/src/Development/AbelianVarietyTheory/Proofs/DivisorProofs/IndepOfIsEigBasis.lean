import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagAgree
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagSec

open GlobalTheory.ShFam.Pad.Guard GlobalTheory.TangentOrigin

section Coord

variable {K : Type} [CommRing K] {Bs Y : Scheme.{0}} {M : Bs.Modules} [M.IsQuasicoherent] {m : ℕ} (π : Y ⟶ Bs)

theorem evalPt_appLE (y : Sp K ⟶ Y) (U : Bs.Opens) (V : Y.Opens) (e : V ≤ π ⁻¹ᵁ U) (hV : ⊤ ≤ y ⁻¹ᵁ V)
    (hU : ⊤ ≤ (y ≫ π) ⁻¹ᵁ U) (f : Γ(Bs, U)) : evalPt y V hV (π.appLE U V e f) = evalPt (y ≫ π) U hU f := by
  have := Scheme.Hom.appLE_comp_appLE y π U V ⊤ e hV
  unfold evalPt
  rw [← this]
  rfl

theorem repr_change {V V' : Bs.Opens} {f : Fin m → Γ(M, V)} {f' : Fin m → Γ(M, V')} (hf : IsFrame f)
    (hf' : IsFrame f') {W : Y.Opens} (h : W ≤ π ⁻¹ᵁ V) (h' : W ≤ π ⁻¹ᵁ V') (h'' : W ≤ π ⁻¹ᵁ (V ⊓ V'))
    (s : Γ((Scheme.Modules.pullback π).obj M, W)) (b : Fin m) :
    ((hf.pullback π).basis h).repr s b =
      ∑ a, π.appLE _ W h'' (trCo hf f' b a) * ((hf'.pullback π).basis h').repr s a := by
  have e (a : Fin m) : (hf'.pullback π).basis h' a =
      QCoh.pullbackSections π M h'' (Twist.resM M inf_le_right (f' a)) := by
    rw [IsFrame.basis_apply]
    exact ((QCoh.pullbackSections_res π M h'' inf_le_right _).trans (QCoh.res_pullbackSections π M _ _ _).symm).symm
  conv_lhs => rw [← ((hf'.pullback π).basis h').sum_repr s]
  rw [map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm, e]
  exact congrArg (· * _) (hf.pullback_basis_repr π inf_le_left h'' _ b)

theorem coord_rel (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) m) (y : Sp K ⟶ Y) (z : Sp K ⟶ Bs)
    (hz : z = y ≫ π) (i : Fin m) {U : Y.Opens} (e : Γ(fl.gr i, U)) {V V' : Bs.Opens} {f : Fin m → Γ(M, V)}
    {f' : Fin m → Γ(M, V')} (hf : IsFrame f) (hf' : IsFrame f') {W W' : Y.Opens} (hW : W ≤ U) (hW' : W' ≤ U)
    (hWV : W ≤ π ⁻¹ᵁ V) (hWV' : W' ≤ π ⁻¹ᵁ V') (t : Γ(fl.F i.succ, W)) (t' : Γ(fl.F i.succ, W'))
    (ht : (fl.π i).app W t = Twist.resM _ hW e) (ht' : (fl.π i).app W' t' = Twist.resM _ hW' e)
    (hx : ⊤ ≤ y ⁻¹ᵁ W) (hx' : ⊤ ≤ y ⁻¹ᵁ W') (hx'' : ⊤ ≤ y ⁻¹ᵁ (W ⊓ W')) (hxx : ⊤ ≤ z ⁻¹ᵁ (V ⊓ V')) :
    ∃ s : Γ(fl.F i.castSucc, W ⊓ W'), ∀ b,
      ∑ a, evalPt z (V ⊓ V') hxx (trCo hf f' b a) *
          evalPt y W' hx' (((hf'.pullback π).basis hWV').repr ((fl.ι i.succ).app W' t') a) =
        evalPt y W hx (((hf.pullback π).basis hWV).repr ((fl.ι i.succ).app W t) b) +
        evalPt y (W ⊓ W') hx'' (((hf.pullback π).basis (inf_le_left.trans hWV)).repr
          ((fl.ι i.castSucc).app (W ⊓ W') s) b) := by
  subst hz
  have hex : Function.Exact ((fl.step i).app (W ⊓ W')) ((fl.π i).app (W ⊓ W')) :=
    QCoh.exact_app_of_exact_of_mono (ShortComplex.exact_cokernel (fl.step i)) (W ⊓ W')
  have h0 : (fl.π i).app (W ⊓ W') (Twist.resM _ inf_le_right t' - Twist.resM _ inf_le_left t) = 0 := by
    rw [map_sub, Twist.app_resM, Twist.app_resM, ht, ht', Twist.resM_resM, Twist.resM_resM, sub_self]
  obtain ⟨s, hs⟩ := (hex _).1 h0
  refine ⟨s, fun b => ?_⟩
  have h1 : (fl.ι i.castSucc).app (W ⊓ W') s = Twist.resM _ inf_le_right ((fl.ι i.succ).app W' t') -
      Twist.resM _ inf_le_left ((fl.ι i.succ).app W t) := by
    rw [← Twist.app_resM, ← Twist.app_resM, ← map_sub, ← hs, ← fl.step_ι i]
    rfl
  have h2 : W ⊓ W' ≤ π ⁻¹ᵁ (V ⊓ V') := fun p hp => ⟨hWV hp.1, hWV' hp.2⟩
  rw [h1, map_sub, Finsupp.sub_apply, map_sub, IsFrame.repr_resM _ hWV inf_le_left, evalPt_res y _ hx, add_sub_cancel,
    repr_change π hf hf' _ (inf_le_right.trans hWV') h2, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, evalPt_appLE π y _ _ h2 hx'' hxx, IsFrame.repr_resM _ hWV' inf_le_right, evalPt_res y _ hx']

end Coord

section Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {K : Type} [CommRing K] {x : Sp K ⟶ X} {m n : ℕ}
  {u u' : Fin m → (Sp (DualNumber K) ⟶ t.G.left)} {v : Fin n → (Sp (DualNumber K) ⟶ t.G.left)}

theorem comb_add (hu : ∀ k, IsTanAtG t x (u k)) (hv : ∀ k, IsTanAtG t x (v k)) {a b : Fin m → K} {c d : Fin n → K}
    {w₁ w₂ w : Sp (DualNumber K) ⟶ t.G.left} (h₁ : IsCombAtG t x u a w₁) (h₁' : IsCombAtG t x v c w₁)
    (h₂ : IsCombAtG t x u b w₂) (h₂' : IsCombAtG t x v d w₂) (h : IsCombAtG t x u (a + b) w) :
    IsCombAtG t x v (c + d) w := by
  obtain ⟨w', -, hw⟩ := exists_comb (u := ![w₁, w₂]) (t := t) (x := x)
    (Fin.forall_fin_two.2 ⟨comb_tan hu h₁, comb_tan hu h₂⟩) ![1, 1]
  have e1 := tanLinG u hu ![w₁, w₂] (Matrix.of fun j i => ![a j, b j] i) _ w' (Fin.forall_fin_two.2 ⟨h₁, h₂⟩) hw
  have e2 := tanLinG v hv ![w₁, w₂] (Matrix.of fun j i => ![c j, d j] i) _ w' (Fin.forall_fin_two.2 ⟨h₁', h₂'⟩) hw
  have e3 : (Matrix.of fun j i => ![a j, b j] i).mulVec ![1, 1] = a + b := by
    ext j; simp [Matrix.mulVec, dotProduct]
  have e4 : (Matrix.of fun j i => ![c j, d j] i).mulVec ![1, 1] = c + d := by
    ext j; simp [Matrix.mulVec, dotProduct]
  rw [e3] at e1
  rw [e4] at e2
  exact comb_unique hu e1 h ▸ e2

theorem coeff_eq (hu : ∀ k, IsTanAtG t x (u k)) (hv : ∀ k, IsTanAtG t x (v k)) (hi : Indep t x v)
    {T : Fin m → Fin m → K} (hT : ∀ i, IsCombAtG t x u (fun b => T b i) (u' i)) {a a' s : Fin m → K}
    (hrel : ∀ b, ∑ k, T b k * a' k = a b + s b) {c c' d : Fin n → K} {w w' w₀ : Sp (DualNumber K) ⟶ t.G.left}
    (h₁ : IsCombAtG t x u a w) (h₁' : IsCombAtG t x v c w) (h₂ : IsCombAtG t x u' a' w') (h₂' : IsCombAtG t x v c' w')
    (h₃ : IsCombAtG t x u s w₀) (h₃' : IsCombAtG t x v d w₀) : c' = c + d := by
  have e1 := tanLinG u hu u' (Matrix.of T) a' w' hT h₂
  rw [show (Matrix.of T).mulVec a' = a + s from funext hrel] at e1
  exact hi _ _ _ h₂' (comb_add hu hv h₁ h₁' h₃ h₃' e1)

theorem value_eq (hu' : ∀ k, IsTanAtG t x (u' k)) (hi : Indep t x u')
    {T : Fin m → Fin m → K} (hT : ∀ i, IsCombAtG t x u' (fun b => T i b) (u i)) {a a' s : Fin m → K}
    (hrel : ∀ b, ∑ k, T b k * a' k = a b + s b) {d d' : Fin m → K} {w : Sp (DualNumber K) ⟶ t.G.left}
    (h : IsCombAtG t x u d w) (h' : IsCombAtG t x u' d' w) :
    ∑ b, a' b * d' b = ∑ b, a b * d b + ∑ b, s b * d b := by
  have e1 := hi _ _ _ h' (tanLinG u' hu' u (Matrix.of fun j i => T i j) d w hT h)
  rw [← Finset.sum_add_distrib]
  simp only [← add_mul, ← hrel, e1, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end Lin

section Eig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

attribute [local instance] Over.cartesianMonoidalCategory in

theorem indep_of_isEigBasis {K : Type} [CommRing K] {φ : c.F →+* K} {x : Sp K ⟶ Z.X} {τ : E →+* ℂ} {m : ℕ}
    {u : Fin m → (Sp (DualNumber K) ⟶ Z.t.G.left)} (hu : IsEigBasis Z φ x τ u) : Indep Z.t x u := by
  intro cf cf' w h1 h2
  refine (hu.2 w ⟨comb_tan (fun j => (hu.1 j).1) h1, fun a => ?_⟩).unique h1 h2
  rw [← (isCombAtG_iff Z.t _ (fun j => ovT (hu.1 j).1) _ _).1 h1]
  have := Z.t.act.hom a
  exact congrArg (fun f => f.left) (combT_eig _ (fun j => ovT (hu.1 j).1) (Z.t.act.act a) _
    (fun j => Over.OverMorphism.ext ((hu.1 j).2 a)) cf)

end Eig

theorem exists_unit {K : Type} [Field K] (P : K → Prop) (h0 : ∀ a, P a → a ≠ 0) (h1 : ∀ a b, P a → P b → a = b) :
    ∃ r : Kˣ, ∀ a, P a → a = (r⁻¹ : Kˣ) := by
  by_cases h : ∃ a, P a
  · obtain ⟨a, ha⟩ := h
    exact ⟨(Units.mk0 a (h0 a ha))⁻¹, fun b hb => by simpa using h1 b a hb ha⟩
  · exact ⟨1, fun a ha => (h ⟨a, ha⟩).elim⟩

open GlobalTheory.FlagCov in

theorem exists_isFrameSec : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (Bs : Scheme.{0}) (E : D.what₂.Tau × Bool → Bs.Modules)
    (hE : ∀ a, IsVB (E a) (rkB D.what₂.Tau O.N O.j a)) (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB)
    (hu : ∀ a, IsLieFrames O.s.T.Z O.κ.e jB πB (E a) _ (embB D a) (!a.2) (u a))
    (Y₀ : Scheme.{0}) (π₀ : Y₀ ⟶ Bs)
    (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a))
    (G : Scheme.{0}) [IsIntegral G] (j : G ⟶ Y₀) (πG : G ⟶ (O.var c).X) (φ : (O.var c).Fn →+* G.functionField)
    (_ : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X))
    (jG : G ⟶ Bg) (_ : jG ≫ jB = j ≫ π₀) (_ : jG ≫ πB = πG ≫ (O.Φ.C c).π),
    (∀ a (hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a)), GlobalTheory.FlagCov.FlagAgree hE jB πB u π₀ fl₀ j φ jG a hr) →
    ∃ r : ∀ a i, (((fl₀ a).root i).pull j).ι → G.functionFieldˣ,
      ∀ a i (hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a)),
        GlobalTheory.FlagCov.IsFrameSec hE jB πB u π₀ fl₀ j φ jG a i hr (r a i) := by
  intro D O c Bs E hE Bg jB πB u hu Y₀ π₀ fl₀ G _ j πG φ hgen jG h1 h2 hA
  suffices h : ∀ a i, ∃ r : (((fl₀ a).root i).pull j).ι → G.functionFieldˣ,
      ∀ hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a), IsFrameSec hE jB πB u π₀ fl₀ j φ jG a i hr r by
    choose r hr using h
    exact ⟨r, hr⟩
  intro a i
  by_cases hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a)
  swap
  · exact ⟨fun _ => 1, fun h => (hr h).elim⟩
  have := (hE a).isQuasicoherent
  obtain ⟨hA1, hA2⟩ := hA a hr
  obtain ⟨hu1, hu2, -⟩ := hu a
  have hx0 : genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z =
      spMap φ ≫ genericPt (O.Φ.C c).Y ≫ (O.Φ.C c).π ≫ genι O.s.T.Z := by
    rw [reassoc_of% h2]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hgen).trans (Category.assoc _ _ _))
  have hz : (genPt G ≫ jG) ≫ jB = (genPt G ≫ j) ≫ π₀ := by rw [Category.assoc, h1, Category.assoc]
  have hv : ∀ k, IsTanAtG O.s.T.Z.t (genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z)
      (spMap (dualMap φ) ≫ (O.Φ.C c).f0.v (embB D a) k) := fun k =>
    hx0 ▸ GlobalTheory.FactorDepth.isTanAtG_map _ φ ((O.Φ.C c).f0.tan _ k)
  have hvi : Indep O.s.T.Z.t (genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z)
      fun k => spMap (dualMap φ) ≫ (O.Φ.C c).f0.v (embB D a) k :=
    hx0 ▸ Indep.map φ ((O.Φ.C c).f0.tan _) (indep_of_isEigBasis
      ⟨fun k => ⟨(O.Φ.C c).f0.tan _ k, (O.Φ.C c).f0.eig _ k⟩, fun w hw => (O.Φ.C c).f0.basis _ w hw.1 hw.2⟩)
  have hb := fun V f hf hxV => hu1 V f hf G.functionField (genPt G ≫ jG) hxV
    (Spec.preimage ((genPt G ≫ jG) ≫ πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom)).hom (Spec.map_preimage _).symm
  have hT := fun V V' f f' hf hf' hx hx' hxx => hu2 V V' f f' hf hf' G.functionField (genPt G ≫ jG) hx hx' hxx
  rw [Category.assoc _ jG (πB ≫ genι _)] at hb hT
  have hut := fun V f hf hxV k => ((hb V f hf hxV).1 k).1
  have hui := fun V f hf hxV => indep_of_isEigBasis (hb V f hf hxV)
  clear hb hu1 hu2
  obtain ⟨τ, _ | _⟩ := a
  · have key := fun ch : (((fl₀ (τ, false)).root i).pull j).ι => exists_unit
      (fun val : G.functionField => ∃ (V : Bs.Opens) (f : _ → Γ(E (τ, false), V)) (hf : IsFrame f) (W : Y₀.Opens)
        (hW : W ≤ (ch PUnit.unit).U) (hWV : W ≤ π₀ ⁻¹ᵁ V) (t : Γ((fl₀ (τ, false)).F i.succ, W))
        (_ : ((fl₀ (τ, false)).π i).app W t = Twist.resM _ hW ((ch PUnit.unit).e 0))
        (hx : ⊤ ≤ (genPt G ≫ j) ⁻¹ᵁ W) (hxV : ⊤ ≤ ((genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V)
        (k : Fin (O.S.Dw.mult (embB D (τ, false)))) (d : _ → G.functionField),
        IsCombAtG O.s.T.Z.t (genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z) (u _ V f hf G.functionField (genPt G ≫ jG) hxV) d
          (spMap (dualMap φ) ≫ (O.Φ.C c).f0.v (embB D (τ, false)) k) ∧
        (k : ℕ) + i + 1 = rkB D.what₂.Tau O.N O.j (τ, false) ∧
        ∑ b, evalPt (genPt G ≫ j) W hx
          (((hf.pullback π₀).basis hWV).repr (((fl₀ (τ, false)).ι i.succ).app W t) b) * d b = val)
      (by
        rintro _ ⟨V, f, hf, W, hW, hWV, t, ht, hx, hxV, k, d, hd, hk, rfl⟩
        exact hA2 i ch V f hf W hW hWV t ht hx hxV k d hd hk)
      (by
        rintro _ _ ⟨V, f, hf, W, hW, hWV, t, ht, hx, hxV, k, d, hd, hk, rfl⟩
          ⟨V', f', hf', W', hW', hWV', t', ht', hx', hxV', k', d', hd', hk', rfl⟩
        obtain rfl : k = k' := Fin.ext (by omega)
        have hx'' : ⊤ ≤ (genPt G ≫ j) ⁻¹ᵁ (W ⊓ W') := fun p hp => ⟨hx hp, hx' hp⟩
        have hxx : ⊤ ≤ ((genPt G ≫ jG) ≫ jB) ⁻¹ᵁ (V ⊓ V') := fun p hp => ⟨hxV hp, hxV' hp⟩
        obtain ⟨s, hs⟩ := coord_rel π₀ (fl₀ _) _ _ hz i _ hf hf' hW hW' hWV hWV' t t' ht ht' hx hx' hx'' hxx
        have e0 := hA1 i.castSucc V f hf _ (inf_le_left.trans hWV) s hx'' hxV k d hd (by
          rw [Fin.val_castSucc]; omega)
        exact ((value_eq (hut V' f' hf' hxV') (hui V' f' hf' hxV') (hT V V' f f' hf hf' hxV hxV' hxx) hs hd hd').trans
          ((congrArg (_ + ·) e0).trans (add_zero _))).symm)
    choose r hr' using key
    refine ⟨r, fun _ ch V f hf W hW hWV t ht hx hxV k d hd => ⟨fun hk => ?_, fun hk => ?_⟩⟩
    · exact hA1 i.succ V f hf W hWV t hx hxV k d hd hk
    · exact hr' ch _ ⟨V, f, hf, W, hW, hWV, t, ht, hx, hxV, k, d, hd, hk, rfl⟩
  · have key := fun ch : (((fl₀ (τ, true)).root i).pull j).ι => exists_unit
      (fun val : G.functionField => ∃ (V : Bs.Opens) (f : _ → Γ(E (τ, true), V)) (hf : IsFrame f) (W : Y₀.Opens)
        (hW : W ≤ (ch PUnit.unit).U) (hWV : W ≤ π₀ ⁻¹ᵁ V) (t : Γ((fl₀ (τ, true)).F i.succ, W))
        (_ : ((fl₀ (τ, true)).π i).app W t = Twist.resM _ hW ((ch PUnit.unit).e 0))
        (hx : ⊤ ≤ (genPt G ≫ j) ⁻¹ᵁ W) (hxV : ⊤ ≤ ((genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V)
        (w : Sp (DualNumber G.functionField) ⟶ O.s.T.Z.t.G.left)
        (cf : Fin (O.S.Dw.mult (embB D (τ, true))) → G.functionField),
        IsCombAtG O.s.T.Z.t (genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z) (u _ V f hf G.functionField (genPt G ≫ jG) hxV)
          (fun b => evalPt (genPt G ≫ j) W hx
            (((hf.pullback π₀).basis hWV).repr (((fl₀ (τ, true)).ι i.succ).app W t) b)) w ∧
        IsCombAtG O.s.T.Z.t (genPt G ≫ jG ≫ πB ≫ genι O.s.T.Z)
          (fun k => spMap (dualMap φ) ≫ (O.Φ.C c).f0.v (embB D (τ, true)) k) cf w ∧
        cf (Fin.cast hr i) = val)
      (by
        rintro _ ⟨V, f, hf, W, hW, hWV, t, ht, hx, hxV, w, cf, hw, hc, rfl⟩
        obtain ⟨w', cf', hw', hc', h0⟩ := hA2 i ch V f hf W hW hWV t ht hx hxV
        obtain rfl := comb_unique (hut V f hf hxV) hw hw'
        rwa [hvi _ _ _ hc hc'])
      (by
        rintro _ _ ⟨V, f, hf, W, hW, hWV, t, ht, hx, hxV, w, cf, hw, hc, rfl⟩
          ⟨V', f', hf', W', hW', hWV', t', ht', hx', hxV', w', cf', hw', hc', rfl⟩
        have hx'' : ⊤ ≤ (genPt G ≫ j) ⁻¹ᵁ (W ⊓ W') := fun p hp => ⟨hx hp, hx' hp⟩
        have hxx : ⊤ ≤ ((genPt G ≫ jG) ≫ jB) ⁻¹ᵁ (V ⊓ V') := fun p hp => ⟨hxV hp, hxV' hp⟩
        obtain ⟨s, hs⟩ := coord_rel π₀ (fl₀ _) _ _ hz i _ hf hf' hW hW' hWV hWV' t t' ht ht' hx hx' hx'' hxx
        obtain ⟨w₀, d, hw₀, hd, h0⟩ := hA1 i.castSucc V f hf _ (inf_le_left.trans hWV) s hx'' hxV
        rw [coeff_eq (hut V f hf hxV) hv hvi (hT V V' f f' hf hf' hxV hxV' hxx) hs hw hc hw' hc' hw₀ hd, Pi.add_apply,
          h0 (Fin.cast hr i) le_rfl, add_zero])
    choose r hr' using key
    refine ⟨r, fun _ ch V f hf W hW hWV t ht hx hxV => ?_⟩
    obtain ⟨w, cf, hw, hc, h0⟩ := hA1 i.succ V f hf W hWV t hx hxV
    exact ⟨w, cf, hw, hc, hr' ch _ ⟨V, f, hf, W, hW, hWV, t, ht, hx, hxV, w, cf, hw, hc, rfl⟩, fun k hk => h0 k hk⟩

end GlobalTheory.FlagSec

end
