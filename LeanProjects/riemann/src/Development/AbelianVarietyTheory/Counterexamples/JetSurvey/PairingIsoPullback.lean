import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.AlphaPair
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.RigidAndInjective

noncomputable section

namespace GlobalTheory.LevelRigid

section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

theorem pullCongr_heq {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F F' : X' ⟶ X} (h : F = F')
    (w : LB.Iso L' (L.pull F)) : HEq (pullCongr h w) w := by
  subst h; rfl

set_option maxHeartbeats 1600000 in
theorem exists_comparison : PairThetaSt := by
  intro E _ _ _ H D l c k _ bF a P _ oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ d₁ d₂
  letI := H.starRing
  obtain ⟨s1, s2, -, s4, s5, -⟩ := d₁
  obtain ⟨s1', s2', -, s4', s5', -⟩ := d₂
  obtain ⟨θ, hθ, hθφ⟩ := grpPullback_iso s1 s1'
  have g₁ := (isGen_iff w₁).1 s2
  have g₂ := (isGen_iff w₂).1 s2'
  obtain ⟨wθ, T⟩ := exists_cancel a.D₀.P.isLB w₂ (pullCongr hθφ.symm w₁) g₂ (pgen_pullCongr hθφ.symm g₁)
    P.toPre.P.isLB P.toPre.P.isLB
  refine ⟨θ, wθ, pullCongr hθφ.symm w₁, hθ, hθφ, fun x => ?_, fun y => ?_,
    (isGen_iff wθ).2 (T.pgen_cancel a.D₀.P.isLB g₂ (pgen_pullCongr hθφ.symm g₁)), pullCongr_heq _ _, T⟩
  · apply Over.OverMorphism.ext
    apply s1'.1.hom_ext
    · simp only [Over.comp_left, Category.assoc, s4', reassoc_of% hθφ, hθφ, s4]
    · rw [Over.w, Over.w]
  · apply s1'.1.hom_ext
    · rw [Category.assoc, hθφ, s5, s5']
    · rw [Category.assoc, Over.w θ.hom, Over.w, Over.w]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {c : Coeff l}

def AgreeOnLevel {k : Type} [Field k] {bF : c.F →+* k} (a : ArcIn D l (RingHom.id c.F) k bF) {t : SAB H (Sp (PowerSeries k))}
    (P : PELUnif (Ideal.span {PowerSeries.X}) t) (φ₁ φ₂ : P.D.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.D.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.D.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.D.toPre.X) : Prop :=
  WitData a P.D P.oD φ₁ he₁ w₁ e₁ ∧ WitData a P.D P.oD φ₂ he₂ w₂ e₂ ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F]
      (uF : F),
      (∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
        algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x))) →
      uF = algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X) →
      ∀ (n : ℕ) (p₀ : Out.QkPt a.D₀ (FractionRing k) n),
        ((n = l.A ∧ ∃ v, HEq p₀ (a.etaA v)) ∨
          (n = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), HEq p₀ (a.eta v))) →
        ∀ (q₀ : Out.QkPt a.D₀ F n) (q₁ q₂ : Out.QkPt P.D.toPre F n),
          QkExt (algebraMap _ F) p₀ q₀ → q₁.y = e₁ q₀.y → q₂.y = e₂ q₀.y →
          (∀ z, GenRel w₁ (q₁.g.s (e₁ z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / n))) →
          (∀ z, GenRel w₂ (q₂.g.s (e₂ z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / n))) →
          Out.QkPt.Equiv P.D.toPre F q₁ q₂

def FixesHalfTorsion : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (t : SAB H (Sp (PowerSeries k)))
    (P : PELUnif (Ideal.span {PowerSeries.X}) t), P.TorsionIso →
    ∀ (φ₁ φ₂ : P.D.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.D.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.D.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ : a.D₀.X ≃ₗ[𝓞 E] P.D.toPre.X), AgreeOnLevel a P φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₁ →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F]
      (x : Over.mk (Out.jFK (R := PowerSeries k) F ≫ Out.jK (PowerSeries k)) ⟶ P.D.toPre.P.A),
      (letI := H.starRing; ∀ m ∈ l.Mb, x ≫ P.oD.onB.act m = 1) → x.left ≫ φ₁ = x.left ≫ φ₂

def HalfToFullTorsion : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X),
    WitData a P oP φ₁ he₁ w₁ e₁ → WitData a P oP φ₂ he₂ w₂ e₂ →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F],
      (∀ x : Over.mk (Out.jFK (R := PowerSeries k) F ≫ Out.jK (PowerSeries k)) ⟶ P.toPre.P.A,
        (letI := H.starRing; ∀ m ∈ l.Mb, x ≫ oP.onB.act m = 1) → x.left ≫ φ₁ = x.left ≫ φ₂) →
      ∀ x : Over.mk (Out.jFK (R := PowerSeries k) F ≫ Out.jK (PowerSeries k)) ⟶ P.toPre.P.A,
        x ^ l.M = 1 → x.left ≫ φ₁ = x.left ≫ φ₂

def SerreFromPoints : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X),
    WitData a P oP φ₁ he₁ w₁ e₁ → WitData a P oP φ₂ he₂ w₂ e₂ →
    (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F]
      (x : Over.mk (Out.jFK (R := PowerSeries k) F ≫ Out.jK (PowerSeries k)) ⟶ P.toPre.P.A),
        x ^ l.M = 1 → x.left ≫ φ₁ = x.left ≫ φ₂) → φ₁ = φ₂

def WeilAdjoint : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (O : Type) [Ring O] [StarRing O] (o : P.OAct O)
    (k : ℕ) (T : Over S) (x y : T ⟶ P.A) (a : O) (c : Γ(T.left, ⊤)ˣ), x ^ k = 1 → y ^ k = 1 →
    (Out.WeilIs P.A P.L k (x ≫ o.act a) y c ↔ Out.WeilIs P.A P.L k x (y ≫ o.act (star a)) c)

end
section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_local_gen {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (y : Y) : ∃ V : Y.Opens, y ∈ V ∧ ∃ t : LB.Gen (LB.LinComb M (fun k => V.ι ≫ φ k) ε), t.IsGen := by
  choose j₀ hj using fun k => exists_chart hM (φ k y)
  refine ⟨LB.wchart M φ j₀, Set.mem_iInter.2 hj, ?_⟩
  have all : ∀ w : (LB.wchart M φ j₀).toScheme, w ∈ LB.wchart M (fun k => (LB.wchart M φ j₀).ι ≫ φ k) j₀ := fun w =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 w.2 k
  have le : ∀ j, LB.wchart M (fun k => (LB.wchart M φ j₀).ι ≫ φ k) j ≤ LB.wchart M (fun k => (LB.wchart M φ j₀).ι ≫ φ k) j ⊓
      LB.wchart M (fun k => (LB.wchart M φ j₀).ι ≫ φ k) j₀ := fun j w hw => ⟨hw, all w⟩
  refine ⟨⟨fun j => res (le j) ((LB.LinComb M (fun k => (LB.wchart M φ j₀).ι ≫ φ k) ε).g j j₀)⟩,
    isGen_of_gm _ fun w j j' h h' => ?_⟩
  exact ((gm_res _ w (le j) h _).trans (gm_linComb M _ ε (𝟙 _) w j j₀ h (all w))).trans
    ((trF_trans hM _ ε (𝟙 _) w h h' (all w)).symm.trans (congrArg _
      ((gm_res _ w (le j') h' _).trans (gm_linComb M _ ε (𝟙 _) w j' j₀ h' (all w))).symm))

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L)

include c in
theorem exists_theta {k : ℕ} {T : Over S} {x : T ⟶ A} (hx : x ^ k = 1) {K : Type} [Fintype K] {φ : K → (T.left ⟶ A.left)}
    {ε : K → ℤ} (v : LB.Gen (LB.LinComb L.L φ ε)) (hv : v.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (h : (T.left ⟶ A.left) → U), ∏ i, h (φ i) ^ ε i =
      h (1 : T ⟶ A).left ^ (k : ℤ) * h x.left ^ (-(k : ℤ))) : ∃ θ : ThetaGrp A L.L k T, θ.pt = x := by
  obtain ⟨t, ht, -⟩ := exists_cubN c (1 : T ⊗ A ⟶ A) (fst T A ≫ x) (snd T A) k
  obtain ⟨u, hu, -⟩ := exists_gen L.isLB (φ' := ![(snd T A).left, (translPt A x).left]) (ε' := ![(k : ℤ), -(k : ℤ)])
    (fun U _ h => by
      have p := hF U fun q => h ((fst T A).left ≫ q)
      rw [← Over.comp_left, ← Over.comp_left, MonObj.comp_one] at p
      refine (prod_sum₂ (K := K) (K' := Fin 8) (U := U) _ p (Fin.prod_univ_eight _)).trans ?_
      rw [Fin.prod_univ_two, translPt_eq]
      simp only [Sum.elim_inr, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← MonObj.comp_pow, hx, MonObj.comp_one, _root_.one_mul (1 : T ⊗ A ⟶ A), _root_.one_mul (snd T A)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module) (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ v (fst T A).left) t)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hv _) ht)
  exact ⟨⟨x, u, hu⟩, rfl⟩

theorem exists_weil {k : ℕ} {T : Over S} {x y : T ⟶ A} (hx : x ^ k = 1) (hy : y ^ k = 1) : ∃ w : Γ(T.left, ⊤)ˣ,
    ∀ (T' : Over S) (σ : T' ⟶ T) (z : T'.left) (J), Good L.L z J → gm σ.left z ⊤ w =
      cubN (cubV c z J) k 1 (σ ≫ y) (σ ≫ x) * (cubN (cubV c z J) k 1 (σ ≫ x) (σ ≫ y))⁻¹ := by
  obtain ⟨t, ht, vt⟩ := exists_cubN c (1 : T ⟶ A) y x k
  obtain ⟨t', ht', vt'⟩ := exists_cubN c (1 : T ⟶ A) x y k
  obtain ⟨u, -, vu⟩ := exists_gen L.isLB (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (prod_sum₂ (K := Fin 8) (K' := Fin 8) (U := U) _ (Fin.prod_univ_eight _)
        (prod_neg _ _ (Fin.prod_univ_eight _))).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inr, Sum.elim_inl, Matrix.cons_val]
      rw [hx, hy, _root_.one_mul (1 : T ⟶ A), mul_comm y x]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
      module) (LB.mulGen L.L _ _ _ _ t (LB.invGen L.L _ _ t')) (mulGen_isGen _ _ _ _ _ _ _ ht (invGen_isGen _ _ _ _ ht'))
  have le : (⊤ : T.left.Opens) ≤ LB.wchart L.L (PEmpty.elim : PEmpty → (T.left ⟶ A.left)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (u.s PEmpty.elim), fun T' σ z J hJ => (gm_res σ.left z le trivial _).trans
    ((val_of u σ.left z J PEmpty.elim fun k => k.elim).symm.trans ?_)⟩
  rw [vu _ _ z J hJ, val_mul hJ, val_inv, vt _ σ z J hJ, vt' _ σ z J hJ, MonObj.comp_one]

def thG {k : ℕ} {T : Over S} (W : ThetaGrp A L.L k T) :
    LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (translPt A W.pt).left] ![(k : ℤ), -(k : ℤ)]) := W.φ

theorem thG_mul (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {k : ℕ} {T : Over S} (W W' : ThetaGrp A L.L k T)
    (hW : W.pt ^ k = 1) (hW' : W'.pt ^ k = 1) {T' : Over S} (σ : T' ⟶ T) (y : T' ⟶ A) {z : T'.left} {J} (hJ : Good L.L z J) :
    val (LB.mulGen L.L _ _ _ _ (thG W) (LB.pullGen L.L _ _ (thG W') (translT A W.pt).left)) (lift σ y).left z J =
      val (thG W) (lift σ 1).left z J * cubN (cubV c z J) k 1 (σ ≫ W.pt) y *
        (val (thG W') (lift σ 1).left z J * cubN (cubV c z J) k 1 (σ ≫ W'.pt) ((σ ≫ W.pt) * y)) := by
  have v : ∀ (W : ThetaGrp A L.L k T), W.pt ^ k = 1 → ∀ y : T' ⟶ A, val (thG W) (lift σ y).left z J =
      val (thG W) (lift σ 1).left z J * cubN (cubV c z J) k 1 (σ ≫ W.pt) y := fun W hW y =>
    val_theta c hG hA hW (thG W) W.isGen (fun V _ h => by
      rw [Fin.prod_univ_two]
      show h _ ^ (k : ℤ) * h _ ^ (-(k : ℤ)) = _
      rw [zpow_neg, zpow_natCast, zpow_natCast]; rfl) σ y hJ
  rw [val_mul hJ, val_pull hJ, ← Over.comp_left, lift_transl, v W hW y, v W' hW' (_ * y)]

theorem comm_val (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {k : ℕ} {T : Over S} (θ θ' : ThetaGrp A L.L k T)
    (hx : θ.pt ^ k = 1) (hy : θ'.pt ^ k = 1) (e : Γ(T.left, ⊤)ˣ) {T' : Over S} (σ : T' ⟶ T) (y : T' ⟶ A) {z : T'.left} {J}
    (hJ : Good L.L z J) :
    val (LB.mulGen L.L _ _ _ _ (thG θ) (LB.pullGen L.L _ _ (thG θ') (translT A θ.pt).left)) (lift σ y).left z J =
      val (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (thG θ') (LB.pullGen L.L _ _ (thG θ) (translT A θ'.pt).left))
        (constGen A L.L e)) (lift σ y).left z J ↔ gm σ.left z ⊤ e =
      cubN (cubV c z J) k 1 (σ ≫ θ'.pt) (σ ≫ θ.pt) * (cubN (cubV c z J) k 1 (σ ≫ θ.pt) (σ ≫ θ'.pt))⁻¹ := by
  have C : IsCub (cubV c z J) := isCub_cubV c hJ
  have pk : ∀ {x : T ⟶ A}, x ^ k = 1 → (σ ≫ x) ^ k = 1 := fun h => by rw [← MonObj.comp_pow, h, MonObj.comp_one]
  have hm : (lift σ y).left z ∈ LB.wchart L.L (PEmpty.elim : PEmpty → ((T ⊗ A).left ⟶ A.left)) PEmpty.elim :=
    Set.mem_iInter.2 fun k => k.elim
  have vc : val (constGen A L.L e) (lift σ y).left z J = gm σ.left z ⊤ e := by
    rw [val_of _ _ z J PEmpty.elim fun k => k.elim]
    refine (gm_res (lift σ y).left z le_top hm _).trans ((gm_pull (lift σ y).left (fst T A).left z ⊤ trivial e).trans ?_)
    rw [← Over.comp_left, lift_fst]
  rw [thG_mul c hG hA θ θ' hx hy σ y hJ, val_mul hJ, thG_mul c hG hA θ' θ hy hx σ y hJ, vc]
  have a₁ := cubN_right C (pk hx) (σ ≫ θ'.pt) y
  have a₂ := cubN_right C (pk hy) (σ ≫ θ.pt) y
  rw [C.s01] at a₂
  have E := fun {p q : (T'.left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have b₁ := E a₁
  have b₂ := E a₂
  simp only [ofMul_mul] at b₁ b₂
  refine ⟨fun h => Additive.ofMul.injective ?_, fun h => Additive.ofMul.injective ?_⟩
  · have h' := E h
    simp only [ofMul_mul, ofMul_inv] at h' ⊢
    linear_combination (norm := abel) b₂ - b₁ - h'
  · have h' := E h
    simp only [ofMul_mul, ofMul_inv] at h' ⊢
    linear_combination (norm := abel) b₂ - b₁ - h'

theorem weilIs_iff (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {k : ℕ} {T : Over S} {x y : T ⟶ A} (hx : x ^ k = 1)
    (hy : y ^ k = 1) {w : Γ(T.left, ⊤)ˣ} (hw : ∀ (T' : Over S) (σ : T' ⟶ T) (z : T'.left) (J), Good L.L z J → gm σ.left z ⊤ w =
      cubN (cubV c z J) k 1 (σ ≫ y) (σ ≫ x) * (cubN (cubV c z J) k 1 (σ ≫ x) (σ ≫ y))⁻¹) (e : Γ(T.left, ⊤)ˣ) :
    WeilIs A L.L k x y e ↔ e = w := by
  have pk : ∀ {T' : Over S} (σ : T' ⟶ T) {x : T ⟶ A}, x ^ k = 1 → (σ ≫ x) ^ k = 1 := fun σ _ h => by
    rw [← MonObj.comp_pow, h, MonObj.comp_one]
  constructor
  · refine fun h => unit_ext fun p _ => ?_
    obtain ⟨V, hV, ⟨θ, θ', h₁, h₂⟩, hc⟩ := h p
    let z : (overRes V).left := ⟨p, hV⟩
    choose J hJ using fun ψ : (overRes V).left ⟶ A.left => exists_chart L.isLB (ψ z)
    have e₁ := (comm_val c hG hA θ θ' (h₁ ▸ pk _ hx) (h₂ ▸ pk _ hy) (unitRes V e) (𝟙 _) 1 hJ).1
      (val_corr hJ (hc θ θ' h₁ h₂) _)
    rw [Category.id_comp, Category.id_comp, h₁, h₂, ← hw _ (overResι V) z J hJ] at e₁
    exact gm_inj V.ι z (U := ⊤) (U' := ⊤) trivial trivial (((gm_pull (𝟙 _) V.ι z ⊤ trivial e).trans (by rw [Category.id_comp])).symm.trans e₁)
  · rintro rfl p
    obtain ⟨V₁, hV₁, v₁, hv₁⟩ := exists_local_gen L.isLB (K := Fin 2) ![(1 : T ⟶ A).left, x.left] ![(k : ℤ), -(k : ℤ)] p
    obtain ⟨V₂, hV₂, v₂, hv₂⟩ := exists_local_gen L.isLB (K := Fin 2) ![(1 : T ⟶ A).left, y.left] ![(k : ℤ), -(k : ℤ)] p
    have ex : ∀ (W : T.left.Opens) (le : V₁ ⊓ V₂ ≤ W) (q : T ⟶ A), q ^ k = 1 → ∀ v : LB.Gen (LB.LinComb L.L
        (fun i => W.ι ≫ (![(1 : T ⟶ A).left, q.left] : Fin 2 → _) i) ![(k : ℤ), -(k : ℤ)]), v.IsGen →
        ∃ θ : ThetaGrp A L.L k (overRes (V₁ ⊓ V₂)), θ.pt = overResι (V₁ ⊓ V₂) ≫ q := fun W le q hq v hv =>
      exists_theta c (pk _ hq) (LB.pullGen L.L _ _ v (T.left.homOfLE le)) (pullGen_isGen _ _ _ _ hv _) fun U _ h => by
        rw [Fin.prod_univ_two, ← Category.assoc, ← Category.assoc, Scheme.homOfLE_ι, ← MonObj.comp_one (overResι (V₁ ⊓ V₂))]
        rfl
    obtain ⟨θ₁, e₁⟩ := ex V₁ inf_le_left x hx v₁ hv₁
    obtain ⟨θ₂, e₂⟩ := ex V₂ inf_le_right y hy v₂ hv₂
    refine ⟨V₁ ⊓ V₂, ⟨hV₁, hV₂⟩, ⟨θ₁, θ₂, e₁, e₂⟩, fun θ θ' h₁ h₂ => corr_of_val L.isLB fun z J hJ => ?_⟩
    have i₁ : (lift (fst (overRes (V₁ ⊓ V₂)) A) (snd _ A)).left = 𝟙 _ := by
      rw [lift_fst_snd]; rfl
    have key := (comm_val c hG hA θ θ' (h₁ ▸ pk _ hx) (h₂ ▸ pk _ hy) (unitRes (V₁ ⊓ V₂) e) (fst _ A) (snd _ A) hJ).2 (by
      rw [h₁, h₂, ← Category.assoc, ← Category.assoc, ← hw _ (fst _ A ≫ overResι (V₁ ⊓ V₂)) z J hJ]
      exact gm_pull _ (V₁ ⊓ V₂).ι z ⊤ trivial e)
    rw [i₁] at key
    exact key

theorem ros_pair (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb L.L (rosatiφ A f g) rosatiε)) (hu : u.IsGen)
    (n : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ u (zero2 A)) (LB.oneGen L.L)) {T : Over S} {z : T.left} {J}
    (hJ : Good L.L z J) {k : ℕ} {x y : T ⟶ A} (hx : x ^ k = 1) (hy : y ^ k = 1) :
    cubN (cubV c z J) k 1 y (x ≫ f) * (cubN (cubV c z J) k 1 (x ≫ f) y)⁻¹ =
      cubN (cubV c z J) k 1 (y ≫ g) x * (cubN (cubV c z J) k 1 x (y ≫ g))⁻¹ := by
  have C : IsCub (cubV c z J) := isCub_cubV c hJ
  have ra := fun x x' y => ros_add c hG hA f g u hu n hJ x x' y
  have u₁ : val₂ u z J (1 : T ⟶ A) y = 1 := by
    have e := (ra 1 1 y).1
    rw [_root_.mul_one, MonObj.one_comp f, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
    exact mul_eq_left.1 e.symm
  have u₂ : val₂ u z J x (1 : T ⟶ A) = 1 := by
    have e := (ra 1 1 x).2
    rw [_root_.mul_one, MonObj.one_comp g, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
    exact mul_eq_left.1 e.symm
  have E := fun {p q : (T.left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have a : ∀ j, val₂ u z J (x ^ j) y * cubN (cubV c z J) j 1 x (y ≫ g) =
      cubN (cubV c z J) j 1 (x ≫ f) y * val₂ u z J x y ^ j := fun j => by
    induction j with
    | zero => simp [cubN, u₁]
    | succ j ih =>
      have e := (ra (x ^ j) x y).1
      rw [MonObj.pow_comp] at e
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul, pow_succ] at ih ⊢
      apply Additive.ofMul.injective
      have b₁ := E ih; have b₂ := E e
      simp only [ofMul_mul] at b₁ b₂ ⊢
      linear_combination (norm := abel) b₁ + b₂
  have b : ∀ j, val₂ u z J x (y ^ j) * cubN (cubV c z J) j 1 (y ≫ g) x =
      cubN (cubV c z J) j 1 y (x ≫ f) * val₂ u z J x y ^ j := fun j => by
    induction j with
    | zero => simp [cubN, u₂]
    | succ j ih =>
      have e := (ra (y ^ j) y x).2
      rw [MonObj.pow_comp, C.s01 x, C.s12 _ x, C.s01 (x ≫ f), C.s12 _ (x ≫ f)] at e
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul, pow_succ] at ih ⊢
      apply Additive.ofMul.injective
      have b₁ := E ih; have b₂ := E e
      simp only [ofMul_mul] at b₁ b₂ ⊢
      linear_combination (norm := abel) b₁ + b₂
  have a' := a k
  have b' := b k
  rw [hx, u₁, _root_.one_mul] at a'
  rw [hy, u₂, _root_.one_mul] at b'
  rw [a', b', mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.mul_one]

theorem weilAdjoint (hG : GlobalFnsSt) (hC : CubeSt) : WeilAdjoint := by
  intro S _ P O _ _ o k T x y a e hx hy
  have := P.isAb.comm
  have := o.hom a
  have := o.hom (star a)
  obtain ⟨r, hr⟩ := P.rigid
  obtain ⟨⟨c⟩, -⟩ := hC S P ⟨P.L, r, P.isLB, hr⟩ rfl
  obtain ⟨u, hu, n⟩ := exists_ros hG P.isAb P.isLB _ _ (o.rosati a)
  have hx' : (x ≫ o.act a) ^ k = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have hy' : (y ≫ o.act (star a)) ^ k = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  obtain ⟨w, hw⟩ := exists_weil c hx' hy
  refine (weilIs_iff c hG P.isAb hx' hy hw e).trans (weilIs_iff c hG P.isAb hx hy' (fun T' σ z J hJ => ?_) e).symm
  rw [hw T' σ z J hJ, ← Category.assoc, ← Category.assoc]
  exact ros_pair c hG P.isAb _ _ u hu n hJ (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
    (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])

end
section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

theorem pairing_weilMove (hW : Out.WeilSt) {S S' X : Scheme.{0}} [IsLocallyNoetherian S'] (hX : Subsingleton X)
    {G : Over S} [GrpObj G] {L₀ : LB G.left} (hL₀ : L₀.IsLB) (P₁ : Out.PolAV S') {f : S' ⟶ S}
    {φ : P₁.A.left ⟶ G.left} (hp : IsGrpPullback P₁.A G f φ) (w : LB.Iso P₁.L (L₀.pull φ)) (hw : w.IsGen)
    {tS : X ⟶ S'} {t₀ : X ⟶ S} (ht : t₀ = tS ≫ f) (n : ℕ) (x y : Over.mk tS ⟶ P₁.A) (hx : x ^ n = 1)
    (hy : y ^ n = 1) (x₀ y₀ : Over.mk t₀ ⟶ G) (hx₀ : x₀.left = x.left ≫ φ) (hy₀ : y₀.left = y.left ≫ φ)
    (c : Γ(X, ⊤)ˣ) (hG : Out.WeilIs G L₀ n x₀ y₀ c) : Out.WeilIs P₁.A P₁.L n x y c := by
  obtain ⟨c', hc', -⟩ := (hW S' P₁ n (Over.mk tS)).1 x y hx hy
  intro p
  obtain ⟨V, hpV, ⟨θx₀, θy₀, hpx₀, hpy₀⟩, hall₀⟩ := hG p
  obtain ⟨V', hpV', -, hall'⟩ := hc' p
  have hVV : V = V' := by
    ext q
    rw [@Subsingleton.elim _ hX q p]
    exact ⟨fun _ => hpV', fun _ => hpV⟩
  subst hVV
  have hτ : 𝟙 _ ≫ (Out.overRes (T := Over.mk t₀) V).hom = (Out.overRes (T := Over.mk tS) V).hom ≫ f := by
    rw [Category.id_comp]
    show V.ι ≫ t₀ = (V.ι ≫ tS) ≫ f
    rw [ht, Category.assoc]
  have mvx : 𝟙 _ ≫ θx₀.pt.left = (Out.overResι (T := Over.mk tS) V ≫ x).left ≫ φ := by
    rw [hpx₀, Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc, hx₀]; rfl
  have mvy : 𝟙 _ ≫ θy₀.pt.left = (Out.overResι (T := Over.mk tS) V ≫ y).left ≫ φ := by
    rw [hpy₀, Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc, hy₀]; rfl
  obtain ⟨θx, hθx, mx⟩ := H1.exists_theta_move (T := Out.overRes (T := Over.mk tS) V)
    (T₀ := Out.overRes (T := Over.mk t₀) V) hp (𝟙 _) hτ hL₀ P₁.isLB w hw n _ θx₀ mvx
  obtain ⟨θy, hθy, my⟩ := H1.exists_theta_move (T := Out.overRes (T := Over.mk tS) V)
    (T₀ := Out.overRes (T := Over.mk t₀) V) hp (𝟙 _) hτ hL₀ P₁.isLB w hw n _ θy₀ mvy
  have hm := H1.commIsOf_move (T := Out.overRes (T := Over.mk tS) V) (T₀ := Out.overRes (T := Over.mk t₀) V) hp
    (𝟙 _) hτ hL₀ P₁.isLB w n θx₀ θy₀ θx θy (by rw [hθx]; exact mvx) (by rw [hθy]; exact mvy) mx my
    (Out.unitRes (T := Over.mk t₀) V c) (Out.unitRes (T := Over.mk tS) V c)
    (fun Z r z => by rw [Category.comp_id]; rfl) (hall₀ θx₀ θy₀ hpx₀ hpy₀)
  have hcc := H1.commIsOf_unique P₁.isLB θx θy _ _ hm (hall' θx θy hθx hθy)
  refine ⟨V, hpV, ⟨θx, θy, hθx, hθy⟩, fun θx' θy' h₁ h₂ => ?_⟩
  rw [hcc]
  exact hall' θx' θy' h₁ h₂

theorem pairing_isoPullback {S : Scheme.{0}} (B : Out.PolAV S) (θ : B.A ≅ B.A) (hθ : IsMonHom θ.hom) :
    IsGrpPullback B.A B.A (𝟙 S) θ.hom.left := by
  have := hθ
  refine ⟨?_, fun T x y x₀ y₀ hx hy => ?_⟩
  · have : IsIso θ.hom.left := (inferInstance : IsIso ((Over.forget S).map θ.hom))
    exact IsPullback.of_horiz_isIso ⟨by rw [Over.w θ.hom, Category.comp_id]⟩
  · let i : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 _) (by simp)
    have ex : x₀ = i ≫ x ≫ θ.hom := Over.OverMorphism.ext (by simp [i, hx])
    have ey : y₀ = i ≫ y ≫ θ.hom := Over.OverMorphism.ext (by simp [i, hy])
    rw [ex, ey, ← MonObj.comp_mul, ← MonObj.mul_comp]
    simp [i]

theorem pairing_weilTheta (hW : Out.WeilSt) {S X : Scheme.{0}} [IsLocallyNoetherian S] (hX : Subsingleton X)
    (B : Out.PolAV S) (θ : B.A ≅ B.A) (hθ : IsMonHom θ.hom) (wθ : LB.Iso B.L (B.L.pull θ.hom.left))
    (hwθ : wθ.IsGen) {t : X ⟶ S} (n : ℕ) (x y : Over.mk t ⟶ B.A) (hx : x ^ n = 1) (hy : y ^ n = 1)
    (c : Γ(X, ⊤)ˣ) (h : Out.WeilIs B.A B.L n (x ≫ θ.hom) (y ≫ θ.hom) c) : Out.WeilIs B.A B.L n x y c :=
  pairing_weilMove hW hX B.isLB B (pairing_isoPullback B θ hθ) wθ hwθ (tS := t) (t₀ := t)
    (Category.comp_id t).symm n x y hx hy (x ≫ θ.hom) (y ≫ θ.hom) rfl rfl c h

theorem pairing_weilInv (hW : Out.WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (B : Out.PolAV S) {T : Over S}
    (n : ℕ) (p z : T ⟶ B.A) (hp : p ^ n = 1) (hz : z ^ n = 1) (c : Γ(T.left, ⊤)ˣ)
    (h : Out.WeilIs B.A B.L n p z c) : Out.WeilIs B.A B.L n p⁻¹ z c⁻¹ := by
  obtain ⟨d, hd, -⟩ := (hW S B n T).1 p⁻¹ z (by rw [inv_pow, hp, inv_one]) hz
  obtain ⟨e, he, hu⟩ := (hW S B n T).1 1 z (one_pow n) hz
  have he1 : e = 1 := by
    have h2 := (hW S B n T).2.1 1 1 z e e he he
    rw [_root_.one_mul] at h2
    have h3 := hu _ h2
    exact mul_left_cancel (a := e) (by rw [_root_.mul_one]; exact h3)
  have h4 := (hW S B n T).2.1 p p⁻¹ z c d h hd
  rw [mul_inv_cancel] at h4
  have h5 : c * d = 1 := (hu _ h4).trans he1
  rw [← eq_inv_of_mul_eq_one_right h5]
  exact hd

theorem pairing_nondeg (hW : Out.WeilSt) (hND : Out.WeilNondegSt) (hBC : Out.PolBaseChangeSt)
    {S : Scheme.{0}} (B : Out.PolAV S) (F : Type) [Field F] [IsAlgClosed F]
    (t : Spec (CommRingCat.of F) ⟶ S) (n : ℕ) (hn : (n : F) ≠ 0) (u : Over.mk t ⟶ B.A)
    (hu : u ^ n = 1) (h : ∀ z : Over.mk t ⟶ B.A, z ^ n = 1 → Out.WeilIs B.A B.L n u z 1) : u = 1 := by
  obtain ⟨P', g, hg, -, hmul, tw, htw⟩ := hBC S (Spec (CommRingCat.of F)) t B
  obtain ⟨w, hw⟩ := LBIso.symm ⟨tw, htw⟩
  have hp : IsGrpPullback P'.A B.A t g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [show x₀ = Out.toBase hg.w x from Over.OverMorphism.ext hx,
      show y₀ = Out.toBase hg.w y from Over.OverMorphism.ext hy, ← hmul]
    rfl⟩
  let i : Over.mk ((Out.baseOver (Spec (CommRingCat.of F))).hom ≫ t) ⟶ Over.mk t :=
    Over.homMk (𝟙 _) (by simp)
  have hi : ∀ a b : Over.mk t ⟶ B.A, i ≫ a = i ≫ b → a = b := fun a b hab => by
    apply Over.OverMorphism.ext
    have := congrArg CommaMorphism.left hab
    simpa [i] using this
  have tb1 : Out.toBase hg.w (1 : Out.baseOver _ ⟶ P'.A) = 1 := by
    have e := hmul (Out.baseOver _) 1 1
    rw [_root_.one_mul] at e
    exact mul_left_cancel (a := Out.toBase hg.w (1 : Out.baseOver _ ⟶ P'.A)) (by rw [_root_.mul_one]; exact e.symm)
  have tbpow : ∀ (z : Out.baseOver _ ⟶ P'.A) (m : ℕ), Out.toBase hg.w (z ^ m) = Out.toBase hg.w z ^ m := by
    intro z m
    induction m with
    | zero => rw [pow_zero, pow_zero, tb1]
    | succ m ih => rw [pow_succ, hmul, ih, pow_succ]
  let push : (Out.baseOver (Spec (CommRingCat.of F)) ⟶ P'.A) → (Over.mk t ⟶ B.A) := fun z =>
    Over.homMk (z.left ≫ g) (by
      show (z.left ≫ g) ≫ B.A.hom = t
      rw [Category.assoc, hg.w, ← Category.assoc, Over.w z]; simp)
  have tbpush : ∀ z, Out.toBase hg.w z = i ≫ push z := fun z =>
    Over.OverMorphism.ext (by simp [i, push, Out.toBase])
  have pinj : ∀ a b : Out.baseOver (Spec (CommRingCat.of F)) ⟶ P'.A, a.left ≫ g = b.left ≫ g → a = b :=
    fun a b hab => Over.OverMorphism.ext (hg.hom_ext hab (by rw [Over.w a, Over.w b]))
  let u' : Out.baseOver (Spec (CommRingCat.of F)) ⟶ P'.A :=
    Over.homMk (hg.lift u.left (𝟙 _) (by rw [Over.w u]; simp)) (hg.lift_snd _ _ _)
  have hu'g : u'.left ≫ g = u.left := hg.lift_fst _ _ _
  have hpu : push u' = u := Over.OverMorphism.ext hu'g
  have hu' : u' ^ n = 1 := by
    apply pinj
    have e : Out.toBase hg.w (u' ^ n) = Out.toBase hg.w 1 := by
      rw [tbpow, tb1, tbpush, hpu, ← MonObj.comp_pow, hu, MonObj.comp_one]
    exact congrArg CommaMorphism.left e
  have hall : ∀ y' : Out.baseOver (Spec (CommRingCat.of F)) ⟶ P'.A, y' ^ n = 1 →
      Out.WeilIs P'.A P'.L n u' y' 1 := by
    intro y' hy'
    have hy : push y' ^ n = 1 := by
      apply hi
      rw [MonObj.comp_pow, ← tbpush, ← tbpow, hy', tb1, MonObj.comp_one]
    exact pairing_weilMove hW inferInstance B.isLB P' hp w hw (tS := 𝟙 _) (t₀ := t) (Category.id_comp t).symm n
      u' y' hu' hy' u (push y') hu'g.symm rfl 1 (h _ hy)
  have h1 := hND F P' n hn u' hu' hall
  apply hi
  rw [← hpu, ← tbpush, h1, tb1, MonObj.comp_one]

section Act

variable {S : Scheme.{0}} {B : Out.PolAV S} {O : Type} [Ring O] [StarRing O] (o : B.OAct O) {T : Over S}

theorem pairing_act_add (z : T ⟶ B.A) (a b : O) : z ≫ o.act (a + b) = (z ≫ o.act a) * (z ≫ o.act b) := by
  rw [o.map_add, H1.comp_padd]

theorem pairing_act_zero (z : T ⟶ B.A) : z ≫ o.act 0 = 1 := by
  have h := pairing_act_add o z 0 0
  rw [add_zero] at h
  exact mul_left_cancel (a := z ≫ o.act 0) (by rw [_root_.mul_one]; exact h.symm)

theorem pairing_act_nat (z : T ⟶ B.A) (n : ℕ) : z ≫ o.act (n : O) = z ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, pow_zero, pairing_act_zero]
  | succ n ih => rw [Nat.cast_succ, pairing_act_add, ih, o.map_one, Category.comp_id, pow_succ]

theorem pairing_act_mul (z : T ⟶ B.A) (a b : O) : z ≫ o.act (a * b) = (z ≫ o.act b) ≫ o.act a := by
  rw [o.map_mul, Category.assoc]

theorem pairing_act_kill (z : T ⟶ B.A) (n : ℕ) (hz : z ^ n = 1) (r : O) : z ≫ o.act (r * n) = 1 := by
  have := o.hom r
  rw [pairing_act_mul, pairing_act_nat, hz, MonObj.one_comp]

end Act

theorem pairing_tors {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] {T : Over S} (z : T ⟶ G)
    (f : G ⟶ G') (hf : IsMonHom f) (n : ℕ) (hz : z ^ n = 1) : (z ≫ f) ^ n = 1 := by
  have := hf
  rw [← MonObj.pow_comp, hz, MonObj.one_comp]

theorem halfToFullTorsion (hR : WeilAdjoint) (hW : Out.WeilSt) (hND : Out.WeilNondegSt) (hBC : Out.PolBaseChangeSt) :
    HalfToFullTorsion := by
  intro E _ _ _ H D l c k _ bF a P _ oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ d₁ d₂ F _ _ _ hfix x hx
  letI := H.starRing
  obtain ⟨θ, wθ, -, hθm, hθφ, hθact, -, hwθ, -, -⟩ :=
    exists_comparison E H D l c k bF a P oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ d₁ d₂
  have := hθm

  have hMk : (l.M : k) ≠ 0 := by
    have h0 : l.M ≠ 0 := by have := l.three_le; omega
    rw [← map_natCast bF]
    exact (map_ne_zero bF).2 (Nat.cast_ne_zero.mpr h0)
  have hM0 : (l.M : F) ≠ 0 := by
    have hC : (PowerSeries.C (l.M : k)) ≠ 0 := by
      intro h
      have := congrArg PowerSeries.constantCoeff h
      simp only [PowerSeries.constantCoeff_C, map_zero] at this
      exact hMk this
    have hfr : algebraMap (PowerSeries k) (FractionRing (PowerSeries k)) (PowerSeries.C (l.M : k)) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (PowerSeries k) (FractionRing (PowerSeries k)))).2 hC
    have e : (l.M : F) = algebraMap (FractionRing (PowerSeries k)) F
        (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)) (PowerSeries.C (l.M : k))) := by
      simp
    rw [e]
    exact (map_ne_zero _).2 hfr

  have inj : ∀ y y' : Over.mk (Out.jFK (R := PowerSeries k) F ≫ Out.jK (PowerSeries k)) ⟶ P.toPre.P.A,
      y.left ≫ φ₂ = y'.left ≫ φ₂ → y = y' := fun y y' h =>
    Over.OverMorphism.ext (d₂.1.1.hom_ext h (by rw [Over.w y, Over.w y']))
  have fixMb : ∀ z : Over.mk (Out.jFK (R := PowerSeries k) F ≫ Out.jK (PowerSeries k)) ⟶ P.toPre.P.A,
      (∀ m ∈ l.Mb, z ≫ oP.onB.act m = 1) → z ≫ θ.hom = z := fun z hz =>
    inj _ _ (by rw [Over.comp_left, Category.assoc, hθφ]; exact hfix z hz)

  have h1mem : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.coprime]; exact Submodule.mem_top
  obtain ⟨m1, hm1, m2, hm2, hm12⟩ := Submodule.mem_sup.mp h1mem
  have kill : ∀ z : Over.mk (Out.jFK (R := PowerSeries k) F ≫ Out.jK (PowerSeries k)) ⟶ P.toPre.P.A,
      z ^ l.M = 1 → ∀ m ∈ l.Mb, ∀ m' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), z ≫ oP.onB.act (m * m') = 1 := by
    intro z hz m hm m' hm'
    have hmm := Ideal.mul_mem_mul hm hm'
    rw [l.prod] at hmm
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmm
    rw [← hr]
    exact pairing_act_kill oP.onB z l.M hz r
  have hs : star m1 ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mem_map_of_mem _ hm1
  have hxθ : (x ≫ θ.hom) ^ l.M = 1 := pairing_tors x θ.hom hθm l.M hx
  have hx2 : (x ≫ oP.onB.act m1) ^ l.M = 1 := pairing_tors x _ (oP.onB.hom m1) l.M hx
  have hx2θ : ((x ≫ oP.onB.act m1) ≫ θ.hom) ^ l.M = 1 := pairing_tors _ θ.hom hθm l.M hx2

  have hfix1 : (x ≫ oP.onB.act m2) ≫ θ.hom = x ≫ oP.onB.act m2 := fixMb _ fun m hm => by
    rw [← pairing_act_mul]; exact kill x hx m hm m2 hm2

  have hpair : ∀ z : Over.mk (Out.jFK (R := PowerSeries k) F ≫ Out.jK (PowerSeries k)) ⟶ P.toPre.P.A,
      z ^ l.M = 1 → Out.WeilIs P.toPre.P.A P.toPre.P.L l.M
        (((x ≫ oP.onB.act m1) ≫ θ.hom) * (x ≫ oP.onB.act m1)⁻¹) z 1 := by
    intro z hz
    have hwt : (z ≫ oP.onB.act (star m1)) ^ l.M = 1 := pairing_tors z _ (oP.onB.hom (star m1)) l.M hz
    have hwfix : (z ≫ oP.onB.act (star m1)) ≫ θ.hom = z ≫ oP.onB.act (star m1) := fixMb _ fun m hm => by
      rw [← pairing_act_mul]; exact kill z hz m hm (star m1) hs
    obtain ⟨cv, hcv, huniq⟩ := (hW _ P.toPre.P l.M _).1 x (z ≫ oP.onB.act (star m1)) hx hwt
    obtain ⟨cv', hcv', -⟩ := (hW _ P.toPre.P l.M _).1 (x ≫ θ.hom) (z ≫ oP.onB.act (star m1)) hxθ hwt
    have hcvx : Out.WeilIs P.toPre.P.A P.toPre.P.L l.M x (z ≫ oP.onB.act (star m1)) cv' :=
      pairing_weilTheta hW inferInstance P.toPre.P θ hθm wθ hwθ l.M x _ hx hwt cv' (by rw [hwfix]; exact hcv')
    have hcc : cv' = cv := huniq cv' hcvx
    rw [hcc] at hcv'
    have h1 : Out.WeilIs P.toPre.P.A P.toPre.P.L l.M ((x ≫ oP.onB.act m1) ≫ θ.hom) z cv := by
      rw [Category.assoc, hθact m1, ← Category.assoc]
      exact (hR _ P.toPre.P (𝓞 E) oP.onB l.M _ (x ≫ θ.hom) z m1 cv hxθ hz).2 hcv'
    have h2 : Out.WeilIs P.toPre.P.A P.toPre.P.L l.M (x ≫ oP.onB.act m1) z cv :=
      (hR _ P.toPre.P (𝓞 E) oP.onB l.M _ x z m1 cv hx hz).2 hcv
    have h3 := pairing_weilInv hW P.toPre.P l.M _ z hx2 hz cv h2
    have h4 := (hW _ P.toPre.P l.M _).2.1 _ _ z cv cv⁻¹ h1 h3
    rwa [mul_inv_cancel] at h4
  have hu : ((x ≫ oP.onB.act m1) ≫ θ.hom) * (x ≫ oP.onB.act m1)⁻¹ = 1 :=
    pairing_nondeg hW hND hBC P.toPre.P F _ l.M hM0 _
      (by rw [mul_pow, inv_pow, hx2θ, hx2, inv_one, _root_.one_mul]) hpair
  have hfix2 : (x ≫ oP.onB.act m1) ≫ θ.hom = x ≫ oP.onB.act m1 := mul_inv_eq_one.mp hu
  have hsplit : (x ≫ oP.onB.act m1) * (x ≫ oP.onB.act m2) = x := by
    rw [← pairing_act_add, hm12, oP.onB.map_one, Category.comp_id]
  have hθx : x ≫ θ.hom = x := by
    calc x ≫ θ.hom = ((x ≫ oP.onB.act m1) * (x ≫ oP.onB.act m2)) ≫ θ.hom := by rw [hsplit]
      _ = ((x ≫ oP.onB.act m1) ≫ θ.hom) * ((x ≫ oP.onB.act m2) ≫ θ.hom) := MonObj.mul_comp _ _ _
      _ = x := by rw [hfix1, hfix2, hsplit]
  rw [← hθφ, ← Category.assoc, ← Over.comp_left, hθx]

end
section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

theorem ext_of_schDom {W X Y Z : Scheme.{0}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) [IsSchemeTheoreticallyDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  haveI : IsSeparated Y'.hom := ‹IsSeparated s›
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let ι' : U' ⟶ X' := Over.homMk ι
  have e : ι' ≫ f' = ι' ≫ g' := by
    ext1
    exact hU
  let l := equalizer.lift ι' e
  have hι : ι = l.left ≫ (equalizer.ι f' g').left := by
    rw [← Over.comp_left, equalizer.lift_ι]; rfl
  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    apply le_bot_iff.1
    calc _ ≤ (l.left ≫ (equalizer.ι f' g').left).ker := Scheme.Hom.le_ker_comp _ _
      _ = ⊥ := by rw [← hι]; exact ι.ker_eq_bot
  haveI : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.2 hker
  have h0 : IsIso ((Over.forget Z).map (equalizer.ι f' g')) := (inferInstance : IsIso (equalizer.ι f' g').left)
  have : IsIso (equalizer.ι f' g') := isIso_of_reflects_iso _ (Over.forget Z)
  have hfg : f' = g' := (cancel_epi (equalizer.ι f' g')).1 (equalizer.condition f' g')
  exact congrArg CommaMorphism.left hfg

theorem schDom_spec_map {A B : Type} [CommRing A] [CommRing B] [IsReduced A] (φ : A →+* B)
    (hφ : Function.Injective φ) : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom φ)) := by
  haveI : IsDominant (Spec.map (CommRingCat.ofHom φ)) := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le
  exact IsSchemeTheoreticallyDominant.of_isDominant _

set_option maxHeartbeats 800000 in

theorem over_ext_of_points {F : Type} [Field F] [IsAlgClosed F] {K Y : Over (Spec (CommRingCat.of F))}
    [LocallyOfFiniteType K.hom] [FormallyUnramified Y.hom] [LocallyOfFiniteType Y.hom] (u v : K ⟶ Y)
    (h : ∀ p : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ K, p ≫ u = p ≫ v) : u = v := by
  have hop : IsOpenImmersion (equalizer.ι u v).left := by
    refine MorphismProperty.of_isPullback ((Limits.isPullback_equalizer_prod u v).map (Over.forget _)).flip ?_
    show IsOpenImmersion (prod.lift (𝟙 Y) (𝟙 Y)).left
    rw [← MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _ (Over.prodLeftIsoPullback Y Y).hom]
    convert! (inferInstance : IsOpenImmersion (pullback.diagonal Y.hom))
    ext1 <;> simp [← Over.comp_left] <;> first | rw [prod.lift_fst, Over.id_left] | rw [prod.lift_snd, Over.id_left]
  have : JacobsonSpace K.left := LocallyOfFiniteType.jacobsonSpace K.hom
  have hcl : closedPoints K.left ⊆ Set.range (equalizer.ι u v).left := by
    intro x hx
    let p : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ K :=
      Over.homMk (pointOfClosedPoint K.hom x hx) (pointOfClosedPoint_comp K.hom x hx)
    let q := equalizer.lift p (h p)
    let pt : (𝟙_ (Over (Spec (CommRingCat.of F)))).left := IsLocalRing.closedPoint F
    refine ⟨q.left pt, ?_⟩
    have e : q.left ≫ (equalizer.ι u v).left = p.left := by rw [← Over.comp_left, equalizer.lift_ι]
    have e' : (q.left ≫ (equalizer.ι u v).left) pt = p.left pt := by rw [e]
    exact e'.trans (pointOfClosedPoint_apply K.hom x hx pt)
  have hsurj : Function.Surjective (equalizer.ι u v).left := by
    by_contra hns
    obtain ⟨x, hx⟩ := not_forall.1 hns
    have hC : IsClosed (Set.range (equalizer.ι u v).left)ᶜ :=
      (equalizer.ι u v).left.isOpenEmbedding.isOpen_range.isClosed_compl
    obtain ⟨y, hy1, hy2⟩ := nonempty_inter_closedPoints ⟨x, hx⟩ hC.isLocallyClosed
    exact hy1 (hcl hy2)
  have : Surjective (equalizer.ι u v).left := ⟨hsurj⟩
  have : IsIso (equalizer.ι u v).left := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨hop, this⟩
  have h0 : IsIso ((Over.forget _).map (equalizer.ι u v)) := (inferInstance : IsIso (equalizer.ι u v).left)
  have : IsIso (equalizer.ι u v) := isIso_of_reflects_iso _ (Over.forget _)
  exact (cancel_epi (equalizer.ι u v)).1 (equalizer.condition u v)

open MonObj in
set_option maxHeartbeats 1600000 in

theorem fix_torsion (hMul : Out.MulNSt) {F : Type} [Field F] [IsAlgClosed F] (P : Out.PolAV (Spec (CommRingCat.of F)))
    (M : ℕ) (hM1 : 1 ≤ M) (hM : (M : F) ≠ 0) (σ : P.A ⟶ P.A) [IsMonHom σ]
    (hσ : ∀ x : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ P.A, x ^ M = 1 → x ≫ σ = x)
    (T : Over (Spec (CommRingCat.of F))) (x : T ⟶ P.A) (hx : x ^ M = 1) : x ≫ σ = x := by
  obtain ⟨-, -, -, het, -⟩ := hMul _ P M hM1
  have hunit : IsUnit ((M : ℕ) : Γ(Spec (CommRingCat.of F), ⊤)) := by
    have e := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
    have : IsUnit (e.symm (M : F)) := (isUnit_iff_ne_zero.2 hM).map e.symm
    rwa [map_natCast] at this
  have : Etale (Out.mulA P.A M).left := het hunit
  have hpow : ∀ {Z : Over (Spec (CommRingCat.of F))} (z : Z ⟶ P.A), z ^ M = z ≫ Out.mulA P.A M := fun z =>
    (congrArg (· ^ M) (Category.comp_id z).symm).trans (MonObj.comp_pow (𝟙 P.A) M z).symm
  have hcomm : σ ≫ Out.mulA P.A M = Out.mulA P.A M ≫ σ := by
    rw [← hpow, Out.mulA, MonObj.pow_comp, Category.id_comp]
  let m := (Out.mulA P.A M).left
  let e := (η[P.A]).left
  let K : Over (Spec (CommRingCat.of F)) := Over.mk (show pullback m e ⟶ Spec (CommRingCat.of F) from pullback.snd m e)
  have hw : pullback.fst m e ≫ P.A.hom = pullback.snd m e := by
    rw [← Over.w (Out.mulA P.A M), ← Category.assoc, pullback.condition, Category.assoc, Over.w η[P.A]]
    exact Category.comp_id _
  have hσm : (pullback.fst m e ≫ σ.left) ≫ m = pullback.snd m e ≫ e := by
    have h1 : σ.left ≫ m = m ≫ σ.left := congrArg CommaMorphism.left hcomm
    have h2 : e ≫ σ.left = e := congrArg CommaMorphism.left (IsMonHom.one_hom σ)
    rw [Category.assoc, h1, ← Category.assoc, pullback.condition, Category.assoc, h2]
  let τ : K ⟶ K := Over.homMk (pullback.lift _ _ hσm) (pullback.lift_snd _ _ _)
  have hKe : Etale K.hom := by show Etale (pullback.snd m e); infer_instance
  have : LocallyOfFinitePresentation K.hom := inferInstance
  have : LocallyOfFiniteType K.hom := inferInstance
  have : FormallyUnramified K.hom := inferInstance
  have hτ : τ = 𝟙 K := by
    refine over_ext_of_points τ (𝟙 K) fun p => ?_
    rw [Category.comp_id]
    ext1
    apply pullback.hom_ext
    · show p.left ≫ pullback.lift _ _ hσm ≫ pullback.fst m e = p.left ≫ pullback.fst m e
      rw [pullback.lift_fst]
      have hp1 : p.left ≫ pullback.snd m e = 𝟙 _ := Over.w p
      let q : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ P.A := Over.homMk (p.left ≫ pullback.fst m e) (by
        rw [Category.assoc, hw, hp1]; rfl)
      have hq : q ^ M = 1 := by
        rw [hpow]
        ext1
        show (p.left ≫ pullback.fst m e) ≫ m = (toUnit _ ≫ η[P.A]).left
        rw [Category.assoc, pullback.condition, ← Category.assoc, hp1, Category.id_comp, Over.comp_left]
        have : toUnit (𝟙_ (Over (Spec (CommRingCat.of F)))) = 𝟙 _ := Subsingleton.elim _ _
        rw [this, Over.id_left, Category.id_comp]
      have := congrArg CommaMorphism.left (hσ q hq)
      rw [← Category.assoc]
      exact this
    · show p.left ≫ pullback.lift _ _ hσm ≫ pullback.snd m e = p.left ≫ pullback.snd m e
      rw [pullback.lift_snd]
  have hxm : x.left ≫ m = T.hom ≫ e := by
    have := congrArg CommaMorphism.left ((hpow x).symm.trans hx)
    exact this
  let κ : T ⟶ K := Over.homMk (pullback.lift x.left T.hom hxm) (pullback.lift_snd _ _ _)
  have hτl : pullback.lift _ _ hσm = 𝟙 _ := congrArg CommaMorphism.left hτ
  ext1
  show x.left ≫ σ.left = x.left
  have k1 : x.left = κ.left ≫ pullback.fst m e := (pullback.lift_fst _ _ _).symm
  rw [k1, Category.assoc, ← pullback.lift_fst (pullback.fst m e ≫ σ.left) (pullback.snd m e) hσm, hτl,
    Category.id_comp]

end
section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

def isoInv {X : Scheme.{0}} {L M : LB X} (t : LB.Iso L M) : LB.Iso M L :=
  ⟨fun p => (res (fun _ hx => ⟨hx.2, hx.1⟩ : L.U p.1 ⊓ M.U p.2 ≤ M.U p.2 ⊓ L.U p.1) (t.s (p.2, p.1)))⁻¹⟩

theorem isoInv_isGen {X : Scheme.{0}} {L M : LB X} {t : LB.Iso L M} (ht : t.IsGen) : (isoInv t).IsGen := by
  intro p q
  apply unit_ext
  intro x hx
  have hp : x ∈ L.U p.1 ⊓ M.U p.2 := hx.1
  have hq : x ∈ L.U q.1 ⊓ M.U q.2 := hx.2
  have hx' : x ∈ (LB.div M L).U (p.2, p.1) ⊓ (LB.div M L).U (q.2, q.1) := ⟨⟨hp.2, hp.1⟩, ⟨hq.2, hq.1⟩⟩
  have eu : ∀ r, x ∈ (LB.div L M).U r →
      gm (𝟙 X) x _ ((isoInv t).s r) = (gm (𝟙 X) x _ (t.s (r.2, r.1)))⁻¹ := fun r hr => by
    show gm _ x _ ((res _ _)⁻¹) = _
    rw [map_inv]
    exact congrArg Inv.inv (gm_res (𝟙 X) x _ hr _)
  have e : gm (𝟙 X) x _ (t.s (p.2, p.1)) = gm (𝟙 X) x _ (M.g p.2 q.2) * (gm (𝟙 X) x _ (L.g p.1 q.1))⁻¹ *
      gm (𝟙 X) x _ (t.s (q.2, q.1)) :=
    (gm_res (𝟙 X) x _ hx' _).symm.trans ((congrArg (gm (𝟙 X) x _) (ht (p.2, p.1) (q.2, q.1))).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div L M (𝟙 X) x (p.2, p.1) (q.2, q.1) hx')
        (gm_res (𝟙 X) x _ hx' _))))
  refine (gm_res _ _ _ hx _).trans ((eu p hp).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_div M L (𝟙 X) x p q hx) ((gm_res _ _ _ hx _).trans (eu q hq)))).symm))
  rw [e]
  simp only [mul_inv_rev, inv_inv]
  ac_rfl

def pullGenLB {X Y : Scheme.{0}} {L : LB X} (c : LB.Gen L) (h : Y ⟶ X) : LB.Gen (L.pull h) :=
  ⟨fun j => res (fun _ hy => Set.mem_iInter.1 hy PUnit.unit : (L.pull h).U j ≤ h ⁻¹ᵁ L.U (j PUnit.unit))
    (pullU h _ (c.s (j PUnit.unit)))⟩

theorem pullGenLB_isGen {X Y : Scheme.{0}} {L : LB X} {c : LB.Gen L} (hc : c.IsGen) (h : Y ⟶ X) :
    (pullGenLB c h).IsGen := by
  intro j j'
  apply unit_ext
  intro y hy
  have m1 : h y ∈ L.U (j PUnit.unit) := Set.mem_iInter.1 hy.1 PUnit.unit
  have m2 : h y ∈ L.U (j' PUnit.unit) := Set.mem_iInter.1 hy.2 PUnit.unit
  have m12 : h y ∈ L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit) := ⟨m1, m2⟩
  have e := congrArg (gm h y _) (hc (j PUnit.unit) (j' PUnit.unit))
  rw [gm_res h y _ m12, map_mul, gm_res h y _ m12] at e
  rw [gm_res (𝟙 Y) y _ hy, map_mul, gm_res (𝟙 Y) y _ hy]
  have hs : ∀ i, y ∈ (L.pull h).U i →
      gm (𝟙 Y) y _ ((pullGenLB c h).s i) = gm h y _ (c.s (i PUnit.unit)) := fun i hi => gm_rp₁ h y _ _ _ hi _
  rw [hs j hy.1, hs j' hy.2, e]
  congr 1
  symm
  show gm (𝟙 Y) y _ (∏ _k : PUnit, (res _ (pullU h _ (L.g (j PUnit.unit) (j' PUnit.unit)))) ^ (1 : ℤ)) =
    gm h y _ (L.g (j PUnit.unit) (j' PUnit.unit))
  simp only [Fintype.prod_unique, zpow_one]
  exact gm_rp₁ h y _ _ _ hy _

end
section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

theorem exists_gen_congr {X Y : Scheme.{0}} {L : LB X} {f f' g : Y ⟶ X} (h : f = f') {ε : Fin 2 → ℤ}
    (H : ∃ c : LB.Gen (LB.LinComb L (K := Fin 2) ![f, g] ε), c.IsGen) :
    ∃ c : LB.Gen (LB.LinComb L (K := Fin 2) ![f', g] ε), c.IsGen := by
  subst h; exact H

set_option maxHeartbeats 6400000 in
theorem serreFromPoints (hS : Out.SerreSt) (hMul : Out.MulNSt) (hBC : Out.PolBaseChangeSt) : SerreFromPoints := by
  intro E _ _ _ H D l c k _ bF a P _ oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ d₁ d₂ hpts
  letI := H.starRing
  obtain ⟨θ, wθ, -, hθ, hθφ, -, -, gθ, -, -⟩ := exists_comparison E H D l c k bF a P oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ d₁ d₂
  have d₁' := d₁
  have d₂' := d₂
  unfold WitData at d₁' d₂'
  obtain ⟨s1, -⟩ := d₁'
  obtain ⟨s1', -⟩ := d₂'
  have : CharZero k := charZero_of_injective_ringHom bF.injective
  have : CharZero (PowerSeries k) := charZero_of_injective_ringHom (f := PowerSeries.C (R := k))
    (fun a b h => by simpa using congrArg (PowerSeries.constantCoeff (R := k)) h)
  have : CharZero (FractionRing (PowerSeries k)) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (PowerSeries k) _)
  let F := AlgebraicClosure (FractionRing (PowerSeries k))
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing (PowerSeries k)) F).injective
  let jFR : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of (PowerSeries k)) :=
    Out.jFK (R := PowerSeries k) F ≫ Out.jK (PowerSeries k)
  obtain ⟨P', g', hg, -, hmul, t, gt⟩ := hBC _ _ jFR P.toPre.P
  have gpA : IsGrpPullback P'.A P.toPre.P.A jFR g' := ⟨hg, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase hg.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase hg.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← hmul]; rfl⟩
  have mθ : IsMonHom θ.hom := hθ
  obtain ⟨θF, mθF, hθF⟩ := grpPullback_iso ((gpA.comp (isGrpPullback_of_iso θ)).congr (Category.comp_id _) rfl) gpA
  have hθF' : θF.hom.left ≫ g' = g' ≫ θ.hom.left := hθF
  have hM1 : 1 ≤ l.M := le_trans (by norm_num) l.three_le
  have hMF : (l.M : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let tb : (𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ P'.A) →*
      (Over.mk ((𝟙_ (Over (Spec (CommRingCat.of F)))).hom ≫ jFR) ⟶ P.toPre.P.A) :=
    MonoidHom.mk' (Out.toBase hg.w) (fun x y => hmul _ x y)
  let eT : Over.mk ((𝟙_ (Over (Spec (CommRingCat.of F)))).hom ≫ jFR) ≅ Out.TF (R := PowerSeries k) F :=
    Over.isoMk (Iso.refl _) (by simp [jFR, Out.TF])
  have hσ : ∀ x' : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ P'.A, x' ^ l.M = 1 → x' ≫ θF.hom = x' := by
    intro x' hx'
    let x : Out.TF (R := PowerSeries k) F ⟶ P.toPre.P.A := eT.inv ≫ tb x'
    have hx : x ^ l.M = 1 := by
      show (eT.inv ≫ tb x') ^ l.M = 1
      rw [← MonObj.comp_pow, ← map_pow, hx', map_one]
      simp
    have h1 := hpts F x hx
    have hxl : x.left = x'.left ≫ g' := by
      show (eT.inv ≫ Out.toBase hg.w x').left = _
      simp [eT, Out.toBase]
    rw [hxl] at h1
    have h2 : (x'.left ≫ g') ≫ θ.hom.left = x'.left ≫ g' := by
      apply s1'.1.hom_ext
      · rw [Category.assoc, hθφ]; exact h1
      · rw [Category.assoc, Over.w θ.hom]
    ext1
    apply hg.hom_ext
    · rw [Over.comp_left, Category.assoc, hθF', ← Category.assoc]; exact h2
    · rw [Over.comp_left, Category.assoc, Over.w θF.hom]
  have hgen : ∀ p : Spec (CommRingCat.of F), ∃ V : (Spec (CommRingCat.of F)).Opens, p ∈ V ∧
      ∃ c : LB.Gen ((LB.LinComb P'.L (K := Fin 2) ![θF.hom.left, 𝟙 P'.A.left] ![1, -1]).pull
        (P'.A.hom ⁻¹ᵁ V).ι), c.IsGen := by
    intro p
    have pu := (isGen_iff (isoInv t)).1 (isoInv_isGen gt)
    have pθ := (isGen_iff wθ).1 gθ
    obtain ⟨w₁c, T₁⟩ := exists_comp P.toPre.P.isLB wθ (isoInv t) pθ pu P.toPre.P.isLB P'.isLB
    have hc : g' ≫ θ.hom.left = θF.hom.left ≫ g' := hθF'.symm
    have pc := pgen_pullCongr hc (T₁.pgen_comp P.toPre.P.isLB pθ pu)
    obtain ⟨w', T₂⟩ := exists_cancel P.toPre.P.isLB (isoInv t) (pullCongr hc w₁c) pu pc P'.isLB P'.isLB
    have pw' := T₂.pgen_cancel P.toPre.P.isLB pu pc
    obtain ⟨c₁, gc₁⟩ := exists_gen_congr (Category.id_comp θF.hom.left) (gen_of_iso pw' (𝟙 _))
    exact ⟨⊤, trivial, pullGenLB c₁ _, pullGenLB_isGen gc₁ _⟩
  have hθ1 : θF.hom = 𝟙 P'.A := hS _ P' l.M l.three_le θF mθF hgen
    (fun T x hx => fix_torsion hMul P' l.M hM1 hMF θF.hom hσ T x hx)
  have hg1 : g' ≫ θ.hom.left = g' := by rw [← hθF', hθ1, Over.id_left, Category.id_comp]
  haveI : IsSchemeTheoreticallyDominant (Out.jK (PowerSeries k)) :=
    schDom_spec_map _ (IsFractionRing.injective (PowerSeries k) _)
  haveI : IsSchemeTheoreticallyDominant (Out.jFK (R := PowerSeries k) F) :=
    schDom_spec_map _ (algebraMap (FractionRing (PowerSeries k)) F).injective
  haveI : IsSchemeTheoreticallyDominant jFR := by show IsSchemeTheoreticallyDominant (_ ≫ _); infer_instance
  haveI : QuasiCompact jFR := by show QuasiCompact (_ ≫ _); infer_instance
  haveI := P.toPre.P.isAb.smooth
  haveI := a.D₀.P.isAb.proper
  haveI : IsSchemeTheoreticallyDominant g' := IsSchemeTheoreticallyDominant.of_isPullback hg.flip
  refine ext_of_schDom a.D₀.P.A.hom (s1.1.w.trans s1'.1.w.symm) g' ?_
  rw [← hθφ, ← Category.assoc, hg1]

end

section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem fixesHalfTorsion : FixesHalfTorsion := by
  intro E _ _ _ H D l c k _ bF a t P _ φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ hin F _ _ _ x _
  obtain ⟨d₁, d₂, hl⟩ := hin
  rw [(GlobalTheory.DataRigid.dataRigid E H D l c k bF a P.D P.oD φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₁ d₁ d₂ hl).1]

theorem all_four : FixesHalfTorsion ∧ HalfToFullTorsion ∧ SerreFromPoints ∧ WeilAdjoint :=
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hR : WeilAdjoint := weilAdjoint hL.globalFns hL.cube
  ⟨fixesHalfTorsion, halfToFullTorsion hR hL.weil hL.weilNondeg hL.polBaseChange,
    serreFromPoints hL.serre hL.mulN hL.polBaseChange, hR⟩

end

end GlobalTheory.LevelRigid
