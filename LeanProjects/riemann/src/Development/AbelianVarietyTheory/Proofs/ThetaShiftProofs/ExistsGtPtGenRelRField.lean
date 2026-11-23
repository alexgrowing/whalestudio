import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCommonField
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension

noncomputable section

namespace GlobalTheory.ConstPoint

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

section Pull

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {f : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} {Φ : D'.P.A.left ⟶ D.P.A.left}

theorem th_pushPt (hG : GlobalFnsSt) (gp : IsGrpPullback D'.P.A D.P.A (spMap f) Φ)
    {w : LB.Iso D'.P.L (D.P.L.pull Φ)} (hw : PGen w) {T' : Over (Sp R')} {z : T'.left} {J J'}
    (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') (a b c : T' ⟶ D'.P.A) :
    th D (T := Over.mk (T'.hom ≫ spMap f)) z J (pushPt gp.1.w a) (pushPt gp.1.w b) (pushPt gp.1.w c) =
      ConstFam.wVal w z J J' (a * b * c).left * (ConstFam.wVal w z J J' (a * b).left)⁻¹ *
        (ConstFam.wVal w z J J' (a * c).left)⁻¹ * (ConstFam.wVal w z J J' (b * c).left)⁻¹ *
        ConstFam.wVal w z J J' a.left * ConstFam.wVal w z J J' b.left * ConstFam.wVal w z J J' c.left *
        (ConstFam.wVal w z J J' (1 : T' ⟶ D'.P.A).left)⁻¹ * th D' z J' a b c := by
  have e := ArcTransport.cub_push hG gp hw (T' := T') hJ hJ' a b c
  have q : (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 =
      (lift (pushPt gp.1.w a) (lift (pushPt gp.1.w b) (pushPt gp.1.w c))).left := hom_ext_triple _ fun i => by
    rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i <;> simp [x3, pushPt, cubeMapOf]
  rw [q] at e
  exact e.trans (congrArg₂ (· * ·) (prod_cub a b c (fun q => Geo.Tor.gw w q z (J (q ≫ Φ)) (J' q))) rfl)

theorem exists_gtPt_through (hG : GlobalFnsSt) (gp : IsGrpPullback D'.P.A D.P.A (spMap f) Φ)
    {w : LB.Iso D'.P.L (D.P.L.pull Φ)} (hw : w.IsGen) (e : D'.X →+ D.X)
    (hc : ∀ y, (D'.c y).left ≫ Φ = spMap f ≫ (D.c (e y)).left) {T : Over (Sp R)} {T' : Over (Sp R')}
    (h : T'.left ⟶ T.left) (hh : h ≫ T.hom = T'.hom ≫ spMap f) (g₀ : GtPt D T) :
    ∃ g : GtPt D' T', ∀ y, (∀ k, DegPre.gtφT D' T' g.b y k ≫ Φ = h ≫ DegPre.gtφT D T g₀.b (e y) k) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T'.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
        val (g₀.s (e y)) (r ≫ h) z J =
          (∏ k, ConstFam.wVal w z J J' (r ≫ DegPre.gtφT D' T' g.b y k) ^ DegPre.gtε k) * val (g.s y) r z J' := by
  let ρ : Over.mk (T'.hom ≫ spMap f) ⟶ T := Over.homMk h hh
  have sq : (h ≫ g₀.b.left) ≫ D.P.A.hom = T'.hom ≫ spMap f := by rw [Category.assoc, Over.w, hh]
  let b : T' ⟶ D'.P.A := Over.homMk (gp.1.lift (h ≫ g₀.b.left) T'.hom sq) (gp.1.lift_snd _ _ _)
  have hb : pushPt gp.1.w b = ρ ≫ g₀.b := Over.OverMorphism.ext (gp.1.lift_fst _ _ _)
  have hcP : ∀ y, pushPt gp.1.w (cP D' T' y) = cP D _ (e y) := fun y => Over.OverMorphism.ext (by
    show (T'.hom ≫ (D'.c y).left) ≫ Φ = (T'.hom ≫ spMap f) ≫ (D.c (e y)).left
    rw [Category.assoc, hc, Category.assoc])
  have hψ : ∀ y k, DegPre.gtφT D' T' b y k ≫ Φ = h ≫ DegPre.gtφT D T g₀.b (e y) k := fun y k => by
    fin_cases k
    · refine congrArg (fun q => q.left) ((map_mul (pushHom gp T') (cP D' T' y) b).trans
        (Eq.trans ?_ (MonObj.comp_mul ρ (cP D T (e y)) g₀.b).symm))
      rw [comp_cP, ← hb, ← hcP]; rfl
    · exact congrArg (fun q => q.left) ((hcP y).trans (comp_cP D ρ (e y)).symm)
    · exact congrArg (fun q => q.left) hb
    · exact congrArg (fun q => q.left) ((map_one (pushHom gp T')).trans (MonObj.comp_one ρ).symm)
  choose t ht vt using fun y =>
    ConstFam.exists_gen_through hw D.P.isLB D'.P.isLB (hψ y) (g₀.s (e y)) (g₀.isGen (e y))
  have vt' : ∀ y (z : T'.left) J J', Good D.P.L z J → Good D'.P.L z J' → val (g₀.s (e y)) h z J =
      (ConstFam.wVal w z J J' (cP D' T' y * b).left)⁻¹ * ConstFam.wVal w z J J' (cP D' T' y).left *
        ConstFam.wVal w z J J' b.left * (ConstFam.wVal w z J J' (1 : T' ⟶ D'.P.A).left)⁻¹ *
        val (t y) (𝟙 _) z J' := fun y z J J' hJ hJ' => by
    have v := vt y _ (𝟙 _) z J J' hJ hJ'
    have p := FormalPoint.prod_gtφT (𝟙 T') b y (ConstFam.wVal w z J J')
    rw [Category.id_comp] at v p
    exact v.trans (congrArg (· * _) p)
  refine ⟨⟨b, t, ht, corr_of_val D'.P.isLB fun z J' hJ' => ?_, fun y y' => corr_of_val D'.P.isLB fun z J' hJ' => ?_⟩,
    fun y => ⟨hψ y, vt y⟩⟩
  · obtain ⟨J, hJ⟩ := ConstFam.exists_good' D.P.isLB z
    have v := vt' 0 z J J' hJ hJ'
    rw [map_zero, (val_corr hJ g₀.s_zero h).trans (val_one _), cPoint_zero, _root_.one_mul] at v
    rw [val_one]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul v
    simp only [ofMul_mul, ofMul_inv, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'
  · obtain ⟨J, hJ⟩ := ConstFam.exists_good' D.P.isLB z
    have e₁ := FormalPoint.val_s_add g₀ ρ (z := z) hJ (e y) (e y')
    rw [← hb, ← hcP, ← hcP, th_pushPt hG gp ((isGen_iff w).1 hw) hJ hJ', ← map_add] at e₁
    have v₁ := vt' y z J J' hJ hJ'
    have v₂ := vt' y' z J J' hJ hJ'
    have v₃ := vt' (y + y') z J J' hJ hJ'
    rw [cPoint_add] at v₃
    have c := val_cub D'.cub (𝟙 T') hJ' (cP D' T' y) (cP D' T' y') b
    rw [Category.id_comp, Category.id_comp, Category.id_comp] at c
    refine (val_mul hJ' _ _ _).trans (Eq.trans (congrArg₂ (· * ·) rfl c) (Eq.trans ?_ (val_mul hJ' _ _ _).symm))
    change val (g₀.s (e (y + y'))) h z J * _ = val (g₀.s (e y)) h z J * val (g₀.s (e y')) h z J at e₁
    rw [v₁, v₂, v₃] at e₁
    apply Additive.ofMul.injective
    have a₁ := congrArg Additive.ofMul e₁
    simp only [ofMul_mul, ofMul_inv] at a₁ ⊢
    linear_combination (norm := abel) a₁

end Pull

section Local

variable {A : Type} [CommRing A] [IsLocalRing A] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {φ : B ⟶ B₀}

theorem genRelR_of_val {w : LB.Iso M (M₀.pull φ)} (hw : w.IsGen) (hM : M.IsLB) (hM₀ : M₀.IsLB) {K : Type} [Fintype K]
    {ε : K → ℤ} {pt : K → (Sp A ⟶ B)} {pt₀ : K → (Sp A ⟶ B₀)} {t : LB.Gen (LB.LinComb M pt ε)}
    {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} (ht : t.IsGen) (ht₀ : t₀.IsGen) (hp : ∀ k, pt k ≫ φ = pt₀ k)
    (H : ∀ J J', Good M₀ (cpt A) J → Good M (cpt A) J' → val t₀ (𝟙 _) (cpt A) J =
      (∏ k, ConstFam.wVal w (cpt A) J J' (𝟙 _ ≫ pt k) ^ ε k) * val t (𝟙 _) (cpt A) J') : GenRelR w t t₀ := by
  obtain rfl : (fun k => pt k ≫ φ) = pt₀ := funext hp
  refine (genRelR_iff w t t₀).2 ⟨hp, fun j j₀ h₀ h₁ => ?_⟩
  set z := cpt A
  obtain ⟨J, hJ⟩ := ConstFam.exists_good' hM₀ z
  obtain ⟨J', hJ'⟩ := ConstFam.exists_good' hM z
  have H' := H J J' hJ hJ'
  rw [val_of t _ z J' (fun k => J' (pt k)) (fun k => by rw [Category.id_comp]),
    val_of t₀ _ z J (fun k => J (pt k ≫ φ)) (fun k => by rw [Category.id_comp])] at H'
  have m₀ : (𝟙 (Sp A) : Sp A ⟶ Sp A) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) j₀ := Set.mem_iInter.2 h₀
  have m₁ : (𝟙 (Sp A) : Sp A ⟶ Sp A) z ∈ LB.wchart M pt j := Set.mem_iInter.2 h₁
  have n₀ : (𝟙 (Sp A) : Sp A ⟶ Sp A) z ∈ LB.wchart M₀ (fun k => pt k ≫ φ) (fun k => J (pt k ≫ φ)) :=
    Set.mem_iInter.2 fun k => hJ (pt k ≫ φ)
  have n₁ : (𝟙 (Sp A) : Sp A ⟶ Sp A) z ∈ LB.wchart M pt (fun k => J' (pt k)) :=
    Set.mem_iInter.2 fun k => hJ' (pt k)
  have a := pw_trans ((isGen_iff w).1 hw) pt ε (𝟙 _) z m₀ n₀ m₁ n₁
  simp only [pw, ConstFam.wVal, Category.id_comp] at a H'
  refine congrArg Units.val ?_
  rw [a, gen_trans ht (𝟙 _) z m₁ n₁, gen_trans ht₀ (𝟙 _) z m₀ n₀, H']
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem valR_iso_trans {w : LB.Iso M (M₀.pull φ)} (hw : w.IsGen) (x : Sp A ⟶ B) {j j' : M₀.ι} {k k' : M.ι}
    (h : ⊤ ≤ x ⁻¹ᵁ (LB.div (M₀.pull φ) M).U (fun _ => j, k))
    (h' : ⊤ ≤ x ⁻¹ᵁ (LB.div (M₀.pull φ) M).U (fun _ => j', k')) :
    valR x _ (w.s (fun _ => j, k)).val * valR x _ (M.g k k').val =
      valR (x ≫ φ) _ (M₀.g j j').val * valR x _ (w.s (fun _ => j', k')).val := by
  have m := (top_le_iff_cpt _ _).1 h
  have m' := (top_le_iff_cpt _ _).1 h'
  have e := (isGen_iff w).1 hw _ x (cpt A) j j' k k' (mem_pull.1 m.1) (mem_pull.1 m'.1) m.2 m'.2
  apply toStkA_injective
  rw [map_mul, map_mul, toStkA_valR x _ _ h, toStkA_valR x _ _ h',
    toStkA_valR x (M.U k ⊓ M.U k') _ ((top_le_iff_cpt _ _).2 ⟨m.2, m'.2⟩),
    toStkA_valR (x ≫ φ) (M₀.U j ⊓ M₀.U j') _ ((top_le_iff_cpt _ _).2 ⟨mem_pull.1 m.1, mem_pull.1 m'.1⟩),
    ← Units.val_mul, ← Units.val_mul]
  refine congrArg Units.val ((congrArg (· * _) e).trans ?_)
  rw [mul_right_comm, inv_mul_cancel_right]
  rfl

theorem valR_g_self (hM : M.IsLB) (x : Sp A ⟶ B) {k : M.ι} (h : ⊤ ≤ x ⁻¹ᵁ M.U k) :
    valR x _ (M.g k k).val = 1 := by
  have m := (top_le_iff_cpt _ _).1 h
  apply toStkA_injective
  rw [toStkA_valR x (M.U k ⊓ M.U k) _ ((top_le_iff_cpt _ _).2 ⟨m, m⟩), gm_self hM x _ m, map_one, Units.val_one]

end Local

theorem exists_gtPt_genRelR {R R' A : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing A]
    [IsLocalRing A] {f : R →+* R'} {D : Out.DegPre R} {D' : Out.DegPre R'} {Φ : D'.P.A.left ⟶ D.P.A.left}
    (hG : Out.GlobalFnsSt) (gp : IsGrpPullback D'.P.A D.P.A (spMap f) Φ)
    {w : LB.Iso D'.P.L (D.P.L.pull Φ)} (hw : w.IsGen) (e : D'.X →+ D.X)
    (hc : ∀ y, (D'.c y).left ≫ Φ = spMap f ≫ (D.c (e y)).left) {T : Over (Sp R)} (s : Sp A ⟶ Sp R')
    (h : Sp A ⟶ T.left) (hh : h ≫ T.hom = s ≫ spMap f) (g₀ : Out.GtPt D T) :
    ∃ g : Out.GtPt D' (Over.mk s), ∀ y, GenRelR (A := A) w (g.s y) (LB.pullGen _ _ _ (g₀.s (e y)) h) := by
  obtain ⟨g, hg⟩ := exists_gtPt_through hG gp hw e hc (T' := Over.mk s) h hh g₀
  exact ⟨g, fun y => genRelR_of_val hw D'.P.isLB D.P.isLB (g.isGen y) (DVR.pullGen_isGen _ _ _ _ (g₀.isGen _) _) (hg y).1
    fun J J' hJ hJ' => (val_pull hJ _ _ _).trans ((hg y).2 _ (𝟙 _) _ J J' hJ hJ')⟩

theorem exists_gtPt_genRelR_field {R R' A F : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing A]
    [IsLocalRing A] [Field F] [Algebra (FractionRing R) F] {f : R →+* R'} {D : Out.DegPre R} {D' : Out.DegPre R'}
    {Φ : D'.P.A.left ⟶ D.P.A.left} (hG : Out.GlobalFnsSt) (gp : IsGrpPullback D'.P.A D.P.A (spMap f) Φ)
    {w : LB.Iso D'.P.L (D.P.L.pull Φ)} (hw : w.IsGen) (e' : D'.X →+ D.X) (e : D.X → D'.X) (he : ∀ x, e' (e x) = x)
    (hc : ∀ y, (D'.c y).left ≫ Φ = spMap f ≫ (D.c (e' y)).left) (s : Sp A ⟶ Sp R')
    (h : Sp A ⟶ Sp F) (hh : h ≫ (Out.TF (R := R) F).hom = s ≫ spMap f) (g₀ : Out.GtPtF D F) :
    ∃ g : Out.GtPt D' (Over.mk s), ∀ x, GenRelR (A := A) w (g.s (e x)) (LB.pullGen _ _ _ (g₀.s x) h) := by
  obtain ⟨g, hg⟩ := exists_gtPt_genRelR hG gp hw e' hc (T := Out.TF (R := R) F) s h hh
    ⟨g₀.b, g₀.s, g₀.isGen, g₀.s_zero, g₀.mult⟩
  refine ⟨g, fun x => ?_⟩
  have := hg (e x)
  rw [he] at this
  exact this

theorem unit_rearrange {A : Type} [CommRing A] {t t' g g₀ v r r' : A} {ω : Aˣ} (e₁ : t * g = t')
    (e₂ : v * g = g₀ * ω) (e₃ : r = g₀ * r') : v * ((ω⁻¹).val * (t' * r')) = t * r := by
  rw [← e₁, e₃, ← (Units.mul_inv_eq_iff_eq_mul _).2 e₂]
  ring

section Wit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] {Y : Model Xo c β} {b : O →+* ℂ}
  {a : ArcIn D l β ℂ b} {χ : Sp ℂ⟦X⟧ ⟶ Y.X}

theorem tf_hom_eq_id : (Out.TF (R := ℂ) ℂ).hom = 𝟙 (Sp ℂ) :=
  ((spMap_comp (algebraMap ℂ (FractionRing ℂ)) (algebraMap (FractionRing ℂ) ℂ)).symm.trans
    (congrArg spMap (IsScalarTower.algebraMap_eq ℂ (FractionRing ℂ) ℂ).symm)).trans (Spec.map_id _)

theorem exists_gtPt_const (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ)
    (g₀ : Out.GtPtF a.D₀ ℂ) : ∃ g : Out.GtPt W.P.D.toPre (Over.mk (spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧))),
      ∀ x, GenRelR (A := ℂ⟦X⟧) W.w (g.s (W.e x)) (LB.pullGen _ _ _ (g₀.s x) (spMap (PowerSeries.C (R := ℂ)))) := by
  obtain ⟨gp, hw, -, -, hc, -⟩ := W.spec
  exact exists_gtPt_genRelR_field globalFns_holds gp hw W.e.symm.toAddEquiv.toAddMonoidHom W.e W.e.symm_apply_apply
    (fun y => by have := hc (W.e.symm y); rwa [LinearEquiv.apply_symm_apply] at this)
    (spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) (spMap (PowerSeries.C (R := ℂ)))
    (by
      have e : spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) = 𝟙 _ := Spec.map_id _
      rw [tf_hom_eq_id, e, Category.id_comp]
      exact Category.comp_id _) g₀

theorem exists_constPoint (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ)
    {n : ℕ} (u : HolUnif a.D₀.P.A a.D₀.P.L n) (g₀ : Out.GtPtF a.D₀ ℂ) (z : Fin n → ℂ)
    (hz : (show Sp ℂ ⟶ _ from g₀.b.left) = (u.ex z).left) :
    ∃ (g : Out.GtPt W.P.D.toPre (Over.mk (spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧))))
      (x : Over.mk (spMap (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) ⟶ W.t.G) (τ : W.P.U.LG.L.ι → ℂ⟦X⟧),
      (∀ y, GenRelR (A := ℂ⟦X⟧) W.w (g.s (W.e y)) (LB.pullGen _ _ _ (g₀.s y) (spMap (PowerSeries.C (R := ℂ))))) ∧
      FormalPoint.IsPointOf W.P.U.toUnifPre g x ∧
      FormalValue.IsFormalPt W.P.U.toUnifPre
        ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) g x.left ∧
      ∀ (jL : W.P.U.LG.L.ι) (jM : W.P.D.toPre.P.L.ι) (j₀ : a.D₀.P.L.ι), ⊤ ≤ x.left ⁻¹ᵁ W.P.U.LG.L.U jL →
        ⊤ ≤ g.b.left ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) →
        valR (A := ℂ⟦X⟧) g.b.left _ (W.w.s (fun _ => j₀, jM)).val * τ jL =
          (FormalValue.tau W.P.U.toUnifPre ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧))
            x.left jL jM).val * PowerSeries.C (u.fr j₀ z) := by
  haveI : IsAdicComplete ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) ℂ⟦X⟧ := by
    rw [Algebra.algebraMap_self, Ideal.map_id]; infer_instance
  obtain ⟨g, hg⟩ := exists_gtPt_const W g₀
  obtain ⟨x, hx, -⟩ := FormalPoint.existsUnique_isPointOf W.P.U.toUnifPre (φ := algebraMap ℂ⟦X⟧ ℂ⟦X⟧) g
  have hf : FormalValue.IsFormalPt W.P.U.toUnifPre
      ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) g x.left :=
    FormalValue.isFormalPt_of_forall (Over.w x) fun e xe h => ⟨h, hx e _ _ xe h⟩
  let p : Sp ℂ⟦X⟧ ⟶ W.P.D.toPre.P.A.left := g.b.left
  have hp : p ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (u.ex z).left := by
    rw [← hz]; exact (hg 0).1 2
  obtain ⟨k, hk⟩ := exists_chart W.P.D.toPre.P.isLB (p (cpt _))
  obtain ⟨i, hi⟩ := exists_chart a.D₀.P.isLB (W.φ (p (cpt _)))
  have hki : ⊤ ≤ p ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => i, k) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 hi, hk⟩
  obtain ⟨ω, hω⟩ := FormalValue.isUnit_valR p _ hki (W.w.s (fun _ => i, k))
  refine ⟨g, x, fun jL => (ω⁻¹).val * ((FormalValue.tau W.P.U.toUnifPre
    ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) x.left jL k).val * PowerSeries.C (u.fr i z)),
    hg, hx, hf, fun jL jM j₀ hL hM => ?_⟩
  have m := (top_le_iff_cpt p _).1 hM
  have hM' : ⊤ ≤ p ⁻¹ᵁ W.P.D.toPre.P.L.U jM := (top_le_iff_cpt _ _).2 m.2
  have hk' : ⊤ ≤ p ⁻¹ᵁ W.P.D.toPre.P.L.U k := (top_le_iff_cpt _ _).2 hk
  have e₁ := FormalValue.tau_trans hf hL hL hM' hk'
  rw [valR_g_self W.P.U.LG.isLB _ hL, _root_.one_mul] at e₁
  have e₂ := valR_iso_trans W.spec.2.1 p hM hki
  have h₀ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (a.D₀.P.L.U j₀ ⊓ a.D₀.P.L.U i) := by
    have : (p ≫ W.φ) (cpt _) ∈ a.D₀.P.L.U j₀ ⊓ a.D₀.P.L.U i := ⟨mem_pull.1 m.1, hi⟩
    rw [hp] at this
    intro y _
    have e : y = spMap (PowerSeries.C (R := ℂ)) (cpt _) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [e]; exact this
  have e₃ : PowerSeries.C (u.fr j₀ z) = valR (p ≫ W.φ) _ (a.D₀.P.L.g j₀ i).val * PowerSeries.C (u.fr i z) := by
    rw [hp, FormalValue.valR_spMap _ _ _ h₀, u.fr_compat j₀ i z h₀, map_mul]
    rfl
  rw [← hω] at e₂
  exact unit_rearrange e₁ e₂ e₃

end Wit

end GlobalTheory.ConstPoint
