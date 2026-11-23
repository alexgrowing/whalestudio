import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEndomorphismActionUniformizationData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two

open CoordCompare TorusCoord in

theorem exists_level_ratio {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegPre R} {e : ℕ}
    {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂) (a : thickObj R I e G₁ ⟶ thickObj R I e G₂) [IsMonHom a]
    (b : D₁.P.A ⟶ D₂.P.A) (h : D₂.X → D₁.X)
    (t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.X)
    (ht : TorusHomOf h t) (hi : g₁.i ≫ a = t ≫ g₂.i) (hq : a ≫ g₂.q = g₁.q ≫ (Over.pullback (thick R I e)).map b)
    (χ : D₂.X) :
    ∃ u : LB.Gen (LB.LinComb (JN D₁ D₂) (Y := (thickObj R I e D₁.P.A).left)
      (fun k => pullback.fst D₁.P.A.hom (thick R I e) ≫
        Sum.elim (fun k => D₁.Oφ (𝟙 _) (h χ) k ≫ coprod.inl) (fun k => D₂.Oφ b χ k ≫ coprod.inr) k)
      (Sum.elim Oε Oinvε)), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good (JN D₁ D₂) z J →
        val (g₂.t χ) (x ≫ a.left) z (rr J) = val (g₁.t (h χ)) x z (rl J) * val u (x ≫ g₁.q.left) z J := by
  have := g₁.q_flat
  have := g₁.q_surj
  have := g₁.q_affine
  have p₁ := isPart_inl D₁.P.L D₂.P.L
  have p₂ := isPart_inr D₁.P.L D₂.P.L
  have hp : (Over.map (thick R I e)).map a ≫ g₂.pG = g₁.pG ≫ b := by
    refine Over.OverMorphism.ext ?_
    have h1 : a.left ≫ g₂.q.left = g₁.q.left ≫ ((Over.pullback (thick R I e)).map b).left :=
      congrArg (fun q => q.left) hq
    have h2 : ((Over.pullback (thick R I e)).map b).left ≫ pullback.fst D₂.P.A.hom (thick R I e) =
        pullback.fst D₁.P.A.hom (thick R I e) ≫ b.left := pullback.lift_fst _ _ _
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm)))
  have e₁ : ∀ k, a.left ≫ D₂.Oφ g₂.pG χ k =
      g₁.q.left ≫ pullback.fst D₁.P.A.hom (thick R I e) ≫ D₂.Oφ b χ k := fun k =>
    (WeightPf.Oφ_comp ((Over.map (thick R I e)).map a) g₂.pG χ k).trans
      ((congrArg (D₂.Oφ · χ k) hp).trans
        ((WeightPf.Oφ_comp g₁.pG b χ k).symm.trans (Category.assoc _ _ _)))
  have e₂ : ∀ k, D₁.Oφ g₁.pG (h χ) k =
      g₁.q.left ≫ pullback.fst D₁.P.A.hom (thick R I e) ≫ D₁.Oφ (𝟙 _) (h χ) k := fun k =>
    (congrArg (D₁.Oφ · (h χ) k) (Category.comp_id g₁.pG).symm).trans
      ((WeightPf.Oφ_comp g₁.pG (𝟙 _) (h χ) k).symm.trans (Category.assoc _ _ _))
  obtain ⟨u, hu, hu'⟩ := exists_gen (jn_isLB D₁ D₂)
    (φ' := fun k => g₁.q.left ≫ pullback.fst D₁.P.A.hom (thick R I e) ≫
      Sum.elim (fun k => D₁.Oφ (𝟙 _) (h χ) k ≫ coprod.inl) (fun k => D₂.Oφ b χ k ≫ coprod.inr) k)
    (ε' := Sum.elim Oε Oinvε)
    (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_sum_type _).symm)
      refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) (Finset.prod_congr rfl fun k _ => ?_)
      · refine congrArg₂ (· ^ ·) (congrArg f ?_) (show -Oinvε k = Oε k by fin_cases k <;> rfl)
        exact (congrArg (· ≫ coprod.inl) (e₂ k)).trans
          ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)))
      · refine congrArg (fun ψ => f ψ ^ Oinvε k) ?_
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ coprod.inr) (e₁ k)).trans
          ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)))))
    (LB.mulGen (JN D₁ D₂) _ _ _ _ (LB.invGen (JN D₁ D₂) _ _ (p₁.gen (g₁.t (h χ))))
      (LB.pullGen (JN D₁ D₂) _ _ (p₂.gen (g₂.t χ)) a.left))
    (mulGen_isGen _ _ _ _ _ _ _ (invGen_isGen _ _ _ _ (p₁.gen_isGen (g₁.t_gen _)))
      (pullGen_isGen _ _ _ _ (p₂.gen_isGen (g₂.t_gen χ)) _))
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good (JN D₁ D₂) z J →
      val u r z J = (val (g₁.t (h χ)) r z (rl J))⁻¹ * val (g₂.t χ) (r ≫ a.left) z (rr J) := fun Z r z J hJ =>
    (hu' Z r z J hJ).trans ((Geo.Tor.val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((Geo.Tor.val_inv _ _).trans (congrArg (·⁻¹) (p₁.val_gen _ _ z hJ)))
        ((Geo.Tor.val_pull hJ _ _ _).trans (p₂.val_gen _ _ z hJ))))
  obtain ⟨v, hv₁, hv₂⟩ := exists_gen_of_val_eq (jn_isLB D₁ D₂) _ _ g₁.q.left u hu (fun Z r r' z J hJ hr => by
    rw [hv Z r z J hJ, hv Z r' z J hJ]
    have hw : r ≫ (thickObj R I e G₁).hom = r' ≫ (thickObj R I e G₁).hom := by
      rw [← Over.w g₁.q, reassoc_of% hr]
    let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (r' ≫ (thickObj R I e G₁).hom)
    let c : Z' ⟶ thickObj R I e G₁ := Over.homMk r hw
    let c' : Z' ⟶ thickObj R I e G₁ := Over.homMk r' rfl
    obtain ⟨τ, hτ⟩ := exists_torus g₁ c c' (Over.OverMorphism.ext hr)
    have hτa : c ≫ a = ((τ ≫ t) ≫ g₂.i) * (c' ≫ a) := by
      rw [hτ, MonObj.mul_comp, Category.assoc, hi, Category.assoc]
    have v₁ := val_torus g₁ (h χ) (Z := Z') (p₁.good hJ) τ c'
    have v₂ := val_torus g₂ χ (Z := Z') (p₂.good hJ) (τ ≫ t) (c' ≫ a)
    rw [← hτ] at v₁
    rw [← hτa] at v₂
    have v₀ : gm (τ ≫ t).left z ⊤ (charUnit _ D₂.X χ) = gm τ.left z ⊤ (charUnit _ D₁.X (h χ)) :=
      (gm_pull τ.left t.left z ⊤ trivial _).symm.trans
        ((gm_res τ.left z (V := ⊤) (U := t.left ⁻¹ᵁ ⊤) (fun _ _ => trivial) trivial _).symm.trans (congrArg _ (ht χ)))
    refine (congrArg₂ (fun s s' => s⁻¹ * s') v₁ v₂).trans ?_
    rw [v₀, mul_inv, _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul]
    rfl)
  refine ⟨v, hv₁, fun Z x z J hJ => ?_⟩
  rw [hv₂ Z x z J hJ, hv Z x z J hJ, mul_inv_cancel_left]

theorem prod_unit_hom {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {B : Over (Sp R)} [GrpObj B] (p : B ⟶ D.P.A)
    [IsMonHom p] (χ : D.X) {U : Type} [CommGroup U] (h : (Spec (CommRingCat.of R) ⟶ D.P.A.left) → U) :
    ∏ k, h (eSec B ≫ D.Oφ p χ k) ^ Oinvε k = 1 := by
  have e0 : ∀ k, eSec B ≫ D.Oφ p χ k = eSec D.P.A ≫ D.Oφ (𝟙 _) χ k := fun k =>
    (WeightPf.Oφ_comp η[B] p χ k).trans ((congrArg (D.Oφ · χ k)
      ((IsMonHom.one_hom p).trans (Category.comp_id _).symm)).trans (WeightPf.Oφ_comp η[D.P.A] (𝟙 _) χ k).symm)
  simp only [e0]
  exact (EndData.prod_unit D (𝟙 _) χ h).2

open EndData in

theorem coord_of_lin : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Lin U₁ U₂ a b h → Coord U₁ U₂ a b h := by
  intro R _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a b h ⟨ha, hb, hq, hh⟩ χ
  have hC := hR.2.2.2
  have hB := jn_isLB D₁.toPre D₂.toPre
  have p₁ := isPart_inl D₁.toPre.P.L D₂.toPre.P.L
  have p₂ := isPart_inr D₁.toPre.P.L D₂.toPre.P.L
  choose t ht hi using hh
  choose v hv vv using fun e => exists_level_ratio (U₁.gt e) (U₂.gt e) ((Over.pullback (thick R I e)).map a) b h (t e)
    (ht e) (hi e) (hq e) χ
  have down₁ : ∀ χ e (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good D₁.toPre.P.L z J →
      val ((U₁.gt (e + 1)).t χ) (r ≫ thickMap R I e G₁) z J = val ((U₁.gt e).t χ) r z J :=
    fun χ e Z r z J hJ => (val_pull hJ _ _ _).symm.trans (val_corr hJ (U₁.gt_t e χ) r)
  have down₂ : ∀ χ e (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₂).left) (z : Z) (J), Good D₂.toPre.P.L z J →
      val ((U₂.gt (e + 1)).t χ) (r ≫ thickMap R I e G₂) z J = val ((U₂.gt e).t χ) r z J :=
    fun χ e Z r z J hJ => (val_pull hJ _ _ _).symm.trans (val_corr hJ (U₂.gt_t e χ) r)
  obtain ⟨u, hu, uv⟩ := T.exists_generator_of_compatible_thickening_generators R I hC D₁.toPre.P.A D₁.toPre.P.isAb.smooth
    (AbProj.isProjBy_of_isPullback D₁.toPre.P (IsPullback.id_horiz _)) _ (JN D₁.toPre D₂.toPre) _ _ _ _ hB
    (fun _ _ => rfl) v hv (fun e z J hJ => by
      have := (U₁.gt e).q_flat
      have := (U₁.gt e).q_surj
      refine val_eq_of_flat hB _ _ _ _ (fun k => ?_) (U₁.gt e).q.left (fun x J hJ => ?_) z J hJ
      · rw [← Category.assoc, trans_fst, Category.id_comp]
      · have k₁ := vv (e + 1) _ (𝟙 _ ≫ thickMap R I e G₁) x J hJ
        have k₀ := vv e _ (𝟙 _) x J hJ
        rw [down₁ _ _ _ _ _ _ (p₁.good hJ), Category.assoc, trans_map, ← Category.assoc,
          down₂ _ _ _ _ _ _ (p₂.good hJ), k₀, Category.id_comp, Category.id_comp, UnifCompare.trans_comp_q] at k₁
        rw [Category.comp_id]
        exact (mul_left_cancel k₁).symm)
  refine ⟨u, ⟨hu, fun Z r z J hJ => ?_⟩, fun e Z x z J hJ => ?_⟩
  · refine (val_pull hJ _ _ _).symm.trans ((val_corr hJ (t' := LB.oneGen _)
      (corr_of_val hB fun y J hJ => Eq.trans ?_ (val_one _).symm) r).trans (val_one _))
    refine val_eq_one I hB (fun V _ k => ?_) _ (pullGen_isGen _ _ _ _ hu _) (fun e z J hJ => ?_) y J hJ
    · refine (Fintype.prod_sum_type _).trans ((congrArg₂ (· * ·)
        (Eq.trans ?_ (prod_unit D₁.toPre (𝟙 _) (h χ) (fun ψ => k (ψ ≫ coprod.inl))).1)
        (Eq.trans ?_ (prod_unit_hom D₂.toPre b χ (fun ψ => k (ψ ≫ coprod.inr))))).trans
        ((_root_.mul_one _).trans (Fintype.prod_empty _).symm))
      · exact Finset.prod_congr rfl fun j _ => congrArg (fun ψ => k ψ ^ Oε j) (Category.assoc _ _ _).symm
      · exact Finset.prod_congr rfl fun j _ => congrArg (fun ψ => k ψ ^ Oinvε j) (Category.assoc _ _ _).symm
    · have := (U₁.gt e).q_hom
      have k := vv e _ (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G₁).left z J hJ
      rw [← Over.comp_left, ← Over.comp_left, MonObj.one_comp, MonObj.one_comp, TorusCoord.val_unit _ _ (p₂.good hJ),
        TorusCoord.val_unit _ _ (p₁.good hJ), _root_.one_mul, ← uv e _ _ z J hJ] at k
      have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e D₁.toPre.P.A) =
        η[thickObj R I e D₁.toPre.P.A] := by simp [Hom.one_def]
      rw [o] at k
      exact (val_pull hJ _ _ _).trans ((congrArg (fun p => val u p z J)
        (UnitValue.eSec_pullback_fst (thick R I e) D₁.toPre.P.A).symm).trans k.symm)
  · refine (vv e Z x z J hJ).trans (congrArg (_ * ·) ((uv e Z _ z J hJ).symm.trans ?_))
    exact congrArg (fun p => val u p z J) (Category.assoc _ _ _)

end GlobalTheory.Mum.Two
