import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullPt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.LinearRestriction.ResPullUVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.RedVal

theorem commGroup_fourFactor_exponents_cancel_pow {M : Type} [CommGroup M] (a b c d : M) (k : ℕ) :
    a ^ ((k:ℤ)-1) * b ^ (1:ℤ) * c ^ (-1:ℤ) * d ^ (1:ℤ) * (b ^ (-1:ℤ) * c ^ (1:ℤ) * a ^ (1:ℤ) * d ^ (-1:ℤ)) = a ^ k := by
  rw [zpow_sub_one]; simp only [zpow_neg, zpow_one, zpow_natCast]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem gs_pow' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs f y U (a ^ n) = gs f y U a ^ n := by
  simp only [gs_eq f y U h, map_pow]

theorem gs_sum' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {Ix : Type} (s : Finset Ix)
    (a : Ix → Γ(X, U)) : gs f y U (∑ i ∈ s, a i) = ∑ i ∈ s, gs f y U (a i) := by
  simp only [gs_eq f y U h, map_sum]

theorem sval_zero_of_van {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') {k : ℕ} (a : D'.X) (b : D.SecB k (hD.xe a))
    (b' : D'.SecB k a) (hb : PullB hD a b b') (I : Ideal R) (e : ℕ) (hv : VanMod I b e) {Z : Scheme.{0}}
    (r : Z ⟶ D'.P.A.left) (h' : Z ⟶ pullback D.P.A.hom (thick R I e))
    (hh : h' ≫ pullback.fst D.P.A.hom (thick R I e) = r ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))
    (z : Z) {J₁ : (Z ⟶ D'.P.A.left) → D'.P.L.ι} (hJ₁ : Good D'.P.L z J₁) : sval b' r z J₁ = 0 := by
  obtain ⟨J', hJ'⟩ := GlobalTheory.TorusCoord.exists_good' D.P.isLB z
  have E := hb Z r z (fun κ => J' ((r ≫ D'.famφB a κ) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
    (fun κ => J₁ (r ≫ D'.famφB a κ)) (fun κ => hJ' _) (fun κ => hJ₁ _)
  have h0 : gs (r ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) z
      (LB.wchart D.P.L (D.famφB (hD.xe a))
        (fun κ => J' ((r ≫ D'.famφB a κ) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))))
      (b.f (fun κ => J' ((r ≫ D'.famφB a κ) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) = 0 := by
    rw [← hh]
    by_cases hm : (h' ≫ pullback.fst D.P.A.hom (thick R I e)) z ∈ LB.wchart D.P.L (D.famφB (hD.xe a))
        (fun κ => J' ((r ≫ D'.famφB a κ) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
    · exact (gs_pull h' _ z _ hm _).symm.trans ((congrArg (gs h' z _) (hv _)).trans (gs_zero' _ _ _))
    · unfold gs
      exact dif_neg hm
  rw [h0] at E
  exact (Units.mul_right_eq_zero _).1 E.symm

theorem expand_eval {W : Type} [CommRing W] [IsDomain W] {I : Ideal W} {D : DegData W I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing W)))} {G : Over (Spec (CommRingCat.of W))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) {k : ℕ} (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α)
    (hX : U.ExpandsAt 0 k σ f) {Z : Scheme.{0}} (g : Z ⟶ (thickObj W I 0 G).left) (z : Z)
    {J₁ : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι} {J₂ : (Z ⟶ G.left) → U.LG.L.ι}
    (hJ₁ : Good D.toPre.P.L z J₁) (hJ₂ : Good U.LG.L z J₂) (x : D.toPre.X)
    (hv : ∀ a, a ≠ x → sval (f a) (g ≫ (U.gt 0).pG.left) z J₁ = 0) :
    (gm g z _ ((U.w 0).s (fun _ => J₁ (g ≫ (U.gt 0).pG.left),
        fun _ => J₂ ((g ≫ (fstG I 0 G).left) ≫ 𝟙 G.left)))).val ^ k *
      sval σ (g ≫ (fstG I 0 G).left) z J₂ =
    sval (f x) (g ≫ (U.gt 0).pG.left) z J₁ * (val ((U.gt 0).t x) g z J₁).val := by
  obtain ⟨S, hS0, hS⟩ := hX
  let p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι) :=
    (fun _ => J₁ (g ≫ (U.gt 0).pG.left), fun _ => J₂ ((g ≫ (fstG I 0 G).left) ≫ 𝟙 G.left))
  let j₁ : Fin 1 → U.LG.L.ι := fun _ => J₂ ((g ≫ (fstG I 0 G).left) ≫ 𝟙 G.left)
  let jf : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun a κ => J₁ ((g ≫ (U.gt 0).pG.left) ≫ D.toPre.famφB a κ)
  let jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun a κ => J₁ (g ≫ D.toPre.Oφ (U.gt 0).pG a κ)
  have hcoh : CohAll D.toPre.P.L
      (Sum.elim (fun _ : PUnit.{1} => (U.gt 0).pG.left)
        (Sum.elim (fun a : S × Fin 4 => (U.gt 0).pG.left ≫ D.toPre.famφB a.1.1 a.2)
          (fun a : S × Fin 4 => D.toPre.Oφ (U.gt 0).pG a.1.1 a.2)))
      (Sum.elim (fun _ => p.1 PUnit.unit)
        (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) := by
    have key : ∀ i, (Sum.elim (fun _ => p.1 PUnit.unit)
        (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) i =
        J₁ (g ≫ (Sum.elim (fun _ : PUnit.{1} => (U.gt 0).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt 0).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt 0).pG a.1.1 a.2))) i) := by
      rintro (_ | (_ | _))
      · rfl
      · simp only [Sum.elim_inl, Sum.elim_inr, jf, Category.assoc]
      · rfl
    intro a b e
    rw [key a, key b, e]
  have E := hS p j₁ jf jt rfl hcoh
  have hA : g z ∈ (LB.div (D.toPre.P.L.pull (U.gt 0).pG.left) (U.LG.L.pull (fstG I 0 G).left)).U p :=
    ⟨mem_pull.2 (hJ₁ (g ≫ (U.gt 0).pG.left)), mem_pull.2 (hJ₂ ((g ≫ (fstG I 0 G).left) ≫ 𝟙 G.left))⟩
  have hB : g z ∈ (fstG I 0 G).left ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁ :=
    hJ₂.mem (fun _ : Fin 1 => 𝟙 G.left) (g ≫ (fstG I 0 G).left)
  have hC : ∀ a, g z ∈ (U.gt 0).pG.left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB a) (jf a) := fun a =>
    hJ₁.mem (D.toPre.famφB a) (g ≫ (U.gt 0).pG.left)
  have hD' : ∀ a, g z ∈ LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt 0).pG a) (jt a) := fun a =>
    hJ₁.mem (D.toPre.Oφ (U.gt 0).pG a) g
  have hm : g z ∈ U.expW 0 p j₁ S jf jt := by
    refine ⟨⟨hA, hB⟩, ?_⟩
    exact Finset.inf_induction (p := fun V : (thickObj W I 0 G).left.Opens => g z ∈ V) trivial
      (fun _ h₁ _ h₂ => ⟨h₁, h₂⟩) (fun a _ => ⟨hC a, hD' a⟩)
  have E' := congrArg (gs g z (U.expW 0 p j₁ S jf jt)) E
  rw [gs_mul g z _ hm, gs_pow' g z _ hm, gs_unit g z _ hm, gm_res g z _ hm, gs_res g z _ hm, gs_sum' g z _ hm] at E'
  erw [gs_pull g (fstG I 0 G).left z _ hB] at E'
  refine E'.trans ?_
  have hterm : ∀ a : S, gs g z (U.expW 0 p j₁ S jf jt)
      (((thickObj W I 0 G).left.presheaf.map (homOfLE (U.expW_le_f 0 p j₁ jf jt a.2)).op).hom
        (((U.gt 0).pG.left.app _).hom ((f a.1).f (jf a.1))) *
        (res (U.expWeight_le_chart_weight 0 p j₁ jf jt a.2) (((U.gt 0).t a.1).s (jt a.1))).val) =
      sval (f a.1) (g ≫ (U.gt 0).pG.left) z J₁ * (val ((U.gt 0).t a.1) g z J₁).val := fun a => by
    rw [gs_mul g z _ hm, gs_res g z _ hm, gs_unit g z _ hm]
    erw [gm_res g z (U.expWeight_le_chart_weight 0 p j₁ jf jt a.2) hm, gs_pull g (U.gt 0).pG.left z _ (hC a.1)]
    rfl
  rw [Finset.sum_congr rfl (fun a _ => hterm a)]
  rw [Finset.sum_attach S (fun a => sval (f a) (g ≫ (U.gt 0).pG.left) z J₁ * (val ((U.gt 0).t a) g z J₁).val)]
  refine Finset.sum_eq_single x (fun b _ hb => by rw [hv b hb, zero_mul]) (fun hx => ?_)
  have h0 : sval (f x) (g ≫ (U.gt 0).pG.left) z J₁ = 0 :=
    (gs_pull g (U.gt 0).pG.left z _ (hC x) _).symm.trans ((congrArg (gs g z _) (hS0 x hx _)).trans (gs_zero' _ _ _))
  rw [h0, zero_mul]

theorem closedFibre_val : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (Y : Ext D.toPre) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (Z : Scheme.{0}) (p' : Z ⟶ T.G.left) (y : Z ⟶ Y.H.left) (g : Z ⟶ (thickObj W (maximalIdeal W) 0 T.G).left) (ξ' : GtPt T.D'.toPre (Over.mk (g ≫ (thickObj W (maximalIdeal W) 0 T.G).hom ≫ thick W (maximalIdeal W) 0))), g ≫ (fstG (maximalIdeal W) 0 T.G).left = p' → GlobalTheory.TorusCoord.IsPointOf (T.U.gt 0) g ξ' → IsPullPt T.hD (𝟙 Z) (Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)) ξ' → ∀ (k : ℕ) (u : Wˣ) (z : Z) J J', Good C.P.L.L z J → Good D.toPre.P.L z J' → ∃ c : (Z.presheaf.stalk z)ˣ, ∀ (α : D.toPre.X) (b : D.toPre.SecB k α) (τ : SecK D.toPre.P.L Y.q.left k) (F : IntFam (maximalIdeal R) D.toPre k) (σ : SecK C.P.L.L T.β k), IsTermOf Y b τ → F.Lead α b → T.ExpBy u σ F → sval σ p' z J = c.val * sval τ y z J' := by
  intro R _ _ _ _ D C Y W _ _ _ T Z p' y g ξ' hg hpt hpull k u z J J' hJ hJ'
  subst hg
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.TorusCoord.exists_good' T.D'.toPre.P.isLB z
  obtain ⟨J₂, hJ₂⟩ := GlobalTheory.TorusCoord.exists_good' T.U.LG.isLB z
  set Fm := T.hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf T.φ) with hFm
  set r := g ≫ (T.U.gt 0).pG.left with hr
  set p' := g ≫ (fstG (maximalIdeal W) 0 T.G).left with hp'
  let Gw : (Z ⟶ T.D'.toPre.P.A.left) → (Z.presheaf.stalk z)ˣ := fun f => gw T.hD.w f z (J' (f ≫ Fm)) (J₁ f)
  let W0 := gm g z _ ((T.U.w 0).s (fun _ => J₁ (g ≫ (T.U.gt 0).pG.left), fun _ => J₂ (p' ≫ 𝟙 T.G.left)))
  let uG : Γ(T.G.left, ⊤)ˣ := Units.map
    (T.G.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom).toMonoidHom u
  refine ⟨gm p' z ⊤ uG * gw T.ℓ p' z (J (p' ≫ T.β)) (J₂ p') ^ k * (W0 ^ k)⁻¹ * (Gw r ^ k)⁻¹, ?_⟩
  intro α b τ F σ hτ hL hE
  obtain ⟨x, rfl⟩ := T.hD.xe.surjective α
  obtain ⟨σ', f', hC, hP, hX⟩ := hE

  have hb' : ξ'.b.left = r := hpt.1
  have hq : (Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)).b.left = y ≫ Y.q.left := by
    have h := (Y.rep.1 (Over.mk (y ≫ Y.H.hom)) Y.H (Over.homMk y rfl) (𝟙 _)).1
    rw [Category.comp_id] at h
    exact h
  have hrF : r ≫ Fm = y ≫ Y.q.left := by
    have h := hpull.1
    rw [hb'] at h
    exact h.trans ((Category.id_comp _).trans hq)
  haveI := T.loc
  have hmm : maximalIdeal R ^ (0 + 1) ≤ (maximalIdeal W ^ (0 + 1)).comap T.φ := by
    simp only [zero_add, pow_one]
    intro a ha
    exact (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit T.φ a hu)
  let qm : R ⧸ maximalIdeal R ^ (0 + 1) →+* W ⧸ maximalIdeal W ^ (0 + 1) := Ideal.quotientMap _ T.φ hmm
  have hsq : thick W (maximalIdeal W) 0 ≫ specOf T.φ =
      Spec.map (CommRingCat.ofHom qm) ≫ thick R (maximalIdeal R) 0 := by
    simp only [thick, specOf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have hcond : (r ≫ Fm) ≫ D.toPre.P.A.hom = (g ≫ (thickObj W (maximalIdeal W) 0 T.G).hom ≫
      Spec.map (CommRingCat.ofHom qm)) ≫ thick R (maximalIdeal R) 0 := by
    have e1 : Fm ≫ D.toPre.P.A.hom = T.D'.toPre.P.A.hom ≫ specOf T.φ := by
      rw [hFm, Category.assoc, pullback.condition, ← Category.assoc]
      congr 1
      exact Over.w T.hD.e.hom
    have e2 : r ≫ T.D'.toPre.P.A.hom =
        g ≫ (thickObj W (maximalIdeal W) 0 T.G).hom ≫ thick W (maximalIdeal W) 0 := by
      rw [hr, Category.assoc, Over.w (T.U.gt 0).pG]; rfl
    rw [Category.assoc, e1, ← Category.assoc, e2, Category.assoc, Category.assoc, hsq, Category.assoc,
      Category.assoc]
  let h' := pullback.lift (r ≫ Fm) _ hcond
  have hh : h' ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0) =
      r ≫ T.hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf T.φ) := pullback.lift_fst _ _ _
  have hvan : ∀ a, a ≠ x → sval (f' a) r z J₁ = 0 := fun a ha =>
    sval_zero_of_van T.hD a (F.f (T.hD.xe a)) (f' a) (hP a) (maximalIdeal R) 0
      (hL.2 _ (fun e => ha (T.hD.xe.injective e))) r h' hh z hJ₁
  have E1 := expand_eval T.U.toUnifPre σ' f' (hX 0) g z hJ₁ hJ₂ x hvan
  have E2 := hC Z p' z J J₂ hJ hJ₂
  have E3 := hτ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl) z J' hJ'
  have E4 := hP x Z r z (fun κ => J' ((r ≫ T.D'.toPre.famφB x κ) ≫ Fm)) (fun κ => J₁ (r ≫ T.D'.toPre.famφB x κ))
    (fun κ => hJ' _) (fun κ => hJ₁ _)
  rw [hL.1] at E4
  have E4' : sval b (y ≫ Y.q.left) z J' = (∏ κ, Gw (r ≫ T.D'.toPre.famφB x κ) ^ DegPre.famε k κ).val *
      sval (f' x) r z J₁ := by
    have hfam : ∀ κ, (r ≫ Fm) ≫ D.toPre.famφB (T.hD.xe x) κ = (r ≫ T.D'.toPre.famφB x κ) ≫ Fm := fun κ => by
      have e := GlobalTheory.ExpGTrans.famφB_pull T.hD x κ
      rw [← hFm] at e
      exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) e.symm).trans (Category.assoc _ _ _).symm)
    rw [sval_of b (y ≫ Y.q.left) z J' (fun κ => J' ((r ≫ T.D'.toPre.famφB x κ) ≫ Fm)) (fun κ => by
      rw [← hrF, hfam])]
    rw [← hrF]
    exact E4
  have E5 : val ((T.U.gt 0).t x) g z J₁ = val (ξ'.s x) (𝟙 Z) z J₁ := by
    rw [val_corr hJ₁ (hpt.2 x) (𝟙 Z), val_pull hJ₁, Category.id_comp]
  obtain ⟨hψ, hM⟩ := hpull.2 x
  have E6 := ReciprocityTheory.ChartRestriction.G.Out.OLinPf.ILin.val_maps _ T.hD.w _ DegPre.gtε _ (𝟙 Z) hψ _ _ hM (𝟙 Z) z J₁ J' hJ₁ hJ'
  have hO := (GlobalTheory.TorusCoord.comp_eq_of_left ξ'.b (𝟙 T.D'.toPre.P.A) (𝟙 Z) r (by rw [hb']; simp)).1 x
  have Gprod : (∏ κ, Gw (r ≫ T.D'.toPre.famφB x κ) ^ DegPre.famε k κ) *
      (∏ κ, Gw (𝟙 Z ≫ DegPre.gtφT _ _ ξ'.b x κ) ^ DegPre.gtε κ) = Gw r ^ k := by
    simp only [hO, Fin.prod_univ_four]
    simp only [DegPre.famφB, DegPre.Oφ, DegPre.famε, DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Over.id_left, Category.comp_id]
    exact commGroup_fourFactor_exponents_cancel_pow _ _ _ _ k
  have E3' : sval τ y z J' = sval b (y ≫ Y.q.left) z J' *
      (val ((Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)).s (T.hD.xe x)) (𝟙 Z) z J').val := E3
  have E6' : val ((Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)).s (T.hD.xe x)) (𝟙 Z) z J' =
      (∏ κ, Gw (𝟙 Z ≫ DegPre.gtφT _ _ ξ'.b x κ) ^ DegPre.gtε κ) * val ((T.U.gt 0).t x) g z J₁ := by
    rw [E5]
    exact (congrArg (fun q => val ((Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)).s (T.hD.xe x)) q z J')
      (Category.comp_id (𝟙 Z)).symm).trans E6
  have hu : gs p' z ⊤ (scal T.G.hom u.val) = (gm p' z ⊤ uG).val := gs_unit p' z ⊤ trivial uG
  have hW : ((W0 ^ k)⁻¹ : (Z.presheaf.stalk z)ˣ).val * W0.val ^ k = 1 := by
    rw [← Units.val_pow_eq_pow_val, Units.inv_mul]
  have hG : ((Gw r ^ k)⁻¹ : (Z.presheaf.stalk z)ˣ).val *
      ((∏ κ, Gw (r ≫ T.D'.toPre.famφB x κ) ^ DegPre.famε k κ).val *
        (∏ κ, Gw (𝟙 Z ≫ DegPre.gtφT _ _ ξ'.b x κ) ^ DegPre.gtε κ).val) = 1 := by
    rw [← Units.val_mul, Gprod, Units.inv_mul]
  rw [E2, hu, E3', E4', E6']
  simp only [Units.val_mul]
  linear_combination (-((gm p' z ⊤ uG).val * (gw T.ℓ p' z (J (p' ≫ T.β)) (J₂ p') ^ k).val *
      ((W0 ^ k)⁻¹ : (Z.presheaf.stalk z)ˣ).val * sval (f' x) r z J₁ * (val ((T.U.gt 0).t x) g z J₁).val)) * hG -
    ((gm p' z ⊤ uG).val * (gw T.ℓ p' z (J (p' ≫ T.β)) (J₂ p') ^ k).val * sval σ' p' z J₂) * hW +
    ((gm p' z ⊤ uG).val * (gw T.ℓ p' z (J (p' ≫ T.β)) (J₂ p') ^ k).val *
      ((W0 ^ k)⁻¹ : (Z.presheaf.stalk z)ˣ).val) * E1

end GlobalTheory.Mum.RedVal
