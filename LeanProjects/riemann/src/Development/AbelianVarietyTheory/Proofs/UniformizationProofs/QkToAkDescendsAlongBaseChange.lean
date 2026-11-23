import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkBaseChange

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaDescent

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar GlobalTheory.ThetaBaseChange
  GlobalTheory.FamFieldPull

section Theta

variable {S S' W : Scheme.{0}} {g : S' ⟶ S} {t : W ⟶ S} {t' : W ⟶ S'}

theorem inv_cmp {A : Over S} {A' : Over S'} {Φ : A'.left ⟶ A.left}
    {ω : (Over.mk t ⊗ A).left ⟶ (Over.mk t' ⊗ A').left} {Ω : (Over.mk t' ⊗ A').left ⟶ (Over.mk t ⊗ A).left}
    (h₁ : ω ≫ (fst (Over.mk t') A').left = (fst (Over.mk t) A).left)
    (h₂ : ω ≫ (snd (Over.mk t') A').left ≫ Φ = (snd (Over.mk t) A).left)
    (H₁ : Ω ≫ (fst (Over.mk t) A).left = (fst (Over.mk t') A').left)
    (H₂ : Ω ≫ (snd (Over.mk t) A).left = (snd (Over.mk t') A').left ≫ Φ) : ω ≫ Ω = 𝟙 _ := by
  refine pullback.hom_ext (f := t) (g := A.hom) ?_ ?_
  · show (ω ≫ Ω) ≫ (fst (Over.mk t) A).left = 𝟙 _ ≫ (fst (Over.mk t) A).left
    rw [Category.assoc, H₁, h₁, Category.id_comp]
  · show (ω ≫ Ω) ≫ (snd (Over.mk t) A).left = 𝟙 _ ≫ (snd (Over.mk t) A).left
    rw [Category.assoc, H₂, h₂, Category.id_comp]

variable {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {Φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}

theorem pow_eq_one_of_pull (ht : t' ≫ g = t) (hp : IsGrpPullback A' A g Φ) {x : Over.mk t ⟶ A}
    {x' : Over.mk t' ⟶ A'} (hx : x'.left ≫ Φ = x.left) {k : ℕ} (h : x' ^ k = 1) : x ^ k = 1 := by
  subst ht
  have e : pushHom hp (Over.mk t') x' = x := Over.OverMorphism.ext hx
  have e₂ := congrArg (pushHom hp (Over.mk t')) h
  rw [map_pow, map_one, e] at e₂
  exact e₂

omit [GrpObj A] [GrpObj A'] in

theorem moved_val {v : LB.Iso L' (L.pull Φ)} {ω : (Over.mk t ⊗ A).left ⟶ (Over.mk t' ⊗ A').left}
    {Ω : (Over.mk t' ⊗ A').left ⟶ (Over.mk t ⊗ A).left} (hΩ : Ω ≫ ω = 𝟙 _)
    (H₂ : Ω ≫ (snd (Over.mk t) A).left = (snd (Over.mk t') A').left ≫ Φ) {k : ℤ}
    {s' : LB.Sec (LPow A' L' k (Over.mk t'))} {s : LB.Sec (LPow A L k (Over.mk t))} (m : Moved v ω s' s)
    {Z : Scheme.{0}} (r : Z ⟶ (Over.mk t' ⊗ A').left) (z : Z) {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    secVal s (r ≫ Ω) z J = (wGerm v z J J' (r ≫ (snd (Over.mk t') A').left) ^ k).val * secVal s' r z J' := by
  have e : (r ≫ Ω) ≫ ω = r := by rw [Category.assoc, hΩ, Category.comp_id]
  have e₂ : (r ≫ Ω) ≫ (snd (Over.mk t) A).left = (r ≫ (snd (Over.mk t') A').left) ≫ Φ := by
    rw [Category.assoc, H₂, Category.assoc]
  have c := m Z (r ≫ Ω) z _ _ (hJ ((r ≫ Ω) ≫ (snd (Over.mk t) A).left))
    (hJ' (((r ≫ Ω) ≫ ω) ≫ (snd (Over.mk t') A').left))
  rw [e] at c
  refine c.trans ?_
  rw [e₂]
  rfl

theorem exists_theta_pulled (hL : L.IsLB) (hL' : L'.IsLB) (ht : t' ≫ g = t) (hp : IsGrpPullback A' A g Φ)
    {v : LB.Iso L' (L.pull Φ)} (hv : PGen v) {ω : (Over.mk t ⊗ A).left ⟶ (Over.mk t' ⊗ A').left}
    {Ω : (Over.mk t' ⊗ A').left ⟶ (Over.mk t ⊗ A).left}
    (h₁ : ω ≫ (fst (Over.mk t') A').left = (fst (Over.mk t) A).left)
    (h₂ : ω ≫ (snd (Over.mk t') A').left ≫ Φ = (snd (Over.mk t) A).left)
    (H₁ : Ω ≫ (fst (Over.mk t) A).left = (fst (Over.mk t') A').left)
    (H₂ : Ω ≫ (snd (Over.mk t) A).left = (snd (Over.mk t') A').left ≫ Φ) (hΩ : Ω ≫ ω = 𝟙 _) {k : ℤ}
    (θ : ThetaGrp A L k (Over.mk t)) {x' : Over.mk t' ⟶ A'} (hx : x'.left ≫ Φ = θ.pt.left) :
    ∃ θ' : ThetaGrp A' L' k (Over.mk t'), θ'.pt = x' ∧ ∀ s' s₂' s s₂, Moved v ω s' s → Moved v ω s₂' s₂ →
      IsActOf A L k θ s s₂ → IsActOf A' L' k θ' s' s₂' := by
  have c₁ := translPt_cmp ht hp hx h₁ h₂
  have c₂ := translT_cmp ht hp hx h₁ h₂
  have hω := inv_cmp h₁ h₂ H₁ H₂
  have c₃ : (translPt A' x').left ≫ Φ = Ω ≫ (translPt A θ.pt).left := by
    rw [← c₁, ← Category.assoc Ω, hΩ, Category.id_comp]
  have c₄ : (translT A' x').left ≫ Ω = Ω ≫ (translT A θ.pt).left := by
    have e := congrArg (fun q => Ω ≫ q ≫ Ω) c₂
    simp only [Category.assoc, hω, Category.comp_id] at e
    rw [e, ← Category.assoc Ω, hΩ, Category.id_comp]
  obtain ⟨u, hu, hval⟩ := exists_genPull v ((isGen_iff v).2 hv) hL hL' (K := Fin 2)
    ![(snd (Over.mk t') A').left, (translPt A' x').left]
    ![(snd (Over.mk t) A).left, (translPt A θ.pt).left] ![k, -k] Ω
    (fun κ => by fin_cases κ; exacts [H₂.symm, c₃]) θ.φ θ.isGen
  refine ⟨⟨x', u, hu⟩, rfl, fun s' s₂' s s₂ m m₂ H => ActVal.isActOf hL' fun Z r z J' hJ' => ?_⟩
  choose J hJ using fun ψ : Z ⟶ A.left => exists_chart hL (ψ z)
  have hJ : Good L z J := hJ
  have a := actVal_of_isActOf H Z (r ≫ Ω) z J hJ
  have b := hval Z r z J J' hJ hJ'
  have c := moved_val hΩ H₂ m₂ r z hJ hJ'
  have d := moved_val hΩ H₂ m (r ≫ (translT A' x').left) z hJ hJ'
  rw [Category.assoc, c₄, ← Category.assoc, Category.assoc r (translT A' x').left, translT_snd_left] at d
  rw [Fin.prod_univ_two] at b
  have f := c.symm.trans (a.trans (congrArg₂ (· * ·) (congrArg Units.val b) d))
  refine (Units.mul_right_inj (wGerm v z J J' (r ≫ (snd (Over.mk t') A').left) ^ k)).1 (f.trans ?_)
  show (wGerm v z J J' (r ≫ (snd (Over.mk t') A').left) ^ k * wGerm v z J J' (r ≫ (translPt A' x').left) ^ (-k) *
    thetaVal ⟨x', u, hu⟩ r z J').val * _ = _
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, zpow_neg, mul_right_comm _ _⁻¹,
    inv_mul_cancel_right]

end Theta

section Gen

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {K : Type} [Fintype K]

theorem exists_pmaps_up {w : LB.Iso L' (L.pull Φ)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (hc : ∀ κ, φ' κ ≫ Φ = 𝟙 _ ≫ φ κ)
    (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧ PMaps w φ' φ ε a t (𝟙 _) := by
  obtain rfl : φ = fun k => φ' k ≫ Φ := funext fun k => ((hc k).trans (Category.id_comp _)).symm
  obtain ⟨t, ht, h⟩ := exists_up hw hL hL' a ha
  refine ⟨t, ht, fun Z r z p q hp hq => ?_⟩
  rw [Category.comp_id]
  exact h Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)

theorem sec_eq_of_pull (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull Φ)} {φ' : K → (Y' ⟶ X')}
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y} {n : Y ⟶ Y'} (hn : n ≫ h = 𝟙 _) (hc : ∀ κ, φ' κ ≫ Φ = h ≫ φ κ)
    {a : LB.Sec (LB.LinComb L' φ' ε)} {s s₂ : LB.Sec (LB.LinComb L φ ε)} (H : IsSecPull w φ' φ ε h a s)
    (H₂ : IsSecPull w φ' φ ε h a s₂) (j : K → L.ι) : s.f j = s₂.f j := by
  refine sec_ext_val hL (fun y J hJ => ?_) j
  choose J' hJ' using fun ψ : Y ⟶ X' => exists_chart hL' (ψ y)
  have hJ' : Good L' y J' := hJ'
  have e := (H.val hc n y hJ hJ').trans (H₂.val hc n y hJ hJ').symm
  rwa [hn] at e

end Gen

end GlobalTheory.ThetaDescent

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaBaseChange GlobalTheory.ThetaDescent in
set_option maxHeartbeats 1600000 in

theorem qkToAk_of_baseChange : GlobalFnsSt → SecBaseChangeSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ (φ : R →+* R') (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (U' : Unif I' D' A' G'), IsPullUnif φ hD bc U U' → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) = algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) → ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (x : TFK (R := R) F ⟶ A.A) (p' : QkPt D'.toPre F k) (x' : TFK (R := R') F ⟶ A'.A), p'.y = hD.xe.symm p.y → IsPullGtF φ hD F p.g p'.g → x'.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) → QkToAkU U'.toUnifPre F k p' x' → QkToAkU U.toUnifPre F k p x := by
  intro hG _ R R' _ _ _ _ I I' _ _ φ D A G _ _ U G' _ _ bc hbc A' D' hD U' hU F _ _ _ hF k hk p x p' x' hy hg hx H w hw
  obtain ⟨wL, hwL, -, -, hlev⟩ := (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU
  obtain ⟨w', hw'⟩ := U'.ext
  obtain ⟨hx1, H⟩ := H w' hw'
  obtain ⟨g, hg₁, hg₂⟩ := exists_fraction_map φ F hF
  have gA := grp_generic U.toUnifPre
  have gΨ : IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl
  have hΘF : (jFK (R := R') F ≫ jK R') ≫ specOf φ = jFK (R := R) F ≫ jK R := by
    rw [Category.assoc, ← hg₁, ← Category.assoc, hg₂]
  obtain ⟨Θ, hΘ₁, hΘ₂⟩ := exists_cmp hΘF (pull_grp hD).1.w
  have gA' := (grp_generic U'.toUnifPre).comp gΨ
  obtain ⟨Φ, hΦ₁, hΦ₂⟩ : ∃ Φ : A'.A.left ⟶ A.A.left, Φ ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R')) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) ∧
      Φ ≫ A.A.hom = A'.A.hom ≫ g :=
    ⟨gA.1.lift _ (A'.A.hom ≫ g) (by rw [gA'.1.w, Category.assoc, hg₁]), gA.1.lift_fst _ _ _, gA.1.lift_snd _ _ _⟩
  have gΦ : IsGrpPullback A'.A A.A g Φ := gA.cancel (gA'.congr hg₁.symm hΦ₁.symm) hΦ₂
  have hxΦ : x'.left ≫ Φ = x.left := gA.1.hom_ext (by
    rw [Category.assoc, hΦ₁, ← hx]; simp only [Category.assoc]) (by
    rw [Category.assoc, hΦ₂, ← Category.assoc, Over.w x', Over.w x]; exact hg₂)
  refine ⟨pow_eq_one_of_pull hg₂ gΦ hxΦ hx1, fun θ hθ => ?_⟩
  have n₁ : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
  have n₂ : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U'.gen.inv_hom_id, Over.id_left]
  have n₃ : U'.gen.hom.left ≫ U'.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U'.gen.hom_inv_id, Over.id_left]
  have hΦ₃ : (U'.gen.hom.left ≫ Φ) ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) := by
    rw [Category.assoc, hΦ₁, ← Category.assoc, ← Category.assoc U'.gen.hom.left, n₃]
    exact congrArg (· ≫ _) (Category.id_comp _)
  obtain ⟨v₂, hv₂, hsq⟩ := exists_side A.isLB A'.isLB U.LG.isLB U'.LG.isLB hw _ n₁ hw' hwL _ hΦ₃
  obtain ⟨v, hv, hvv⟩ := exists_unpull hv₂ _ n₂ (P := Φ) (by rw [← Category.assoc, n₂, Category.id_comp])
  obtain ⟨Ω, hΩ₁, hΩ₂⟩ := exists_cmp hg₂ hΦ₂
  obtain ⟨ω, hω₁, hω₂⟩ := exists_cmp_inv hg₂ gΦ.1
  have hΩω : Ω ≫ ω = 𝟙 _ := cmp_ext gΦ.1 (by rw [Category.assoc, hω₁, hΩ₁, Category.id_comp])
    (by rw [Category.assoc, hω₂, hΩ₂, Category.id_comp])
  let n : TFK (R := R) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n.left ≫ (U.toUnifPre.genF F).left = 𝟙 _ := congrArg (fun q => q.left) (show n ≫ U.toUnifPre.genF F = 𝟙 _ by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n])
  have hn₁ : n.left ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = (fst (TFK (R := R) F) A.A).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : n ≫ fst _ _ = _)
  have hn₂ : n.left ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
      (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left :=
    congrArg (fun q => q.left) (lift_snd _ _ : n ≫ snd _ _ = _)
  have hh₁ : (U'.toUnifPre.genF F).left ≫ (fst (TFK (R := R') F) A'.A).left =
      (fst (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : U'.toUnifPre.genF F ≫ fst _ _ = _)
  have hh₂ : (U'.toUnifPre.genF F).left ≫ (snd (TFK (R := R') F) A'.A).left =
      (snd (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left ≫ U'.gen.hom.left :=
    congrArg (fun q => q.left) (lift_snd _ _ : U'.toUnifPre.genF F ≫ snd _ _ = _)
  obtain ⟨Ξ, hΞ⟩ : ∃ Ξ : (UnifPre.GF (G := G') F).left ⟶ (UnifPre.GF (G := G) F).left,
      Ξ = (U'.toUnifPre.genF F).left ≫ Ω ≫ n.left := ⟨_, rfl⟩
  have x₁ : (Ξ ≫ (U.toUnifPre.genF F).left) ≫ ω = (U'.toUnifPre.genF F).left := by
    rw [hΞ, Category.assoc _ (Ω ≫ n.left), Category.assoc Ω, hn, Category.comp_id, Category.assoc, hΩω,
      Category.comp_id]
  have x₂ : Ξ ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
      (snd (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left ≫ (U'.gen.hom.left ≫ Φ) ≫ U.gen.inv.left := by
    rw [hΞ, Category.assoc, Category.assoc, hn₂, ← Category.assoc Ω]
    refine (congrArg (fun a => _ ≫ a ≫ _) hΩ₂).trans ?_
    rw [← Category.assoc, ← Category.assoc, hh₂]
    simp only [Category.assoc]
  have hΞ₁ : Ξ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
      (fst (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left := by
    rw [hΞ, Category.assoc, Category.assoc, hn₁]
    exact (congrArg (_ ≫ ·) hΩ₁).trans hh₁
  have hΞ₂ : Ξ ≫ UnifPre.gFK (G := G) F = UnifPre.gFK (G := G') F ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) := by
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) x₂).trans ?_)
    refine Eq.trans ?_ ((congrArg (_ ≫ ·) hΦ₃).trans (Category.assoc _ _ _).symm)
    simp only [Category.assoc]
  obtain ⟨θ', hθ', hact⟩ := exists_theta_pulled A.isLB A'.isLB hg₂ gΦ hv hω₁ hω₂ hΩ₁ hΩ₂ hΩω θ (x' := x')
    (by rw [hθ]; exact hxΦ)
  obtain ⟨ν', hν', Hν'⟩ := H θ' hθ'
  have hl : ∀ i, DegPre.lineφ D'.toPre F p'.g.b i ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) =
      𝟙 _ ≫ DegPre.lineφ D.toPre F p.g.b i := fun i => by
    obtain ⟨hψ, -⟩ := hg.2 0
    fin_cases i
    · exact hψ 3
    · exact hψ 2
  obtain ⟨ν, hν, pm⟩ := exists_pmaps_up ((isGen_iff hD.w).1 hD.w_gen) D.toPre.P.isLB D'.toPre.P.isLB hl ν' hν'
  refine ⟨ν, hν, fun t t₂ s s₂ E E₂ hA => ?_⟩
  have bij := expandsF_bijective U.toUnifPre F hG hk (U.expand k hk) hw
  have bij' := expandsF_bijective U'.toUnifPre F hG hk (U'.expand k hk) hw'
  choose pl hpl using exists_fam_field_pull hG R R' φ D.toPre D'.toPre hD F hF Θ hΘ₁ hΘ₂ k
  have hT := PhiPull.base_eq hF
  obtain ⟨Λ, hΛ₁, hΛ₂⟩ := exists_cmp_inv hΘF (pull_grp hD).1
  have hΛ := inv_cmp hΛ₁ hΛ₂ hΘ₁ hΘ₂
  have inj : ∀ b b₂, pl b = pl b₂ → b = b₂ := fun b b₂ e => fam_ext fun α j => by
    obtain ⟨α', rfl⟩ := hD.xe.surjective α
    have h₂ := hpl b₂ α'
    rw [← e] at h₂
    exact sec_eq_of_pull D.toPre.P.isLB D'.toPre.P.isLB hΛ (FamFieldPull.famφ_pr hD F hT hΘ₁ hΘ₂ α')
      (hpl b α') h₂ j
  have key : ∀ a b, U.toUnifPre.ExpandsF F k w a b → ∃ a', Moved v ω a' a ∧
      U'.toUnifPre.ExpandsF F k w' a' (pl b) := fun a₀ b₀ E₀ => by
    obtain ⟨a', E⟩ := (bij'.2 (pl b₀)).exists
    obtain ⟨a, ha⟩ := exists_moved A.isLB A'.isLB hω₂ n₂ hv₂ hvv a'
    obtain ⟨b, σ, h₁, h₂⟩ := (bij.1 a).exists
    have e : pl b = pl b₀ := by
      refine (bij'.1 a').unique ?_ E
      obtain ⟨σ', h₁', -⟩ := E
      exact ⟨σ', h₁', expandsG_transport R R' I I' φ D D' hD A A' G G' bc hbc U.toUnifPre U'.toUnifPre wL hwL hlev F hF
        Θ hΘ₁ hΘ₂ Ξ hΞ₁ hΞ₂ k σ σ' b (pl b)
        (moved_sec A.isLB A'.isLB n₃ n₁ hΦ₃ hsq hvv x₁ x₂ ha h₁ h₁') (hpl b) h₂⟩
    obtain rfl := inj _ _ e
    obtain rfl : a = a₀ := (bij.2 b).unique ⟨σ, h₁, h₂⟩ E₀
    exact ⟨a', ha, E⟩
  obtain ⟨t', m, e⟩ := key t s E
  obtain ⟨t₂', m₂, e₂⟩ := key t₂ s₂ E₂
  have P' := (phiRel_iff hG p' ν' hν' _ _).1 (Hν' t' t₂' _ _ e e₂ (hact t' t₂' t t₂ m m₂ hA))
  obtain ⟨s₃, P⟩ := exists_phi hG p ν hν D.tau_bimult s
  have P'' := PhiPull.phiVal_pull hD hT hΘ₁ hΘ₂ hG p p' hy hg ν ν' hl pm s s₃ _ _ (hpl s) (hpl s₃) P
  obtain rfl := inj _ _ (phi_unique p' ν' P'' P')
  exact (phiRel_iff hG p ν hν _ _).2 P

end GlobalTheory
