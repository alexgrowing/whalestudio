import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubicalSymmetryTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PulledComparisonEven
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNeZeroIffSvalGenericPointNeZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullbackSectionFamilyNeZeroIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPsiThetaExpansionPsiRelation

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section

namespace GlobalTheory.PsiBaseChange

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {φ : R →+* V} {D : DegPre R} {D' : DegPre V}
  {β : D'.P.A.left ⟶ D.P.A.left} {v : LB.Iso D'.P.L (D.P.L.pull β)} {xe : D'.X ≃+ D.X}

theorem secCmp_val {f : ∀ α, SecBT D (𝟙_ _) 1 α} {f' : ∀ α, SecBT D' (𝟙_ _) 1 α} (h : SecCmp D D' β v xe f f')
    (α : D'.X) {T : Over (Spec (CommRingCat.of V))} (y : T ⟶ D'.P.A) (r : T.left ⟶ (𝟙_ _ ⊗ D.P.A).left)
    (hr : r ≫ (snd _ D.P.A).left = y.left ≫ β) (z : T.left) {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J')
    (Ω : (T.left ⟶ D'.P.A.left) → (T.left.presheaf.stalk z)ˣ) (hΩ : ∀ q, Ω q = gw v q z (J (q ≫ β)) (J' q)) :
    sval (f (xe α)) r z J = (Ω (y * cT D' T α).left * (Ω (cT D' T α).left)⁻¹ * Ω (1 : T ⟶ D'.P.A).left).val *
      sval (f' α) (lift (toUnit T) y).left z J' := by
  have a : (lift (toUnit T) y).left ≫ (snd _ D'.P.A).left = y.left := congrArg (fun q => q.left) (lift_snd (toUnit T) y)
  refine (h α _ (lift (toUnit T) y).left r (by rw [hr, ← Category.assoc, a]) z J J' hJ hJ').trans ?_
  refine congrArg (fun u : (T.left.presheaf.stalk z)ˣ => u.val * sval (f' α) (lift (toUnit T) y).left z J') ?_
  simp only [← Category.assoc, ← hΩ, PsiExists.comp_famφT, lift_snd]
  simp [Fin.prod_univ_four, DegPre.famε]

theorem val_psi (gp : IsGrpPullback D'.P.A D.P.A (spMap φ) β)
    (hc : ∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) (hrig : RigCmp φ D D' β v)
    {f : ∀ α, SecBT D (𝟙_ _) 1 α} {f' : ∀ α, SecBT D' (𝟙_ _) 1 α} (hf : SecCmp D D' β v xe f f')
    (h : PsiRel D (𝟙_ _) f) (h' : PsiRel D' (𝟙_ _) f') {gam : (TK V).left ⟶ (TK R).left}
    (hg : gam ≫ jK R = jK V ≫ spMap φ) (x : D'.X) {T : Over (Spec (CommRingCat.of V))} [IsIntegral T.left]
    (κ : T ⟶ TK V) (p : T ⟶ D'.P.A) (z : T.left) {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J')
    (ne : sval (f' 0) (lift (toUnit T) p).left z J' ≠ 0) :
    val (D.psi (xe x)) (κ.left ≫ gam) z J =
      (gw v (κ.left ≫ D'.xK x) z (J ((κ.left ≫ D'.xK x) ≫ β)) (J' (κ.left ≫ D'.xK x)))⁻¹ *
        val (D'.psi x) κ.left z J' := by
  let T₀ : Over (Spec (CommRingCat.of R)) := Over.mk (T.hom ≫ spMap φ)
  let κ₀ : T₀ ⟶ TK R := Over.homMk (κ.left ≫ gam) (by
    have w : κ.left ≫ jK V = T.hom := Over.w κ
    show (κ.left ≫ gam) ≫ jK R = T.hom ≫ spMap φ
    rw [Category.assoc, hg, ← Category.assoc, w])
  let b : (T ⟶ D'.P.A) →* (T₀ ⟶ D.P.A) := pushHom gp T
  have bc : b (cT D' T x) = cT D T₀ (xe x) := Over.OverMorphism.ext (by
    show (T.hom ≫ (D'.c x).left) ≫ β = (T.hom ≫ spMap φ) ≫ (D.c (xe x)).left
    rw [Category.assoc, hc, Category.assoc])
  let Ω : (T.left ⟶ D'.P.A.left) → (T.left.presheaf.stalk z)ˣ := fun q => gw v q z (J (q ≫ β)) (J' q)
  let y : T ⟶ D'.P.A := p * (cT D' T x)⁻¹
  have hy : y * cT D' T x = p := inv_mul_cancel_right _ _
  have hyb : b y * cT D T₀ (xe x) = b p := by rw [← bc, ← map_mul, hy]
  have sn : ∀ q : T ⟶ D'.P.A, (lift (toUnit T₀) (b q)).left ≫ (snd _ D.P.A).left = q.left ≫ β := fun q =>
    congrArg (fun q => q.left) (lift_snd (toUnit T₀) (b q))
  have e₁ := h (xe x) T₀ (toUnit _) κ₀ (b y) z J hJ
  have e₂ := h' x T (toUnit _) κ y z J' hJ'
  have e₃ := secCmp_val hf x y _ (sn y) z hJ hJ' Ω fun _ => rfl
  have e₄ := secCmp_val hf 0 p _ (sn p) z hJ hJ' Ω fun _ => rfl
  have e₀ : ∀ α : D.X, α = 0 → sval (f α) (lift (toUnit T₀) (b p)).left z J =
      sval (f 0) (lift (toUnit T₀) (b p)).left z J := by
    rintro _ rfl; rfl
  rw [PsiExists.cT_zero, _root_.mul_one, inv_mul_cancel_right] at e₄
  rw [hy] at e₂ e₃
  rw [hyb] at e₁
  have e₅ : @id (T.left.presheaf.stalk z)ˣ (rigV D (T := T₀) z J) = Ω (1 : T ⟶ D'.P.A).left * rigV D' z J' := by
    have := CubTransport.val_pmaps (fun _ => (cubeMapOf gp).e_comm) hrig T.hom hJ hJ'
    rw [Fintype.prod_unique, zpow_one] at this
    exact this
  have e₆ : κ.left ≫ D'.xK x = (cT D' T x).left :=
    congrArg (fun q => q.left) (show κ ≫ cT D' _ x = cT D' _ x by rw [← Category.assoc, comp_toUnit])
  have e₇ := e₃.symm.trans (e₁.trans (congrArg₂ (· * ·)
    (congrArg (fun u : (T.left.presheaf.stalk z)ˣ => (val (D.psi (xe x)) (κ.left ≫ gam) z J * u).val) e₅)
    ((e₀ _ (map_zero xe)).symm.trans e₄)))
  rw [e₂] at e₇
  rw [e₆]
  refine PsiCompare.unit_cancel (a := Ω p.left) (c := Ω (1 : T ⟶ D'.P.A).left) (q := rigV D' z J') ne ?_
  rw [mul_comm (sval _ _ _ _)]
  exact e₇.trans (mul_comm _ _)

end GlobalTheory.PsiBaseChange

namespace GlobalTheory

open PsiBaseChange in

theorem psiCmp_of_secCmp : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → RigCmp φ D D' β v → ∀ (f : ∀ α, SecBT D (𝟙_ _) 1 α) (f' : ∀ α, SecBT D' (𝟙_ _) 1 α), SecCmp D D' β v xe f f' → PsiRel D (𝟙_ _) f → PsiRel D' (𝟙_ _) f' → (∃ j, (f' 0).f j ≠ 0) → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam := by
  intro R V _ _ _ _ φ D D' β v xe gp hv hc hrig f f' hf h h' hne gam hg x
  have hL := D.P.isLB
  have hL' := D'.P.isLB
  have pg := (isGen_iff v).1 hv
  have := D'.P.isAb.smooth
  have := D'.P.isAb.geomConnected
  have : IsIntegral (TF (R := V) (FractionRing V)).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of _)))
  have : IsIntegral (DegPre.BF D' (FractionRing V)).left :=
    isIntegral_tensor_left_of_smooth_grpObj _ D'.P.A (TF (R := V) (FractionRing V))
  have hx : D'.xK x ≫ β = gam ≫ D.xK (xe x) := by
    show (jK V ≫ (D'.c x).left) ≫ β = gam ≫ jK R ≫ (D.c (xe x)).left
    rw [Category.assoc, hc, ← Category.assoc gam, hg, Category.assoc]
  let T := DegPre.BF D' (FractionRing V)
  let π : T.left ⟶ (TK V).left := (fst (TF (R := V) (FractionRing V)) D'.P.A).left ≫ jFK (R := V) (FractionRing V)
  let κ : T ⟶ TK V := Over.homMk π
    ((Category.assoc _ _ _).trans (Over.w (fst (TF (R := V) (FractionRing V)) D'.P.A)))
  obtain ⟨s, hs⟩ := PsiExists.exists_pullB D' (FractionRing V) (toUnit _) 1 f'
  have hs0 := (pullB_ne_zero_iff V D' _ 1 f' s hs 0).2 hne
  have wl : toUnit (TF (R := V) (FractionRing V)) ▷ D'.P.A = lift (toUnit T) (snd _ D'.P.A) :=
    CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) ((whiskerRight_snd _ _).trans (lift_snd _ _).symm)
  have key : ∀ (z : T.left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (D.psi (xe x)) (π ≫ gam) z J =
        (gw v (π ≫ D'.xK x) z (J ((π ≫ D'.xK x) ≫ β)) (J' (π ≫ D'.xK x)))⁻¹ * val (D'.psi x) π z J' :=
    fun z J J' hJ hJ' => val_psi gp hc hrig hf h h' hg x κ (snd _ D'.P.A) z hJ hJ' (by
      rw [← wl, ← hs 0 z J' hJ']
      exact (exists_ne_zero_iff_sval_ne_zero _ hJ').1 hs0)
  obtain ⟨t, ht, hv⟩ := exists_up pg hL hL' (φ' := fun _ : PUnit => D'.xK x) (D'.psi x) (D'.psi_gen x)
  have hcorr : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (D.psi (xe x)) (π ≫ gam))
      (LB.pullGen D.P.L _ _ t π) :=
    corr_of_val hL fun z J hJ => by
      choose J' hJ' using fun ψ : T.left ⟶ D'.P.A.left => exists_chart hL' (ψ z)
      rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp, key z J J' hJ hJ']
      refine Eq.trans ?_ (hv _ π z _ _ (Good.mem hJ _ π) (Good.mem hJ' _ π)).symm
      rw [pw, Fintype.prod_unique, zpow_neg_one, Category.assoc]; rfl
  have hz : (DegPre.zF D' (FractionRing V)).left ≫ π = 𝟙 (TK V).left := PsiCompare.zF_fst D'
  refine EvenPull.pmaps_of_section pg hL hL' gam (fun _ => hx) _ (D'.psi_gen x) _ (D.psi_gen _) (𝟙 _) (𝟙 _)
    (Category.id_comp _) (by rw [Scheme.Hom.id_appTop]; exact Function.surjective_id) fun y J J' hJ hJ' => ?_
  have := val_corr hJ hcorr (DegPre.zF D' (FractionRing V)).left
  rw [val_pull hJ, val_pull hJ, ← Category.assoc, hz] at this
  refine this.trans ((hv _ (𝟙 _) y _ _ (Good.mem hJ _ _) (Good.mem hJ' _ _)).trans ?_)
  refine congrArg₂ (· * ·) ?_ rfl
  rw [pw, Fintype.prod_unique, Fintype.prod_unique, Category.assoc]

end GlobalTheory
end
