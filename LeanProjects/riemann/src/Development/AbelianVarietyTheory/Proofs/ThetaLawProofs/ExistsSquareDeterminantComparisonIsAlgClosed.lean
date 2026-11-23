import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsGenSimilitudePull
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEnumKerTransposeSimilitudePointsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNormalisedIsoPullbackMulByMStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNormalisingUnitSimilitudeOriginStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BoxProductsBasisSpanPowObjSectionsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSectionBoxProductDivGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPointThetaPullbacksIsUnitStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.EqOfSimilitudeIsoQuotientKernelInvariantStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.SimilDet

theorem eq_zero_of_eigen {K B G Y N : Type} [Field K] [CommRing B] [IsDomain B] [Monoid G] [Fintype N]
    (κ : K →+* B) (χ : N → G →* B) (hχ : Function.Injective χ) (act : G → Y → Y) (F : N → Y → B)
    (hF : ∀ i v y, F i (act v y) = χ i v * F i y) (hne : ∀ i, ∃ y, F i y ≠ 0) (c : N → K)
    (h : ∀ y, ∑ i, κ (c i) * F i y = 0) : c = 0 := by
  funext i
  obtain ⟨y, hy⟩ := hne i
  have li := (linearIndependent_monoidHom G B).comp χ hχ
  have := Fintype.linearIndependent_iff.1 li (fun j => κ (c j) * F j y) (by
    funext v
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, Pi.zero_apply]
    rw [← h (act v y)]
    exact Finset.sum_congr rfl fun j _ => by rw [hF]; ring) i
  exact κ.injective (((mul_eq_zero.1 this).resolve_right hy).trans (map_zero κ).symm)

theorem exists_ratio {X Y S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    (p : Y ⟶ S₀) (hp : Function.Surjective p.appTop.hom)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(S₀, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J * (val u' r z J)⁻¹).val = gs (r ≫ p) z ⊤ a := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, hF U h, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := hp (res le (t.s PEmpty.elim)).val
  refine ⟨a, fun Z r z J hJ => ?_⟩
  rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
    ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))

theorem gs_cst {R : Type} [CommRing R] {Y Z : Scheme.{0}} (f : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) (a : R) :
    gs r z ⊤ (cst f ⊤ a) = gs (r ≫ f) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) :=
  (gs_res r z (V := ⊤) le_top trivial _).trans (gs_pull r f z ⊤ trivial _)

section Map

variable {R : Type} [CommRing R] (x : KeyIn R) (al : Matrix (Fin 4) (Fin 4) ℤ)

theorem mul_comp_alMap {Z : Over (Sp R)} (a b : Z ⟶ Out.powObj x.P.A 4) (r : Fin 4) (ζ : Pt x) :
    (a * b) ≫ alMap x al r ζ = (a ≫ alMap x al r 1) * (b ≫ alMap x al r ζ) := by
  haveI := x.P.isAb.comm
  have e : ∀ (a : Z ⟶ Out.powObj x.P.A 4) (ζ : Pt x), a ≫ alMap x al r ζ =
      (∏ c, (a ≫ Out.powPr x.P.A c) ^ al r c) * (toUnit Z ≫ ζ) := fun a ζ => by
    simp only [alMap, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, MonObj.comp_mul,
      GrpObj.comp_zpow, MonObj.comp_one, Fin.prod_univ_succ, Fin.prod_univ_zero, comp_toUnit_assoc]
  simp only [e, MonObj.mul_comp, mul_zpow, Finset.prod_mul_distrib, MonObj.comp_one, _root_.mul_one,
    _root_.mul_assoc]

def ker : Submonoid (𝟙_ (Over (Sp R)) ⟶ Out.powObj x.P.A 4) where
  carrier := {v | ∀ r, v ≫ alMap x al r 1 = 1}
  one_mem' := fun r => by
    haveI := x.P.isAb.comm
    have := mul_comp_alMap x al (1 : 𝟙_ (Over (Sp R)) ⟶ _) 1 r 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  mul_mem' := fun {a b} ha hb r => by rw [mul_comp_alMap, ha r, hb r, _root_.mul_one]

abbrev tr (v : 𝟙_ (Over (Sp R)) ⟶ Out.powObj x.P.A 4) : Out.powObj x.P.A 4 ⟶ Out.powObj x.P.A 4 :=
  (toUnit (Out.powObj x.P.A 4) ≫ v) * 𝟙 (Out.powObj x.P.A 4)

theorem tr_alMap (v : ker x al) (r : Fin 4) (ζ : Pt x) : tr x v.1 ≫ alMap x al r ζ = alMap x al r ζ := by
  rw [mul_comp_alMap, Category.assoc, v.2 r, MonObj.comp_one, _root_.one_mul, Category.id_comp]

theorem pt_tr (y v : 𝟙_ (Over (Sp R)) ⟶ Out.powObj x.P.A 4) : y ≫ tr x v = v * y := by
  rw [MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

end Map

theorem exists_transl_ratio (laws : Out.Laws) {R : Type} [CommRing R] (x : KeyIn R) (m : ℕ)
    (al : Matrix (Fin 4) (Fin 4) ℤ) (ξ ξ' : Fin 4 → Pt x) (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))) (w' : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ' r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ)))))
    (hw : w.IsGen) (hw' : w'.IsGen) (v : ker x al) :
    ∃ a : Γ(Sp R, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A 4).left) (z : Z) (J), Good x.P.L z J →
      (val w (r ≫ (tr x v.1).left) z J * (val w' (r ≫ (tr x v.1).left) z J)⁻¹ *
        (val w r z J * (val w' r z J)⁻¹)⁻¹).val = gs (r ≫ (Out.powObj x.P.A 4).hom) z ⊤ a := by
  have hu := DVR.mulGen_isGen _ _ _ _ _ _ _ hw (DVR.invGen_isGen _ _ _ _ hw')
  obtain ⟨a, ha⟩ := exists_ratio x.P.isLB (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, ← Over.comp_left, tr_alMap, zpow_neg,
        Finset.prod_inv_distrib, zpow_one, inv_inv]
      simp only [mul_inv, inv_inv, mul_mul_mul_comm _ _⁻¹, inv_mul_cancel])
    (Out.powObj x.P.A 4).hom (laws.globalFns _ _ (AbelianSchemeGerms.isAbelianScheme_powObj _ x.P.isAb 3)).2
    (DVR.pullGen_isGen _ _ _ _ hu (tr x v.1).left) hu
  refine ⟨a, fun Z r z J hJ => ?_⟩
  have := ha Z r z J hJ
  rwa [val_pull hJ, val_mul hJ, val_mul hJ, val_inv, val_inv] at this

theorem exists_l2Val : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin (m ^ x.P.g) → RR x m), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → IsBasis x b → ∃ lam, IsSquareDeterminantComparison x m al b lam := by
  intro laws K _ _ x m al b hm hal hb
  classical
  have hm0 : m ≠ 0 := fun h => hm (by rw [h, Nat.cast_zero])
  have hL := x.P.isLB
  obtain ⟨ξ, hξ, hk⟩ := GlobalTheory.T.exists_enum_ker_transpose_similitude_points laws K x m al hm hal
  obtain ⟨mu, hmu, hmuv⟩ := GlobalTheory.T.exists_normalised_iso_pullback_mul_by_m laws K x m
  choose w hw using fun I => GlobalTheory.SimilPull.exists_gen_similitude_pull laws K x m al (ξ I) hal (hk I)
  choose rho hrho using fun I => GlobalTheory.T.exists_normalising_unit_similitude_origin K x m al (ξ I) mu (w I) hm0 hal (hk I) hmu (hw I)
  choose s hs using fun I => GlobalTheory.T.exists_section_boxProduct_div_generator _ _ x.P.L hL (Fin 4) (Fin 4) _ _ (m : ℤ) x.th (w I) (hw I)
  choose Q hQ using fun I => GlobalTheory.T.boxProducts_basis_span_powObj_sections K x m _ b hb 4 (s I)
  have hdet : (Matrix.of Q).det ≠ 0 := by
    intro h0
    obtain ⟨c, hc, hcQ⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    obtain ⟨I₀, -⟩ := Function.ne_iff.1 hc
    refine hc ?_
    let S : Over (Sp K) := 𝟙_ _
    let T := Out.powObj x.P.A 4
    haveI : IsIntegral S.left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of K)))
    haveI : Subsingleton S.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    let p : S.left := IsLocalRing.closedPoint K
    choose J hJ using fun χ : S.left ⟶ x.P.A.left => exists_chart hL (χ p)
    replace hJ : Good x.P.L p J := hJ
    let ev : Γ(S.left, ⊤) →+* S.left.presheaf.stalk p := (S.left.presheaf.germ ⊤ p trivial).hom
    have hev : ∀ (y : S ⟶ T) a, gs (y.left ≫ T.hom) p ⊤ a = ev a := fun y a => by
      rw [Over.w y]
      exact gs_eq (𝟙 S.left) p ⊤ trivial a
    let κ : K →+* S.left.presheaf.stalk p := ev.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    choose a ha using fun I v => exists_transl_ratio laws x m al (ξ I₀) (ξ I) (w I₀) (w I) (hw I₀) (hw I) v
    let u : (Fin 4 → Fin (m ^ x.P.g)) → (S ⟶ T) → (S.left.presheaf.stalk p)ˣ := fun I y =>
      val (w I₀) y.left p J * (val (w I) y.left p J)⁻¹
    have hu : ∀ I (v : ker x al) (y : S ⟶ T), (u I (v.1 * y)).val = ev (a I v) * (u I y).val := fun I v y => by
      have := ha I v _ y.left p J hJ
      rw [hev, ← Over.comp_left, pt_tr] at this
      rw [← this, ← Units.val_mul, inv_mul_cancel_right]
    let χ : (Fin 4 → Fin (m ^ x.P.g)) → ker x al →* S.left.presheaf.stalk p := fun I =>
      { toFun := fun v => ev (a I v)
        map_one' := by
          have := hu I 1 1
          rw [Submonoid.coe_one, _root_.one_mul] at this
          exact (Units.mul_left_inj (u I 1)).1 (this.symm.trans (_root_.one_mul _).symm)
        map_mul' := fun v v' => by
          have := hu I (v * v') 1
          rw [Submonoid.coe_mul, _root_.mul_assoc, hu, hu, ← _root_.mul_assoc] at this
          exact ((Units.mul_left_inj (u I 1)).1 this).symm }
    have hχ : Function.Injective χ := fun I I' h => by
      by_contra hne
      obtain ⟨r, hr⟩ := hξ I I' hne p
      have e := GlobalTheory.T.eq_of_similitudeIso_quotient_kernel_invariant laws K x m al (ξ I) (ξ I') (w I) (w I') hm hal (hw I) (hw I') (fun v hv Z r z J hJ => by
        have e₁ : a I ⟨v, hv⟩ = a I' ⟨v, hv⟩ := fn_ext (X := S.left) fun y _ => by
          obtain rfl : y = p := Subsingleton.elim _ _
          exact (gs_eq (𝟙 S.left) p ⊤ trivial _).trans ((DFunLike.congr_fun h ⟨v, hv⟩).trans
            (gs_eq (𝟙 S.left) p ⊤ trivial _).symm)
        have e₂ := Units.ext ((ha I ⟨v, hv⟩ Z r z J hJ).trans (e₁ ▸ (ha I' ⟨v, hv⟩ Z r z J hJ).symm))
        have alg : ∀ {U : Type} [CommGroup U] (A B B' C D D' : U),
            A * B⁻¹ * (C * D⁻¹)⁻¹ = A * B'⁻¹ * (C * D'⁻¹)⁻¹ → B * D' = B' * D := fun A B B' C D D' h => by
          rw [mul_inv, mul_inv, inv_inv, inv_inv, _root_.mul_assoc, _root_.mul_assoc, mul_right_inj, mul_left_comm,
            mul_left_comm B'⁻¹, mul_right_inj, inv_mul_eq_iff_eq_mul] at h
          rw [h, mul_left_comm B', mul_inv_cancel_left]
        exact alg _ _ _ _ _ _ e₂)
      exact hr (by rw [e])
    let θ : (Fin 4 → Fin (m ^ x.P.g)) → (S ⟶ T) → S.left.presheaf.stalk p := fun I y =>
      ∏ r, gs (y.left ≫ (alMap x al r (ξ I r)).left) p _ (x.th.f (J (y.left ≫ (alMap x al r (ξ I r)).left)))
    refine eq_zero_of_eigen κ χ hχ (fun v y => v.1 * y) (fun I y => θ I y * (u I y).val) (fun I v y => ?_)
      (fun I => ?_) c (fun y => ?_)
    · have e : θ I (v.1 * y) = θ I y := Finset.prod_congr rfl fun r _ =>
        congrArg (fun ψ : S.left ⟶ x.P.A.left => gs ψ p _ (x.th.f (J ψ))) (by
          rw [← Over.comp_left, ← Over.comp_left, ← pt_tr, Category.assoc, tr_alMap])
      simp only [hu, e]
      exact mul_left_comm _ _ _
    · obtain ⟨y, hy⟩ := GlobalTheory.T.exists_point_thetaPullbacks_isUnit laws K x m al (ξ I) hm hal
      exact ⟨y, mul_ne_zero (Finset.prod_ne_zero_iff.2 fun r _ => (hy p J hJ r).ne_zero) (Units.ne_zero _)⟩
    · have e : ∀ I, θ I y * (u I y).val = (val (w I₀) y.left p J).val * ∑ I', κ (Q I I') *
          ∏ c, gs (y.left ≫ (Out.powPr x.P.A c).left) p _ ((b (I' c)).f (J (y.left ≫ (Out.powPr x.P.A c).left))) :=
        fun I => by
        have e₁ : θ I y = _ := hs I _ y.left p J hJ
        rw [e₁, hQ I _ y.left p J hJ, mul_right_comm, ← Units.val_mul, mul_comm (val (w I) y.left p J),
          inv_mul_cancel_right]
        refine congrArg _ (Finset.sum_congr rfl fun I' _ => ?_)
        rw [gs_cst, hev]
        rfl
      simp only [e, mul_left_comm _ (val (w I₀) y.left p J).val, ← Finset.mul_sum]
      refine mul_eq_zero_of_right _ ?_
      simp only [Finset.mul_sum, ← _root_.mul_assoc, ← map_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun I' _ => ?_
      rw [← Finset.sum_mul, ← map_sum, show ∑ I, c I * Q I I' = 0 from congrFun hcQ I', map_zero, zero_mul]
  refine ⟨Units.mk0 _ hdet ^ (2 * m ^ 2) * ∏ I, rho I ^ 2, ξ, mu, w, Matrix.of Q, rho, hξ, hk, hmu, hw,
    fun p J hJ => ⟨hmuv p J hJ, fun I => hrho I p J hJ⟩, fun I y J hJ => ?_, by simp⟩
  have e := hs I _ (𝟙 _) y J hJ
  rw [hQ I _ (𝟙 _) y J hJ] at e
  have i : ∀ (f : ∀ j, Γ(x.P.A.left, x.P.L.U j)) (ψ : (Out.powObj x.P.A 4).left ⟶ x.P.A.left),
      gs (𝟙 _ ≫ ψ) y _ (f (J (𝟙 _ ≫ ψ))) = gs ψ y _ (f (J ψ)) := fun f ψ => by rw [Category.id_comp]
  exact (Finset.prod_congr rfl fun r _ => (i _ _).symm).trans (e.trans (congrArg _ (Finset.sum_congr rfl fun I' _ =>
    congrArg _ (Finset.prod_congr rfl fun c _ => i (b (I' c)).f _))))

end GlobalTheory.SimilDet
