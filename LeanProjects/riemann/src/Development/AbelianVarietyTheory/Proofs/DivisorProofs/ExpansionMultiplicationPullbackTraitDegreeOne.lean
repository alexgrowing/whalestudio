import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulSecK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFamPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfUniformisationOverDvr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EqZeroOfSval

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.MulExpand

open ReciprocityTheory.ChartRestriction.G.DVR (mulGen_isGen pullGen_isGen powGen_isGen val_pow cP comp_cP)
open GlobalTheory.UT

section
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'}

abbrev prj (hD : IsPullDeg φ D D') : D'.P.A.left ⟶ D.P.A.left := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)

def om (hD : IsPullDeg φ D D') {Z : Scheme.{0}} (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι)
    (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι) (q : Z ⟶ D'.P.A.left) : (Z.presheaf.stalk z)ˣ :=
  gw hD.w q z (J (q ≫ prj hD)) (J' q)

theorem pullB_val {hD : IsPullDeg φ D D'} {k : ℕ} {x : D'.X} {b : D.SecB k (hD.xe x)} {b' : D'.SecB k x}
    (H : PullB hD x b b') {Z : Scheme.{0}} (r : Z ⟶ D'.P.A.left) (z : Z) {J J'} (hJ : Good D.P.L z J)
    (hJ' : Good D'.P.L z J') :
    sval b (r ≫ prj hD) z J = (∏ κ, om hD z J J' (r ≫ D'.famφB x κ) ^ DegPre.famε k κ).val * sval b' r z J' := by
  rw [sval_of b (r ≫ prj hD) z J (fun κ => J ((r ≫ D'.famφB x κ) ≫ prj hD)) (fun κ => by
    rw [Category.assoc r (prj hD), Category.assoc r _ (prj hD), ExpGTrans.famφB_pull hD x κ])]
  exact H Z r z _ _ (fun κ => hJ ((r ≫ D'.famφB x κ) ≫ prj hD)) (fun κ => hJ' (r ≫ D'.famφB x κ))

theorem prod_fam_unit (D : DegPre R) (α : D.X) (k : ℕ) {U : Type} [CommGroup U] (h : (Sp R ⟶ D.P.A.left) → U) :
    ∏ κ, h (eSec D.P.A ≫ D.famφB α κ) ^ DegPre.famε k κ = h (eSec D.P.A) ^ (k : ℤ) := by
  have e₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) = η[D.P.A] := by rw [Hom.one_def]; simp
  have a₀ : eSec D.P.A ≫ D.famφB α 0 = eSec D.P.A := Category.comp_id _
  have a₁ : eSec D.P.A ≫ D.famφB α 1 = eSec D.P.A ≫ D.famφB α 2 := congrArg (fun z => z.left)
    ((MonObj.comp_mul η[D.P.A] (𝟙 _) (cP D _ α)).trans
      ((congrArg (· * _) ((Category.comp_id _).trans e₁.symm)).trans (_root_.one_mul _)))
  have a₃ : eSec D.P.A ≫ D.famφB α 3 = eSec D.P.A := PullExp.eSec_comp_one
  rw [Fin.prod_univ_four, a₀, a₁, a₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, DegPre.famε, Matrix.cons_val]
  module

theorem mul_val_pull (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') (m k k' : ℕ) (hk : k ≤ k') (x x' : D'.X) (hx : x' = m • x)
    (a : D'.P.A ⟶ D'.P.A) (ha : a = 𝟙 D'.P.A ^ m) (b : D.SecB k (hD.xe x)) (g : ∀ χ, D.SecB k' χ)
    (hM : MulSecB D m (hD.xe x) b (g (m • hD.xe x))) (b' : D'.SecB k x) (hb : PullB hD x b b')
    (c' : D'.SecB k' x') (hc : PullB hD x' (g (hD.xe x')) c')
    (eB : LB.Gen (LB.LinComb D'.P.L (Sum.elim (D'.famφB x') (fun i => a.left ≫ D'.famφB x i))
        (Sum.elim (DegPre.famε k') (fun i => - DegPre.famε k i)))) (heB : eB.IsGen)
    (hn : ∀ y J, Good D'.P.L y J → val eB (eSec D'.P.A) y J = rigV D' (𝟙 _) y J ^ ((k' : ℤ) - k))
    (y : D'.P.A.left) (J') (hJ' : Good D'.P.L y J') :
    sval c' (𝟙 _) y J' = sval b' (𝟙 _ ≫ a.left) y J' * (val eB (𝟙 _) y J').val := by
  subst hx ha
  obtain ⟨u, hu, hun, hrel⟩ := hM
  have gp := pull_grp hD
  have hm : (mulA D'.P.A m).left ≫ prj hD = prj hD ≫ (mulA D.P.A m).left := GlobalTheory.ZH.TorsFrame.mulA_comm gp m
  have hφ : ∀ i, mulφB D' m x i ≫ prj hD = prj hD ≫ mulφB D m (hD.xe x) i := by
    rintro (i | i)
    · have := ExpGTrans.famφB_pull hD (m • x) i
      rw [map_nsmul] at this
      exact this
    · show ((mulA D'.P.A m).left ≫ D'.famφB x i) ≫ prj hD = prj hD ≫ (mulA D.P.A m).left ≫ D.famφB (hD.xe x) i
      rw [Category.assoc, ExpGTrans.famφB_pull hD x i, ← Category.assoc, hm, Category.assoc]
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff hD.w).1 hD.w_gen) D.P.isLB D'.P.isLB (φ' := mulφB D' m x)
    (ε := mulεB k k') eB heB
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val t r z J = (∏ i, om hD z J J' (r ≫ mulφB D' m x i) ^ mulεB k k' i) * val eB r z J' := fun Z r z J J' hJ hJ' => by
    refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun I _ => ?_) rfl)
    rw [om, Category.assoc]
  have hr : PMaps hD.w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap φ) :=
    (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
      (rigPull_le (prj hD) (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig
  have he : eSec D'.P.A ≫ prj hD = spMap φ ≫ eSec D.P.A := hD.he
  have hem : eSec D'.P.A ≫ (mulA D'.P.A m).left = eSec D'.P.A := by
    have e₁ : (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) = η[D'.P.A] := by rw [Hom.one_def]; simp
    refine (GlobalTheory.ZH.TorsFrame.comp_mulA η[D'.P.A] m).trans ?_
    rw [← e₁, one_pow, e₁]; rfl
  have key := gen_unique' D.P.isLB (φ := fun i => prj hD ≫ mulφB D m (hD.xe x) i) (ε := mulεB k k')
    (fun V _ h => Finset.prod_congr rfl fun i _ => congrArg (fun q => h q ^ mulεB k k' i) (hφ i))
    D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2 (pullGen_isGen _ _ _ _ hu (prj hD)) ht (fun y I hI => by
      choose I' hI' using fun χ : Sp R' ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ y)
      have hI' : Good D'.P.L y I' := hI'
      have p : (∏ i, om hD y I I' (eSec D'.P.A ≫ mulφB D' m x i) ^ mulεB k k' i) =
          om hD y I I' (eSec D'.P.A) ^ ((k' : ℤ) - k) := by
        rw [Fintype.prod_sum_type]
        simp only [mulφB, mulεB, Sum.elim_inl, Sum.elim_inr, ← Category.assoc, hem, zpow_neg, Finset.prod_inv_distrib]
        rw [prod_fam_unit D' _ _ (om hD y I I'), prod_fam_unit D' _ _ (om hD y I I'), zpow_sub]
      have q : rigV D (spMap φ) y I = om hD y I I' (eSec D'.P.A) * rigV D' (𝟙 _) y I' := by
        have := hr _ (𝟙 _) y (fun _ => I (eSec D'.P.A ≫ prj hD)) (fun _ => I' (eSec D'.P.A))
          (fun _ => hI (eSec D'.P.A ≫ prj hD)) (fun _ => hI' (eSec D'.P.A))
        rw [Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp] at this
        rw [rigV, rigV, val_of (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig _ y I (fun _ => I (eSec D'.P.A ≫ prj hD)) (fun _ => by rw [he]),
          val_of (L := D'.P.L) (φ := fun _ : PUnit => eSec D'.P.A) (ε := fun _ => 1) D'.rig _ y I' (fun _ => I' (eSec D'.P.A)) (fun _ => by rw [Category.id_comp])]
        exact this
      have s := val_corr hI hun (spMap φ)
      rw [val_pull hI, val_pow] at s
      rw [val_pull hI, hv' _ _ y I I' hI hI', p, hn y I' hI', ← mul_zpow, ← q, he, s,
        show ((k' : ℤ) - k) = ((k' - k : ℕ) : ℤ) by omega, zpow_natCast]
      rfl)
  choose J hJ using fun χ : D'.P.A.left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have hJ : Good D.P.L y J := hJ
  have k₁ := (val_pull hJ u (prj hD) (𝟙 _)).symm.trans ((key _ (𝟙 _) y J hJ).trans (hv' _ _ y J J' hJ hJ'))
  have k₂ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ _).1 hrel _ (𝟙 _ ≫ prj hD) y J hJ
  have k₃ := pullB_val hc (𝟙 _) y hJ hJ'
  have k₄ := pullB_val hb (𝟙 _ ≫ (mulA D'.P.A m).left) y hJ hJ'
  have k₅ : sval (g (hD.xe (m • x))) (𝟙 _ ≫ prj hD) y J = sval (g (m • hD.xe x)) (𝟙 _ ≫ prj hD) y J :=
    congrArg (fun χ => sval (g χ) (𝟙 _ ≫ prj hD) y J) (map_nsmul hD.xe m x)
  rw [Category.assoc (𝟙 _) (prj hD), ← hm, ← Category.assoc (𝟙 _) _ (prj hD), k₄, k₁, ← k₅, k₃, Fintype.prod_sum_type] at k₂
  simp only [mulφB, mulεB, Sum.elim_inl, Sum.elim_inr, ← Category.assoc, zpow_neg, Finset.prod_inv_distrib] at k₂
  refine (Units.mul_right_inj _).1 (k₂.trans ?_)
  generalize (∏ κ, om hD y J J' (𝟙 _ ≫ D'.famφB (m • x) κ) ^ DegPre.famε k' κ) = P
  generalize (∏ κ, om hD y J J' ((𝟙 _ ≫ (mulA D'.P.A m).left) ≫ D'.famφB x κ) ^ DegPre.famε k κ) = Q
  rw [Units.val_mul, Units.val_mul]
  linear_combination (P.val * sval b' (𝟙 _ ≫ (mulA D'.P.A m).left) y J' * (val eB (𝟙 _) y J').val) * Q.mul_inv

end

theorem expand : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (m : ℕ), Odd m →
    ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)), MulFam m F₁ G →
    ∀ (σ' : H0 T.U.LG.L 1) (f' : ∀ x, T.D'.toPre.SecB 1 x), (∀ x, PullB T.hD x (F₁.f (T.hD.xe x)) (f' x)) →
    (∀ e, T.U.ExpandsAt e 1 σ' f') →
    ∀ (f'' : ∀ x, T.D'.toPre.SecB (m ^ 2) x), (∀ x, PullB T.hD x (G.f (T.hD.xe x)) (f'' x)) →
    ∃ (uG : LB.Gen (LB.LinComb T.U.LG.L (K := Fin 2) ![𝟙 T.G.left, (mulA T.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
      (σ'' : H0 T.U.LG.L (m ^ 2)), uG.IsGen ∧
      (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ T.G.left) → T.U.LG.L.ι), Good T.U.LG.L z J →
        sval σ'' r z J = (val uG (r ≫ 𝟙 _) z J).val * sval σ' (r ≫ (mulA T.G m).left) z J) ∧
      ∀ e, T.U.ExpandsAt e (m ^ 2) σ'' f'' := by
  intro R _ _ _ _ D C W _ _ _ T m hm F₁ G hFG σ' f' hf' hσ' f'' hf''
  obtain ⟨hd, hV, hz⟩ := T.cdvr
  have hL := GlobalTheory.firstFiveLaws
  have hI : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  have hGF := hL.1.globalFns
  have hG : IsSemiAbelian T.G := GlobalTheory.isSemiAbelian_of_unifPre_dvr W T.D' T.A T.G T.U.toUnifPre
  obtain ⟨E, hEG, -, hEB, hEh, -⟩ := (GlobalTheory.IntEnd.exists_nsmul_and_neg hL W (maximalIdeal W) hI T.D' T.A T.G hG T.U).1 m
  have := E.homG
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  have hsm : Function.Injective fun χ : T.D'.toPre.X => m • χ := fun a b h => by
    have h' : (m : ℤ) • a = (m : ℤ) • b := by simpa only [natCast_zsmul] using h
    exact smul_right_injective T.D'.toPre.X (Int.natCast_ne_zero.2 hm0) h'
  have hinj : Function.Injective E.h := fun a b h => hsm (by simpa only [hEh] using h)
  obtain ⟨β₀, hβ₀⟩ := ThetaSum.exists_gen_pow T.U.LG T.U.cubG T.U.symG T.U.symG_gen m E.aG hEG
  obtain ⟨β, hβ, hβ'⟩ := PullExp.exists_normalised T.U.LG.isLB E.aG _ _ β₀ hβ₀
  obtain ⟨κ₀, hκ₀, hrel⟩ := GlobalTheory.T.descent_powerIso_endomorphism_abelianPart_uniformization hL W (maximalIdeal W) hI T.D' T.A T.G hG T.U E (m ^ 2) 1 β hβ hβ'
  obtain ⟨σ₃, f₃, p₁, p₂, p₃, p₄⟩ := GlobalTheory.T.pullback_section_endomorphism_expansion W (maximalIdeal W) T.D' T.A T.G T.U.toUnifPre E hinj (m ^ 2) 1 β hβ κ₀
    hκ₀.1 hrel σ' f' hσ'
  have hf : f₃ = f'' := funext fun b => ReciprocityTheory.ChartRestriction.G.DVR.SecOps.sec_ext (sec_ext_val T.D'.toPre.P.isLB fun y J hJ => by
    by_cases hb : b ∈ Set.range E.h
    · obtain ⟨χ, rfl⟩ := hb
      obtain ⟨eB, heB, hvB⟩ := NsmulPull.gen_shape T.D'.toPre E.aB (m ^ 2) 1 hm2 (E.h χ) χ κ₀ hκ₀.1 (E.u χ) (E.u_norm χ).1
      have h := mul_val_pull hGF T.hD m 1 (m ^ 2) hm2 χ (E.h χ) (hEh χ) E.aB hEB _ G.f (hFG.1 _) _ (hf' χ) _ (hf'' _) eB heB
        (fun y J hJ => by
          have a := val_corr hJ hκ₀.2 (𝟙 _)
          have a' := val_corr hJ (E.u_norm χ).2 (𝟙 _)
          rw [val_pull hJ, Category.id_comp, val_one] at a a'
          rw [hvB _ _ y J hJ, a, a', _root_.one_mul, _root_.mul_one]
          exact congrArg (fun q => rigV T.D'.toPre q y J ^ _) (Over.w η[T.D'.toPre.P.A])) y J hJ
      rw [h, hvB _ _ y J hJ]
      exact p₃ χ _ _ y J hJ
    · choose J₀ hJ₀ using fun χ : T.D'.toPre.P.A.left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ y)
      have h := pullB_val (hf'' b) (𝟙 _) y hJ₀ hJ
      rw [GlobalTheory.PullComp.sval_eq_zero _ (hFG.2 _ fun χ e => hb ⟨T.hD.xe.symm χ, by
        rw [hEh, ← map_nsmul, ← e, AddEquiv.symm_apply_apply]⟩)] at h
      rw [GlobalTheory.PullComp.sval_eq_zero _ (p₄ b hb), (Units.mul_right_eq_zero _).1 h.symm])
  subst hf
  let ρ := LB.pullGen T.U.LG.L (K := PUnit) (fun _ => eSec T.G) (fun _ => 1) T.U.LG.rig T.G.hom
  have hρ : ρ.IsGen := pullGen_isGen _ _ _ _ T.U.LG.rigGen _
  obtain ⟨uG, huG, hv⟩ := exists_gen T.U.LG.isLB (K' := Fin 2) (φ' := ![𝟙 T.G.left, (mulA T.G m).left])
    (ε' := ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]) (fun U _ h => by
      rw [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_three, Fintype.prod_unique]
      show h (𝟙 _) ^ ((m ^ 2 : ℕ) : ℤ) * h E.aG.left ^ (-((1 : ℕ) : ℤ)) * h (1 : T.G ⟶ T.G).left ^ (((1 : ℕ) : ℤ) - (m ^ 2 : ℕ)) *
        h (T.G.hom ≫ eSec T.G) ^ (((m ^ 2 - 1 : ℕ) : ℤ) * 1) = h (𝟙 _) ^ ((m ^ 2 : ℕ) : ℤ) * h (mulA T.G m).left ^ (-((1 : ℕ) : ℤ))
      rw [hEG, GlobalTheory.ZH.TorsFrame.one_left, _root_.mul_assoc, ← zpow_add, Nat.cast_sub hm2]
      simp)
    (LB.mulGen _ _ _ _ _ β (GeneratorPullback.powGen _ _ _ ρ (m ^ 2 - 1))) (mulGen_isGen _ _ _ _ _ _ _ hβ (powGen_isGen _ _ _ _ hρ _))
  refine ⟨uG, σ₃, huG, fun Z r z J hJ => ?_, p₁⟩
  rw [p₂ Z r z J hJ, hv _ _ z J hJ, val_mul hJ, val_pow, val_pull hJ, Category.comp_id, mul_comm,
    show r ≫ E.aG.left = r ≫ (mulA T.G m).left by rw [hEG],
    show (((m ^ 2 : ℕ) : ℤ) - (1 : ℕ)) = ((m ^ 2 - 1 : ℕ) : ℤ) by omega, zpow_natCast]

end GlobalTheory.Mum.MulExpand
