import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExpandsAtOfIntegral
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecBGeneratesOfIsUnit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecUnitClosedFibre
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDivOfExpandsAt

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ThetaSectionTest

open GlobalTheory.FieldBaseChange GlobalTheory.ConstFam GlobalTheory.IndivisibleSection GlobalTheory.ThetaUnit

theorem exists_nonzero_closed (hS : SecBaseChangeSt) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] (D : DegPre R) :
    ∃ th : D.SecB 1 0, ∃ x, D.P.A.hom x = closedPoint R ∧ x ∈ nonzeroLocus th := by
  obtain ⟨U, hU, b, hb⟩ := hS (Spec (CommRingCat.of R)) D.P 1 le_rfl (closedPoint R)
  obtain rfl : U = ⊤ := eq_top_of_closedPoint_mem U hU
  let t : Spec (CommRingCat.of (ResidueField R)) ⟶ (overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤).left :=
    spMap (residue R) ≫ (Spec (CommRingCat.of R)).topIso.inv
  have ht : t ≫ (overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤).hom = spMap (residue R) := by
    show (spMap (residue R) ≫ (Spec (CommRingCat.of R)).topIso.inv) ≫ (Scheme.Opens.ι ⊤ ≫ 𝟙 _) = _
    rw [Category.comp_id, Category.assoc]
    exact (congrArg (spMap (residue R) ≫ ·) (Spec (CommRingCat.of R)).topIso.inv_hom_id).trans (Category.comp_id _)
  have pull : ∀ i, ∃ b' : LB.Sec (LPow D.P.A D.P.L (1 : ℕ) (baseAt t)),
      IsPullSec D.P.A D.P.L (1 : ℕ) (homAt t ▷ D.P.A) (whiskerRight_snd (homAt t) D.P.A) (b i) b' := fun i => by
    obtain ⟨s', hs'⟩ := exists_pull_chart (K := Fin 1) (b i) (homAt t ▷ D.P.A).left
      (fun _ => (snd (baseAt t) D.P.A).left)
      (fun _ => congrArg CommaMorphism.left (whiskerRight_snd (homAt t) D.P.A))
    exact ⟨s', fun j => hs' j _⟩
  choose b' hb' using pull
  obtain ⟨hli, -⟩ := hb _ t b' hb'
  have hq : Unique (Fin (1 ^ D.P.g)) := by rw [one_pow]; infer_instance
  have hnt : Nontrivial Γ((baseAt t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (ResidueField R))).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have hne := hli.ne_zero hq.default
  obtain ⟨j, hj⟩ : ∃ j, (b' hq.default).f j ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (Subtype.ext (funext h))
  have := D.P.isAb.smooth
  have : IsReduced (baseAt t).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (ResidueField R))))
  have hr : IsReduced (baseAt t ⊗ D.P.A).left :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.fst (baseAt t).hom D.P.A.hom)
  obtain ⟨y, hy⟩ : ∃ y, y ∈ (baseAt t ⊗ D.P.A).left.basicOpen ((b' hq.default).f j) := by
    by_contra h
    push Not at h
    exact hj ((basicOpen_eq_bot_iff _).1 (eq_bot_iff.2 fun y hy => (h y hy).elim))
  let W := overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤
  let u : D.P.A ⟶ W := Over.homMk (D.P.A.hom ≫ (Spec (CommRingCat.of R)).topIso.inv) (by
    show (_ ≫ (Spec (CommRingCat.of R)).topIso.inv) ≫ (Scheme.Opens.ι ⊤ ≫ 𝟙 _) = _
    rw [Category.comp_id, Category.assoc]
    exact (congrArg (D.P.A.hom ≫ ·) (Spec (CommRingCat.of R)).topIso.inv_hom_id).trans (Category.comp_id _))
  have hmono : Mono W.hom := by
    show Mono (Scheme.Opens.ι ⊤ ≫ 𝟙 _)
    infer_instance
  have hu : snd (baseAt t) D.P.A ≫ lift u (𝟙 D.P.A) = homAt t ▷ D.P.A := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · refine Over.OverMorphism.ext ((cancel_mono W.hom).1 ?_)
      rw [Over.w, Over.w]
    · rw [Category.assoc, lift_snd, Category.comp_id]; exact (whiskerRight_snd (homAt t) D.P.A).symm
  obtain ⟨th, hth⟩ := exists_pull_val D.P.isLB (b hq.default) (lift u (𝟙 D.P.A)).left (φ' := D.famφB 0)
    (ε' := DegPre.famε 1) (fun U _ h => by
      rw [prod_fam_zero]
      have e : (lift u (𝟙 D.P.A)).left ≫ (snd W D.P.A).left = 𝟙 _ := congrArg CommaMorphism.left (lift_snd u (𝟙 D.P.A))
      simp only [Fin.prod_univ_one]
      erw [e]
      simp)
  refine ⟨th, (snd (baseAt t) D.P.A).left y, ?_, ?_⟩
  · have e : (snd (baseAt t) D.P.A).left ≫ D.P.A.hom = (fst (baseAt t) D.P.A).left ≫ spMap (residue R) := by
      rw [Over.w, ← ht]; exact (Over.w (fst (baseAt t) D.P.A)).symm
    refine (congrArg (fun q => q y) e).trans ?_
    exact PrimeSpectrum.comap_residue R _
  · obtain ⟨J, hJ⟩ := exists_good' D.P.isLB y
    have h₁ := hth _ (snd (baseAt t) D.P.A).left y J hJ
    have e : (snd (baseAt t) D.P.A).left ≫ (lift u (𝟙 D.P.A)).left = (homAt t ▷ D.P.A).left :=
      congrArg CommaMorphism.left hu
    rw [e] at h₁
    have hm : (homAt t ▷ D.P.A).left y ∈ nonzeroLocus (b hq.default) := by
      rw [hb' hq.default j, Scheme.basicOpen_res, ← Scheme.preimage_basicOpen] at hy
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hy.2⟩
    have hu' := isUnit_sval (b hq.default) _ y hm hJ
    rw [← h₁] at hu'
    exact (SectionBaseChange.mem_nonzeroLocus th _).2 ⟨_, hJ.mem _ _, (isUnit_gs_iff _ y _ (hJ.mem _ _) _).1 hu'⟩

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G]

theorem nonzero_and_spans (hG : GlobalFnsSt) (hS : SecBaseChangeSt) [IsNoetherianRing R] (hI : I ≤ maximalIdeal R)
    (U : Unif I D A G) {ϑ : H0 U.LG.L 1} (hϑ : IsTheta U ϑ) :
    (∃ g, G.hom g = closedPoint R ∧ g ∈ nonzeroLocus ϑ) ∧ ∀ σ : H0 U.LG.L 1, ∃ b : R, SecIsMul G.hom b σ ϑ := by
  obtain ⟨sK, hsK⟩ := exists_pull_val U.LG.isLB ϑ (pullback.fst G.hom (jK R))
    (φ' := fun _ : Fin 1 => pullback.fst G.hom (jK R)) (ε' := fun _ => ((1 : ℕ) : ℤ))
    (fun U _ h => by simp only [Category.comp_id])
  obtain ⟨E, hE, -⟩ := (U.expand 1 le_rfl).1 sK
  obtain ⟨g, hg, hgE⟩ := IntegralExpansionLocal.main R I hI D A G U.toUnifPre 1 ϑ sK
    (SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => (hsK _ _ y J hJ).symm) E hE
  obtain ⟨f, hf, hgen⟩ := hϑ 0
  obtain ⟨th, x, hx, hn⟩ := exists_nonzero_closed hS D.toPre
  obtain ⟨y, rfl⟩ := exists_group_pt hI U.toUnifPre 0 x hx
  obtain ⟨J, hJ⟩ := exists_good' D.toPre.P.isLB y
  obtain ⟨c, hc, -⟩ := hgen th
  have hfu : IsUnit (sval (f 0) (pGl U.toUnifPre 0) y J) := by
    have := isUnit_sval th _ y hn hJ
    rw [sval_of_secIsMul hc _ y hJ] at this
    exact isUnit_of_mul_isUnit_right this
  obtain ⟨a, ha, -⟩ := hgen (g 0)
  let g' : ∀ α, SecBMod D.toPre 1 α := g
  let f' : ∀ α, SecBMod D.toPre 1 α := f
  let θ : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ))) := ϑ
  have hE₀ := expandsAt_add U.toUnifPre (σ := θ) (f := g') (hg 0) (expandsAt_smul U.toUnifPre (-1 : R) (σ := θ) (f := f') hf)
  have h₁ := WeightDvd.dvd_on_group U.toUnifPre 0 1 0 _ θ _ ((secIsMul_iff _ _ _ _).2
    (by rw [neg_one_smul, add_neg_cancel, zero_smul])) hE₀ 0 y J hJ
  have h₂ : (g' + (-1 : R) • f') 0 = (a - 1) • f' 0 := by
    rw [Pi.add_apply, Pi.smul_apply, sub_smul, sub_eq_add_neg, neg_smul, ← (secIsMul_iff _ _ (g' 0) (f' 0)).1 ha]
  rw [h₂, GermDiv.cst_zero, zero_dvd_iff, sval_of_secIsMul ((secIsMul_iff _ _ _ _).2 rfl) _ y hJ,
    hfu.mul_left_eq_zero, cst_sub, cst_one', sub_eq_zero] at h₁
  have hgu : IsUnit (sval (g 0) (pGl U.toUnifPre 0) y J) := by
    rw [sval_of_secIsMul ha _ y hJ, h₁, _root_.one_mul]; exact hfu
  have h0 : ∃ x, D.toPre.P.A.hom x = closedPoint R ∧ x ∈ nonzeroLocus (g 0) :=
    ⟨_, hx, (SectionBaseChange.mem_nonzeroLocus _ _).2 ⟨_, hJ.mem _ _, (isUnit_gs_iff _ y _ (hJ.mem _ _) _).1 hgu⟩⟩
  refine ⟨exists_mem_nonzeroLocus hI U.toUnifPre (hg 0) h0 (LevelOneIdeal.main hG R I D E g hgE), fun σ => ?_⟩
  obtain ⟨b, hb⟩ := exists_eq_smul_group hG hI U (σ := θ) (f := g') hg
    (fun α => (secScal_one_iff D.toPre E α _).1 (hgE α)) (exists_eq_smul hS D.toPre _ h0) σ
  exact ⟨b, (secIsMul_iff _ _ _ _).2 hb⟩

theorem unit_mul_iff_nonzero (hG : GlobalFnsSt) (hS : SecBaseChangeSt) [IsNoetherianRing R] (hI : I ≤ maximalIdeal R)
    (U : Unif I D A G) {ϑ : H0 U.LG.L 1} (hϑ : IsTheta U ϑ) (σ : H0 U.LG.L 1) :
    (∃ u : Rˣ, SecIsMul G.hom (u : R) σ ϑ) ↔ NonzeroOnSpecial U σ := by
  obtain ⟨⟨g, hg, hn⟩, hsp⟩ := nonzero_and_spans hG hS hI U hϑ
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨J, hJ⟩ := exists_good' U.LG.isLB g
    have e := sval_of_secIsMul hu (𝟙 _) g hJ
    have hc : IsUnit (cst (𝟙 _ ≫ G.hom) g u.val) :=
      IsUnit.of_mul_eq_one (cst (𝟙 _ ≫ G.hom) g u⁻¹.val) (by rw [← cst_mul', u.mul_inv, cst_one'])
    exact nonzeroOnSpecial_of_mem U σ g hg ((SectionBaseChange.mem_nonzeroLocus σ _).2 ⟨_, hJ.mem _ (𝟙 _),
      (e ▸ hc.mul (isUnit_sval ϑ (𝟙 _) g hn hJ) : IsUnit (sval σ _ g J))⟩)
  · intro h
    obtain ⟨b, hb⟩ := hsp σ
    obtain ⟨u, rfl⟩ := isUnit_of_nonzeroOnSpecial U hb h
    exact ⟨u, hb⟩

theorem spans_iff_nonzero (hG : GlobalFnsSt) (hS : SecBaseChangeSt) [IsNoetherianRing R] (hI : I ≤ maximalIdeal R)
    (U : Unif I D A G) {ϑ : H0 U.LG.L 1} (hϑ : IsTheta U ϑ) (σ : H0 U.LG.L 1) :
    (∀ s : H0 U.LG.L 1, ∃ b : R, SecIsMul G.hom b s σ) ↔ NonzeroOnSpecial U σ := by
  have h₁ : NonzeroOnSpecial U ϑ := (unit_mul_iff_nonzero hG hS hI U hϑ ϑ).1
    ⟨1, (secIsMul_iff _ _ _ _).2 (one_smul R _).symm⟩
  obtain ⟨-, hsp⟩ := nonzero_and_spans hG hS hI U hϑ
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h ϑ
    obtain ⟨c, hc⟩ := hsp σ
    have hu := isUnit_of_nonzeroOnSpecial U (IntegralExpansion.SecIsMul.comp hb hc) h₁
    obtain ⟨u, rfl⟩ := isUnit_of_mul_isUnit_right hu
    exact (unit_mul_iff_nonzero hG hS hI U hϑ σ).1 ⟨u, hc⟩
  · intro h s
    obtain ⟨u, hu⟩ := (unit_mul_iff_nonzero hG hS hI U hϑ σ).2 h
    obtain ⟨b, hb⟩ := hsp s
    refine ⟨b * u⁻¹.val, (secIsMul_iff _ _ _ _).2 ?_⟩
    refine ((secIsMul_iff _ _ _ _).1 hb).trans (Eq.symm ?_)
    refine (congrArg _ ((secIsMul_iff _ _ _ _).1 hu)).trans ((smul_smul _ _ _).trans ?_)
    rw [Units.inv_mul_cancel_right]

theorem exists_isTheta_of_dvr (hLaws : Laws) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V))))
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) :
    ∃ ϑ : H0 U.LG.L 1, IsTheta U ϑ ∧ ∀ s : H0 U.LG.L 1, ∃ b : V, SecIsMul G.hom b s ϑ := by
  have hG := hLaws.globalFns
  obtain ⟨th, hth⟩ := exists_nonzero_closed hLaws.secBaseChange D.toPre
  obtain ⟨Φ, hΦ, -⟩ := FamFree.exists_fam_single (F := FractionRing V) hG D.tau_bimult le_rfl 0
    (resF D.toPre (FractionRing V) 1 0 th)
  have h₀ := (secScal_one_iff D.toPre Φ 0 th).2 hΦ.symm
  have ex : ∀ α, ∃ g : D.toPre.SecB 1 α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α)
      (DegPre.famε 1) (Φ.s α) (D.toPre.famφB α) (DegPre.famε 1) g (DegPre.prB D.toPre (FractionRing V)).left 1 :=
    fun α => by
      by_cases hα : α = 0
      · subst hα
        exact ⟨th, h₀⟩
      · obtain ⟨a, -, g, g', -, h₂⟩ := exists_integral_term hG D Φ th h₀ α hα
        exact ⟨g, h₂⟩
  choose fam hfam using ex
  obtain rfl : fam 0 = th := resF_injective D.toPre (FractionRing V) 1 0
    (((secScal_one_iff D.toPre Φ 0 _).1 (hfam 0)).trans hΦ)
  obtain ⟨σ, hσ⟩ := IntegralExpansion.main hLaws V D A G U 1 le_rfl Φ fam hfam
  obtain ⟨g, hg, hn⟩ := exists_mem_nonzeroLocus le_rfl U.toUnifPre (hσ 0) hth
    (LevelOneIdeal.main hG V _ D Φ fam hfam)
  have h := ThetaLocalDomain.main hLaws V _ le_rfl D A G U σ (nonzeroOnSpecial_of_mem U σ g hg hn)
  exact ⟨σ, h, (nonzero_and_spans hG hLaws.secBaseChange le_rfl U h).2⟩

end GlobalTheory.ThetaSectionTest
