import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegDataPsiOfSectionNonzeroFibres
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibrewiseNonzeroSectionProdAndBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfMemAdjoinInv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationCompleteDVR
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OverExtOfPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraMore

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.LN GlobalTheory.PsiRing

noncomputable section
namespace GlobalTheory.SectionUnif

theorem exists_shift {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R) {q : R} (hq : q ≠ 0) :
    ∃ c : ℕ, ∀ (n : ℕ) (a : R), q * a ∈ I ^ (n + c) → a ∈ I ^ n := by
  first
  | exact @_root_.GlobalTheory.ClosingLemmaSecond.main
  | exact _root_.GlobalTheory.ClosingLemmaSecond.main
  | (apply _root_.GlobalTheory.ClosingLemmaSecond.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClosingLemmaSecond.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClosingLemmaSecond.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClosingLemmaSecond.main ..)

section
variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {I : Ideal R} {I' : Ideal V}
  {D : DegPre R} {D' : DegPre V} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {G' : Over (Spec (CommRingCat.of V))} [GrpObj G']
  [IsCommMonObj G']

theorem exists_term_ne_zero [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥) (U : PreU I D A G) (k : ℕ)
    (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α) (hf : U.ExpT (𝟙_ _) k σ f) (y : (𝟙_ _ ⊗ G).left)
    (hy : y ∈ nonzeroLocus σ) : ∃ α j, (f α).f j ≠ 0 := by
  by_contra h0
  push Not at h0
  have := U.semi.smooth
  have := U.semi.geomConnected
  have hL := U.P.L.isLB
  have lam : (snd (𝟙_ _) G).left ≫ (λ_ G).inv.left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]
  obtain ⟨s, hs⟩ := BaseExpansionExists.exists_pull (λ_ G).inv.left (fun _ => rfl) σ
  have h₀ := (sec_eq_zero_and_hom_eq_of_thickenings R I hI G).1 _ (DVR.linComb_isLB _ hL _ _) s
    fun e j => fn_ext fun z hz => by
      have hz' : (𝟙 (thickObj R I e G).left : _ ⟶ _) z ∈ (fstG I e G).left ⁻¹ᵁ _ := hz
      refine (gs_pull (𝟙 _) (fstG I e G).left z _ hz' _).trans (Eq.trans ?_ ((gs_eq (𝟙 _) z _ hz' _).trans
        ((congrArg _ (map_zero _)).trans (map_zero _))).symm)
      refine ExpUniq.gs_eq_zero_of_sval hL s _ z (fun JG hJG => (hs _ _ z JG hJG).trans ?_) j hz'
      let T : Over (Spec (CommRingCat.of R)) := (Over.map (thick R I e)).obj (thickObj R I e G)
      let b : T ⟶ D.P.A := (U.gt e).pG
      let x : T ⟶ G := fstG I e G
      have hG : (lift (toUnit T) x).left ≫ (snd _ G).left = x.left := by rw [← Over.comp_left, lift_snd]
      have hB : (lift (toUnit T) b).left ≫ (snd _ D.P.A).left = b.left := by rw [← Over.comp_left, lift_snd]
      have hF : (lift (toUnit T) b).left ≫ (fst _ D.P.A).left = (lift (toUnit T) x).left ≫ (fst _ G).left := by
        rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
      have hi : lift (toUnit T) x = x ≫ (λ_ G).inv := by ext1 <;> simp [toUnit_unique]
      have hi' : (lift (toUnit T) x).left = (𝟙 _ ≫ (fstG I e G).left) ≫ (λ_ G).inv.left := by
        rw [hi, Category.id_comp]; rfl
      obtain ⟨J, hJ⟩ := exists_good_pt (Z := T.left) D.P.isLB z
      obtain ⟨t, ht⟩ := hf e
      obtain ⟨-, hsum⟩ := ht T.left (𝟙 _) _ _ (hG.trans (Category.id_comp _).symm)
        (hB.trans (Category.id_comp _).symm) hF z JG J hJG hJ
      rw [Finset.sum_eq_zero fun α _ => by
        rw [ThetaScalar.sval_eq_zero _ (h0 α) _ z hJ, MulZeroClass.zero_mul]] at hsum
      rw [← hi']
      exact (((Units.isUnit _).pow k).mul_right_eq_zero).1 hsum
  obtain ⟨J, hJ⟩ := exists_good_pt hL y
  have E := (hs _ (snd (𝟙_ _) G).left y J hJ).symm.trans (ThetaScalar.sval_eq_zero _ h₀ _ y hJ)
  rw [lam] at E
  have u := (MulPullSec.mem_nonzeroLocus_iff σ (𝟙 _) y hJ).1 hy
  rw [E] at u
  exact not_isUnit_zero u

theorem exists_sec_point (U : PreU I D A G) (θ : LB.Sec U.P.L.L) (k : U.P.L.L.ι) (hθ : θ.f k ≠ 0) :
    ∃ (σ : U.SecGT (𝟙_ _) 1) (y : (𝟙_ _ ⊗ G).left), y ∈ nonzeroLocus σ := by
  have := U.semi.smooth
  have : IsReduced G.left := isReduced_of_smooth_of_isReduced G.hom
  have := FibreNonzero.isIso_snd_left G
  have h : G.left.basicOpen (θ.f k) ≠ ⊥ := fun h => hθ ((basicOpen_eq_bot_iff _).1 h)
  obtain ⟨g, hg⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 h
  obtain ⟨z, rfl⟩ := (snd (𝟙_ _) G).left.surjective g
  exact ⟨FibreNonzero.pullOne θ _, z, FibreNonzero.mem_nonzeroLocus_pullOne θ _ z k hg⟩

theorem exists_point_of_cmp {φ : R →+* V} (hφ : Function.Injective φ) {U : PreU I D A G} {U' : PreU I' D' A' G'}
    {F : G'.left ⟶ G.left} (C : Cmp φ U U' F) (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (σ' : U'.SecGT (𝟙_ _) k)
    (h : ∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left),
      r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' →
      sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ k *
        sval σ' r' z J') (y : (𝟙_ _ ⊗ G).left) (hy : y ∈ nonzeroLocus σ) : ∃ y', y' ∈ nonzeroLocus σ' := by
  have := U.semi.smooth
  have := FibreNonzero.isIso_snd_left G
  have := FibreNonzero.isIso_snd_left G'
  have : IsSchemeTheoreticallyDominant (spMap φ) := schDom_spec_map φ hφ
  have : IsSchemeTheoreticallyDominant F := .of_isPullback C.pb.1.flip
  have : QuasiCompact F := MorphismProperty.of_isPullback C.pb.1.flip inferInstance
  let r : (𝟙_ _ ⊗ G').left ⟶ (𝟙_ _ ⊗ G).left := (snd (𝟙_ _) G').left ≫ F ≫ inv (snd (𝟙_ _) G).left
  have hr : r ≫ (snd _ G).left = 𝟙 _ ≫ (snd _ G').left ≫ F := by simp [r]
  have : IsDominant r := by unfold r; infer_instance
  obtain ⟨z', hz'⟩ := r.denseRange.exists_mem_open (nonzeroLocus σ).isOpen ⟨y, hy⟩
  obtain ⟨J, hJ⟩ := exists_good_pt U.P.L.isLB z'
  obtain ⟨J', hJ'⟩ := exists_good_pt U'.P.L.isLB z'
  have u := (MulPullSec.mem_nonzeroLocus_iff σ r z' hJ).1 hz'
  rw [h _ (𝟙 _) r hr z' J J' hJ hJ'] at u
  exact ⟨z', (MulPullSec.mem_nonzeroLocus_iff σ' (𝟙 _) z' hJ').2 (isUnit_of_mul_isUnit_right u)⟩

end

theorem ne_zero_and_psiCmp (h₁ : Laws) (h₂ : Laws2) {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]
    [IsLocalRing V] {I : Ideal R} (hV : CDvr V) {φ : R →+* V} (hφ : Function.Injective φ) {D : DegPre R}
    {D' : DegData V (IsLocalRing.maximalIdeal V)} {A : PolAV (Sp (FractionRing R))} {A' : PolAV (Sp (FractionRing V))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {G' : Over (Spec (CommRingCat.of V))} [GrpObj G']
    [IsCommMonObj G'] {U : PreU I D A G} {U' : PreU (IsLocalRing.maximalIdeal V) D'.toPre A' G'}
    {U₀ : Unif (IsLocalRing.maximalIdeal V) D' A' G'} {F : G'.left ⟶ G.left} (C : Cmp φ U U' F)
    (hU : Under U' U₀.toUnifPre) (σ : U.SecGT (𝟙_ _) 1) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (hf : U.ExpT (𝟙_ _) 1 σ f)
    (y : (𝟙_ _ ⊗ G).left) (hy : y ∈ nonzeroLocus σ) :
    (∀ α, ∃ j, (f α).f j ≠ 0) ∧ ∀ psi h, PsiRel (withPsi D psi h) (𝟙_ _) f →
      RigCmp φ (withPsi D psi h) D'.toPre C.β C.v ∧ ∃ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ ∧
        PsiCmp (withPsi D psi h) D'.toPre C.β C.v C.xe gam := by
  have := hV.1
  have hV' : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  have hm : IsLocalRing.maximalIdeal V ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal V).ne_top
  obtain ⟨σ', f', hf', hσσ, hff⟩ := ExpCmp.expT_cmp R V I _ φ C.map_le D D'.toPre A A' G G' U U' F C 1 σ f hf
  have hcmp : SecCmp D D'.toPre C.β C.v C.xe f f' := hff
  have hrel' := GlobalTheory.T.psiRel_of_expT' h₁ h₂ V _ hV' D' A' G' U' U₀ hU σ' f' hf'
  obtain ⟨y', hy'⟩ := exists_point_of_cmp hφ C 1 σ σ' hσσ y hy
  have hne' : ∀ α, ∃ j, (f' α).f j ≠ 0 := GlobalTheory.T.forall_term_ne_zero_of_psiRelation V D'.toPre f' hrel'
    (exists_term_ne_zero (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge U' 1 σ' f' hf' y' hy')
  refine ⟨ne_zero_of_secCmp C.pbB.1.w hcmp hne', fun psi h hrel => ?_⟩
  have hrig : RigCmp φ (withPsi D psi h) D'.toPre C.β C.v :=
    GlobalTheory.T.rigidification_comparison_uniformisation R V I _ φ hm C.map_le D D'.toPre A G A' G' U U' F C
  obtain ⟨gam, hgam⟩ := exists_generic_map hφ
  exact ⟨hrig, gam, hgam, GlobalTheory.T.psiCmp_of_secCmp' R V φ (withPsi D psi h) D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig f f' hcmp
    hrel hrel' (hne' 0) gam hgam⟩

set_option maxHeartbeats 1600000 in

theorem exists_cmp {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} (hR : AdmBase R I)
    {D : DegPre R} {A : PolAV (Sp (FractionRing R))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    (U : PreU I D A G) (hW : HypW G U.P.L.L) (hsp : SplitOver G I)
    (hA : LBIso (A.L.pull U.gen.hom.left) (U.P.L.L.pull (pullback.fst G.hom (jK R))))
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V) (hV : CDvr V) (hφ : Function.Injective φ)
    (hc : (IsLocalRing.maximalIdeal V).comap φ = I) :
    ∃ (D' : DegData V (IsLocalRing.maximalIdeal V)) (A' : PolAV (Sp (FractionRing V)))
      (G' : Over (Spec (CommRingCat.of V))) (_ : GrpObj G') (_ : IsCommMonObj G') (F : G'.left ⟶ G.left)
      (U₀ : Unif (IsLocalRing.maximalIdeal V) D' A' G') (U' : PreU (IsLocalRing.maximalIdeal V) D'.toPre A' G'),
      Under U' U₀.toUnifPre ∧ Nonempty (Cmp φ U U' F) := by
  obtain ⟨hL, hL2, hL3, -⟩ := GlobalTheory.allSixLaws
  have := hV.1
  have := U.gen_hom
  have hB : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  have hle : I.map φ ≤ IsLocalRing.maximalIdeal V := Ideal.map_le_iff_le_comap.2 hc.ge
  obtain ⟨A', s, w, hw⟩ := PrimeUnif.exists_setting hL hL2 hL3 U.P U.semi hW hsp A U.gen hA hV φ hφ hc.ge
  obtain ⟨D', U₀, hLG, -, -⟩ := GlobalTheory.uniformisation_dvr_unconditional V A' _ s
  obtain ⟨U', hU'⟩ := (GlobalTheory.LN.PreForm.under_exists_and_expands hL hL2 V _ D' A' _ s.semi).1 U₀.toUnifPre
  have := s.semi.smooth
  obtain ⟨w', hw'⟩ := PrimeUnif.isCPMap_of_eq hL.globalFns s.gen s.P U'.P (hU'.2.1.trans hLG) hw
  obtain ⟨C, -⟩ := GlobalTheory.T.exists_compare_uniformisationData_pullback hL hL2 ega_holds R V I _ hR hB (IsLocalRing.maximalIdeal.isMaximal V).ne_top φ hle D _ A A'
    G _ U U' _ (isGrpPullback_pullback G _) w' hw'
  exact ⟨D', A', _, _, _, _, U₀, U', hU', ⟨C⟩⟩

set_option maxHeartbeats 1600000 in

theorem exists_unif_of_ne_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.admitted R (IsLocalRing.maximalIdeal R) → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → GlobalTheory.LN.SplitOver G (IsLocalRing.maximalIdeal R) → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → (∃ (σ : LB.Sec P.L.L) (k : P.L.L.ι), σ.f k ≠ 0) → ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (U : Unif (IsLocalRing.maximalIdeal R) D A G), U.LG = P.L ∧ U.gen = gen := by
  intro R _ _ _ hR G _ _ P hS hW hsp A gen hgen hA ⟨θ, k, hθ⟩
  obtain ⟨h₁, h₂, h₃, -⟩ := GlobalTheory.allSixLaws
  have := hR.1.1
  have := hR.1.2.2.1
  have := hR.2.2.1
  have hI : IsLocalRing.maximalIdeal R ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have hpi : IsPrincipalIdealRing (R ⧸ IsLocalRing.maximalIdeal R) := by
    letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
    infer_instance
  obtain ⟨D, U, rfl, rfl⟩ := GlobalTheory.T.exists_uniformization_data_complete_local_prime h₁ h₂ h₃ ega_holds GlobalTheory.uniformisation_dvr_unconditional R _ hR hpi G P hS hW hsp
    A gen hgen hA
  obtain ⟨σ, y, hy⟩ := exists_sec_point U θ k hθ
  obtain ⟨f, hf, -⟩ := CompleteBaseExpansion.main h₁ h₂ ega_holds R _ hR.1 hI D A G U 1 σ
  obtain ⟨V, _, _, _, φ, hV, hφ, hc⟩ := PrimeUnif.exists_cdvr R (IsLocalRing.maximalIdeal R)
  obtain ⟨D', A', G', _, _, F, U₀, U', hU', ⟨C⟩⟩ := exists_cmp hR.1 U hW hsp hA V φ hV hφ hc
  obtain ⟨hne, hps⟩ := ne_zero_and_psiCmp h₁ h₂ hV hφ C hU' σ f hf y hy
  obtain ⟨psi, h, hrel⟩ := exists_psi_psiRel h₁ h₂ R D f hne
  let E : DegPre R := withPsi D psi h
  have hrelE : PsiRel E (𝟙_ _) f := hrel
  obtain ⟨hrig, gam, hgam, hpsi⟩ := hps psi h hrel
  have hev : E.PsiEven :=
    GlobalTheory.T.psiEven_descend_baseChange h₁.globalFns R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr gam hgam hpsi D'.psi_even
  have hbi : E.TauBimult :=
    GlobalTheory.T.tauBimult_of_baseChange' h₁.globalFns R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig gam hgam hpsi D'.tau_bimult
  obtain ⟨hD, hD₁, hD₂, hD₃⟩ :=
    GlobalTheory.T.exists_isPullDeg_of_comparison R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig gam hgam hpsi hbi
  obtain ⟨ga, a, hSc⟩ := exists_psiScal R E
  obtain ⟨th, hth, hmul⟩ := GlobalTheory.T.exists_thetaSection_nonzeroFibres_localRing h₂.secTwist R D
  obtain ⟨q, hq⟩ := hmul (f 0)
  choose b hb using fun χ : D.X => GlobalTheory.T.exists_twistedSection_thetaTranslate_coef R D th hmul χ (ga χ) (hSc χ).1 (f χ)
  have hab : ∀ χ, algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) (b χ) := fun χ =>
    GlobalTheory.T.psiScalar_eq_expansionCoef_ratio R E ga a f th hSc hrelE hth χ q (b χ) hq (hb χ)
  have hq0 : q ≠ 0 := by
    rintro rfl
    obtain ⟨j, hj⟩ := hne 0
    refine hj (ThetaScalar.eq_zero_of_sval D.P.isLB _ (fun z J hJ => ?_) j)
    rw [hq _ _ z J hJ, Geo.Tor.cst, map_zero, gs_eq _ _ ⊤ trivial, map_zero, map_zero, MulZeroClass.zero_mul]
  have hW' : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (g : R →+* W), CDvr W → Function.Injective g →
      (IsLocalRing.maximalIdeal W).comap g = IsLocalRing.maximalIdeal R → ∀ χ : D.X, χ ≠ 0 →
      ∃ m ∈ IsLocalRing.maximalIdeal W, g (b χ) = g q * m := fun W _ _ _ g hW₁ hg hgc χ hχ => by
    obtain ⟨D₁, A₁, G₁, _, _, F₁, U₁, U₂, hU₁, ⟨C₁⟩⟩ := exists_cmp hR.1 U hW hsp hA W g hW₁ hg hgc
    obtain ⟨-, gam₁, hgam₁, hpsi₁⟩ := (ne_zero_and_psiCmp h₁ h₂ hW₁ hg C₁ hU₁ σ f hf y hy).2 psi h hrel
    obtain ⟨x, rfl⟩ := C₁.xe.surjective χ
    exact GlobalTheory.T.psiScalar_mem_of_psi_mem_ideal R W g E D₁.toPre C₁.β C₁.v C₁.xe C₁.pbB C₁.v_gen C₁.c_pr gam₁ hgam₁ hpsi₁ ga a hSc x _
      (D₁.psi_pos x fun h0 => hχ (by rw [h0, map_zero])) _ q (hab _)
  have hdiv : ∀ χ : D.X, χ ≠ 0 → ∃ r ∈ IsLocalRing.maximalIdeal R, b χ = q * r := fun χ hχ => by
    obtain ⟨r, hr⟩ := ValCrit.dvd_of_forall_cdvr R (b χ) q hq0 fun W _ _ _ g hW₁ hg hgc =>
      (hW' W g hW₁ hg hgc χ hχ).elim fun m hm => ⟨m, hm.2⟩
    obtain ⟨m, hm₁, hm₂⟩ := hW' V φ hV hφ hc χ hχ
    rw [hr, map_mul] at hm₂
    refine ⟨r, hc.le (Ideal.mem_comap.2 ?_), hr⟩
    rwa [mul_left_cancel₀ ((map_ne_zero_iff φ hφ).2 hq0) hm₂]
  have hin : ∀ (χ : D.X) (J : Ideal R) (r : R), r ∈ J → b χ = q * r → E.PsiIn χ J := fun χ J r hJ e =>
    (PsiScalIn.main_local E ga a hSc χ J).2 ⟨r, hJ, mul_left_cancel₀
      ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hq0) (((map_mul _ q r).symm.trans (congrArg _ e.symm)).trans (hab χ).symm)⟩
  obtain ⟨c, hcs⟩ := exists_shift (IsLocalRing.maximalIdeal R) hq0
  let Dd : DegData R (IsLocalRing.maximalIdeal R) :=
    ⟨E, hev, hbi, fun χ hχ => (hdiv χ hχ).elim fun r hr => hin χ _ r hr.1 hr.2, fun n => by
      classical
      obtain ⟨s, hs⟩ := GlobalTheory.T.expansionCoef_mem_adic_pow R _ hI D A G U σ f th hf hth (n + c)
      refine (insert 0 s).finite_toSet.subset fun χ hχ => ?_
      by_contra hn
      rw [Finset.mem_coe, Finset.mem_insert, not_or] at hn
      obtain ⟨r, -, hr⟩ := hdiv χ hn.1
      exact hχ (hin χ _ r (hcs n r (hr ▸ Ideal.pow_le_pow_right (Nat.le_succ _) (hs χ hn.2 _ _ (hb χ)))) hr)⟩
  have := hV.1
  have hB : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  obtain ⟨U₂, C₂, hD₄, eP, eg, k₁, k₂, k₃⟩ := PrimeUnif.exists_move psi h C hD Dd.toPre rfl hD₁ hD₂ hD₃
  obtain ⟨U₁, -, hU₁, -⟩ := GlobalTheory.UnifDescent.exists_unif_of_cmp h₁ h₂ ega_holds R V _ _ hR.1 hB hI φ hφ C.map_le Dd D' A A'
    G _ U₂ U' U₀ _ C₂ hD₄ hU' k₁ k₂ k₃
  exact ⟨Dd, U₁, hU₁.2.1.symm.trans (congrArg CP.L eP), hU₁.1.symm.trans eg⟩

end GlobalTheory.SectionUnif
end
