import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingAndIsRelParam
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem lbIso_pull_both {X X' Y Z : Scheme.{0}} {L : LB X} {M : LB X'} {a : Y ⟶ X} {b : Y ⟶ X'}
    (h : LBIso (L.pull a) (M.pull b)) (j : Z ⟶ Y) {a' : Z ⟶ X} {b' : Z ⟶ X'} (ea : a' = j ≫ a) (eb : b' = j ≫ b) :
    LBIso (L.pull a') (M.pull b') :=
  LBIso.chartPull (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => ea)
    (Geo.Tor.chartPullSame M _ (fun _ => b) _ j fun _ => eb) h

theorem isSquare_eq {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ φ' : G'.left ⟶ G.left}
    {a b : (G' ⊗ G').left ⟶ (G ⊗ G).left} (ha : IsSquare φ a) (hb : IsSquare φ' b) (e : φ = φ') : a = b := by
  subst e
  apply pullback.hom_ext
  · exact ha.1.trans hb.1.symm
  · exact ha.2.trans hb.2.symm

set_option backward.isDefEq.respectTransparency false in

theorem IsMumPol.exists_isMumfordFam {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {R : Type} [CommRing R]
    [IsDomain R] [IsLocalRing R] {Q : Data R} {G₁ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] {P : LB (G2 G₁).left}
    (h : IsMumPol Q G₁ P) {T : Scheme.{0}} {i : T ⟶ Sp R} {l : Sp (FractionRing R) ⟶ T} (hl : l ≫ i = jK R)
    {A₀ : Over T} [GrpObj A₀] [IsCommMonObj A₀] {P₀ : LB (G2 A₀).left} (hP₀ : P₀.IsLB)
    {a : A₀.left ⟶ G₁.left} {a₂ : (G2 A₀).left ⟶ (G2 G₁).left} (ha : IsGrpPullback A₀ G₁ i a) (ha₂ : IsSquare a a₂)
    (hPa : LBIso P₀ (P.pull a₂)) {yU : T ⟶ F.X} {φ : A₀.left ⟶ F.univ.A.left} {φ₂ : (G2 A₀).left ⟶ (G2 F.univ.A).left}
    (hφ : IsGrpPullback A₀ F.univ.A yU φ) (hφ₂ : IsSquare φ φ₂) (hPφ : LBIso P₀ (F.univ.P.pull φ₂)) :
    ∃ α₁ : pullback G₁.hom (jK R) ⟶ F.univ.A.left, IsGenFibre F (l ≫ yU) α₁ ∧ IsMumfordFam F (l ≫ yU) α₁ Q := by
  obtain ⟨hR, hpos, -, hbi, hU⟩ := h
  have w : pullback.fst G₁.hom (jK R) ≫ G₁.hom = (pullback.snd G₁.hom (jK R) ≫ l) ≫ i := by
    rw [Category.assoc, hl, pullback.condition]
  obtain ⟨ω, ω₁, ω₂⟩ : ∃ ω : pullback G₁.hom (jK R) ⟶ A₀.left, ω ≫ a = pullback.fst G₁.hom (jK R) ∧
      ω ≫ A₀.hom = pullback.snd G₁.hom (jK R) ≫ l := ⟨ha.1.lift _ _ w, ha.1.lift_fst _ _ w, ha.1.lift_snd _ _ w⟩
  have h₁ := isGrpPullback_pullback G₁ (jK R)
  have hω : IsGrpPullback ((Over.pullback (jK R)).obj G₁) A₀ l ω := ha.cancel (h₁.congr hl.symm ω₁.symm) ω₂
  refine ⟨ω ≫ φ, hω.comp hφ, hR, hpos, fun R' _ _ _ ρ hR' hρ hf D ε hD => ?_⟩
  obtain ⟨G', _, _, π, π₂, A, U, hπ, hπ₂, hL⟩ := hU R' ρ hR' hρ hf D ε hD
  obtain ⟨κ, hκ⟩ := exists_genericMap hρ
  letI := A.isAb.comm
  have w' : (pullback.fst G'.hom (jK R') ≫ π) ≫ G₁.hom = (pullback.snd G'.hom (jK R') ≫ κ) ≫ jK R := by
    rw [Category.assoc, hπ.1.w, Category.assoc, hκ, pullback.condition_assoc]
  obtain ⟨πK, p₁, p₂⟩ : ∃ πK : pullback G'.hom (jK R') ⟶ pullback G₁.hom (jK R),
      πK ≫ pullback.fst G₁.hom (jK R) = pullback.fst G'.hom (jK R') ≫ π ∧
      πK ≫ pullback.snd G₁.hom (jK R) = pullback.snd G'.hom (jK R') ≫ κ :=
    ⟨pullback.lift _ _ w', pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have h₂ := isGrpPullback_pullback G' (jK R')
  have hπK : IsGrpPullback ((Over.pullback (jK R')).obj G') ((Over.pullback (jK R)).obj G₁) κ πK :=
    h₁.cancel ((h₂.comp hπ).congr hκ.symm p₁.symm) p₂
  haveI := U.gen_hom
  haveI : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have hi := isGrpPullback_of_iso U.gen.symm
  have e₁ : U.gen.hom.left ≫ U.gen.symm.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.symm_hom, U.gen.hom_inv_id, Over.id_left]
  have e₂ : U.gen.symm.hom.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.symm_hom, U.gen.inv_hom_id, Over.id_left]
  have hβ := hi.comp (hπK.comp hω)
  have hδ := hi.comp h₂
  obtain ⟨β₂, hβ₂⟩ : ∃ β₂, IsSquare _ β₂ := ⟨_, GlobalTheory.LamPull.exists_isSquare hβ.1.w⟩
  obtain ⟨δ₂, hδ₂⟩ : ∃ δ₂, IsSquare _ δ₂ := ⟨_, GlobalTheory.LamPull.exists_isSquare hδ.1.w⟩
  have r : LBIso A.L (U.LG.L.pull (U.gen.symm.hom.left ≫ pullback.fst G'.hom (jK R'))) :=
    LBIso.trans A.isLB (pull_isLB A.isLB _) (pull_isLB U.LG.isLB _)
      (LBIso.chartPull (chartPullId A.L) (Geo.Tor.chartPullPull A.L (𝟙 _) (𝟙 _) rfl) (GlobalTheory.PolBaseChange.lbIso_refl A.isLB))
      (lbIso_pull_both U.ext U.gen.symm.hom.left e₂.symm rfl)
  have l₁ := GlobalTheory.LamPull.lbIso_lam_pull hδ U.LG.isLB A.isLB r hδ₂
  have i₁ : (abelian₂ G' U.LG.L).IsLB := DVR.linComb_isLB _ U.LG.isLB _ _
  have i₀ : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  have e₃ : β₂ ≫ a₂ = δ₂ ≫ π₂ := isSquare_eq (isSquare_comp hβ₂ ha₂) (isSquare_comp hδ₂ hπ₂) (by
    simp only [Category.assoc]
    rw [ω₁, p₁])
  have l₂ := lbIso_pull_comp hL δ₂ e₃
  have l₃ := (lbIso_pull_comp hPa β₂ rfl).symm
  have l₄ := lbIso_pull_comp hPφ β₂ rfl
  refine ⟨G', inferInstance, inferInstance, π, A, U, hπ, κ, πK, (U.gen.symm.hom.left ≫ πK ≫ ω) ≫ φ, β₂ ≫ φ₂, hκ, p₁,
    (hβ.comp hφ).congr (by simp only [Category.id_comp, Category.assoc]) rfl, isSquare_comp hβ₂ hφ₂,
    LBIso.trans i₀ (pull_isLB i₁ _) (pull_isLB F.univ.isLB _) l₁
      (LBIso.trans (pull_isLB i₁ _) (pull_isLB hbi.1 _) (pull_isLB F.univ.isLB _) l₂
        (LBIso.trans (pull_isLB hbi.1 _) (pull_isLB hP₀ _) (pull_isLB F.univ.isLB _) l₃ l₄)), ?_⟩
  simp only [Category.assoc]
  rw [← Category.assoc, e₁, Category.id_comp]

theorem dense_generic_away {o R : Type} [CommRing o] [CommRing R] [IsDomain R] {b : o →+* R} (hb : Function.Injective b)
    {f : R} (hf : f ≠ 0) :
    Dense {x : Sp (Localization.Away f) | (spMap ((algebraMap R (Localization.Away f)).comp b) x).asIdeal = ⊥} := by
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle
  have hinj : Function.Injective ((algebraMap R (Localization.Away f)).comp b) :=
    (IsLocalization.injective (Localization.Away f) hle).comp hb
  let p : PrimeSpectrum (Localization.Away f) := ⟨⊥, Ideal.isPrime_bot⟩
  have hp : Dense ({p} : Set (PrimeSpectrum (Localization.Away f))) := by
    rw [dense_iff_closure_eq, PrimeSpectrum.closure_singleton]
    simp [p]
  refine Dense.mono ?_ hp
  rintro x rfl
  exact (RingHom.injective_iff_ker_eq_bot _).1 hinj

set_option backward.isDefEq.respectTransparency false in

theorem Taut.exists_isFam_of_siegPre : ∀ (g n : ℕ) (φ : InvFun ℤ), 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) → ∀ c : SiegPre g n (zetaAway n) (spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b)), c.Principal → (∃ (a : c.A.left ⟶ G₁.left) (a₂ : (G2 c.A).left ⟶ (G2 G₁).left), IsGrpPullback c.A G₁ (spMap (algebraMap C.R (Localization.Away (∏ k, C.t k)))) a ∧ IsSquare a a₂ ∧ LBIso c.P (P.pull a₂)) → ∃ (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (yU : Sp (Localization.Away (∏ k, C.t k)) ⟶ F.X) (l : Localization.Away (∏ k, C.t k) →+* FractionRing C.R), C.IsFam F G₁ y α₁ ∧ SiegPB c F.univ yU ∧ l.comp (algebraMap C.R (Localization.Away (∏ k, C.t k))) = algebraMap C.R (FractionRing C.R) ∧ y = spMap l ≫ yU := by
  intro g n φ hn _ F C G₁ _ _ P hM hab c hc ⟨a, a₂, ha, ha₂, hPa⟩
  obtain ⟨-, -, hinj, -, hrel, -⟩ := Taut.isRegularLocalRing_and_isRelParam g n φ hn C
  have hf : ∏ k, C.t k ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ne_zero_of_isRelParam hrel i
  haveI : IsDomain (Localization.Away (∏ k, C.t k)) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  obtain ⟨yU, hs, hPB⟩ := F.rep _ _ c inferInstance (dense_generic_away hinj hf) hc
  have hu : IsUnit (algebraMap C.R (FractionRing C.R) (∏ k, C.t k)) :=
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective C.R _)).2 hf)
  let l : Localization.Away (∏ k, C.t k) →+* FractionRing C.R := IsLocalization.Away.lift _ hu
  have hl : l.comp (algebraMap C.R (Localization.Away (∏ k, C.t k))) = algebraMap C.R (FractionRing C.R) :=
    IsLocalization.Away.lift_comp _ hu
  have hl' : spMap l ≫ spMap (algebraMap C.R (Localization.Away (∏ k, C.t k))) = jK C.R := by
    rw [← Geo.Tor.spMap_comp, hl]
  obtain ⟨ψ, ψ₂, h₁, h₂, h₃, h₄⟩ := hPB
  obtain ⟨α₁, hα, hF⟩ := hM.exists_isMumfordFam F hl' c.isLB ha ha₂ hPa h₁ h₂ h₃
  refine ⟨spMap l ≫ yU, α₁, yU, l, ⟨hM.2.2.1, hab, hα, hF, ?_⟩, ⟨ψ, ψ₂, h₁, h₂, h₃, h₄⟩, hl, rfl⟩
  rw [Category.assoc, hs, Geo.Tor.spMap_comp, ← Category.assoc, hl']

end GlobalTheory.TChart
