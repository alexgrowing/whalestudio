import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShiftedNormalisation
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGenMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.PhiProj

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem val_scale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (c : Γ(Y, ⊤)ˣ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) :
    val (scaleGen c t) r z J = gm r z ⊤ c * val t r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) c) rfl)

def cUnit (ζ : F) (hζ : ζ ≠ 0) : Γ((TF (R := R) F).left, ⊤)ˣ :=
  ((Ne.isUnit hζ).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom).unit

theorem phiRel_of_ratio (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k) {w w' : Frm D F k p.g.b} (hw : w.IsGen)
    (hw' : w'.IsGen) (c : F) (hc : c ≠ 0)
    (hv : ∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = cst F z c * (val w (𝟙 _) z J).val)
    (s t : Fam D F k) (h : PhiRel D F k p w s t) : PhiRel D F k p w' s (c • t) := by
  have hcorr : LB.Gen.Corr D.P.L _ _ _ _ w' (scaleGen (cUnit (R := R) c hc) w) :=
    corr_of_val D.P.isLB fun z J hJ => Units.ext (by
      rw [hv z J hJ, val_scale hJ, Units.val_mul]
      exact congrArg₂ (· * ·) (gs_unit _ z ⊤ trivial (cUnit (R := R) c hc)) rfl)
  refine (phiRel_iff hG p w' hw' s _).2 fun a β hβ T ρ z J hJ => ?_
  have h1 := (phiRel_iff hG p w hw s t).1 h a β hβ T ρ z J hJ
  have hu : gs (ρ.left ≫ (fst (TF (R := R) F) D.P.A).left) z ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) =
      (gm (ρ ≫ fst (TF (R := R) F) D.P.A).left z ⊤ (cUnit (R := R) c hc)).val :=
    gs_unit _ z ⊤ trivial (cUnit (R := R) c hc)
  rw [sval_smul c t β ρ.left z hJ, h1, val_mul hJ, val_mul hJ, val_corr hJ hcorr, val_scale hJ, hu]
  simp only [Units.val_mul]
  ring

theorem exists_scaled {k : ℕ} {b : TF (R := R) F ⟶ D.P.A} {w : Frm D F k b} (hw : w.IsGen) (c : F) (hc : c ≠ 0) :
    ∃ w' : Frm D F k b, w'.IsGen ∧
      ∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = cst F z c * (val w (𝟙 _) z J).val := by
  refine ⟨scaleGen (cUnit (R := R) c hc) w, scaleGen_isGen _ w hw, fun z J hJ => ?_⟩
  rw [val_scale hJ, Units.val_mul]
  exact congrArg₂ (· * ·) (gs_unit _ z ⊤ trivial (cUnit (R := R) c hc)).symm rfl

theorem phiRel_of_equiv (hG : GlobalFnsSt) {k : ℕ} {p p' : QkPt D F k} (he : QkPt.Equiv D F p p')
    {w : Frm D F k p.g.b} (hw : w.IsGen) : ∃ w' : Frm D F k p'.g.b, w'.IsGen ∧
      ∀ s t, PhiRel D F k p w s t → PhiRel D F k p' w' s t := by
  obtain ⟨z, hy, h, hι, ha⟩ := he
  obtain ⟨w', hw', hv⟩ := GlobalTheory.exists_shifted_normalisation k p.g z p'.g.b
    (ha.1.trans (congrArg (p.g.b * ·) hι.1)) w hw
  refine ⟨w', hw', fun s t => ?_⟩
  rw [phiRel_iff hG p w hw, phiRel_iff hG p' w' hw']
  intro H α β hβ T ρ x J hJ
  rw [← GlobalTheory.phi_value_shift hG k p.g h p'.g z hι ha w w' hv s α T ρ x J hJ]
  exact H (α + k • z) β (by rw [← hβ, hy]; abel) T ρ x J hJ

theorem phiRel_zero (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k) (w : Frm D F k p.g.b) (hy : p.y = 0)
    (hg : p.g.IsZero) (hw : FrmOne w) (s : Fam D F k) : PhiRel D F k p w s s := by
  have hb : p.g.b = 1 := hg.1
  have hcorr : LB.Gen.Corr D.P.L _ _ _ _ w (LB.oneGen D.P.L) :=
    corr_of_val D.P.isLB fun z J hJ => (hw.2 z J hJ).trans (val_one _).symm
  refine (phiRel_iff hG p w hw.1 s s).2 fun α β hβ T ρ z J hJ => ?_
  obtain rfl : α = β := by rw [← hβ, hy, add_zero]
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have e₁ : ρ ≫ DegPre.trPt D F p.g.b = ρ := by rw [hb, H1.trPt_one, Category.comp_id]
  have e₂ : uVal D F k α p.g.b ρ z J = 1 := by
    have e : ρ ≫ fst (TF (R := R) F) D.P.A ≫ p.g.b = 1 := by rw [hb, MonObj.comp_one, MonObj.comp_one]
    rw [uVal, e, C.face₃, inv_one, _root_.mul_one]
    exact Finset.prod_eq_one fun _ _ => C.face₂ _ _
  rw [e₁, e₂, val_mul hJ, val_corr hJ (hg.2 α), val_corr hJ hcorr, val_one, _root_.mul_one, _root_.mul_one,
    Units.val_one, _root_.mul_one]

theorem bijective_of_pow {F V : Type} [Field F] [AddCommGroup V] [Module F V] (Φ : V →ₗ[F] V) {k : ℕ} (hk : 1 ≤ k)
    {c : F} (hc : c ≠ 0) (h : ∀ s, (Φ ^ k) s = c • s) : Function.Bijective Φ := by
  obtain ⟨k, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  constructor
  · intro a b hab
    have : (Φ ^ (k + 1)) a = (Φ ^ (k + 1)) b := by
      rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, hab]
    rw [h, h] at this
    exact smul_right_injective V hc this
  · intro b
    refine ⟨(Φ ^ k) (c⁻¹ • b), ?_⟩
    rw [← Module.End.mul_apply, ← pow_succ', h, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem phi_projective : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → ∃ Φ : ∀ (p : QkPt D.toPre F k), Frm D.toPre F k p.g.b → (Fam D.toPre F k →ₗ[F] Fam D.toPre F k), (∀ p w, w.IsGen → Function.Bijective (Φ p w) ∧ ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ p w s) ∧ (∀ p w, w.IsGen → ∀ c : F, c ≠ 0 → ∃ w', w'.IsGen ∧ Φ p w' = c • Φ p w) ∧ (∀ p w w', w.IsGen → w'.IsGen → ∃ c : F, c ≠ 0 ∧ Φ p w' = c • Φ p w) ∧ (∀ p p' w, w.IsGen → QkPt.Equiv D.toPre F p p' → ∃ w', w'.IsGen ∧ Φ p' w' = Φ p w) ∧ (∀ p p' p'' w w', w.IsGen → w'.IsGen → QkAdd p p' p'' → ∃ w'', w''.IsGen ∧ Φ p'' w'' = Φ p w ∘ₗ Φ p' w') ∧ ∀ p w, p.y = 0 → p.g.IsZero → FrmOne w → Φ p w = LinearMap.id := by
  intro hL R _ _ _ I _ D F _ _ _ k hk
  have hG : GlobalFnsSt := hL.1.globalFns
  have ex : ∀ (p : QkPt D.toPre F k) (w : Frm D.toPre F k p.g.b), ∃ Φ : Fam D.toPre F k →ₗ[F] Fam D.toPre F k,
      w.IsGen → ∀ s t, PhiRel D.toPre F k p w s t ↔ t = Φ s := fun p w => by
    by_cases hw : w.IsGen
    · obtain ⟨Φ, h⟩ := phiFun_of_globalFns hG R I D F k hk p w hw
      exact ⟨Φ, fun _ => h⟩
    · exact ⟨0, fun h => (hw h).elim⟩
  choose Φ hΦ using ex
  have rel : ∀ p w, w.IsGen → ∀ s, PhiRel D.toPre F k p w s (Φ p w s) := fun p w hw s => (hΦ p w hw s _).2 rfl
  refine ⟨Φ, fun p w hw => ⟨?_, hΦ p w hw⟩, fun p w hw c hc => ?_, fun p w w' hw hw' => ?_,
    fun p p' w hw he => ?_, fun p p' p'' w w' hw hw' hadd => ?_, fun p w hy hg hw => ?_⟩
  · obtain ⟨c, hc, hcs⟩ := H1.phiPow_core hG p w hw
    refine bijective_of_pow (Φ p w) hk hc fun s => ?_
    have h := hcs (fun i => (Φ p w ^ (i : ℕ)) s) (fun i => by
      rw [hΦ p w hw]
      simp only [Fin.val_succ, Fin.val_castSucc, pow_succ', Module.End.mul_apply])
    rw [isSmul_iff] at h
    simpa only [Fin.val_last, Fin.val_zero, pow_zero, Module.End.one_apply] using h
  · obtain ⟨w', hw', hv⟩ := exists_scaled hw c hc
    exact ⟨w', hw', LinearMap.ext fun s =>
      ((hΦ p w' hw' s _).1 (phiRel_of_ratio hG p hw hw' c hc hv s _ (rel p w hw s))).symm⟩
  · obtain ⟨c, hc, hv⟩ := CoefBasic.exists_frame_ratio hw hw'
    exact ⟨c, hc, LinearMap.ext fun s =>
      ((hΦ p w' hw' s _).1 (phiRel_of_ratio hG p hw hw' c hc hv s _ (rel p w hw s))).symm⟩
  · obtain ⟨w', hw', h⟩ := phiRel_of_equiv hG he hw
    exact ⟨w', hw', LinearMap.ext fun s => ((hΦ p' w' hw' s _).1 (h s _ (rel p w hw s))).symm⟩
  · obtain ⟨q, hy, hg, he⟩ := hadd
    obtain ⟨w₂, hw₂, h₂⟩ := GlobalTheory.ThetaMul.phi_mul_core hG p p' q hy hg w w' hw hw'
    obtain ⟨w'', hw'', h⟩ := phiRel_of_equiv hG he hw₂
    exact ⟨w'', hw'', LinearMap.ext fun s =>
      ((hΦ p'' w'' hw'' s _).1 (h s _ (h₂ s _ _ (rel p' w' hw' s) (rel p w hw _)))).symm⟩
  · exact LinearMap.ext fun s => ((hΦ p w hw.1 s s).1 (phiRel_zero hG p w hy hg hw s)).symm

end GlobalTheory.UT.PhiProj
end
