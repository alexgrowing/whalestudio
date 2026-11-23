import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EndoEqOfSections
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamCoefVal
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralSectionUnitAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsValEqOfNonneg
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFamOfReps

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.SmallPoint
open CoefBasic

theorem le_of_sumV {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {f : Ix → F} (h : SumV v f 0)
    (i₀ : Ix) (q : ℚ) (hq : ∀ i, i ≠ i₀ → (q : WithTop ℚ) ≤ v (f i)) : (q : WithTop ℚ) ≤ v (f i₀) := by
  classical
  obtain ⟨S, hS⟩ := h q
  have h₁ := hS (insert i₀ S) (Finset.subset_insert _ _)
  have h₂ : (q : WithTop ℚ) ≤ v (∑ i ∈ (insert i₀ S).erase i₀, f i) :=
    v.map_le_sum fun i hi => hq i (Finset.ne_of_mem_erase hi)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_insert_self i₀ S), zero_sub, v.map_neg] at h₁
  have := v.map_le_sub h₁ h₂
  rwa [add_sub_cancel_right] at this

theorem eq_zero_of_val {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {x u : F} (hu : v u = 0) {N : ℕ}
    (hN : 1 ≤ N) (h : ∀ n : ℕ, (((N * (n + 1) : ℕ) : ℚ) : WithTop ℚ) ≤ v (x * u ^ n)) : x = 0 := by
  by_contra hx
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hx)
  obtain ⟨n, hn⟩ := exists_nat_gt q
  have e := h n
  rw [v.map_mul, v.map_pow, hu, nsmul_zero, add_zero, ← hq, WithTop.coe_le_coe] at e
  have : ((n + 1 : ℕ) : ℚ) ≤ ((N * (n + 1) : ℕ) : ℚ) := by exact_mod_cast Nat.le_mul_of_pos_left _ hN
  push_cast at this e
  linarith

abbrev PSec {X : Scheme.{0}} (L : LB X) (n : ℕ) : Type :=
  LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (n : ℤ)))

theorem exists_mul_pow {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {N : ℕ} (σ ρ : PSec L N) (n : ℕ) :
    ∃ τ : PSec L (N * (n + 1)), ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J →
      sval τ r z J = sval σ r z J * sval ρ r z J ^ n := by
  obtain ⟨τ, hτ⟩ := exists_sec hL (φ' := fun _ : Fin 1 => 𝟙 X) (ε' := fun _ => ((N * (n + 1) : ℕ) : ℤ))
    (H1.SquareUnits.formEq_of_add fun U _ h => by
      simp
      module) (H1.SectionArithmetic.mulSec σ (H1.SectionArithmetic.powSec fun _ : Fin n => ρ))
  refine ⟨τ, fun Z r z J hJ => ?_⟩
  rw [hτ Z r z J hJ, H1.SectionArithmetic.sval_mulSec _ _ _ z hJ, H1.SectionArithmetic.sval_powSec _ _ z hJ, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem eq_of_veryAmple {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    (hS : IsAffineOpen (⊤ : S.Opens)) {n : ℕ} (hV : VeryAmpleAt A L n) {T : Over S} (p q : T ⟶ A)
    (H : ∀ z : T.left, ∃ J, Good L z J ∧ ∃ u : (T.left.presheaf.stalk z)ˣ, ∀ σ : PSec L n,
      sval σ q.left z J = u.val * sval σ p.left z J) : p = q := by
  obtain ⟨M, s, hcov, haff⟩ := hV ⊤ hS
  choose r hr hsurj using fun i => (haff i).2
  obtain ⟨i', hi⟩ : ∃ i' : A.left ⟶ (A.hom ⁻¹ᵁ ⊤).toScheme, i' ≫ (A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨A.left.topIso.inv, A.left.topIso.inv_hom_id⟩
  have sec : ∀ j, ∃ σ : PSec L n, ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z) (J),
      Good L z J → sval σ r z J =
        sval (L := L) (φ := fun _ : Fin n => (A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j) (r ≫ i') z J := fun j => by
    obtain ⟨s', hs'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => 𝟙 A.left) (ε' := fun _ => (n : ℤ))
      (fun U _ f => by
        simp only [hi, zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, zpow_natCast])
      (H1.SectionArithmetic.pullSec (L := L) (φ := fun _ : Fin n => (A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j) i')
    exact ⟨s', fun Z r z J hJ => (hs' Z r z J hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ r z hJ)⟩
  choose σ hσ using sec
  have key : p.left ≫ i' = q.left ≫ i' := by
    refine AutUniq.hom_eq_of_sval (L := L) (φ := fun _ : Fin n => (A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) s (A.hom ∣_ ⊤) _ _ ?_
      hcov (fun i => (haff i).1) r hr hsurj fun y => ?_
    · rw [← cancel_mono (⊤ : S.Opens).ι]
      simp only [Category.assoc, morphismRestrict_ι, reassoc_of% hi, Over.w]
    · obtain ⟨J, hJ, u, hu⟩ := H y
      exact ⟨J, hJ, u, fun j => by rw [← hσ j _ _ y J hJ, ← hσ j _ _ y J hJ, hu]⟩
  refine Over.OverMorphism.ext ?_
  have := congrArg (fun q => q ≫ (A.hom ⁻¹ᵁ ⊤).ι) key
  simpa only [Category.assoc, hi, Category.comp_id] using this

section Values

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

abbrev PGen (m : TWM.TO hϖ hv ⟶ D.toPre.P.A) : Type :=
  LB.Gen (LB.LinComb D.toPre.P.L (K := PUnit) (fun _ => m.left) (fun _ => 1))

def Ev {m : TWM.TO hϖ hv ⟶ D.toPre.P.A} (G : PGen hϖ hv m) {n : ℕ} (σ : PSec D.toPre.P.L n) (x : F) : Prop :=
  ∀ z J, Good D.toPre.P.L z J →
    sval σ (TWM.ιS hϖ hv ≫ m).left z J = cst F z x * (val G (TWM.ιS hϖ hv).left z J).val ^ n

variable {hϖ hv}

theorem exists_ev_int {m : TWM.TO hϖ hv ⟶ D.toPre.P.A} (G : PGen hϖ hv m) (hG : G.IsGen) {n : ℕ}
    (σ : PSec D.toPre.P.L n) : ∃ x : TWO.Ov v, Ev hϖ hv G σ x ∧
      ∀ (z : Spec (CommRingCat.of (ResidueField (TWO.Ov v)))) (J), Good D.toPre.P.L z J →
        IsUnit (sval σ (Spec.map (CommRingCat.ofHom (residue (TWO.Ov v))) ≫ m.left) z J) → IsUnit x := by
  have hL := D.toPre.P.isLB
  obtain ⟨G', hG', vG'⟩ := exists_gen hL (φ' := fun _ : Fin 1 => m.left ≫ 𝟙 _) (ε' := fun _ => (n : ℤ))
    (fun U _ h => by simp) (GeneratorPullback.powGen _ _ _ G n) (powGen_isGen _ _ _ _ hG n)
  obtain ⟨x₀, hx₀⟩ := TwistUnit.exists_ratio_local (R := TWO.Ov v) hL (H1.SectionArithmetic.pullSec σ m.left) G' hG'
  have key : ∀ {E : Type} [CommRing E] (φ : TWO.Ov v →+* E) (z : Spec (CommRingCat.of E)),
      gs (Spec.map (CommRingCat.ofHom φ)) z ⊤ x₀ = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom
        (φ ((Scheme.ΓSpecIso (CommRingCat.of (TWO.Ov v))).hom.hom x₀))) := fun φ z => by
    have e := gs_pull (𝟙 _) (Spec.map (CommRingCat.ofHom φ)) z ⊤ trivial x₀
    rw [Category.id_comp] at e
    exact e.symm.trans (congrArg (gs (𝟙 _) z ⊤) (TWM.appTop_specMap (CommRingCat.ofHom φ) x₀))
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (TWO.Ov v))).hom.hom x₀, fun z J hJ => ?_, fun z J hJ hu => ?_⟩
  · rw [Over.comp_left, ← H1.SectionArithmetic.sval_pullSec σ m.left _ z hJ]
    refine (hx₀ _ _ z J hJ).trans (congrArg₂ (· * ·) (key (algebraMap (TWO.Ov v) F) z) ?_)
    rw [vG' _ _ z J hJ, UUA.val_powGen', Units.val_pow_eq_pow_val]
  · have e := hx₀ _ (Spec.map (CommRingCat.ofHom (residue (TWO.Ov v)))) z J hJ
    rw [H1.SectionArithmetic.sval_pullSec _ _ _ z hJ] at e
    have h₁ := isUnit_of_mul_isUnit_left ((congrArg IsUnit e).mp hu)
    rw [key] at h₁
    refine isUnit_of_map_unit (residue (TWO.Ov v)) _ (IsUnit.mk0 _ fun h0 => ?_)
    rw [h0, map_zero, gs_eq _ _ ⊤ trivial, map_zero, map_zero] at h₁
    exact not_isUnit_zero h₁

theorem exists_ev {m : TWM.TO hϖ hv ⟶ D.toPre.P.A} (G : PGen hϖ hv m) (hG : G.IsGen) {n : ℕ}
    (σ : PSec D.toPre.P.L n) : ∃ x : F, 0 ≤ v x ∧ Ev hϖ hv G σ x := by
  obtain ⟨x, hx, -⟩ := exists_ev_int G hG σ
  exact ⟨x, x.2, hx⟩

theorem exists_ev_unit (hA : AmpleSt) {m : TWM.TO hϖ hv ⟶ D.toPre.P.A} (G : PGen hϖ hv m) (hG : G.IsGen) {n : ℕ}
    (hn : 4 ≤ n) : ∃ (σ : PSec D.toPre.P.L n) (x : F), v x = 0 ∧ Ev hϖ hv G σ x := by
  have hL := D.toPre.P.isLB
  let z : Spec (CommRingCat.of (ResidueField (TWO.Ov v))) := closedPoint _
  obtain ⟨σ, hσ⟩ := TwistUnit.unitAt_pow hA D.toPre.P n hn (𝟙 _)
    ((Spec.map (CommRingCat.ofHom (residue (TWO.Ov v))) ≫ m.left) z)
  obtain ⟨J, hJ⟩ := exists_good' hL z
  obtain ⟨x, hx, hu⟩ := exists_ev_int G hG σ
  exact ⟨σ, x, TWO.v_unit v (hu z J hJ (TwistUnit.isUnit_sval_of hL σ _ z hσ J hJ)).unit, hx⟩

theorem Ev.mul_pow {m : TWM.TO hϖ hv ⟶ D.toPre.P.A} {G : PGen hϖ hv m} {N n : ℕ} {σ ρ : PSec D.toPre.P.L N}
    {τ : PSec D.toPre.P.L (N * (n + 1))} (hτ : ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J),
      Good D.toPre.P.L z J → sval τ r z J = sval σ r z J * sval ρ r z J ^ n) {x y : F}
    (hx : Ev hϖ hv G σ x) (hy : Ev hϖ hv G ρ y) : Ev hϖ hv G τ (x * y ^ n) := fun z J hJ => by
  rw [hτ _ _ z J hJ, hx z J hJ, hy z J hJ]
  simp only [cst_eq, map_mul, map_pow]
  ring

theorem exists_fam (hG : GlobalFnsSt) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) (hϖ : Irreducible ϖ)
    (hv : ValOver ϖ F v) {j : ℕ} (hj : 1 ≤ j) (σ : PSec D.toPre.P.L j) :
    ∃ S : Fam D.toPre F j, NuGe D Q F v j S 0 ∧ (∀ β, (∀ mu, β ≠ j • mu) → ∀ i, (S.s β).f i = 0) ∧
      ∀ (b : TF (R := V) F ⟶ D.toPre.P.A) z J, Good D.toPre.P.L z J →
        sval (S.s 0) (lift (𝟙 (TF (R := V) F)) b).left z J = sval σ b.left z J := by
  have hL := D.toPre.P.isLB
  obtain ⟨σB, hσB⟩ := exists_sec hL (φ' := D.toPre.famφB 0) (ε' := DegPre.famε j) (fun U _ h => by
    have p := SectionScalarValuation.prod_famB D.toPre (𝟙 _) 0 j h
    have c : SectionScalarValuation.cQ D.toPre D.toPre.P.A 0 = 1 := cPoint_zero _
    simp only [Over.id_left, Category.id_comp, c, _root_.mul_one] at p
    rw [p, Fin.prod_univ_one, inv_mul_cancel_right, zpow_sub_one, inv_mul_cancel_right]) σ
  have hformF : FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB 0 i) (DegPre.famε j)
      (DegPre.famφ D.toPre F 0) (DegPre.famε j) := fun U _ g =>
    Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq]
  obtain ⟨s, hs⟩ := exists_sec hL hformF (H1.SectionArithmetic.pullSec σB (DegPre.prB D.toPre F).left)
  have hs' : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
      sval s ρ z J = sval σB (ρ ≫ (DegPre.prB D.toPre F).left) z J := fun Z ρ z J hJ =>
    (hs Z ρ z J hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ ρ z hJ)
  obtain ⟨S, rfl, hS⟩ := FamFree.exists_fam_single hG D.tau_bimult hj 0 s
  refine ⟨S, ExactTerm.nuGe_of_single hϖ hQ hv hj S 0 0 hS
    ⟨1, fun _ => 1, fun _ => σB, fun _ => S.s 0, fun _ => ?_, fun _ => ?_, fun j => ?_⟩,
    fun β hβ => hS β fun mu e => hβ mu (by rw [← e, zero_add]), fun b z J hJ => ?_⟩
  · exact SectionScalarValuation.secScal_of_sval hL fun y J hJ => (hs' _ (𝟙 _) y J hJ).symm
  · rw [AddValuation.map_one, QForm.Q_zero hϖ D hQ]; simp
  · rw [Fin.sum_univ_one, DVR.constBF_eq, map_one]
    simp [resTop]
  · rw [hs' _ _ z J hJ, ← Over.comp_left, lift_snd, hσB _ _ z J hJ]

theorem exists_frame_val {m : TWM.TO hϖ hv ⟶ D.toPre.P.A} (G : PGen hϖ hv m) (hG : G.IsGen)
    (G₀ : PGen hϖ hv (1 : _ ⟶ D.toPre.P.A)) (hG₀ : G₀.IsGen) {j : ℕ} {b : TF (R := V) F ⟶ D.toPre.P.A}
    (hb : TWM.ιS hϖ hv ≫ m = b) (w : Frm D.toPre F j b) (hw : w.IsGen) :
    ∃ (c : F) (ω : ℚ), v c = ω ∧ GenV hϖ hv w ω ∧ ∀ z J, Good D.toPre.P.L z J →
      (val w (𝟙 _) z J).val * (val G (TWM.ιS hϖ hv).left z J).val ^ j =
        cst F z c * (val G₀ (TWM.ιS hϖ hv).left z J).val ^ j := by
  have hL := D.toPre.P.isLB
  obtain ⟨W, hW, vW⟩ := exists_gen hL (φ' := TWM.lineφO hϖ hv m) (ε' := DegPre.lineε j)
    (fun U _ h => by
      simp [Fintype.prod_sum_type, Fin.prod_univ_two, TWM.lineφO, DegPre.lineε])
    (LB.mulGen _ _ _ _ _ (GeneratorPullback.powGen _ _ _ G₀ j) (LB.invGen _ _ _ (GeneratorPullback.powGen _ _ _ G j)))
    (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ hG₀ j) (invGen_isGen _ _ _ _ (powGen_isGen _ _ _ _ hG j)))
  have hφ : ∀ i, DegPre.lineφ D.toPre F b i = (TWM.ιS hϖ hv).left ≫ TWM.lineφO hϖ hv m i := fun i => by
    fin_cases i
    · exact congrArg (fun q : TF (R := V) F ⟶ D.toPre.P.A => q.left)
        (MonObj.comp_one (M := D.toPre.P.A) (TWM.ιS hϖ hv)).symm
    · exact congrArg (fun q : TF (R := V) F ⟶ D.toPre.P.A => q.left) hb.symm
  obtain ⟨c, hc, vc⟩ := TWM.exists_ratio (F := F) hL w hw (LB.pullGen _ _ _ W (TWM.ιS hϖ hv).left)
    (pullGen_isGen _ _ _ _ hW _) (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [hφ])
  obtain ⟨ω, hω⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hc)
  have e : ∀ z J, Good D.toPre.P.L z J →
      (val w (𝟙 _) z J).val = cst F z c * (val W (TWM.ιS hϖ hv).left z J).val := fun z J hJ => by
    have e₁ := val_pull hJ W (TWM.ιS hϖ hv).left (𝟙 _)
    rw [Category.id_comp] at e₁
    exact (vc _ (𝟙 _) z J hJ).trans (congrArg (fun u : _ˣ => cst F z c * u.val) e₁)
  refine ⟨c, ω, hω.symm, ⟨_, hφ, W, hW, c, hω.symm, e⟩, fun z J hJ => ?_⟩
  rw [e z J hJ, vW _ _ z J hJ, val_mul hJ, val_inv, UUA.val_powGen', UUA.val_powGen', _root_.mul_assoc,
    ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_mul_cancel_right, Units.val_pow_eq_pow_val]

theorem exists_rig : ∃ G₀ : PGen hϖ hv (1 : _ ⟶ D.toPre.P.A), G₀.IsGen ∧ ∀ z J, Good D.toPre.P.L z J →
    val G₀ (TWM.ιS hϖ hv).left z J = rigV D.toPre (TF (R := V) F).hom z J := by
  refine ⟨LB.pullGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig (TWM.TO hϖ hv).hom,
    pullGen_isGen _ _ _ _ D.toPre.rig_gen _, fun z J hJ => ?_⟩
  have e := val_pull (φ := fun _ : PUnit => eSec D.toPre.P.A) (ε := fun _ => 1) hJ D.toPre.rig (TWM.TO hϖ hv).hom
    (TWM.ιS hϖ hv).left
  rw [Over.w] at e
  exact e

theorem gtV_zero {o : GtPtF D.toPre F} (ho : o.IsZero) : GtV hϖ hv o 0 := by
  intro χ
  obtain ⟨hb, hs⟩ := (isZero_iff o).1 ho
  obtain ⟨t, ht, vt⟩ := exists_gen D.toPre.P.isLB (φ' := TWM.gtφO hϖ hv (D := D) 1 χ) (ε' := DegPre.gtε)
    (fun U _ h => by
      rw [Fintype.prod_empty]
      simp [Fin.prod_univ_four, TWM.gtφO, DegPre.gtε])
    (LB.oneGen D.toPre.P.L (Y := (TWM.TO hϖ hv).left))
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  have e₁ : TWM.ιS hϖ hv ≫ (1 : _ ⟶ D.toPre.P.A) = 1 := MonObj.comp_one _
  have e₂ := comp_cP D.toPre (TWM.ιS hϖ hv) χ
  refine ⟨_, fun i => ?_, t, ht, 1, by rw [v.map_one]; rfl, fun z J hJ => ?_⟩
  · rw [hb]
    fin_cases i
    · refine congrArg (fun q : TF (R := V) F ⟶ D.toPre.P.A => q.left)
        (show cP D.toPre _ χ * 1 = TWM.ιS hϖ hv ≫ (cP D.toPre _ χ * 1) from ?_)
      rw [_root_.mul_one, _root_.mul_one, e₂]
    · exact congrArg (fun q : TF (R := V) F ⟶ D.toPre.P.A => q.left) e₂.symm
    · exact congrArg (fun q : TF (R := V) F ⟶ D.toPre.P.A => q.left) e₁.symm
    · exact congrArg (fun q : TF (R := V) F ⟶ D.toPre.P.A => q.left) e₁.symm
  · rw [hs χ z J hJ, vt _ _ z J hJ, val_one, cst_eq, map_one, _root_.one_mul]

theorem coef_zero {j : ℕ} (S : Fam D.toPre F j) (g : GtPtF D.toPre F) (w : Frm D.toPre F j g.b) {β : D.toPre.X}
    (h : ∀ i, (S.s β).f i = 0) : coef S g w β = 0 :=
  coef_eq fun z J hJ => by
    rw [UUA.sval_zero_of h _ z J (hJ.mem _ _), cst_eq, map_zero]
    simp only [MulZeroClass.zero_mul]

theorem coef_at_zero {m : TWM.TO hϖ hv ⟶ D.toPre.P.A} {G : PGen hϖ hv m} {j : ℕ} (S : Fam D.toPre F j)
    (g : GtPtF D.toPre F) (hb : TWM.ιS hϖ hv ≫ m = g.b) (w : Frm D.toPre F j g.b) {σ : PSec D.toPre.P.L j} {x c : F}
    (hS : ∀ (b : TF (R := V) F ⟶ D.toPre.P.A) z J, Good D.toPre.P.L z J →
      sval (S.s 0) (lift (𝟙 (TF (R := V) F)) b).left z J = sval σ b.left z J) (hx : Ev hϖ hv G σ x)
    (hc : ∀ z J, Good D.toPre.P.L z J → (val w (𝟙 _) z J).val * (val G (TWM.ιS hϖ hv).left z J).val ^ j =
        cst F z c * (rigV D.toPre (TF (R := V) F).hom z J).val ^ j) : coef S g w 0 = c * x :=
  coef_eq fun z J hJ => by
    have e := hx z J hJ
    have e' := hc z J hJ
    rw [hb] at e
    rw [hS _ z J hJ, e, val_corr hJ g.s_zero, val_one, Units.val_one]
    simp only [cst_eq, map_mul] at e' ⊢
    linear_combination (-cstH z x) * e'

end Values

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ (k : ℕ), 1 ≤ k → ∀ (d o : GtPtF D.toPre F) (l : D.toPre.X → ℚ), o.IsZero → GtV hϖ hv d l → (∀ m, |l m| ≤ Q m) → (∀ (n j : ℕ), 1 ≤ n → j = k * n → ∀ (w₁ : Frm D.toPre F j o.b), FrmOne w₁ → ∃ w : Frm D.toPre F j d.b, w.IsGen ∧ ∀ S₁ S₂ : Fam D.toPre F j, ¬ SumV v (coef S₂ o w₁) 0 → ∀ α, SumV v (fun χ => coef S₁ d w χ * coef S₂ o w₁ (α - χ) - coef S₂ d w χ * coef S₁ o w₁ (α - χ)) 0) → d.b = 1 := by
  intro hL hT hVR hTW hUU V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv k hk d o l ho hl hlQ H
  have I := GlobalTheory.UT.CoefVal.main hL hT hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv
  have I' := GlobalTheory.UT.CoefUnit.exists_fam_coef_val hL hT hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv
  have hM := D.toPre.P.isLB
  have hob : o.b = 1 := ((isZero_iff o).1 ho).1
  have hob' : TWM.ιS hϖ hv ≫ (1 : _ ⟶ D.toPre.P.A) = o.b := (MonObj.comp_one _).trans hob.symm
  obtain ⟨l', hl', -⟩ := (I d).1
  have hll : ∀ χ, l χ = l' χ := by
    obtain ⟨w, hw⟩ := (coef_basic V D.toPre F 4 d).1
    obtain ⟨ω, hω, -⟩ := (I d).2.1 4 w hw
    have le : ∀ l₁ l₂, GtV hϖ hv d l₁ → GtV hϖ hv d l₂ → ∀ χ, l₁ χ ≤ l₂ χ := fun l₁ l₂ h₁ h₂ χ => by
      obtain ⟨s, hs, -, e⟩ := I' 4 le_rfl d w l₂ ω hw h₂ hω χ
      have := ((I d).2.2.2.2.2.2 4 (by omega) w s hw).2 l₁ ω 0 h₁ hω hs χ
      rw [e, WithTop.coe_le_coe] at this
      linarith
    exact fun χ => le_antisymm (le _ _ hl hl' χ) (le _ _ hl' hl χ)
  obtain ⟨m, hm⟩ := TWM.exists_liftO hϖ hv (D := D) d.b
  obtain ⟨G, hG⟩ : ∃ G : PGen hϖ hv m, G.IsGen := exists_gen_of_local (V := TWO.Ov v) _ hM _ _
  obtain ⟨G₀, hG₀, vG₀⟩ := exists_rig (hϖ := hϖ) (hv := hv) (D := D)
  have A : ∀ n j : ℕ, 1 ≤ n → j = k * n → ∀ (σ₁ σ₂ : PSec D.toPre.P.L j) (x₁ x₂ y₁ y₂ : F), Ev hϖ hv G σ₁ x₁ →
      Ev hϖ hv G σ₂ x₂ → Ev hϖ hv G₀ σ₁ y₁ → Ev hϖ hv G₀ σ₂ y₂ → v y₂ = 0 →
      ((j : ℚ) : WithTop ℚ) ≤ v (x₁ * y₂ - x₂ * y₁) := by
    intro n j hn hj σ₁ σ₂ x₁ x₂ y₁ y₂ hx₁ hx₂ hy₁ hy₂ hu
    have hj1 : 1 ≤ j := hj ▸ Nat.mul_pos hk hn
    have hj0 : (0 : ℚ) < j := by exact_mod_cast hj1
    obtain ⟨w₁, hw₁⟩ := (coef_basic V D.toPre F j o).2.1 hob
    obtain ⟨w, hw, Hw⟩ := H n j hn hj w₁ hw₁
    obtain ⟨c, ω, hcω, hω, vw⟩ := exists_frame_val G hG G₀ hG₀ hm w hw
    have vw' : ∀ z J, Good D.toPre.P.L z J → (val w (𝟙 _) z J).val * (val G (TWM.ιS hϖ hv).left z J).val ^ j =
        cst F z c * (rigV D.toPre (TF (R := V) F).hom z J).val ^ j := fun z J hJ => by rw [vw z J hJ, vG₀ z J hJ]
    have vw₁ : ∀ z J, Good D.toPre.P.L z J → (val w₁ (𝟙 _) z J).val * (val G₀ (TWM.ιS hϖ hv).left z J).val ^ j =
        cst F z 1 * (rigV D.toPre (TF (R := V) F).hom z J).val ^ j := fun z J hJ => by
      rw [hw₁.2 z J hJ, vG₀ z J hJ, cst_eq, map_one, Units.val_one]
    obtain ⟨S₁, n₁, z₁, e₁⟩ := exists_fam hL.1.globalFns hQ hϖ hv hj1 σ₁
    obtain ⟨S₂, n₂, z₂, e₂⟩ := exists_fam hL.1.globalFns hQ hϖ hv hj1 σ₂
    have hQj : ∀ mu, (Q (j • mu) : ℚ) / j = j * Q mu := fun mu => by
      rw [Q_nsmul hϖ hQ]; push_cast; field_simp
    have bo : ∀ S : Fam D.toPre F j, NuGe D Q F v j S 0 → ∀ mu,
        (((j : ℚ) * Q mu : ℚ) : WithTop ℚ) ≤ v (coef S o w₁ (j • mu)) := fun S hS mu => by
      have := ((I o).2.2.2.2.2.2 j hj1 w₁ S hw₁.1).2 0 0 0 (gtV_zero ho) ((I o).2.2.1 j w₁ hw₁ hob) hS (j • mu)
      rwa [hQj, Pi.zero_apply, add_zero, add_zero, zero_add] at this
    have bd : ∀ S : Fam D.toPre F j, NuGe D Q F v j S 0 → ∀ mu,
        ((ω : ℚ) : WithTop ℚ) ≤ v (coef S d w (j • mu)) := fun S hS mu => by
      refine le_trans (WithTop.coe_le_coe.2 ?_) (((I d).2.2.2.2.2.2 j hj1 w S hw).2 l' ω 0 hl' hω hS (j • mu))
      have := (abs_le.1 (hlQ mu)).1
      rw [hQj, map_nsmul, ← hll, nsmul_eq_mul]
      nlinarith
    have hQ1 : ∀ mu, j • mu ≠ 0 → (j : ℚ) ≤ j * Q mu := fun mu h => by
      have : (1 : ℚ) ≤ Q mu := by exact_mod_cast QForm.Q_pos hϖ D hQ (fun e => h (by rw [e, smul_zero]))
      nlinarith
    have hne : ¬ SumV v (coef S₂ o w₁) 0 := fun h => by
      have := le_of_sumV h 0 j fun χ hχ => by
        by_cases e : ∃ mu, χ = j • mu
        · obtain ⟨mu, rfl⟩ := e
          exact le_trans (WithTop.coe_le_coe.2 (hQ1 mu hχ)) (bo S₂ n₂ mu)
        · rw [coef_zero S₂ o w₁ (z₂ χ fun mu h => e ⟨mu, h⟩), v.map_zero]; exact le_top
      rw [coef_at_zero S₂ o hob' w₁ e₂ hy₂ vw₁, _root_.one_mul, hu, ← WithTop.coe_zero, WithTop.coe_le_coe] at this
      linarith
    have term : ∀ S S' : Fam D.toPre F j, NuGe D Q F v j S 0 → NuGe D Q F v j S' 0 →
        (∀ β, (∀ mu, β ≠ j • mu) → ∀ i, (S.s β).f i = 0) → ∀ χ, χ ≠ 0 →
        ((ω + j : ℚ) : WithTop ℚ) ≤ v (coef S d w χ * coef S' o w₁ (0 - χ)) := fun S S' hS hS' hz χ hχ => by
      by_cases e : ∃ mu, χ = j • mu
      · obtain ⟨mu, rfl⟩ := e
        rw [v.map_mul, zero_sub, ← smul_neg, WithTop.coe_add]
        refine add_le_add (bd S hS mu) (le_trans (WithTop.coe_le_coe.2 (hQ1 (-mu) ?_)) (bo S' hS' (-mu)))
        rwa [smul_neg, neg_ne_zero]
      · rw [coef_zero S d w (hz χ fun mu h => e ⟨mu, h⟩), MulZeroClass.zero_mul, v.map_zero]; exact le_top
    have key := le_of_sumV (Hw S₁ S₂ hne 0) 0 (ω + j) fun χ hχ =>
      v.map_le_sub (term S₁ S₂ n₁ n₂ z₁ χ hχ) (term S₂ S₁ n₂ n₁ z₂ χ hχ)
    rw [sub_zero, coef_at_zero S₁ d hm w e₁ hx₁ vw', coef_at_zero S₂ d hm w e₂ hx₂ vw',
      coef_at_zero S₁ o hob' w₁ e₁ hy₁ vw₁, coef_at_zero S₂ o hob' w₁ e₂ hy₂ vw₁,
      show c * x₁ * (1 * y₂) - c * x₂ * (1 * y₁) = c * (x₁ * y₂ - x₂ * y₁) by ring, v.map_mul, hcω,
      WithTop.coe_add] at key
    exact (WithTop.add_le_add_iff_left WithTop.coe_ne_top).1 key
  have hN : 4 ≤ k * 4 := by omega
  obtain ⟨ρ, y, hy0, hy⟩ := exists_ev_unit hL.1.ample G₀ hG₀ hN
  obtain ⟨x, hx0', hx⟩ := exists_ev G hG ρ
  have hx0 : v x = 0 := by
    obtain ⟨ρ', x', hx'0, hx'⟩ := exists_ev_unit hL.1.ample G hG hN
    obtain ⟨y', hy'0, hy'⟩ := exists_ev G₀ hG₀ ρ'
    have h₁ := A 4 _ (by omega) rfl ρ' ρ x' x y' y hx' hx hy' hy hy0
    have h₂ : (0 : WithTop ℚ) < v (x' * y - x * y') :=
      lt_of_lt_of_le (by exact_mod_cast (by omega : 0 < k * 4)) h₁
    by_contra hne
    have h₃ : 0 < v (x * y') := by
      rw [v.map_mul]; exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne hx0' (Ne.symm hne)) hy'0
    have h₄ := v.map_lt_add h₂ h₃
    rw [sub_add_cancel, v.map_mul, hx'0, hy0, add_zero] at h₄
    exact lt_irrefl _ h₄
  have B : ∀ (σ : PSec D.toPre.P.L (k * 4)) (a b : F), Ev hϖ hv G σ a → Ev hϖ hv G₀ σ b → a * y = x * b := by
    intro σ a b ha hb
    refine sub_eq_zero.1 (eq_zero_of_val (v := v) (u := x * y) (N := k * 4)
      (by rw [v.map_mul, hx0, hy0, add_zero]) (by omega) fun n => ?_)
    obtain ⟨τ₁, hτ₁⟩ := exists_mul_pow hM σ ρ n
    obtain ⟨τ₂, hτ₂⟩ := exists_mul_pow hM ρ ρ n
    have := A (4 * (n + 1)) _ (by omega) (_root_.mul_assoc _ _ _) τ₁ τ₂ _ _ _ _ (ha.mul_pow hτ₁ hx) (hx.mul_pow hτ₂ hx)
      (hb.mul_pow hτ₁ hy) (hy.mul_pow hτ₂ hy) (by rw [v.map_mul, v.map_pow, hy0, nsmul_zero, add_zero])
    convert this using 2
    ring
  have hxne : x ≠ 0 := fun h => by rw [h, v.map_zero] at hx0; exact WithTop.top_ne_zero hx0
  have hyne : y ≠ 0 := fun h => by rw [h, v.map_zero] at hy0; exact WithTop.top_ne_zero hy0
  refine (eq_of_veryAmple hM (isAffineOpen_top _) (hL.1.ample _ D.toPre.P _ hN).2 1 d.b fun z => ?_).symm
  obtain ⟨J, hJ⟩ := exists_good' hM z
  refine ⟨J, hJ, Units.map (cstH (R := V) z).toMonoidHom (Units.mk0 (x / y) (div_ne_zero hxne hyne)) *
    val G (TWM.ιS hϖ hv).left z J ^ (k * 4) * (val G₀ (TWM.ιS hϖ hv).left z J ^ (k * 4))⁻¹, fun σ => ?_⟩
  obtain ⟨a, -, ha⟩ := exists_ev G hG σ
  obtain ⟨b, -, hb⟩ := exists_ev G₀ hG₀ σ
  have e : a = x / y * b := by
    have := B σ a b ha hb
    field_simp
    linear_combination this
  have ea := ha z J hJ
  have eb := hb z J hJ
  rw [hm] at ea
  rw [hob', hob] at eb
  rw [ea, eb, e, Units.val_mul, Units.val_mul, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, cst_eq, cst_eq,
    map_mul]
  have := Units.inv_mul (val G₀ (TWM.ιS hϖ hv).left z J ^ (k * 4))
  show _ = cstH z (x / y) * _ * _ * _
  linear_combination (-(cstH z (x / y) * cstH z b * (val G (TWM.ιS hϖ hv).left z J ^ (k * 4)).val)) * this

end GlobalTheory.UT.SmallPoint
end
