import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IntegralFamilyPrescribedTermUnitAtPrime
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FamWtZero

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FamIntAt

variable {R : Type} [CommRing R] [IsDomain R]

theorem gs_thick_eq_zero (I : Ideal R) {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (0 + 1)))) (z : T)
    (V : (Spec (CommRingCat.of R)).Opens) (hz : (g ≫ thick R I 0) z ∈ V) {a : Γ(Spec (CommRingCat.of R), V)}
    (ha : a ∈ I.map (DegPre.toOpen V)) : gs (g ≫ thick R I 0) z V a = 0 := by
  let θ : Γ(Spec (CommRingCat.of R), V) →+* T.presheaf.stalk z :=
    (T.presheaf.germ ((g ≫ thick R I 0) ⁻¹ᵁ V) z hz).hom.comp ((g ≫ thick R I 0).app V).hom
  have hθ : ∀ b, gs (g ≫ thick R I 0) z V b = θ b := fun b => gs_eq _ _ _ hz b
  rw [hθ]
  suffices h : I.map (DegPre.toOpen V) ≤ RingHom.ker θ from h ha
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  rw [Ideal.mem_comap, RingHom.mem_ker, ← hθ]
  have e1 : DegPre.toOpen V r = ((Spec (CommRingCat.of R)).presheaf.map (homOfLE le_top).op).hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := rfl
  rw [e1, gs_res _ _ le_top hz, ← gs_pull g (thick R I 0) z ⊤ trivial]
  have h0 : Ideal.Quotient.mk (I ^ (0 + 1)) r = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using hr)
  have nat := congrArg (fun q => q.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1)))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, h0, map_zero] at nat
  have e2 : ((thick R I 0).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = 0 := nat.symm
  rw [e2, gs_eq g z (thick R I 0 ⁻¹ᵁ ⊤) (show g z ∈ thick R I 0 ⁻¹ᵁ ⊤ from trivial), map_zero, map_zero]

end GlobalTheory.FamWtZero

namespace GlobalTheory.FamWtZero

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FamIntAt

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_psi_van {I : Ideal R} (D : DegData R I) (χ : D.toPre.X) (hχ : χ ≠ 0) :
    ∃ Ψ : LB.Sec (LB.LinComb D.toPre.P.L (Y := Spec (CommRingCat.of R)) (K := PUnit) (fun _ => (D.toPre.c χ).left)
      (fun _ => -1)),
      (∀ (T : Over (Spec (CommRingCat.of R))) (σ : T ⟶ TF (R := R) (FractionRing R)) (z : T.left) (J),
        Good D.toPre.P.L z J → sval Ψ ((σ.left ≫ jFK (R := R) (FractionRing R)) ≫ jK R) z J =
          (val (D.toPre.psi χ) (σ.left ≫ jFK (R := R) (FractionRing R)) z J).val) ∧
      ∀ (T : Scheme.{0}) (g : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (0 + 1)))) (z : T) (J), Good D.toPre.P.L z J →
        sval Ψ (g ≫ thick R I 0) z J = 0 := by
  have hP := D.psi_pos χ hχ
  obtain ⟨Ψ, hΨ⟩ := exists_psi_of_psiIn hP
  refine ⟨Ψ, fun T σ z J hJ => hΨ _ _ z J hJ, fun T g z J hJ => ?_⟩
  set p := J ((g ≫ thick R I 0) ≫ (D.toPre.c χ).left) with hp
  have hm : (g ≫ thick R I 0) z ∈ (D.toPre.c χ).left ⁻¹ᵁ D.toPre.P.L.U p := hJ _
  obtain ⟨_, ⟨V, hV, rfl⟩, hvV, hVp⟩ := (Spec (CommRingCat.of R)).isBasis_affineOpens.exists_subset_of_mem_open
    (show (g ≫ thick R I 0) z ∈ ((D.toPre.c χ).left ⁻¹ᵁ D.toPre.P.L.U p : (Spec (CommRingCat.of R)).Opens) from hm)
    ((D.toPre.c χ).left ⁻¹ᵁ D.toPre.P.L.U p).isOpen
  have h' : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.toPre.P.L (K := PUnit) (fun _ => D.toPre.xK χ) (fun _ => -1)).U (fun _ => p) :=
    fun y hy => PsiInPull.mem_wchart _ _ _ _ (hVp hy)
  obtain ⟨a, ha, hae⟩ := hP (fun _ => p) V hV hVp h'
  have hVW : V ≤ LB.wchart D.toPre.P.L (fun _ : PUnit => (D.toPre.c χ).left) (fun _ => p) :=
    fun y hy => PsiInPull.mem_wchart _ _ _ _ (hVp hy)
  have hgen : jK R (genPt R) ∈ V := PsiInPull.jK_mem _ V fun h0 =>
    (h0.le hvV : (g ≫ thick R I 0) z ∈ (⊥ : (Spec (CommRingCat.of R)).Opens))
  have eqa : ((Spec (CommRingCat.of R)).presheaf.map (homOfLE hVW).op).hom (Ψ.f (fun _ => p)) = a := by
    refine PsiInPull.gs_injective (jK R) (genPt R) (PsiInPull.jK_mem _) V hgen ((gs_res _ _ hVW hgen _).trans ?_)
    obtain ⟨J', hJ', eJ'⟩ := exists_good D.toPre.P.L D.toPre.P.isLB (genPt R)
      (fun _ : PUnit => jK R ≫ (D.toPre.c χ).left) (fun _ => p) (fun _ _ _ => rfl) (fun _ => hVp hgen)
    have e1 := hΨ _ (𝟙 _) (genPt R) J' hJ'
    rw [Category.id_comp, sval_of Ψ (jK R) (genPt R) J' (fun _ => p) (fun _ => eJ' PUnit.unit),
      val_of (D.toPre.psi χ) (𝟙 (TK R).left) (genPt R) J' (fun _ => p) (fun _ => (congrArg J' (Category.id_comp _)).trans (eJ' PUnit.unit))] at e1
    rw [e1]
    have e := gs_pull (𝟙 _) (jK R) (genPt R) V hgen a
    rw [Category.id_comp] at e
    rw [← e, hae]
    exact ((gs_res (𝟙 _) (genPt R) h' hgen _).trans (gs_unit _ _ _ (h' hgen) _)).symm
  rw [sval_of Ψ (g ≫ thick R I 0) z J (fun _ => p) (fun _ => rfl)]
  refine (gs_res _ z hVW hvV _).symm.trans ?_
  rw [eqa]
  exact gs_thick_eq_zero I g z V hvV ha

theorem exists_inv_zero {I : Ideal R} (D : DegData R I) :
    ∃ Φ : LB.Sec (LB.LinComb D.toPre.P.L (Y := Spec (CommRingCat.of R)) (K := PUnit) (fun _ => (D.toPre.c 0).left)
      (fun _ => - -1)),
      ∀ (T : Over (Spec (CommRingCat.of R))) (σ : T ⟶ TF (R := R) (FractionRing R)) (z : T.left) (J),
        Good D.toPre.P.L z J → sval Φ ((σ.left ≫ jFK (R := R) (FractionRing R)) ≫ jK R) z J =
          ((val (D.toPre.psi 0) (σ.left ≫ jFK (R := R) (FractionRing R)) z J)⁻¹).val := by
  have c0 : D.toPre.c 0 = 1 := by
    have m : D.toPre.c (0 + 0) = D.toPre.c 0 * D.toPre.c 0 := D.toPre.c_add 0 0
    rw [add_zero] at m
    exact mul_eq_left.1 m.symm
  have c1 : (D.toPre.c 0).left = eSec D.toPre.P.A := by
    rw [c0, Hom.one_def, toUnit_unit, Category.id_comp]; rfl
  obtain ⟨Φ, hΦ⟩ := exists_sec D.toPre.P.isLB (Y := Spec (CommRingCat.of R)) (K' := PUnit)
    (φ' := fun _ => (D.toPre.c 0).left) (ε' := fun _ => - -1) (fun U _ h => by simp only [c1, neg_neg])
    (Geo.Tor.genSec D.toPre.rig D.toPre.rig_gen)
  refine ⟨Φ, fun T σ z J hJ => (hΦ _ _ z J hJ).trans ((sval_genSec _ _ _ z hJ).trans (congrArg Units.val ?_))⟩
  have C : IsCub (th D.toPre z J) := isCub_cubV D.toPre.cub hJ
  have t := tau_mul σ hJ D.tau_bimult 0 0 0
  have q := UUA.psi_add σ hJ (0 : D.toPre.X) 0
  have c2 : cP D.toPre T 0 = 1 := by simpa using cPoint_nsmul D.toPre T 0 0
  have hpt : ∀ a b c : D.toPre.X, a = b → val (D.toPre.tau a c) (σ.left ≫ jFK (R := R) (FractionRing R)) z J =
      val (D.toPre.tau b c) (σ.left ≫ jFK (R := R) (FractionRing R)) z J := by rintro a b c rfl; rfl
  have hpp : ∀ a b : D.toPre.X, a = b → val (D.toPre.psi a) (σ.left ≫ jFK (R := R) (FractionRing R)) z J =
      val (D.toPre.psi b) (σ.left ≫ jFK (R := R) (FractionRing R)) z J := by rintro a b rfl; rfl
  rw [hpt _ _ _ (add_zero 0), c2, C.face] at t
  rw [hpp _ _ (add_zero 0), ← mul_left_cancel t, _root_.one_mul, _root_.mul_assoc] at q
  have q' := (mul_eq_left.1 q.symm)
  have e : val D.toPre.rigK (σ.left ≫ jFK (R := R) (FractionRing R)) z J =
    val D.toPre.rig ((σ.left ≫ jFK (R := R) (FractionRing R)) ≫ jK R) z J := val_pull hJ _ _ _
  rw [e] at q'
  exact eq_inv_of_mul_eq_one_right q'

theorem app_eq_zero_of_sval {X Y Y₀ : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (ρ : Y₀ ⟶ Y)
    (h : ∀ (y : Y₀) J, Good L y J → sval s ρ y J = 0) (j : K → L.ι) :
    (ρ.app (LB.wchart L φ j)).hom (s.f j) = 0 := by
  refine fn_ext fun y hy => ?_
  choose I hI using fun χ : Y₀ ⟶ X => exists_chart hL (χ y)
  have e := gs_pull (𝟙 Y₀) ρ y (LB.wchart L φ j) hy (s.f j)
  rw [Category.id_comp] at e
  rw [e]
  refine (sec_trans s ρ y hy (Good.mem hI φ ρ)).trans ?_
  exact (congrArg (fun t => (trF φ ε ρ y j fun k => I (ρ ≫ φ k)).val * t) (h y I hI)).trans
    (by rw [mul_zero, gs_eq _ _ _ hy, map_zero, map_zero])

end GlobalTheory.FamWtZero

namespace GlobalTheory.FamWtZero

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FamIntAt

variable {R : Type} [CommRing R] [IsDomain R]

open SectionScalarValuation in

theorem exists_const0 {I : Ideal R} (D : DegData R I) (k : ℕ) (mu : D.toPre.X) (hmu : mu ≠ 0) :
    ∃ (Ix : Type) (_ : Fintype Ix) (φV : Ix → (Spec (CommRingCat.of R) ⟶ D.toPre.P.A.left)) (εV : Ix → ℤ)
      (w : LB.Sec (LB.LinComb D.toPre.P.L φV εV)),
      (∀ (U : Type) [CommGroup U] (h : (D.toPre.P.A.left ⟶ D.toPre.P.A.left) → U),
        ∏ i, h (D.toPre.P.A.hom ≫ φV i) ^ εV i =
          (h (cQ D.toPre D.toPre.P.A 0 * cQ D.toPre D.toPre.P.A mu).left)⁻¹ * h (cQ D.toPre D.toPre.P.A 0).left *
            h (cQ D.toPre D.toPre.P.A mu).left * (h (1 : D.toPre.P.A ⟶ D.toPre.P.A).left)⁻¹ *
            (h (cQ D.toPre D.toPre.P.A mu).left ^ (k + 1))⁻¹ * h (1 : D.toPre.P.A ⟶ D.toPre.P.A).left ^ (k + 1)) ∧
      (∀ (T : Over (Spec (CommRingCat.of R))) (σ : T ⟶ TF (R := R) (FractionRing R)) (z : T.left) (J),
        Good D.toPre.P.L z J → sval w ((σ.left ≫ jFK (R := R) (FractionRing R)) ≫ jK R) z J =
            (val (DegPre.famMult D.toPre (FractionRing R) (k + 1) mu 0) σ.left z J).val) ∧
      ∀ (T : Scheme.{0}) (g : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (0 + 1)))) (z : T) (J), Good D.toPre.P.L z J →
        sval w (g ≫ thick R I 0) z J = 0 := by
  choose Ψ hΨ using exists_psi D
  obtain ⟨Ψ₁, hΨ₁, hv⟩ := exists_psi_van D (mu + 0) (by simpa using hmu)
  obtain ⟨Φ, hΦ⟩ := exists_inv_zero D
  refine ⟨_, inferInstance, _, _, SectionArithmetic.mulSec (SectionArithmetic.mulSec Ψ₁ Φ) (SectionArithmetic.mulSec (SectionArithmetic.powSec fun _ : Fin k => Ψ mu)
    (SectionArithmetic.powSec (L := D.toPre.P.L) (Y := Spec (CommRingCat.of R)) (K := PUnit) (φ := fun _ => eSec D.toPre.P.A)
      (ε := fun _ => 1) fun _ : Fin k => Geo.Tor.genSec D.toPre.rig D.toPre.rig_gen)), fun U _ h => ?_,
    fun T σ z J hJ => ?_, fun T g z J hJ => ?_⟩
  · have hc : ∀ χ, D.toPre.P.A.hom ≫ (D.toPre.c χ).left = (cQ D.toPre D.toPre.P.A χ).left := fun χ => by simp [cQ]
    have he : D.toPre.P.A.hom ≫ eSec D.toPre.P.A = (1 : D.toPre.P.A ⟶ D.toPre.P.A).left := by
      rw [Hom.one_def]; simp [eSec]
    simp only [Fintype.prod_sum_type, Fintype.prod_prod_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, hc, he,
      cQ_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_punit, Fintype.card_prod,
      _root_.mul_one]
    rw [mul_comm (cQ D.toPre D.toPre.P.A mu)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
    module
  · have e : val D.toPre.rigK (σ.left ≫ jFK (R := R) (FractionRing R)) z J =
      val D.toPre.rig ((σ.left ≫ jFK (R := R) (FractionRing R)) ≫ jK R) z J := val_pull hJ _ _ _
    refine ((SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
      ((SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·) (hΨ₁ T σ z J hJ) (hΦ T σ z J hJ)))
      ((SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
        ((SectionArithmetic.sval_powSec _ _ z hJ).trans (Finset.prod_congr rfl fun _ _ => hΨ _ T σ z J hJ))
        ((SectionArithmetic.sval_powSec _ _ z hJ).trans (Finset.prod_congr rfl fun _ _ =>
          (sval_genSec _ _ _ z hJ).trans (congrArg Units.val e.symm))))))).trans ?_
    rw [val_famMult σ hJ, UUA.val_powGen', UUA.val_powGen', UUA.psi_add σ hJ, Finset.prod_const, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    linear_combination ((val (D.toPre.tau mu 0) (σ.left ≫ jFK (R := R) (FractionRing R)) z J).val *
      (val (D.toPre.psi mu) (σ.left ≫ jFK (R := R) (FractionRing R)) z J).val ^ (k + 1) *
      (val D.toPre.rigK (σ.left ≫ jFK (R := R) (FractionRing R)) z J).val ^ (k + 1)) *
      (val (D.toPre.psi 0) (σ.left ≫ jFK (R := R) (FractionRing R)) z J).mul_inv
  · rw [SectionArithmetic.sval_mulSec _ _ _ z hJ, SectionArithmetic.sval_mulSec _ _ _ z hJ, hv T g z J hJ, zero_mul, zero_mul]

end GlobalTheory.FamWtZero

namespace GlobalTheory.FamWtZero

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FamIntAt

open SectionScalarValuation in

theorem exists_family : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (D : DegData R (maximalIdeal R)) (k : ℕ), 1 ≤ k → ∀ σ₀ : D.toPre.SecB k 0,
    ∃ (F : Fam D.toPre (FractionRing R) k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α),
      (∀ α : D.toPre.X, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α)
        (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left
        (scal (DegPre.BF D.toPre (FractionRing R)).hom (1 : R))) ∧ f 0 = σ₀ ∧
      ∀ α : D.toPre.X, α ≠ 0 → ∀ j : Fin 4 → D.toPre.P.L.ι,
        ((D.toPre.prBe (maximalIdeal R) 0).left.app _).hom ((f α).f j) = 0 := by
  intro R _ _ _ _ D k hk σ₀
  classical
  have hG : GlobalFnsSt := GlobalTheory.globalFns_holds
  have hL := D.toPre.P.isLB
  have hscal : scal (DegPre.BF D.toPre (FractionRing R)).hom (1 : R) = 1 := by simp [scal]
  rw [hscal]
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨σ, hσ⟩ := exists_sec hL (φ' := DegPre.famφ D.toPre (FractionRing R) 0) (ε' := DegPre.famε (k + 1))
    (fun U _ g => Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq])
    (SectionArithmetic.pullSec σ₀ (DegPre.prB D.toPre (FractionRing R)).left)
  obtain ⟨Φ, hΦ, hΦ0⟩ := UUA.exists_fam_rep (F := FractionRing R) hG D.tau_bimult (k + 1) 0 (fun a b h => by
    have h' : ((k + 1 : ℕ) : ℤ) • a = ((k + 1 : ℕ) : ℤ) • b := by
      rw [natCast_zsmul, natCast_zsmul]; exact add_left_cancel h
    exact smul_right_injective D.toPre.X (by omega : ((k + 1 : ℕ) : ℤ) ≠ 0) h') σ
  have hw0 : (D.toPre.prBe (maximalIdeal R) 0).left ≫ D.toPre.P.A.hom =
      (thickObj R (maximalIdeal R) 0 D.toPre.P.A).hom ≫ thick R (maximalIdeal R) 0 := Over.w _
  have key : ∀ α : D.toPre.X, ∃ f : D.toPre.SecB (k + 1) α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε (k + 1)) (Φ.s α)
        (D.toPre.famφB α) (DegPre.famε (k + 1)) f (DegPre.prB D.toPre (FractionRing R)).left 1 ∧
      (∀ h : (0 : D.toPre.X) = α, f = h ▸ σ₀) ∧
      (α ≠ 0 → ∀ j : Fin 4 → D.toPre.P.L.ι, ((D.toPre.prBe (maximalIdeal R) 0).left.app _).hom (f.f j) = 0) := by
    intro α
    by_cases hα : (0 : D.toPre.X) = α
    · subst hα
      refine ⟨σ₀, secScal_of_sval hL fun y J hJ => ?_, fun _ => rfl, fun h => absurd rfl h⟩
      rw [hΦ]
      exact ((hσ _ _ y J hJ).trans (SectionArithmetic.sval_pullSec _ _ _ y hJ)).symm
    by_cases hc : ∃ mu, (0 : D.toPre.X) + (k + 1) • mu = α
    · obtain ⟨mu, rfl⟩ := hc
      have hmu : mu ≠ 0 := fun h0 => hα (by rw [h0]; simp)
      obtain ⟨Ix, _, φV, εV, w, hC, hw, hwv⟩ := exists_const0 D k mu hmu
      obtain ⟨f, hf⟩ := exists_move D.toPre (k + 1) 0 mu w hC σ₀
      refine ⟨f, secScal_of_sval hL fun y J hJ => ?_, fun h => absurd h hα, fun _ j => ?_⟩
      · obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D.toPre) (F := FractionRing R) hG (k + 1) mu 0
        have e₁ := (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (Φ.fe mu 0 u hu hc) _ (𝟙 _) y J hJ
        have e₂ := hv u hu hc _ (𝟙 _) y J hJ
        rw [uVal_id, Over.id_left, Category.id_comp, comp_cP] at e₂
        have e₃ := hf _ (DegPre.prB D.toPre (FractionRing R)) y J hJ
        have e₄ := hw _ (fst (TF (R := R) (FractionRing R)) D.toPre.P.A) y J hJ
        have a₁ : (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom =
            ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)) ≫ jK R := by
          rw [Over.w, Category.assoc]
          exact (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)).symm
        have a₂ : (DegPre.trF D.toPre (FractionRing R) mu).left ≫ (DegPre.prB D.toPre (FractionRing R)).left =
            (DegPre.prB D.toPre (FractionRing R) * cQ D.toPre _ mu).left := by
          rw [← Over.comp_left, DegPre.trF, DegPre.prB, lift_snd]
          rfl
        have e₅ : sval σ (DegPre.trF D.toPre (FractionRing R) mu).left y J =
            sval σ₀ (DegPre.prB D.toPre (FractionRing R) * cQ D.toPre _ mu).left y J := by
          refine (hσ _ _ y J hJ).trans ((SectionArithmetic.sval_pullSec _ _ _ y hJ).trans ?_)
          rw [a₂]
        rw [a₁, e₄] at e₃
        rw [Category.id_comp, hΦ, e₅, e₂, Units.val_mul] at e₁
        rw [Category.id_comp, e₃, e₁]
        rw [_root_.mul_assoc]; rfl
      · refine app_eq_zero_of_sval hL f _ (fun y J hJ => ?_) j
        rw [hf _ (D.toPre.prBe (maximalIdeal R) 0) y J hJ, hw0, hwv _ _ y J hJ, mul_zero]
    · refine ⟨SecOps.secZero, secScal_of_sval hL fun y J hJ => ?_, fun h => absurd h hα, fun _ j => ?_⟩
      · rw [UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _),
          UUA.sval_zero_of (hΦ0 α fun mu e => hc ⟨mu, e⟩) _ y J (hJ.mem _ _)]
      · exact map_zero _
  choose f h1 h2 h3 using key
  exact ⟨Φ, f, h1, h2 0 rfl, h3⟩

end GlobalTheory.FamWtZero
