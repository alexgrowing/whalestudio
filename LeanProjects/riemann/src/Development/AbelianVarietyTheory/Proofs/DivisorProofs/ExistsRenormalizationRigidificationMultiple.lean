import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors

noncomputable section
namespace GlobalTheory.Poinc.Renorm

theorem alg_renorm {M : Type} [CommGroup M] {q q₀ a p p₀ g g₀ x y : M} (h₀ : q = y * x⁻¹ * q₀)
    (h₁ : a = g₀ * (q₀ * p₀)⁻¹) (h₂ : p = x * p₀) (h₃ : g = y * g₀) : q * (a * p) = g := by
  rw [h₀, h₁, h₂, h₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

section Norm
open GlobalTheory.UT.CoefBasic GlobalTheory.ExpansionValueZero GlobalTheory.BoxExpansion

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem exists_unit_normW (w₀ : W0 U) (hw : w₀.IsGen) (ρ : LB.Gen (A.L.pull (eSec A.A))) (hρ : ρ.IsGen) :
    ∃ a : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)ˣ, NormW U w₀ (GlobalTheory.UU.scaleGen a ρ) := by
  let z₀ : Spec (CommRingCat.of (FractionRing R)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  obtain ⟨JA₀, hA₀⟩ := exists_good' A.isLB z₀
  obtain ⟨JG₀, hG₀⟩ := exists_good' U.LG.isLB z₀
  let eK : Spec (CommRingCat.of (FractionRing R)) ⟶ ((Over.pullback (jK R)).obj G).left :=
    eSec ((Over.pullback (jK R)).obj G)
  have h₁ : eK ≫ U.gen.hom.left = eSec A.A := EvalZero.eK_gen U
  have h₂ : eK ≫ pullback.fst G.hom (jK R) = jK R ≫ eSec G := EvalZero.eK_fst
  have hsurj : ∀ u : ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk z₀)ˣ,
      ∃ a : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)ˣ, gm (𝟙 _) z₀ ⊤ a = u := by
    intro u
    obtain ⟨V, hV, s, hs⟩ := (Spec (CommRingCat.of (FractionRing R))).presheaf.exists_germ_eq u.val
    obtain rfl : V = ⊤ := eq_top_iff.2 fun y _ =>
      (Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) z₀ y) ▸ hV
    have hu : IsUnit s := (Spec (CommRingCat.of (FractionRing R))).toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      obtain rfl : z₀ = y := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) z₀ y
      exact (congrArg IsUnit hs).mpr u.isUnit
    exact ⟨hu.unit, Units.ext ((gm_val _ z₀ ⊤ trivial _).trans hs)⟩
  obtain ⟨a, ha⟩ := hsurj (val (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (jK R) z₀ JG₀ *
    (pw w₀ eK z₀ (JA₀ (eSec A.A)) (JG₀ (jK R ≫ eSec G)) *
      val (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) (Z := Spec (CommRingCat.of (FractionRing R)))
        ρ (𝟙 _) z₀ JA₀)⁻¹)
  refine ⟨a, hw, GlobalTheory.UU.scaleGen_isGen a hρ, fun z JA JG hA hG => ?_⟩
  obtain rfl : z₀ = z := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) z₀ z
  have mA : ∀ J, Good A.L z₀ J → U.gen.hom.left (eK z₀) ∈ A.L.U (J (eSec A.A)) := fun J hJ =>
    (congrArg (fun q => q z₀ ∈ A.L.U (J (eSec A.A))) h₁).mpr (hJ _)
  have mG : ∀ J, Good U.LG.L z₀ J → pullback.fst G.hom (jK R) (eK z₀) ∈ U.LG.L.U (J (jK R ≫ eSec G)) := fun J hJ =>
    (congrArg (fun q => q z₀ ∈ U.LG.L.U (J (jK R ≫ eSec G))) h₂).mpr (hJ _)
  have b₀ : gw w₀ eK z₀ (JG (jK R ≫ eSec G)) (fun _ => JA (eSec A.A)) =
      pw w₀ eK z₀ (JA (eSec A.A)) (JG (jK R ≫ eSec G)) := rfl
  have b₁ := pw_trans hw eK z₀ (mA _ hA) (mA _ hA₀) (mG _ hG) (mG _ hG₀)
  have b₂ := val_tr (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1)
    (Z := Spec (CommRingCat.of (FractionRing R))) hρ (𝟙 _) hA hA₀
  have b₃ := val_tr (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rigGen (jK R) hG hG₀
  have b₄ := GlobalTheory.UU.val_scaleGen (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) a ρ (𝟙 _) hA
  rw [h₁, h₂] at b₁
  rw [Fintype.prod_unique, zpow_one] at b₂ b₃
  rw [Category.id_comp] at b₂
  rw [b₀, b₄]
  exact alg_renorm b₁ ha b₂ b₃

end Norm

theorem alg_rig {M : Type} [CommGroup M] (g v : M) (k : ℤ) :
    g ^ (k - 1) * (v ^ k * v⁻¹) = (g * v) ^ k * (g * v)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem alg_frame {M : Type} [CommGroup M] {g t α r : M} {k : ℤ} (h : t ^ k = α * r ^ (1 : ℤ)) :
    (g * t) ^ k = g ^ (k - 1) * α * (g * r) ^ (1 : ℤ) := by
  apply Additive.ofMul.injective
  replace h := congrArg Additive.ofMul h
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at h ⊢
  linear_combination (norm := module) h

section Tors
variable {S : Scheme.{0}} {P : PolAV S}

theorem isTorsFrame_scale (rig : LB.Gen (P.L.pull (eSec P.A))) (a : Γ(S, ⊤)ˣ) {n : ℕ} {T : Over S} {x : T ⟶ P.A}
    {τ τ' : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))}
    (H : IsTorsFrame P rig n x τ) (hτ' : τ'.IsGen)
    (ht : ∀ z J, Good P.L z J → val τ' (𝟙 _) z J = gm T.hom z ⊤ a * val τ (𝟙 _) z J) :
    IsTorsFrame P (GlobalTheory.UU.scaleGen a rig) n x τ' := by
  obtain ⟨hn, -, α, hα, hN, hc⟩ := H
  let u : Γ(P.A.left, ⊤)ˣ := pullU P.A.hom ⊤ a ^ ((n : ℤ) ^ 2 - 1)
  have hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ P.A.left) (z : Z),
      gm r z ⊤ u = gm (r ≫ P.A.hom) z ⊤ a ^ ((n : ℤ) ^ 2 - 1) := fun Z r z =>
    (map_zpow _ _ _).trans (congrArg (· ^ _) (gm_pull r P.A.hom z ⊤ trivial a))
  have hr : ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) J, Good P.L z J →
      FrameMove.rval (GlobalTheory.UU.scaleGen a rig) r z J = gm r z ⊤ a * FrameMove.rval rig r z J := fun Z r z J hJ =>
    GlobalTheory.UU.val_scaleGen (L := P.L) (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) a rig r hJ
  have hα' : ∀ (Z : Scheme.{0}) (r : Z ⟶ P.A.left) (z : Z) J, Good P.L z J →
      val (GlobalTheory.UU.scaleGen u α) r z J = gm r z ⊤ u * val α r z J := fun Z r z J hJ =>
    GlobalTheory.UU.val_scaleGen u α r hJ
  have he : eSec P.A ≫ P.A.hom = 𝟙 S := Over.w η[P.A]
  refine ⟨hn, hτ', GlobalTheory.UU.scaleGen u α, GlobalTheory.UU.scaleGen_isGen u hα, corr_of_val P.isLB fun y J hJ => ?_,
    corr_of_val P.isLB fun y J hJ => ?_⟩
  · have e0 : val α (𝟙 _ ≫ eSec P.A) y J =
        FrameMove.rval rig (𝟙 _) y J ^ ((n : ℤ) ^ 2) * (FrameMove.rval rig (𝟙 _) y J)⁻¹ :=
      (val_pull hJ α (eSec P.A) (𝟙 _)).symm.trans ((val_corr hJ hN (𝟙 _)).trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (map_zpow _ _ _) (val_inv _ _))))
    have e1 : val (rigPow P.A P.L (GlobalTheory.UU.scaleGen a rig) ((n : ℤ) ^ 2)) (𝟙 _) y J =
        FrameMove.rval (GlobalTheory.UU.scaleGen a rig) (𝟙 _) y J ^ ((n : ℤ) ^ 2) := map_zpow _ _ _
    rw [val_pull hJ, hα' _ _ _ _ hJ, hu, e0, val_mul hJ, e1, val_inv, hr _ _ _ _ hJ, Category.assoc, he,
      Category.id_comp]
    rw [show val (L := P.L) (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) (GlobalTheory.UU.scaleGen a rig) (𝟙 (𝟙_ (Over S)).left) y J = _ from hr _ _ _ _ hJ]
    exact alg_rig (M := (S.presheaf.stalk y)ˣ) _ _ _
  · have a1 : val τ (𝟙 _) y J ^ ((n : ℤ) ^ 2) = val α (𝟙 _ ≫ x.left) y J * FrameMove.rval rig (𝟙 _ ≫ T.hom) y J ^ (1 : ℤ) :=
      (map_zpow _ _ _).symm.trans ((val_corr hJ hc (𝟙 _)).trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (val_pull hJ _ _ _) (FrameMove.val_rigT _ _ _ hJ))))
    rw [FrameMove.val_powFrame, val_mul hJ, val_pull hJ, FrameMove.val_rigT _ _ _ hJ, hα' _ _ _ _ hJ, hu,
      hr _ _ _ _ hJ, ht y J hJ, Category.assoc, Over.w x]
    simp only [Category.id_comp] at a1 ⊢
    exact alg_frame a1

end Tors

theorem cst_gm {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]
    (a : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)ˣ) (z : (TFK (R := R) F).left) :
    (gm (jFK (R := R) F) z ⊤ a).val = cst (R := R) F z (algebraMap (FractionRing R) F
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom a.val)) := by
  rw [← gs_unit _ z ⊤ trivial]
  have e : a.val = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom a.val) := by simp
  conv_lhs => rw [e]
  exact FrameMove.gs_spMap (algebraMap (FractionRing R) F) z _

theorem exists_renorm : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U), w₀.IsGen → ∀ ρ : LB.Gen (A.L.pull (eSec A.A)), ρ.IsGen → ∃ (ρ' : LB.Gen (A.L.pull (eSec A.A))) (c : FractionRing R), c ≠ 0 ∧ NormW U w₀ ρ' ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) (x : TFK (R := R) F ⟶ A.A) (fr fr' : FrAt x), IsTorsFrame A ρ N x fr → fr'.IsGen → (∀ z J, Good A.L z J → (val fr' (𝟙 _) z J).val = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z (algebraMap (FractionRing R) F c)) * (val fr (𝟙 _) z J).val) → IsTorsFrame A ρ' N x fr' := by
  intro R _ _ I D A G _ _ U w₀ hw ρ hρ
  obtain ⟨a, ha⟩ := exists_unit_normW U w₀ hw ρ hρ
  refine ⟨GlobalTheory.UU.scaleGen a ρ, (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom a.val, ?_, ha,
    fun F _ _ N x fr fr' H hfr' hv => ?_⟩
  · exact (a.isUnit.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom).ne_zero
  · refine isTorsFrame_scale ρ a H hfr' fun z J hJ => Units.ext ?_
    rw [Units.val_mul, hv z J hJ]
    exact congrArg (· * _) (cst_gm F a z).symm

end GlobalTheory.Poinc.Renorm
end
