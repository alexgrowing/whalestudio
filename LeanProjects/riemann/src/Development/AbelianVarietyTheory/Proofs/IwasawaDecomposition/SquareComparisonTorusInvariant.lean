import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RigidifiedIsoRespectsCubeAndSymmetry
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationPolarisationsAgreeAtLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GmSqPullG

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace TorusInvarianceSq

open TorusInvariance SqLevel

theorem sq_cube_alg {V K : Type} [CommGroup V] [Fintype K] (ε : K → ℤ) (W W' B a : K → V) (c c' : V)
    (hc : c ^ 2 = (∏ k, B k ^ ε k) * c' ^ 2) (h : ∀ k, a k * W' k ^ 2 = W k ^ 2 * B k) :
    ((∏ k, W k ^ ε k) * c) ^ 2 = (∏ k, a k ^ ε k) * ((∏ k, W' k ^ ε k) * c') ^ 2 := by
  have hk : ∏ k, ((W k ^ ε k) ^ 2 * B k ^ ε k) = ∏ k, (a k ^ ε k * (W' k ^ ε k) ^ 2) :=
    Finset.prod_congr rfl fun k _ => by
      have := congrArg (· ^ ε k) (h k)
      simp only [mul_zpow] at this
      have p : ∀ X : V, (X ^ ε k) ^ 2 = (X ^ 2) ^ ε k := fun X => by rw [sq, sq, mul_zpow]
      rw [p, p]
      exact this.symm
  calc ((∏ k, W k ^ ε k) * c) ^ 2 = (∏ k, (W k ^ ε k) ^ 2) * ((∏ k, B k ^ ε k) * c' ^ 2) := by
        rw [mul_pow, Finset.prod_pow, hc]
    _ = (∏ k, ((W k ^ ε k) ^ 2 * B k ^ ε k)) * c' ^ 2 := by
        rw [Finset.prod_mul_distrib, _root_.mul_assoc]
    _ = (∏ k, (a k ^ ε k * (W' k ^ ε k) ^ 2)) * c' ^ 2 := by rw [hk]
    _ = (∏ k, a k ^ ε k) * ((∏ k, W' k ^ ε k) * c') ^ 2 := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow, mul_pow, _root_.mul_assoc]

section Level

open WCub EvenPull

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] {e : ℕ}
variable {D D' : DegData R I} {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {U : UnifPre I D A G}
  {U' : UnifPre I D' A' G}
  (u : LB.Iso ((sqLB D'.toPre.P.L).pull (U'.gt e).pG.left) ((sqLB D.toPre.P.L).pull (U.gt e).pG.left))

def aVal {Z : Scheme.{0}} (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
    (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι) (r : Z ⟶ (thickObj R I e G).left) : (Z.presheaf.stalk z)ˣ :=
  gw u r z (fun _ => J (r ≫ (U.gt e).pG.left)) (fun _ _ => J' (r ≫ (U'.gt e).pG.left))

variable {wL : LB.Iso (sqLB U'.LG.L) (sqLB U.LG.L)}
  (sq : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι)
    (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM →
    (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (r z) ∈ U.LG.L.U jL →
    (fstG I e G).left (r z) ∈ U'.LG.L.U jL' →
    gw u r z (fun _ => jM) (fun _ _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 =
      gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG I e G).left) z (fun _ => jL) (fun _ => jL'))
include sq

theorem cube_aVal (hc : ∀ (Z : Scheme.{0}) (r : Z ⟶ (G3 G).left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t r z N ^ 2 =
        (∏ k : thK.{0}, gv wL (r ≫ thφ G (x3 G) k) z (fun _ => N (r ≫ thφ G (x3 G) k))
          (fun _ => N' (r ≫ thφ G (x3 G) k)) ^ thε k) *
        val (L := U'.LG.L) (φ := thφ G (x3 G)) (ε := thε) U'.cubG.t r z N' ^ 2)
    {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x : Fin 3 → (T ⟶ thickObj R I e G))
    {z : T.left} {J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L z J) (hJ' : Good D'.toPre.P.L z J') :
    val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
        (tri (thick R I e) (U.gt e).pG x) z J ^ 2 =
      (∏ k : thK.{0}, aVal u z J J' (psum (thickObj R I e G) x k.down).left ^ thε k) *
        val (L := D'.toPre.P.L) (φ := thφ D'.toPre.P.A (x3 D'.toPre.P.A)) (ε := thε) D'.toPre.cub.t
          (tri (thick R I e) (U'.gt e).pG x) z J' ^ 2 := by
  choose N hN using fun χ : T.left ⟶ G.left => exists_chart U.LG.isLB (χ z)
  choose N' hN' using fun χ : T.left ⟶ G.left => exists_chart U'.LG.isLB (χ z)
  have f₃ := tri_thφ (thick R I e) (fstG I e G) x (𝟙 _) (Category.id_comp _).symm
  have e₁ := cube_val U x hJ hN
  have e₂ := cube_val U' x hJ' hN'
  have e₃ := hc _ (tri (thick R I e) (fstG I e G) x) z N N' hN hN'
  have e₄ : val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t (tri (thick R I e) (fstG I e G) x) z N ^ 2 =
      (∏ k : thK.{0}, gv wL ((psum (thickObj R I e G) x k.down).left ≫ (fstG I e G).left) z
        (fun _ => N ((psum (thickObj R I e G) x k.down).left ≫ (fstG I e G).left))
        (fun _ => N' ((psum (thickObj R I e G) x k.down).left ≫ (fstG I e G).left)) ^ thε k) *
      val (L := U'.LG.L) (φ := thφ G (x3 G)) (ε := thε) U'.cubG.t (tri (thick R I e) (fstG I e G) x) z N' ^ 2 :=
    e₃.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => by rw [f₃ k]) rfl)
  rw [e₁, e₂]
  exact sq_cube_alg thε _ _ _ _ _ _ e₄ fun k => sq _ _ z _ _ _ _ (hJ _) (hJ' _) (hN _) (hN' _)

theorem even_aVal (hs : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U.symG r z N ^ 2 =
        (∏ k : Fin 2, gv wL (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k) z
          (fun _ => N (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k))
          (fun _ => N' (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k)) ^ (![1, -1] : Fin 2 → ℤ) k) *
        val (L := U'.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U'.symG r z N' ^ 2)
    {Z : Scheme.{0}} (r : Z ⟶ (thickObj R I e G).left) {z : Z}
    {J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι} {J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L z J) (hJ' : Good D'.toPre.P.L z J') :
    val D.toPre.sym (r ≫ (U.gt e).pG.left) z J ^ 2 * aVal u z J J' r =
      aVal u z J J' (r ≫ (ι[thickObj R I e G]).left) * val D'.toPre.sym (r ≫ (U'.gt e).pG.left) z J' ^ 2 := by
  choose N hN using fun χ : Z ⟶ G.left => exists_chart U.LG.isLB (χ z)
  choose N' hN' using fun χ : Z ⟶ G.left => exists_chart U'.LG.isLB (χ z)
  have iF : (ι[thickObj R I e G]).left ≫ (fstG I e G).left = (fstG I e G).left ≫ (ι[G]).left := inv_fst _ G
  have e₁ := even_val U r hJ hN
  have e₂ := even_val U' r hJ' hN'
  have e₃ := hs _ (r ≫ (fstG I e G).left) z N N' hN hN'
  rw [Fin.prod_univ_two] at e₃
  let d := fun s : Z ⟶ G.left => gv wL s z (fun _ => N s) (fun _ => N' s)
  have e₄ : val U.symG (r ≫ (fstG I e G).left) z N ^ 2 =
      d ((r ≫ (ι[thickObj R I e G]).left) ≫ (fstG I e G).left) * (d (r ≫ (fstG I e G).left))⁻¹ *
        val U'.symG (r ≫ (fstG I e G).left) z N' ^ 2 := by
    refine e₃.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) ((zpow_one _).trans (congrArg d ?_))
      ((zpow_neg_one _).trans (congrArg (fun s => (d s)⁻¹) (Category.comp_id _)))) rfl)
    rw [Category.assoc r (ι[thickObj R I e G]).left, iF, Category.assoc]; rfl
  have e₅ : ∀ s : Z ⟶ (thickObj R I e G).left, aVal u z J J' s * wVal U' e z J' N' s ^ 2 =
      wVal U e z J N s ^ 2 * d (s ≫ (fstG I e G).left) := fun s => sq _ s z _ _ _ _ (hJ _) (hJ' _) (hN _) (hN' _)
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  have a₄ := congrArg Additive.ofMul e₄
  have a₅ := congrArg Additive.ofMul (e₅ r)
  have a₆ := congrArg Additive.ofMul (e₅ (r ≫ (ι[thickObj R I e G]).left))
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow] at a₁ a₂ a₄ a₅ a₆ ⊢
  linear_combination (norm := abel) 2 • a₁ - 2 • a₂ + a₄ + a₅ - a₆

end Level

end TorusInvarianceSq

open ReciprocityTheory.ChartRestriction.G.DVR TorusInvariance TorusInvarianceSq SqLevel in
set_option maxHeartbeats 400000 in

theorem comparison_sq_torus_invariant : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (G3 G).left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t r z N ^ 2 =
        (∏ k : thK.{0}, gv wL (r ≫ thφ G (x3 G) k) z (fun _ => N (r ≫ thφ G (x3 G) k))
          (fun _ => N' (r ≫ thφ G (x3 G) k)) ^ thε k) *
        val (L := U'.LG.L) (φ := thφ G (x3 G)) (ε := thε) U'.cubG.t r z N' ^ 2) →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U.symG r z N ^ 2 =
        (∏ k : Fin 2, gv wL (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k) z
          (fun _ => N (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k))
          (fun _ => N' (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k)) ^ (![1, -1] : Fin 2 → ℤ) k) *
        val (L := U'.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U'.symG r z N' ^ 2) →
    ∀ (e : ℕ) (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A), IsMonHom β.hom →
    (U'.gt e).q ≫ β.hom = (U.gt e).q →
    ∀ u : LB.Iso ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull (U'.gt e).pG.left)
      ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull (U.gt e).pG.left), u.IsGen →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι)
      (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' →
      (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' →
      gw u r z (fun _ => jM) (fun _ _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 =
        gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG I e G).left) z (fun _ => jL) (fun _ => jL')) →
    ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (τ : Z ⟶ splitTorus _ D.toPre.X) (y : Z ⟶ thickObj R I e G)
      (z : Z.left) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι),
      (U.gt e).pG.left (y.left z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (y.left z) ∈ D'.toPre.P.L.U jM' →
      gw u ((τ ≫ (U.gt e).i) * y).left z (fun _ => jM) (fun _ _ => jM') = gw u y.left z (fun _ => jM) (fun _ _ => jM') := by
  intro _ R _ _ _ I _ D D' A A' G _ _ hG U U' wL _ hc hs e β _ hβ u hu sq Z₀ τ₀ y₀ z₀ jM jM' m m'
  have := (U.gt e).q_hom
  have := (U'.gt e).q_hom
  have := (U.gt e).i_hom
  have := hG.geomConnected
  have := connectedSpace_spec_quotient (I ^ (e + 1)) (Z₀.hom z₀)
  have : GeometricallyConnected (thickObj R I e G).hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd G.hom (thick R I e)))
  have : ConnectedSpace (thickObj R I e G).left :=
    GroupConn.connectedSpace_of_section (thickObj R I e G).hom (η : 𝟙_ _ ⟶ thickObj R I e G).left (Over.w _)
  have hq : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.toPre.X),
      (τ ≫ (U.gt e).i) ≫ (U.gt e).q = (1 : Z ⟶ thickObj R I e G) ≫ (U.gt e).q := fun τ => by
    rw [Category.assoc, (U.gt e).isKernel.w, MonObj.one_comp, ← Category.assoc, comp_toUnit, Hom.one_def]
  have hq' : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.toPre.X),
      (τ ≫ (U.gt e).i) ≫ (U'.gt e).q = (1 : Z ⟶ thickObj R I e G) ≫ (U'.gt e).q := fun τ => by
    rw [← cancel_mono β.hom, Category.assoc _ _ β.hom, Category.assoc _ _ β.hom, hβ]
    exact hq τ
  have hp : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.toPre.X)
      (y : Z ⟶ thickObj R I e G), ((τ ≫ (U.gt e).i) * y).left ≫ (U.gt e).pG.left = y.left ≫ (U.gt e).pG.left :=
    fun τ y => pG_congr _ (by rw [MonObj.mul_comp, hq, ← MonObj.mul_comp, _root_.one_mul])
  have hp' : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.toPre.X)
      (y : Z ⟶ thickObj R I e G), ((τ ≫ (U.gt e).i) * y).left ≫ (U'.gt e).pG.left = y.left ≫ (U'.gt e).pG.left :=
    fun τ y => pG_congr _ (by rw [MonObj.mul_comp, hq', ← MonObj.mul_comp, _root_.one_mul])
  obtain ⟨ρ, key⟩ := exists_ratio_translate (U.gt e).i (linComb_isLB _ D.toPre.P.isLB _ _)
    (linComb_isLB _ D'.toPre.P.isLB _ _) u hu (fun _ => hp) (fun _ => hp')
  have triv := ratio_eq_one (U.gt e).i ρ (fun Z z => by
    choose J hJ using fun χ : Z.left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ z)
    choose J' hJ' using fun χ : Z.left ⟶ D'.toPre.P.A.left => exists_chart D'.toPre.P.isLB (χ z)
    refine ⟨aVal u z J J', fun t y => ?_, fun t t' y => ?_, fun t => ?_⟩
    · rw [aVal, aVal, hp, hp']
      exact key Z t y z _ _ (mem_sq.2 (hJ _)) (mem_sq.2 (hJ' _))
    · have a := cube_aVal u sq hc ![t ≫ (U.gt e).i, t' ≫ (U.gt e).i, y] hJ hJ'
      have b := cube_aVal u sq hc ![1, 1, y] hJ hJ'
      rw [tri_congr (U.gt e) y (hq t) (hq t'), tri_congr (U'.gt e) y (hq' t) (hq' t')] at a
      exact mul_right_cancel (a.symm.trans b)
    · have a := even_aVal u sq hs (t ≫ (U.gt e).i).left hJ hJ'
      have b := even_aVal u sq hs (1 : Z ⟶ thickObj R I e G).left hJ hJ'
      rw [pG_congr (U.gt e) (hq t), pG_congr (U'.gt e) (hq' t)] at a
      exact cancel_even a b)
  rw [key Z₀ τ₀ y₀ z₀ (fun _ => jM) (fun _ => jM') (mem_sq.2 m) (mem_sq.2 m'), triv, map_one, _root_.one_mul]

end GlobalTheory
