import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowPolAV
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValPsiZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorTrivialisationPowerLatticePointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorBundleRigidificationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.TensData

def cpt {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {r : ℕ} {P' : PolAV (Spec (CommRingCat.of R))}
    {pr : Fin r → (P'.A ⟶ D.P.A)} (lim : IsLimit (Fan.mk P'.A pr)) (y : Fin r → D.X) :
    𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P'.A :=
  lim.lift (Fan.mk _ fun i => D.c (y i))

theorem cpt_pr {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {r : ℕ} {P' : PolAV (Spec (CommRingCat.of R))}
    {pr : Fin r → (P'.A ⟶ D.P.A)} (lim : IsLimit (Fan.mk P'.A pr)) (y : Fin r → D.X) (i : Fin r) :
    cpt lim y ≫ pr i = D.c (y i) :=
  lim.fac (Fan.mk _ fun i => D.c (y i)) ⟨i⟩

theorem cpt_add {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {r : ℕ} {P' : PolAV (Spec (CommRingCat.of R))}
    {pr : Fin r → (P'.A ⟶ D.P.A)} (hpr : ∀ i, IsMonHom (pr i)) (lim : IsLimit (Fan.mk P'.A pr)) (a b : Fin r → D.X) :
    cpt lim (a + b) = padd P'.A (cpt lim a) (cpt lim b) := by
  refine lim.hom_ext fun ⟨i⟩ => ?_
  show cpt lim (a + b) ≫ pr i = padd P'.A (cpt lim a) (cpt lim b) ≫ pr i
  have := hpr i
  rw [cpt_pr, padd, Category.assoc, IsMonHom.mul_hom, lift_map_assoc, cpt_pr, cpt_pr]
  exact D.c_add _ _

theorem cpt_zero {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {r : ℕ} {P' : PolAV (Spec (CommRingCat.of R))}
    {pr : Fin r → (P'.A ⟶ D.P.A)} (hpr : ∀ i, IsMonHom (pr i)) (lim : IsLimit (Fan.mk P'.A pr)) :
    cpt lim (0 : Fin r → D.X) = η[P'.A] := by
  refine lim.hom_ext fun ⟨i⟩ => ?_
  show cpt lim 0 ≫ pr i = η[P'.A] ≫ pr i
  have := hpr i
  rw [cpt_pr, IsMonHom.one_hom]
  have h := D.c_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

end GlobalTheory.Mum.TensData
end

open GlobalTheory.Mum.TensData in

theorem GlobalTheory.Mum.TensData.main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∃ (D' : DegPre R) (_ : Tens D.toPre D' W), ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (D'.psi 0) (𝟙 _) z J * val D'.rigK (𝟙 _) z J = 1 := by
  intro R _ _ _ hA D r W hW hdet
  haveI : IsNoetherianRing R := hA.1
  obtain ⟨P', pr, hpr, ⟨lim⟩, -, ⟨w, hw⟩⟩ := GlobalTheory.Mum.PowPol.exists_pow_polAV R D.toPre.P W hW hdet
  obtain ⟨sym, hsym, hsr⟩ := GlobalTheory.SelfUnif.exists_sym P'
  obtain ⟨rig, hrig, hrv⟩ := GlobalTheory.T.exists_tensorBundleRigidification R D.toPre W P'.A P'.L P'.isLB pr hpr w hw
  have hL : Laws := GlobalTheory.lawsAndExpansions.1.1
  have cub := (hL.cube _ P' ⟨P'.L, rig, P'.isLB, hrig⟩ rfl).1.some
  choose psi hpsi hpv using fun y : Fin r → D.toPre.X =>
    GlobalTheory.T.exists_tensorTrivialisation_powerLattice_points R D.toPre W P'.A P'.L P'.isLB pr w hw (cpt lim y) y (cpt_pr lim y)
  let D' : DegPre R :=
    { P := P'
      rig := rig
      rig_gen := hrig
      cub := cub
      sym := sym
      sym_gen := hsym
      sym_rig := hsr
      X := Fin r → D.toPre.X
      c := cpt lim
      c_add := cpt_add hpr lim
      psi := psi
      psi_gen := hpsi }
  refine ⟨D', ⟨pr, hpr, lim, AddEquiv.refl _, fun y i => cpt_pr lim y i, w, hw, fun y z J J' hJ hJ' => hpv y z J J' hJ hJ'⟩,
    fun z J' hJ' => ?_⟩
  obtain ⟨J, hJ, -⟩ := exists_good D.toPre.P.L D.toPre.P.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  have hτ : ∀ a b : D.toPre.X, a = 0 → b = 0 → val (D.toPre.tau a b) (𝟙 _) z J = 1 := by
    rintro a b rfl rfl
    have vρ : val D.toPre.rigK (𝟙 _) z J = val D.toPre.rig (jK R) z J := by
      refine (val_pull hJ _ _ _).trans ?_
      rw [Category.id_comp]
      rfl
    have hp : ∀ b : D.toPre.X, b = 0 → val (D.toPre.psi b) (𝟙 _) z J = val (D.toPre.psi 0) (𝟙 _) z J := by
      rintro b rfl; rfl
    have e : val (D.toPre.tau 0 0) (𝟙 _) z J = val (D.toPre.psi (0 + 0)) (𝟙 _) z J * (val (D.toPre.psi 0) (𝟙 _) z J)⁻¹ *
        (val (D.toPre.psi 0) (𝟙 _) z J)⁻¹ * (val D.toPre.rigK (𝟙 _) z J)⁻¹ :=
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
    rw [e, hp (0 + 0) (by simp), vρ, GlobalTheory.PsiZero.val_psi_zero D.tau_bimult hJ]
    group
  have h1 := hpv 0 z J J' hJ hJ'
  have h2 := hrv z J J' hJ hJ'
  have hprod : (∏ i, ∏ j, val (D.toPre.tau ((0 : Fin r → D.toPre.X) i) ((0 : Fin r → D.toPre.X) j)) (𝟙 _) z J ^ W i j) = 1 :=
    Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => by rw [hτ ((0 : Fin r → D.toPre.X) i) ((0 : Fin r → D.toPre.X) j) rfl rfl, one_zpow]
  rw [hprod, _root_.mul_one] at h1
  show val (psi 0) (𝟙 _) z J' * val (LB.pullGen P'.L _ _ rig (toUnit (TK R)).left) (𝟙 _) z J' = 1
  rw [h1, _root_.mul_comm]
  have hz := cpt_zero hpr lim (D := D.toPre)
  revert h2
  generalize cpt lim 0 = x at hz ⊢
  subst hz
  exact id
