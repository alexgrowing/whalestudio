import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrict
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCommonField
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

noncomputable section
namespace GlobalTheory.ValuesStrictPull
open GlobalTheory.TorusExt GlobalTheory.ArcPull GlobalTheory.ArcTransport
open GlobalTheory.PsiEvenPull (proj)
open ReciprocityTheory.ChartRestriction.G.DVR (cP)

section Val
variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem const_vF (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    stalkConst z (vF t r J) = (val t r z J).val :=
  ((gs_unit r z _ (hJ.mem φ r) _).symm.trans (gs_eq_stalkConst r z
    (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _)).symm

theorem const_sF (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    stalkConst z (sF s r J) = sval s r z J :=
  (gs_eq_stalkConst r z (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _).symm

theorem vF_congr {X' Y' : Scheme.{0}} {L' : LB X'} {K' : Type} [Fintype K'] {φ' : K' → (Y' ⟶ X')} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {r : Sp F ⟶ Y} {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J)
    {t' : LB.Gen (LB.LinComb L' φ' ε')} {r' : Sp F ⟶ Y'} {J' : (Sp F ⟶ X') → L'.ι} (hJ' : Good L' z J')
    (h : val t r z J = val t' r' z J') : vF t r J = vF t' r' J' :=
  (stalkConst z).injective ((const_vF t r hJ).trans ((congrArg Units.val h).trans (const_vF t' r' hJ').symm))
end Val

theorem exists_numOf_strict_pull : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D'), Strict hD.w → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F], (∀ x, algebraMap (FractionRing R') F (algebraMap R' _ (φ x)) = algebraMap (FractionRing R) F (algebraMap R _ x)) → ∀ (N : NumD F) (ν : NumOf D F N) (th' : H0 D'.P.L 1), (∀ s : H0 D'.P.L 1, ∃ r : R', ∀ j, s.f j = resTop _ (scal D'.P.A.hom r) * th'.f j) → (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → sval ν.th (r ≫ PsiEvenPull.proj hD) z J = (gw hD.w r z (J (r ≫ PsiEvenPull.proj hD)) (J' r)).val * sval th' r z J') → ∃ ν' : NumOf D' F N, (∀ y, hD.xe (ν'.eX y) = ν.eX y) ∧ ∀ x, (ν'.eA x).left ≫ PsiEvenPull.proj hD = (ν.eA x).left := by
  intro hG R R' _ _ _ _ φ D D' hD hS F _ _ _ hF N ν th' hgen hth
  obtain ⟨c, hc⟩ := hS
  have hT : (TF (R := R') F).hom ≫ spMap φ = (TF (R := R) F).hom := base_comm fun r => (hF r).symm
  have hj : jFK (R := R') F ≫ jK R' ≫ spMap φ = jFK (R := R) F ≫ jK R := (Category.assoc _ _ _).symm.trans hT
  let z : Sp F := IsLocalRing.closedPoint F
  let J' : (Sp F ⟶ D'.P.A.left) → D'.P.L.ι := fun ψ => c (ν.J (ψ ≫ proj hD))
  have hJ : Good D.P.L z ν.J := fun ψ => ν.good ψ trivial
  have good' : ∀ ψ : Sp F ⟶ D'.P.A.left, ⊤ ≤ ψ ⁻¹ᵁ D'.P.L.U (J' ψ) := fun ψ y _ =>
    (hc _ ψ y _ (ν.good (ψ ≫ proj hD) (x := y) trivial)).1
  have hJ' : Good D'.P.L z J' := fun ψ => good' ψ trivial
  have one : ∀ ψ : Sp F ⟶ D'.P.A.left, Geo.Tor.gw hD.w ψ z (ν.J (ψ ≫ proj hD)) (J' ψ) = 1 := fun ψ =>
    (hc _ ψ z _ (hJ (ψ ≫ proj hD))).2
  have one' : ∀ ψ : Sp F ⟶ D'.P.A.left, om hD.w z ν.J J' ψ = 1 := one
  have one'' : ∀ x : TF (R := R') F ⟶ D'.P.A, wVal hD.w z ν.J J' x = 1 := fun x => one x.left
  let P : (TF (R := R') F ⟶ D'.P.A) ≃* (TF (R := R) F ⟶ D.P.A) :=
    MulEquiv.ofBijective (MonoidHom.mk' (pushF (pull_grp hD) hT) (pushF_mul _ _))
      ⟨pushF_injective (pull_grp hD) hT, pushF_surjective (pull_grp hD) hT⟩
  obtain ⟨eA, heA⟩ : ∃ eA : N.A ≃* (TF (R := R') F ⟶ D'.P.A), ∀ x, pushF (pull_grp hD) hT (eA x) = ν.eA x :=
    ⟨ν.eA.trans P.symm, fun x => P.apply_symm_apply _⟩
  have hl : ∀ x, (eA x).left ≫ proj hD = (ν.eA x).left := fun x => congrArg (fun q => q.left) (heA x)
  obtain ⟨eX, heX⟩ : ∃ eX : N.X ≃+ D'.X, ∀ y, hD.xe (eX y) = ν.eX y :=
    ⟨ν.eX.trans hD.xe.symm, fun y => hD.xe.apply_symm_apply _⟩
  have rig : vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := R) F).hom ν.J =
      vF (L := D'.P.L) (φ := fun _ : PUnit => eSec D'.P.A) (ε := fun _ => 1) D'.rig (TF (R := R') F).hom J' := by
    have e := ArcPull.rig_val hD (Z := Sp F) _ _ hj hJ hJ'
    rw [one', _root_.one_mul] at e
    exact vF_congr hJ hJ' ((val_pull hJ _ _ _).symm.trans (e.trans (val_pull hJ' _ _ _)))
  refine ⟨{
    J := J', good := good', th := th', th_gen := hgen, eA := eA, eX := eX
    c_eq := fun χ => ?_, θ_eq := fun x y u => ?_, σ_eq := fun x => ?_, th_eq := fun x => ?_
    ψ_eq := fun χ => ?_ }, heX, hl⟩
  · apply pushF_injective (pull_grp hD) hT
    rw [heA, ν.c_eq, ← heX]
    exact Over.OverMorphism.ext ((cPoint_proj hD (T := TF (R := R) F) (T' := TF (R := R') F) (𝟙 _)
      (hT.trans (Category.id_comp _).symm) _).trans (Category.id_comp _)).symm
  · have k := thS_push (pull_grp hD) hT ((isGen_iff _).1 hD.w_gen) hG hJ hJ' (eA x) (eA y) (eA u)
    simp only [one'', heA, inv_one, _root_.one_mul] at k
    exact (ν.θ_eq x y u).trans (vF_congr hJ hJ' k)
  · have k := PsiEvenPull.sym_pull hG hD (Z := Sp F) (eA x).left z hJ hJ'
    rw [one, one, inv_one, _root_.one_mul, _root_.one_mul] at k
    refine (ν.σ_eq x).trans (vF_congr hJ hJ' (Eq.trans ?_ k))
    exact congrArg (fun q => val (Z := Sp F) D.sym q z ν.J) (hl x).symm
  · have k := hth (Sp F) (eA x).left z ν.J J' hJ hJ'
    rw [one, Units.val_one, _root_.one_mul] at k
    rw [← rig, ν.th_eq x]
    refine (stalkConst z).injective ((const_sF _ _ hJ).trans (Eq.trans ?_ (k.trans (const_sF _ _ hJ').symm)))
    exact congrArg (fun q => sval (Z := Sp F) ν.th q z ν.J) (hl x).symm
  · have k := ArcPull.psi_val hD (Z := Sp F) _ _ hj hJ hJ' (eX χ)
    rw [one', inv_one, _root_.one_mul, heX] at k
    rw [← rig, ν.ψ_eq χ]
    exact congrArg (· * _) (vF_congr hJ hJ' k)

end GlobalTheory.ValuesStrictPull
end
