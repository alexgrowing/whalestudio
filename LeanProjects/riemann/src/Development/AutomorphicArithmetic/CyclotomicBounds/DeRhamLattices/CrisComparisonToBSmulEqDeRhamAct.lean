import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrisComparisonAinfEqDeRhamComparison
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem smul_abstract {Z O A B D M N : Type} [CommRing Z] [CommRing O] [CommRing A] [CommRing B]
    [CommRing D] [Algebra Z O] [Algebra Z A] [Algebra Z B] [Algebra Z D] [AddCommGroup M] [Module O M]
    [AddCommGroup N] (fB : O ⊗[Z] A →ₐ[O] O ⊗[Z] B) (fD : O ⊗[Z] A →ₐ[O] O ⊗[Z] D)
    (gB : A → B) (gD : A → D) (hB : ∀ o w, fB (o ⊗ₜ[Z] w) = o ⊗ₜ[Z] gB w)
    (hD : ∀ o w, fD (o ⊗ₜ[Z] w) = o ⊗ₜ[Z] gD w)
    (X : (O ⊗[Z] B) ⊗[O] M →+ N) (act : O ⊗[Z] D →+ (N →+ N))
    (h : ∀ (o o' : O) (w : A) (b : B) (x : M),
      X (((o * o') ⊗ₜ[Z] (gB w * b)) ⊗ₜ[O] x) = act (o ⊗ₜ[Z] gD w) (X ((o' ⊗ₜ[Z] b) ⊗ₜ[O] x)))
    (c : O ⊗[Z] A) (y : (O ⊗[Z] B) ⊗[O] M) : X (fB c • y) = act (fD c) (X y) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add c c' hc hc' => rw [map_add, add_smul, map_add, hc, hc', map_add, map_add, AddMonoidHom.add_apply]
  | tmul o w =>
    rw [hB, hD]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => rw [smul_add, map_add, hy, hy', map_add, map_add]
    | tmul r x =>
      induction r using TensorProduct.induction_on with
      | zero => simp
      | add r r' hr hr' => rw [TensorProduct.add_tmul, smul_add, map_add, hr, hr', map_add, map_add]
      | tmul o' b =>
        rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, h]

theorem _root_.UpperTheory.KN.crisComparison_toB_smul_eq_deRham_act :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (c : OA l ↥(OL LL)) (y : TW (OB l ↥(OL LL)) T), X (toB l ↥(OL LL) c • y) = act (toOD l ↥(OL LL) c) (X y) := by
  intro l _ LL T Pl AI Td X hX act hact c y
  refine smul_abstract (toB l ↥(OL LL)) (toOD l ↥(OL LL)) (fun w => acrisToBcris l (ainfToAcris l w))
    (fun w => ainfToBdRp l w) (fun _ _ => rfl) (fun _ _ => rfl) X act (fun o o' w b x => ?_) c y
  refine (hX _ _ _).trans ?_
  refine Eq.trans ?_ (congrArg (act _) (hX o' b x)).symm
  refine Eq.trans ?_ (hact _ _ _ _).symm
  have h1 : ((o * o' : ↥(OL LL)) : ↥LL.1) = (o : ↥LL.1) * (o' : ↥LL.1) := rfl
  rw [h1, mul_smul, map_mul, UpperTheory.KN.crisComparison_ainf_eq_deRhamComparison l Pl AI Td w]
