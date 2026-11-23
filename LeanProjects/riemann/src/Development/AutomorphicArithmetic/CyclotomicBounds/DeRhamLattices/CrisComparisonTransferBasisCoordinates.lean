import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrisComparisonToBSmulEqDeRhamAct
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem sum_through_tensor_basis {O A B M V ι κ : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B]
    [AddCommGroup M] [Module O M] [AddCommGroup V] [Fintype ι] [DecidableEq ι] [Fintype κ]
    (f : A →ₐ[O] B) (jB : (ι → B) ≃ₗ[B] B ⊗[O] M) (X : B ⊗[O] M →+ V) (F : A → V → V)
    (hF : ∀ (c : A) (y : B ⊗[O] M), X (f c • y) = F c (X y))
    (c : ι → A) (r : κ → A) (x : κ → M)
    (h : jB (fun i => f (c i)) = TensorProduct.map f.toLinearMap LinearMap.id (∑ k, r k ⊗ₜ[O] x k)) :
    ∑ j, F (c j) (X (jB (Pi.single j 1))) = ∑ k, F (r k) (X ((1 : B) ⊗ₜ[O] x k)) := by
  have e1 : (fun i => f (c i)) = ∑ j, f (c j) • (Pi.single j 1 : ι → B) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have e2 : TensorProduct.map f.toLinearMap LinearMap.id (∑ k, r k ⊗ₜ[O] x k) =
      ∑ k, f (r k) • ((1 : B) ⊗ₜ[O] x k) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [TensorProduct.smul_tmul']
  rw [e1, e2, map_sum] at h
  have h2 := congrArg X h
  simp only [map_sum, map_smul, hF] at h2
  exact h2

theorem _root_.UpperTheory.KN.crisComparison_transfer_basis_coordinates :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (κ : Type) [Fintype κ] (c : ι → OA l ↥(OL LL)) (r : κ → OA l ↥(OL LL)) (x : κ → ↥T.L.T), I.j (inclL (thetaW a LL) ϖ P c) = TWincl (inclO l ↥(OL LL)) T (∑ k, r k ⊗ₜ[↥(OL LL)] x k) → ∑ j, act (toOD l ↥(OL LL) (c j)) (X (jB (Pi.single j 1))) = ∑ k, act (toOD l ↥(OL LL) (r k)) (((x k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I jB Pl AI Td hcmp X hX act hact κ _ c r x h
  have hF := UpperTheory.KN.crisComparison_toB_smul_eq_deRham_act l LL T Pl AI Td X hX act hact
  have h1 := hcmp c _ h
  have h2 := sum_through_tensor_basis (toB l ↥(OL LL)) jB X (fun c v => act (toOD l ↥(OL LL) c) v) hF c r x h1
  refine h2.trans (Finset.sum_congr rfl fun k _ => ?_)
  have h3 : X ((1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x k) =
      ((x k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR) := by
    refine (hX 1 1 (x k)).trans ?_
    rw [map_one, OneMemClass.coe_one, one_smul]
  exact congrArg (fun v => act (toOD l ↥(OL LL) (r k)) v) h3
