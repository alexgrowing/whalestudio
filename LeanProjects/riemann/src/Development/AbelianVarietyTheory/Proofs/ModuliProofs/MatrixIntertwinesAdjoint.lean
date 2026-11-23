import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CohomologyLogDerivativeAdjointEndomorphismsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KodairaSpencerClassCohomologousAlongEndomorphismStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LogDerivativePrincipalPolarisationIndependentStatement
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS

private lemma constFn_sub' {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) (a b : K) :
    constFn q O (a - b) = constFn q O a - constFn q O b := by
  unfold constFn
  simp only [map_sub]

private lemma constFn_mul_moduli {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) (a b : K) :
    constFn q O (a * b) = constFn q O a * constFn q O b := by
  unfold constFn
  simp only [map_mul]

private lemma constFn_sum {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) {n : ℕ}
    (f : Fin n → K) : constFn q O (∑ k, f k) = ∑ k, constFn q O (f k) := by
  unfold constFn
  simp only [map_sum]

private lemma sum_sub_sum_mul_eq_sub_sub_sum {R : Type*} [CommRing R] {n : ℕ} (A B u v : Fin n → R) (M N : Fin n → Fin n → R) :
    ∑ a, (∑ b, A b * M b a - ∑ b, B b * N a b) * v a =
      (∑ a, A a * u a - ∑ a, B a * ∑ b, N b a * v b) - ∑ a, A a * (u a - ∑ b, M a b * v b) := by
  have h1 : ∑ a, ∑ b, A b * M b a * v a = ∑ a, ∑ b, A a * (M a b * v b) := by
    rw [Finset.sum_comm]; simp only [_root_.mul_assoc]
  have h2 : ∑ a, ∑ b, B b * N a b * v a = ∑ a, ∑ b, B a * (N b a * v b) := by
    rw [Finset.sum_comm]; simp only [_root_.mul_assoc]
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, mul_sub, Finset.mul_sum]
  rw [h1, h2]
  abel

theorem lc_row_mul_sub {K : Type} [Field K] {Y : Scheme.{0}} {I : Type} {U : I → Y.Opens} (q : Y ⟶ Sp K) {g : ℕ}
    (F Θ F' : Matrix (Fin g) (Fin g) K) (θ φ : Fin g → C1 U) (x : Fin g) :
    lc q ((F * Θ - Θ * F'.transpose) x) φ =
      (lc q (F x) θ - lc q (Θ x) (fun c => lc q (fun y => F' y c) φ)) -
        lc q (F x) (fun b => θ b - lc q (Θ b) φ) := by
  funext i j
  simp only [lc, Pi.sub_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
    constFn_sub', constFn_sum, constFn_mul_moduli]
  exact sum_sub_sum_mul_eq_sub_sub_sum (fun b => constFn q (U i ⊓ U j) (F x b)) (fun b => constFn q (U i ⊓ U j) (Θ x b))
    (fun b => θ b i j) (fun b => φ b i j) (fun a b => constFn q (U i ⊓ U j) (Θ a b))
    (fun a b => constFn q (U i ⊓ U j) (F' a b))

theorem matrix_intertwines_adjoint : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) (m : P₀.A.left ⟶ P.A.left) (L : LB P.A.left) [Finite L.ι] (D : R → K) (d : L.ι → ∀ O : P.A.left.Opens, Γ(P.A.left, O) → Γ(P₀.A.left, m ⁻¹ᵁ O)) (θ φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i)), IsGrpPullback P₀.A P.A (spMap x₀) m → L.IsLB → (∀ i, IsAffineOpen (L.U i)) → LBIso P₀.L (L.pull m) → KSCoc P₀.A.hom P.A.hom m D L.U dd d θ → IsDlog m L dd φ → ∀ (Θ : Matrix (Fin g) (Fin g) K) (f : P.A ⟶ P.A) (f₀ f₀' : P₀.A ⟶ P₀.A) (F F' : Matrix (Fin g) (Fin g) K), (∀ b, IsCob (fun i => m ⁻¹ᵁ L.U i) (θ b - lc P₀.A.hom (Θ b) φ)) → IsMonHom f₀ → IsMonHom f₀' → f₀.left ≫ m = m ≫ f.left → LBIso (cubeLB P₀.A ![fst P₀.A P₀.A ≫ f₀, snd P₀.A P₀.A] P₀.L) (cubeLB P₀.A ![fst P₀.A P₀.A, snd P₀.A P₀.A ≫ f₀'] P₀.L) → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → (∀ j, IsLieComb (fun i => F' i j) v (v j ≫ f₀')) → F * Θ = Θ * F'.transpose := by
  intro K _ P₀ g v dd hv hdd R _ x₀ P m L _ D d θ φ hpb hL hLaff hLB hKS hφ Θ f f₀ f₀' F F' hcob hf₀ hf₀' hfm hcube hF hF'
  have hsm : Smooth P₀.A.hom := @IsAbelianScheme.smooth _ P₀.A P₀.grp P₀.isAb
  have hA := GlobalTheory.T.kodairaSpencerClass_cohomologous_along_endomorphism K P₀.A g v dd hsm hv hdd R x₀ P.A.left P.A.hom m hpb.1 L.ι L.U D d θ f.left f₀ F hKS hf₀
    (Over.w f) hfm hF
  have hB := GlobalTheory.T.cohomology_logDerivative_adjoint_endomorphisms K P₀ g v dd hv hdd P.A.left m L φ f₀ f₀' F' hL hLB hφ hf₀ hf₀' hcube hF'
  have hI := (GlobalTheory.T.logDerivative_principalPolarisation_independent K P₀ g v dd hv hdd P.A.left m L hL hLB).2 φ hφ |>.2
  have hcov : ⨆ i, m ⁻¹ᵁ L.U i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hL.cover]; rfl
  have hrow : ∀ x, (F * Θ - Θ * F'.transpose) x = 0 := by
    intro x
    apply hI
    rw [lc_row_mul_sub]
    refine IsCob.sub (Cohom.isCob_sub f₀.left hcov (hA x)
      (cohom_lc P₀.A.hom f₀.left (Over.w f₀) (Θ x) _ φ hB) (hcob x)) ?_
    exact isCob_lc P₀.A.hom (F x) _ hcob
  rw [← sub_eq_zero]
  ext x y
  exact congrFun (hrow x) y

end GlobalTheory.KS
end
