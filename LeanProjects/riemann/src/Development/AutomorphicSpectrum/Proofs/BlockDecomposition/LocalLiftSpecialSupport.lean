import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.LiftSupp

section Ring

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem mul_det_eq_of_mul_entries (d : R) {A B : Matrix n n R} (h : ∀ i j, d * A i j = d * B i j) :
    d * A.det = d * B.det := by
  let I : Ideal R := LinearMap.ker (LinearMap.mulLeft R d)
  have hI : ∀ x y : R, d * x = d * y → Ideal.Quotient.mk I x = Ideal.Quotient.mk I y := by
    intro x y hxy
    refine Ideal.Quotient.eq.2 ?_
    change d * (x - y) = 0
    rw [mul_sub, hxy, sub_self]
  have hmap : (Ideal.Quotient.mk I).mapMatrix A = (Ideal.Quotient.mk I).mapMatrix B := by
    ext i j
    exact hI _ _ (h i j)
  have h2 : Ideal.Quotient.mk I A.det = Ideal.Quotient.mk I B.det := by
    rw [RingHom.map_det, RingHom.map_det, hmap]
  have h3 : A.det - B.det ∈ I := Ideal.Quotient.eq.1 h2
  have h4 : d * (A.det - B.det) = 0 := h3
  rw [mul_sub] at h4
  exact sub_eq_zero.1 h4

end Ring

section Tensor

variable {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [Field K] [Algebra F K]
  [TopologicalSpace K]

def pB (P : PlaceMap F K) : AF F ⊗[F] E →ₐ[F] K ⊗[F] E :=
  Algebra.TensorProduct.map P.proj (AlgHom.id F E)

theorem iB_tmul (P : PlaceMap F K) (a : K) (b : E) : iB P (a ⊗ₜ[F] b) = P.inj a ⊗ₜ[F] b := rfl

theorem pB_tmul (P : PlaceMap F K) (a : AF F) (b : E) : pB P (a ⊗ₜ[F] b) = P.proj a ⊗ₜ[F] b := rfl

theorem algebraMap_inj_one (P : PlaceMap F K) :
    algebraMap (AF F) (AF F ⊗[F] E) (P.inj 1) = iB P (1 : K ⊗[F] E) := by
  rw [Algebra.TensorProduct.one_def, iB_tmul, Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem eB_mul_iB (P : PlaceMap F K) (y : K ⊗[F] E) :
    algebraMap (AF F) (AF F ⊗[F] E) (P.inj 1) * iB P y = iB P y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [iB_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    change (P.inj 1 * P.inj a) ⊗ₜ[F] b = _
    rw [← map_mul, one_mul]
  | add x y hx hy => rw [map_add, mul_add, hx, hy]

theorem pB_iB (P : PlaceMap F K) (y : K ⊗[F] E) : pB P (iB P y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [iB_tmul, pB_tmul, P.proj_inj]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem iB_pB (P : PlaceMap F K) (y : AF F ⊗[F] E) :
    iB P (pB P y) = algebraMap (AF F) (AF F ⊗[F] E) (P.inj 1) * y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [pB_tmul, iB_tmul, P.inj_proj, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add]

theorem det_eq_one_of_lift (P : PlaceMap F K) {M : ℕ} {G : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)}
    {X : Matrix (Fin M) (Fin M) (K ⊗[F] E)} (hG : ∀ i j, (G - 1) i j = iB P ((X - 1) i j)) (hX : X.det = 1) :
    G.det = 1 := by
  set e := algebraMap (AF F) (AF F ⊗[F] E) (P.inj 1) with he
  have hGij : ∀ i j, G i j = iB P ((X - 1) i j) + (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j := by
    intro i j
    rw [← hG]
    simp
  have hmap : (pB (E := E) P).toRingHom.mapMatrix G = X := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hGij]
    change pB P _ = _
    rw [map_add, pB_iB]
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.one_apply_ne h]
  have hp : pB P G.det = 1 := by
    have h := RingHom.map_det (pB (E := E) P).toRingHom G
    rw [hmap, hX] at h
    exact h
  have h1 : e * G.det = e := by
    rw [he, ← iB_pB, hp, algebraMap_inj_one]
  have h2 : (1 - e) * G.det = (1 - e) * (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).det := by
    refine mul_det_eq_of_mul_entries (1 - e) fun i j => ?_
    rw [hGij, mul_add, sub_mul, one_mul, he, eB_mul_iB, sub_self, zero_add]
  rw [Matrix.det_one] at h2
  linear_combination h1 + h2

end Tensor

theorem lift_det_one_mem_supp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), ∀ {K : Type}
    [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J), IsLift P σ J L →
    ∀ x : HA K σ J, ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 → L x ∈ SUSupp σ J (P.inj 1) := by
  intro F E _ _ _ _ _ σ _ M J K _ _ P L hL x hx
  refine ⟨StrongApprox.mem_SUAdelic.2 (det_eq_one_of_lift P (hL x) hx), fun i j => ?_⟩
  rw [hL x i j]
  exact eB_mul_iB P _

end GlobalTheory.CompanionTheory.SaGen.LiftSupp
