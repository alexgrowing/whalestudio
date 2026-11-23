import Mathlib
import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Anisotropic

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι E)

section Trace

variable (K E) (R : Type*) [CommRing R] [Algebra K R]

def baseTrace : R ⊗[K] E →ₗ[R] R :=
  (Algebra.TensorProduct.rid K R R).toLinearMap ∘ₗ (Algebra.trace K E).baseChange R

variable {K E R}

omit [Algebra.IsQuadraticExtension K E] in
theorem baseTrace_tmul (r : R) (e : E) :
    baseTrace K E R (r ⊗ₜ e) = algebraMap K R (Algebra.trace K E e) * r := by
  simp [baseTrace, Algebra.smul_def]

theorem baseTrace_conjBase (z : R ⊗[K] E) : baseTrace K E R (conjBase K E R z) = baseTrace K E R z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    rw [conjBase_tmul, baseTrace_tmul, baseTrace_tmul, conj_apply, map_sub,
      trace_algebraMap_quadratic]
    congr 2
    ring
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem baseTrace_algebraMap (t : R) : baseTrace K E R (algebraMap R (R ⊗[K] E) t) = 2 * t := by
  have h1 : Algebra.trace K E 1 = 2 := by
    simpa using trace_algebraMap_quadratic (F := K) (E := E) 1
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    baseTrace_tmul, h1, map_ofNat]

omit [Algebra.IsQuadraticExtension K E] in

theorem baseTrace_tensorMap {S : Type*} [CommRing S] [Algebra K S] (f : R →ₐ[K] S)
    (z : R ⊗[K] E) : baseTrace K E S (tensorMap E f z) = f (baseTrace K E R z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rw [tensorMap_tmul, baseTrace_tmul, baseTrace_tmul, map_mul, AlgHom.commutes]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end Trace

section Pairing

variable (K) (R : Type*) [CommRing R] [Algebra K R]

def hermPair (x y : ι → R ⊗[K] E) : R ⊗[K] E :=
  (fun i => conjBase K E R (x i)) ⬝ᵥ (baseMatrix K H R *ᵥ y)

def hermTrace (x y : ι → R ⊗[K] E) : R := baseTrace K E R (hermPair K H R x y)

variable {K H R}

theorem hermPair_self (x : ι → R ⊗[K] E) : hermPair K H R x x = hermValue K H R x := rfl

omit [Fintype ι] in
theorem conjBase_vec_add (x x' : ι → R ⊗[K] E) :
    (fun i => conjBase K E R ((x + x') i)) =
      (fun i => conjBase K E R (x i)) + fun i => conjBase K E R (x' i) :=
  funext fun _ => map_add _ _ _

theorem hermPair_add_left (x x' y : ι → R ⊗[K] E) :
    hermPair K H R (x + x') y = hermPair K H R x y + hermPair K H R x' y := by
  unfold hermPair
  rw [conjBase_vec_add, add_dotProduct]

theorem hermPair_add_right (x y y' : ι → R ⊗[K] E) :
    hermPair K H R x (y + y') = hermPair K H R x y + hermPair K H R x y' := by
  unfold hermPair
  rw [mulVec_add, dotProduct_add]

theorem hermPair_smul_left (c : R ⊗[K] E) (x y : ι → R ⊗[K] E) :
    hermPair K H R (c • x) y = conjBase K E R c * hermPair K H R x y := by
  unfold hermPair
  have : (fun i => conjBase K E R ((c • x) i)) = conjBase K E R c • fun i => conjBase K E R (x i) :=
    funext fun i => by simp [Pi.smul_apply, smul_eq_mul, map_mul]
  rw [this, smul_dotProduct, smul_eq_mul]

theorem hermPair_smul_right (c : R ⊗[K] E) (x y : ι → R ⊗[K] E) :
    hermPair K H R x (c • y) = c * hermPair K H R x y := by
  unfold hermPair
  rw [mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem conjBase_algebraMap (c : R) :
    conjBase K E R (algebraMap R (R ⊗[K] E) c) = algebraMap R (R ⊗[K] E) c := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    conjBase_tmul, map_one]

theorem conjBase_conjBase (z : R ⊗[K] E) : conjBase K E R (conjBase K E R z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rw [conjBase_tmul, conjBase_tmul, conj_conj]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem hermTrace_add_left (x x' y : ι → R ⊗[K] E) :
    hermTrace K H R (x + x') y = hermTrace K H R x y + hermTrace K H R x' y := by
  rw [hermTrace, hermPair_add_left, map_add]; rfl

theorem hermTrace_add_right (x y y' : ι → R ⊗[K] E) :
    hermTrace K H R x (y + y') = hermTrace K H R x y + hermTrace K H R x y' := by
  rw [hermTrace, hermPair_add_right, map_add]; rfl

theorem hermTrace_smul_left (c : R) (x y : ι → R ⊗[K] E) :
    hermTrace K H R (c • x) y = c * hermTrace K H R x y := by
  rw [hermTrace, ← algebraMap_smul (R ⊗[K] E) c x, hermPair_smul_left, conjBase_algebraMap,
    ← Algebra.smul_def, map_smul, smul_eq_mul]; rfl

theorem hermTrace_smul_right (c : R) (x y : ι → R ⊗[K] E) :
    hermTrace K H R x (c • y) = c * hermTrace K H R x y := by
  rw [hermTrace, ← algebraMap_smul (R ⊗[K] E) c y, hermPair_smul_right, ← Algebra.smul_def,
    map_smul, smul_eq_mul]; rfl

variable (K H R) in

def hermTraceBilin : (ι → R ⊗[K] E) →ₗ[R] (ι → R ⊗[K] E) →ₗ[R] R :=
  LinearMap.mk₂ R (hermTrace K H R) hermTrace_add_left hermTrace_smul_left hermTrace_add_right
    hermTrace_smul_right

@[simp]
theorem hermTraceBilin_apply (x y : ι → R ⊗[K] E) : hermTraceBilin K H R x y = hermTrace K H R x y :=
  rfl

section Invariance

variable [DecidableEq ι]

theorem hermPair_mulVec (g : unitaryPoints K E H R) (x y : ι → R ⊗[K] E) :
    hermPair K H R (unitaryMat g *ᵥ x) (unitaryMat g *ᵥ y) = hermPair K H R x y := by
  have hg : ((unitaryMat g).map (conjBase K E R))ᵀ * baseMatrix K H R * unitaryMat g =
      baseMatrix K H R := g.2
  have h1 : (fun i => conjBase K E R ((unitaryMat g *ᵥ x) i)) =
      (unitaryMat g).map (conjBase K E R) *ᵥ (fun i => conjBase K E R (x i)) := by
    funext i
    exact RingHom.map_mulVec _ _ _ i
  unfold hermPair
  rw [h1, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hg, Matrix.dotProduct_mulVec]

theorem hermTrace_mulVec (g : unitaryPoints K E H R) (x y : ι → R ⊗[K] E) :
    hermTrace K H R (unitaryMat g *ᵥ x) (unitaryMat g *ᵥ y) = hermTrace K H R x y := by
  rw [hermTrace, hermPair_mulVec]; rfl

end Invariance

theorem hermPair_swap (hH : IsHermitianFor (conjHom K E) H) (x y : ι → R ⊗[K] E) :
    hermPair K H R y x = conjBase K E R (hermPair K H R x y) := by
  have hHb : (baseMatrix K H R).map (conjBase K E R) = (baseMatrix K H R)ᵀ := by
    ext i j
    have := congrFun (congrFun hH j) i
    simp only [transpose_apply, map_apply] at this
    simp only [map_apply, transpose_apply, baseMatrix, Algebra.TensorProduct.includeRight_apply,
      conjBase_tmul, ← this]
    rfl
  unfold hermPair
  rw [RingHom.map_dotProduct]
  have h1 : (conjBase K E R) ∘ (fun i => conjBase K E R (x i)) = x :=
    funext fun i => conjBase_conjBase (x i)
  have h2 : (conjBase K E R) ∘ (baseMatrix K H R *ᵥ y) =
      (baseMatrix K H R).map (conjBase K E R) *ᵥ fun i => conjBase K E R (y i) :=
    funext fun i => RingHom.map_mulVec _ _ _ i
  rw [h1, h2, hHb, Matrix.mulVec_transpose, dotProduct_comm x, Matrix.dotProduct_mulVec]

theorem hermTrace_comm (hH : IsHermitianFor (conjHom K E) H) (x y : ι → R ⊗[K] E) :
    hermTrace K H R y x = hermTrace K H R x y := by
  simp only [hermTrace]
  rw [hermPair_swap hH x y, baseTrace_conjBase]

theorem tensorMap_hermPair {S : Type*} [CommRing S] [Algebra K S] (f : R →ₐ[K] S)
    (x y : ι → R ⊗[K] E) :
    tensorMap E f (hermPair K H R x y) =
      hermPair K H S (fun i => tensorMap E f (x i)) (fun i => tensorMap E f (y i)) := by
  unfold hermPair
  have h := RingHom.map_dotProduct (tensorMap E f : R ⊗[K] E →+* S ⊗[K] E)
    (fun i => conjBase K E R (x i)) (baseMatrix K H R *ᵥ y)
  simp only [RingHom.coe_coe] at h
  rw [h]
  congr 1
  · funext i
    exact tensorMap_conjBase f (x i)
  · funext i
    have := RingHom.map_mulVec (tensorMap E f : R ⊗[K] E →+* S ⊗[K] E) (baseMatrix K H R) y i
    simp only [RingHom.coe_coe] at this
    rw [Function.comp_apply, this]
    have h2 := map_includeRight_tensorMap (H := H) f
    simp only [RingHom.coe_coe] at h2
    rw [h2]
    rfl

theorem hermTrace_tensorMap {S : Type*} [CommRing S] [Algebra K S] (f : R →ₐ[K] S)
    (x y : ι → R ⊗[K] E) :
    f (hermTrace K H R x y) =
      hermTrace K H S (fun i => tensorMap E f (x i)) (fun i => tensorMap E f (y i)) := by
  rw [hermTrace, hermTrace, ← tensorMap_hermPair, baseTrace_tensorMap]

theorem hermTrace_self_of_hermValue {x : ι → R ⊗[K] E} {t : R}
    (ht : hermValue K H R x = algebraMap R (R ⊗[K] E) t) : hermTrace K H R x x = 2 * t := by
  rw [hermTrace, hermPair_self, ht, baseTrace_algebraMap]

theorem hermPair_smul_smul (c : R ⊗[K] E) (x y : ι → R ⊗[K] E) :
    hermPair K H R (c • x) (c • y) = (conjBase K E R c * c) * hermPair K H R x y := by
  rw [hermPair_smul_left, hermPair_smul_right, mul_assoc]

end Pairing

section Coordinates

variable [DecidableEq ι] (R : Type*) [CommRing R] [Algebra K R]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

def vecCoords (x : ι → R ⊗[K] E) (a : ι × κ) : R :=
  (Algebra.TensorProduct.basis R b).repr (x a.1) a.2

def stdVec (a : ι × κ) : ι → R ⊗[K] E := Pi.single a.1 ((1 : R) ⊗ₜ b a.2)

variable {R}

omit [Algebra.IsQuadraticExtension K E] in

theorem sum_coords_smul_stdVec (x : ι → R ⊗[K] E) :
    ∑ a : ι × κ, vecCoords R b x a • stdVec R b a = x := by
  funext i
  rw [Finset.sum_apply, Fintype.sum_prod_type]
  simp only [stdVec, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero]
  conv_rhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr (x i)]
  simp [vecCoords, Algebra.TensorProduct.basis_apply]

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [Fintype κ] in

theorem tensorMap_stdVec (a : ι × κ) :
    (fun i => tensorMap E (Algebra.ofId K R) (stdVec K b a i)) = stdVec R b a := by
  funext i
  simp only [stdVec, Pi.single_apply]
  split_ifs with h
  · subst h
    simp
  · simp

theorem hermTrace_eq_sum (x y : ι → R ⊗[K] E) :
    hermTrace K H R x y = ∑ a : ι × κ, ∑ c : ι × κ, vecCoords R b x a *
      vecCoords R b y c * algebraMap K R (hermTrace K H K (stdVec K b a) (stdVec K b c)) := by
  have hval : ∀ a c : ι × κ, algebraMap K R (hermTrace K H K (stdVec K b a) (stdVec K b c)) =
      hermTrace K H R (stdVec R b a) (stdVec R b c) := by
    intro a c
    rw [← tensorMap_stdVec (R := R) b a, ← tensorMap_stdVec (R := R) b c]
    exact hermTrace_tensorMap (Algebra.ofId K R) _ _
  simp only [hval]
  conv_lhs => rw [← sum_coords_smul_stdVec b x, ← sum_coords_smul_stdVec b y]
  rw [← hermTraceBilin_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    hermTraceBilin_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring

end Coordinates

end GroundTheory.Automorphic
