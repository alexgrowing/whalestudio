import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAevalEqOfSeparable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SesqAsym
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntidiagTwistedNorm
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TwTraceForm

theorem phi_transpose (a : ℕ) (L : Type) [Field L] :
    (GlobalTheory.Tw.Phi a L)ᵀ = (-1 : L) ^ (a - 1) • GlobalTheory.Tw.Phi a L :=
  (GlobalTheory.antidiag_twisted_norm L (RingEquiv.refl L) (fun _ => rfl) a (GlobalTheory.Tw.Phi a L) (by
    ext i j
    simp only [GlobalTheory.Tw.Phi, Matrix.of_apply]
    have : ((i : ℕ) + (j : ℕ) + 1 = a) ↔ j = i.rev := by
      rw [Fin.ext_iff, Fin.val_rev]; omega
    simp only [this])).1

theorem phi_map (a : ℕ) (L : Type) [Field L] (c : L →+* L) :
    (GlobalTheory.Tw.Phi a L).map c = GlobalTheory.Tw.Phi a L := by
  ext i j
  simp only [GlobalTheory.Tw.Phi, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem phi_transpose_mul (a : ℕ) (L : Type) [Field L] :
    (GlobalTheory.Tw.Phi a L)ᵀ * GlobalTheory.Tw.Phi a L = 1 :=
  mul_eq_one_comm.1 (GlobalTheory.CuspRep.Phi_mul_transpose a L)

theorem gram_eq (a : ℕ) (L : Type) [Field L] (δ : GL (Fin a) L) :
    ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = ((δ⁻¹ : GL (Fin a) L).val)ᵀ * GlobalTheory.Tw.Phi a L := by
  have h : (δ.val * GlobalTheory.Tw.Phi a L)⁻¹ = (GlobalTheory.Tw.Phi a L)ᵀ * (δ⁻¹ : GL (Fin a) L).val := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (δ⁻¹ : GL (Fin a) L).val, Units.inv_mul, Matrix.one_mul,
      phi_transpose_mul]
  rw [h, Matrix.transpose_mul, Matrix.transpose_transpose]

theorem gram_mul_transpose (a : ℕ) (L : Type) [Field L] (δ : GL (Fin a) L) :
    ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ * (δ.val * GlobalTheory.Tw.Phi a L)ᵀ = 1 := by
  rw [gram_eq, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (GlobalTheory.Tw.Phi a L),
    GlobalTheory.CuspRep.Phi_mul_transpose, Matrix.one_mul, ← Matrix.transpose_mul, Units.mul_inv,
    Matrix.transpose_one]

theorem gram_norm (a : ℕ) (L : Type) [Field L] (c : L →+* L) (δ : GL (Fin a) L) :
    (((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ)ᵀ * (δ * thetaGL a c δ).val
      = (-1 : L) ^ (a - 1) • (((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ).map c := by
  have hθ : (thetaGL a c δ).val
      = GlobalTheory.Tw.Phi a L * (((δ⁻¹ : GL (Fin a) L).val).map c)ᵀ * (GlobalTheory.Tw.Phi a L)ᵀ := rfl
  rw [gram_eq, Units.val_mul, hθ, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.map_mul, Matrix.transpose_map, phi_map]
  set Φ := GlobalTheory.Tw.Phi a L
  set Di := (δ⁻¹ : GL (Fin a) L).val
  set X := (Di.map c)ᵀ
  calc Φᵀ * Di * (δ.val * (Φ * X * Φᵀ))
      = Φᵀ * (Di * δ.val) * Φ * X * Φᵀ := by
        simp only [Matrix.mul_assoc]
    _ = X * Φᵀ := by
        rw [Units.inv_mul, Matrix.mul_one, phi_transpose_mul, Matrix.one_mul]
    _ = (-1 : L) ^ (a - 1) • (X * Φ) := by
        rw [phi_transpose, Matrix.mul_smul]

theorem form_asym {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (σ : k ≃+* k)
    (hσ : ∀ x, σ (σ x) = x) (S N : Matrix n n k) (ε : k) (h : S.map σ = ε • (Sᵀ * N))
    (u v : n → k) :
    σ (v ⬝ᵥ S *ᵥ (fun j => σ (u j))) = (ε • N *ᵥ u) ⬝ᵥ S *ᵥ (fun j => σ (v j)) := by
  have h1 : σ (v ⬝ᵥ S *ᵥ (fun j => σ (u j))) = (fun j => σ (v j)) ⬝ᵥ S.map σ *ᵥ u := by
    rw [show σ (v ⬝ᵥ S *ᵥ (fun j => σ (u j))) = (σ : k →+* k) (v ⬝ᵥ S *ᵥ (fun j => σ (u j))) from rfl,
      RingHom.map_dotProduct]
    congr 1
    funext i
    rw [Function.comp_apply, RingHom.map_mulVec]
    congr 1
    funext j
    simp [hσ]
  rw [h1, h, Matrix.smul_mulVec, dotProduct_smul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, smul_dotProduct, dotProduct_comm, smul_eq_mul]

end GlobalTheory.TwTraceForm

namespace GlobalTheory.TwTraceForm

theorem exists_trace_form : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → (∀ x, c (c x) = x) → B.g * B.σ B.g = 1 → ∀ (a : ℕ) (Q : L[X]), B.P = Q.map e.symm.toRingHom → Q.Separable → Q.natDegree = a → ∀ δ : GL (Fin a) L, (δ * thetaGL a c δ).val.charpoly = Q → ∃ β : B.Aˣ, B.σ (β : B.A) = β * ((-1) ^ (a - 1) * B.g) ∧ ∃ b : Module.Basis (Fin a) K.E B.A, ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = (Matrix.of fun i j => e (B.herm β (b i) (b j))) := by
  intro K B L _ e c hec hcc hg a Q hBP hQs hQd δ hδ
  classical
  let f : L →+* K.E := e.symm.toRingHom
  have hf : ∀ x, f (c x) = K.c (f x) := by
    intro x
    apply e.injective
    show e (e.symm (c x)) = e (K.c (e.symm x))
    rw [hec, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  set G := ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ with hG
  set N := (δ * thetaGL a c δ).val with hN
  set S := G.map f with hS
  set N' := N.map f with hN'
  set ε : K.E := (-1) ^ (a - 1) with hε
  have hεε : ε * ε = 1 := by rw [hε, ← mul_pow]; simp
  have hkey : Sᵀ * N' = ε • S.map K.c := by
    have h0 := congrArg f.mapMatrix (gram_norm a L c δ)
    rw [map_mul] at h0
    simp only [RingHom.mapMatrix_apply] at h0
    rw [Matrix.transpose_map] at h0
    change Sᵀ * N' = _ at h0
    rw [h0]
    ext i j
    simp [f, hf, hε, Matrix.map_apply, Matrix.smul_apply]
    exact hf _
  have hSc : S.map K.c = ε • (Sᵀ * N') := by rw [hkey, smul_smul, hεε, one_smul]
  set Y := ((δ.val * GlobalTheory.Tw.Phi a L)ᵀ).map f with hY
  have hSY : S * Y = 1 := by
    have h0 := congrArg f.mapMatrix (gram_mul_transpose a L δ)
    rw [map_mul, map_one] at h0
    exact h0
  have hsep : (LinearMap.mulLeft K.E B.g).charpoly.Separable := by
    show B.P.Separable
    rw [hBP]; exact hQs.map
  have hchar : (LinearMap.mulLeft K.E B.g).charpoly = (Matrix.toLin' N').charpoly := by
    rw [Matrix.charpoly_toLin', hN', Matrix.charpoly_map, hδ]
    exact hBP
  obtain ⟨ψ, hψ⟩ := GlobalTheory.UnitLemma.PairClass.exists_intertwine K.E B.A (Fin a → K.E)
    (LinearMap.mulLeft K.E B.g) (Matrix.toLin' N') hsep hchar
  have hψ' : ∀ y, ψ (B.g * y) = N' *ᵥ ψ y := fun y => by simpa using hψ y
  have hc1 : ∀ j : Fin a, (fun k => K.c ((Pi.single j (1 : K.E) : Fin a → K.E) k)) = (Pi.single j 1 : Fin a → K.E) := by
    intro j
    funext k
    by_cases h : k = j
    · subst h; simp
    · simp [h]
  let s : B.A → B.A → K.E := fun y z => ψ y ⬝ᵥ S *ᵥ (fun j => K.c (ψ z j))
  have hadd : ∀ x y z, s (x + y) z = s x z + s y z := by
    intro x y z
    simp only [s, map_add, add_dotProduct]
  have hlin : ∀ (r : K.E) x z, s (r • x) z = r * s x z := by
    intro r x z
    simp only [s, map_smul, smul_dotProduct, smul_eq_mul]
  have hnd : ∀ y, (∀ z, s y z = 0) → y = 0 := by
    intro y hy
    have hv : ψ y ᵥ* S = 0 := by
      funext j
      have h1 := hy (ψ.symm (Pi.single j 1))
      simp only [s, LinearEquiv.apply_symm_apply] at h1
      rw [hc1 j, Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at h1
      exact h1
    have h2 : ψ y = 0 := by
      rw [← Matrix.vecMul_one (ψ y), ← hSY, ← Matrix.vecMul_vecMul, hv, Matrix.zero_vecMul]
    exact ψ.injective (by rw [h2, map_zero])
  have hsym : ∀ y z, K.c (s z y) = s ((-1 : B.A) ^ (a - 1) * B.g * y) z := by
    intro y z
    have hψε : ψ ((-1 : B.A) ^ (a - 1) * B.g * y) = ε • N' *ᵥ ψ y := by
      have h1 : (-1 : B.A) ^ (a - 1) = algebraMap K.E B.A ε := by simp [hε]
      rw [h1, mul_assoc, ← Algebra.smul_def, map_smul, hψ']
    simp only [s]
    rw [hψε]
    exact form_asym K.c K.c_c S N' ε hSc (ψ y) (ψ z)
  obtain ⟨β, hβ, hs⟩ := (GlobalTheory.SesqAsym.sesq_asym K B hg hsep ((-1) ^ (a - 1))
    (neg_one_pow_eq_or B.A (a - 1))).2 s hadd hlin hnd hsym
  refine ⟨β, hβ, (Pi.basisFun K.E (Fin a)).map ψ.symm, ?_⟩
  ext i j
  simp only [Matrix.of_apply, Module.Basis.map_apply, Pi.basisFun_apply]
  rw [← hs]
  simp only [s, LinearEquiv.apply_symm_apply]
  rw [hc1 j, Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply, hS, Matrix.map_apply]
  exact (e.apply_symm_apply _).symm

end GlobalTheory.TwTraceForm
