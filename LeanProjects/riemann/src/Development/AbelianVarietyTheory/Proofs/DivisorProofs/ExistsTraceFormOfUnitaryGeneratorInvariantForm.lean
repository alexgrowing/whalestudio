import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat.BetaEx

variable {K : GlobalTheory.UnitLemma.UQ} {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ}

def sv (G : Matrix (Fin m) (Fin m) K.E) (x y : Fin m → K.E) : K.E :=
  x ⬝ᵥ (G *ᵥ fun j => K.c (y j))

def sf (b : Module.Basis (Fin m) K.E B.A) (G : Matrix (Fin m) (Fin m) K.E) (a z : B.A) : K.E :=
  sv G (b.repr a) (b.repr z)

variable (b : Module.Basis (Fin m) K.E B.A) (G : Matrix (Fin m) (Fin m) K.E)

theorem sf_add_left (a a' z : B.A) : sf b G (a + a') z = sf b G a z + sf b G a' z := by
  simp [sf, sv, map_add, add_dotProduct]

theorem sf_smul_left (l : K.E) (a z : B.A) : sf b G (l • a) z = l * sf b G a z := by
  simp [sf, sv, map_smul, smul_dotProduct]

theorem sf_add_right (a z z' : B.A) : sf b G a (z + z') = sf b G a z + sf b G a z' := by
  have : (fun j => K.c ((b.repr (z + z')) j)) = (fun j => K.c (b.repr z j)) + fun j => K.c (b.repr z' j) := by
    ext j; simp
  simp only [sf, sv, this, mulVec_add, dotProduct_add]

theorem sf_smul_right (l : K.E) (a z : B.A) : sf b G a (l • z) = K.c l * sf b G a z := by
  have : (fun j => K.c ((b.repr (l • z)) j)) = K.c l • fun j => K.c (b.repr z j) := by
    ext j; simp
  simp only [sf, sv, this, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem sf_basis (i j : Fin m) : sf b G (b i) (b j) = G i j := by
  simp [sf, sv, dotProduct, mulVec, Finsupp.single_apply, Pi.single_apply]

end GlobalTheory.TwLat.BetaEx

namespace GlobalTheory.TwLat.BetaEx

variable {K : GlobalTheory.UnitLemma.UQ} {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ}
variable (b : Module.Basis (Fin m) K.E B.A) (G : Matrix (Fin m) (Fin m) K.E)

theorem sv_inv (N : Matrix (Fin m) (Fin m) K.E) (hN : Nᵀ * G * N.map K.c = G) (x y : Fin m → K.E) :
    sv G (N *ᵥ x) (N *ᵥ y) = sv G x y := by
  have hc : (fun j => K.c ((N *ᵥ y) j)) = N.map K.c *ᵥ fun j => K.c (y j) := by
    ext j; exact RingHom.map_mulVec (K.c : K.E →+* K.E) N y j
  unfold sv
  rw [hc, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hN]

theorem sf_mul_u (u : B.A) (hN : (LinearMap.toMatrix b b (LinearMap.mulLeft K.E u))ᵀ * G *
    (LinearMap.toMatrix b b (LinearMap.mulLeft K.E u)).map K.c = G) (a z : B.A) :
    sf b G (u * a) (u * z) = sf b G a z := by
  unfold sf
  have h1 := LinearMap.toMatrix_mulVec_repr b b (LinearMap.mulLeft K.E u) a
  have h2 := LinearMap.toMatrix_mulVec_repr b b (LinearMap.mulLeft K.E u) z
  simp only [LinearMap.mulLeft_apply] at h1 h2
  rw [← h1, ← h2, sv_inv G _ hN]

theorem sf_adj (u : B.A) (hu : Algebra.adjoin K.E {u} = ⊤) (hu1 : u * B.σ u = 1)
    (hN : (LinearMap.toMatrix b b (LinearMap.mulLeft K.E u))ᵀ * G *
    (LinearMap.toMatrix b b (LinearMap.mulLeft K.E u)).map K.c = G) (x a z : B.A) :
    sf b G (x * a) z = sf b G a (B.σ x * z) := by
  have hx : x ∈ Algebra.adjoin K.E {u} := hu ▸ Algebra.mem_top
  revert a z
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx; subst hx
    intro a z
    conv_lhs => rw [show z = x * (B.σ x * z) by rw [← mul_assoc, hu1, one_mul]]
    exact sf_mul_u b G x hN a _
  | algebraMap l =>
    intro a z
    rw [← Algebra.smul_def, sf_smul_left, B.σ_alg, ← Algebra.smul_def, sf_smul_right, K.c_c]
  | add x y _ _ hx hy =>
    intro a z
    rw [add_mul, sf_add_left, hx, hy, map_add, add_mul, sf_add_right]
  | mul x y _ _ hx hy =>
    intro a z
    rw [mul_comm x y, mul_assoc, hy, hx, map_mul]; congr 1; ring

end GlobalTheory.TwLat.BetaEx

namespace GlobalTheory.TwLat.BetaEx

theorem exists_beta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A) (u : B.A), Algebra.adjoin K.E {u} = ⊤ → u * B.σ u = 1 → (Algebra.traceForm K.E B.A).Nondegenerate → ∀ G : Matrix (Fin m) (Fin m) (w.adicCompletion E), (GlobalTheory.TwLat.mulMat e b u)ᵀ * G * (cj w).mapMatrix (GlobalTheory.TwLat.mulMat e b u) = G → ∃ β : B.A, GlobalTheory.TwLat.gram e b β = G := by
  intro E _ _ _ w K e he B m b u hu hu1 hnd G hG
  set N := LinearMap.toMatrix b b (LinearMap.mulLeft K.E u) with hNdef
  set G' : Matrix (Fin m) (Fin m) K.E := G.map e.symm with hG'
  have hGG : G = G'.map e := by ext i j; simp [hG']
  have hN : Nᵀ * G' * N.map K.c = G' := by
    have h2 : ((Nᵀ * G' * N.map K.c).map e) = G'.map e := by
      rw [← hGG]
      conv_rhs => rw [← hG]
      rw [hGG]
      have : (Nᵀ * G' * N.map K.c).map e = ((e : K.E →+* w.adicCompletion E).mapMatrix) (Nᵀ * G' * N.map K.c) := rfl
      rw [this, map_mul, map_mul]
      congr 1
      ext i j
      simp [GlobalTheory.TwLat.mulMat, hNdef, RingHom.mapMatrix_apply, he]
    exact Matrix.map_injective e.injective h2
  let ℓ : Module.Dual K.E B.A :=
    { toFun := fun a => sf b G' a 1
      map_add' := fun a a' => sf_add_left b G' a a' 1
      map_smul' := fun l a => sf_smul_left b G' l a 1 }
  refine ⟨(LinearMap.BilinForm.toDual _ hnd).symm ℓ, ?_⟩
  refine Matrix.ext fun i j => ?_
  set β := (LinearMap.BilinForm.toDual _ hnd).symm ℓ
  have hβ : ∀ a, Algebra.trace K.E B.A (β * a) = ℓ a := by
    intro a
    rw [← Algebra.traceForm_apply, ← LinearMap.BilinForm.toDual_def hnd, LinearEquiv.apply_symm_apply]
  simp only [GlobalTheory.TwLat.gram, Matrix.of_apply, GlobalTheory.UnitLemma.InvAlg.herm]
  rw [mul_assoc, hβ]
  show e (sf b G' (b i * B.σ (b j)) 1) = G i j
  rw [mul_comm, sf_adj b G' u hu hu1 hN, B.σ_σ, mul_one, sf_basis, hG']
  simp

end GlobalTheory.TwLat.BetaEx
