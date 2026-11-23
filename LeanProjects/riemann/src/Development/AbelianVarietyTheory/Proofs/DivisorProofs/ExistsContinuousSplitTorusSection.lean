import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne

noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.IdTorus

def frameTorMat {A : Type} [CommRing A] (s : A →+* A) {n r : ℕ} (J : Matrix (Fin n) (Fin n) A)
    (X Y : Matrix (Fin n) (Fin r) A) (d : Fin r → Aˣ) : Matrix (Fin n) (Fin n) A :=
  1 + X * diagonal (fun i => (d i : A) - 1) * (cT s Y * J) +
    Y * diagonal (fun i => s ((d i)⁻¹ : Aˣ) - 1) * (cT s X * J)

section Alg

variable {A : Type} [CommRing A] {s : A →+* A} {n r : ℕ} {J : Matrix (Fin n) (Fin n) A}
  {X Y : Matrix (Fin n) (Fin r) A}

theorem diagonal_sub_one' (a : Fin r → A) : diagonal (fun i => a i - 1) = diagonal a - 1 := by
  rw [← diagonal_one, diagonal_sub]

theorem frameTorMat_mul_X (xx : cT s X * J * X = 0) (yx : cT s Y * J * X = 1) (d : Fin r → Aˣ) :
    frameTorMat s J X Y d * X = X * diagonal fun i => (d i : A) := by
  simp only [frameTorMat, Matrix.add_mul, Matrix.mul_assoc _ (cT s Y * J), Matrix.mul_assoc _ (cT s X * J), xx, yx,
    diagonal_sub_one', Matrix.mul_sub]
  simp

theorem frameTorMat_mul_Y (yy : cT s Y * J * Y = 0) (xy : cT s X * J * Y = 1) (d : Fin r → Aˣ) :
    frameTorMat s J X Y d * Y = Y * diagonal fun i => s ((d i)⁻¹ : Aˣ) := by
  simp only [frameTorMat, Matrix.add_mul, Matrix.mul_assoc _ (cT s Y * J), Matrix.mul_assoc _ (cT s X * J), yy, xy,
    diagonal_sub_one', Matrix.mul_sub]
  simp

theorem frameTorMat_mulVec {z : Fin n → A} (hx : (cT s X * J) *ᵥ z = 0) (hy : (cT s Y * J) *ᵥ z = 0)
    (d : Fin r → Aˣ) : frameTorMat s J X Y d *ᵥ z = z := by
  rw [frameTorMat, add_mulVec, add_mulVec, ← mulVec_mulVec, hy, mulVec_zero, ← mulVec_mulVec, hx, mulVec_zero]
  simp

theorem frameTorMat_mul_inv (xx : cT s X * J * X = 0) (yy : cT s Y * J * Y = 0) (xy : cT s X * J * Y = 1)
    (yx : cT s Y * J * X = 1) (d : Fin r → Aˣ) : frameTorMat s J X Y d * frameTorMat s J X Y d⁻¹ = 1 := by
  conv_lhs => rw [show frameTorMat s J X Y d⁻¹ = 1 + _ + _ from rfl, Matrix.mul_add, Matrix.mul_add, Matrix.mul_one]
  simp only [← Matrix.mul_assoc (frameTorMat s J X Y d), frameTorMat_mul_X xx yx, frameTorMat_mul_Y yy xy,
    Matrix.mul_assoc _ (diagonal _) (diagonal _), diagonal_mul_diagonal]
  have h1 : ∀ i, (d i : A) * (((d⁻¹) i : Aˣ) - 1) = 1 - d i := fun i => by
    rw [Pi.inv_apply, mul_sub, Units.mul_inv, mul_one]
  have h2 : ∀ i, s ((d i)⁻¹ : Aˣ) * (s (((d⁻¹) i)⁻¹ : Aˣ) - 1) = 1 - s ((d i)⁻¹ : Aˣ) := fun i => by
    rw [Pi.inv_apply, inv_inv, mul_sub, ← map_mul, Units.inv_mul, map_one, mul_one]
  simp only [h1, h2, frameTorMat, ← diagonal_sub, diagonal_one, Matrix.mul_sub, Matrix.sub_mul]
  abel

theorem frameTorMat_unitary (hs : ∀ a, s (s a) = a) (hJ : cT s J = J) (xx : cT s X * J * X = 0)
    (yy : cT s Y * J * Y = 0) (xy : cT s X * J * Y = 1) (yx : cT s Y * J * X = 1) (d : Fin r → Aˣ) :
    cT s (frameTorMat s J X Y d) * J * frameTorMat s J X Y d = J := by
  have cc : ∀ Z : Matrix (Fin n) (Fin r) A, cT s (cT s Z) = Z := fun Z => Matrix.ext fun i j => hs _
  have cd : ∀ a : Fin r → A, cT s (diagonal a) = diagonal fun i => s (a i) := fun a => by
    ext i j; by_cases h : i = j <;> simp [cT, diagonal, h, eq_comm]
  have ca : ∀ P Q : Matrix (Fin n) (Fin n) A, cT s (P + Q) = cT s P + cT s Q := fun P Q =>
    Matrix.ext fun i j => map_add s _ _
  have hU : cT s (frameTorMat s J X Y d) * J = J * frameTorMat s J X Y d⁻¹ := by
    simp only [frameTorMat, ca, Formalism.UG.cT_mul, Formalism.UG.cT_one, cc, hJ, cd, map_sub, map_one, hs, Pi.inv_apply, inv_inv,
      Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one]
    abel
  have hM' : frameTorMat s J X Y d⁻¹ * frameTorMat s J X Y d = 1 := by
    simpa only [inv_inv] using frameTorMat_mul_inv xx yy xy yx d⁻¹
  rw [hU, Matrix.mul_assoc, hM', Matrix.mul_one]

end Alg

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in
theorem continuous_frameTorMat {B : Type} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] {s : B →+* B}
    (hs : Continuous s) {n r : ℕ} (J : Matrix (Fin n) (Fin n) B) (X Y : Matrix (Fin n) (Fin r) B) :
    Continuous (frameTorMat s J X Y) := by
  have h1 : Continuous fun d : Fin r → Bˣ => diagonal fun i => (d i : B) - 1 :=
    Continuous.matrix_diagonal (continuous_pi fun i => (Units.continuous_val.comp (continuous_apply i)).sub continuous_const)
  have h2 : Continuous fun d : Fin r → Bˣ => diagonal fun i => s ((d i)⁻¹ : Bˣ) - 1 :=
    Continuous.matrix_diagonal (continuous_pi fun i =>
      (hs.comp (Units.continuous_coe_inv.comp (continuous_apply i))).sub continuous_const)
  exact (continuous_const.add ((continuous_const.matrix_mul h1).matrix_mul continuous_const)).add
    ((continuous_const.matrix_mul h2).matrix_mul continuous_const)

theorem exists_continuous_isIdTorusElt {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}
    {X Y : Matrix (Fin n) (Fin r) E} (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    ∃ t : (Fin r → (AF F ⊗[F] E)ˣ) → GAd σ J, Continuous t ∧ ∀ l, IsIdTorusElt σ J X Y l (t l) := by
  obtain ⟨_, _⟩ := ring_facts (F := F) (E := E)
  set s := sigR (AF F) σ
  have hs : ∀ a, s (s a) = a := fun a => by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (sigma_sigma h x)
  have c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), cT s (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have c3 : ∀ {a : ℕ} (Z : Matrix (Fin n) (Fin a) E),
      (cT s (adMat F Z) * JR (AF F) J : Matrix (Fin a) (Fin n) (AF F ⊗[F] E)) = adMat F (cT (σ : E →+* E) Z * J) :=
    fun Z => by rw [c1]; simp only [adMat, JR, Matrix.map_mul] <;> rfl
  have c2 : ∀ Z Z' : Matrix (Fin n) (Fin r) E,
      (cT s (adMat F Z) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F Z' =
        adMat F (cT (σ : E →+* E) Z * J * Z') := fun Z Z' => by
    rw [c3]; simp only [adMat, Matrix.map_mul]
  have hJ' : cT s (JR (AF F) J) = JR (AF F) J :=
    (c1 J).trans (congrArg (adMat F) (Matrix.ext fun i j => hJ.1 i j))
  have xx : (cT s (adMat F X) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F X = 0 := by
    rw [c2, hW.xx]; exact Matrix.map_zero _ (map_zero _)
  have yy : (cT s (adMat F Y) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F Y = 0 := by
    rw [c2, hW.yy]; exact Matrix.map_zero _ (map_zero _)
  have xy : (cT s (adMat F X) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F Y = 1 := by
    rw [c2, hW.xy]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have yx : (cT s (adMat F Y) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F X = 1 := by
    rw [c2, GlobalTheory.StdPar.yx h hJ hW]; exact Matrix.map_one _ (map_zero _) (map_one _)
  let M := frameTorMat s (JR (AF F) J) (adMat F X) (adMat F Y)
  have hinv : ∀ d, M d * M d⁻¹ = 1 := frameTorMat_mul_inv xx yy xy yx
  have hinv' : ∀ d, M d⁻¹ * M d = 1 := fun d => by simpa only [inv_inv] using hinv d⁻¹
  let t : (Fin r → (AF F ⊗[F] E)ˣ) → GAd σ J := fun l =>
    ⟨⟨M l, M l⁻¹, hinv l, hinv' l⟩, frameTorMat_unitary hs hJ' xx yy xy yx l⟩
  have hc : Continuous M := continuous_frameTorMat (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ) _ _ _
  refine ⟨t, ?_, fun l => ⟨frameTorMat_mul_X xx yx l, ?_, fun z hz => ?_⟩⟩
  · refine Continuous.subtype_mk ((Units.continuous_iff (f := fun l => (⟨M l, M l⁻¹, hinv l, hinv' l⟩ : GL (Fin n) (AF F ⊗[F] E)))).2 ⟨hc, hc.comp continuous_inv⟩) _
  · refine (frameTorMat_mul_Y yy xy l).trans (congrArg (fun D => adMat F Y * diagonal D) (funext fun k => ?_))
    rw [← map_inv]; rfl
  · have key : ∀ C : Matrix (Fin n) (Fin r) E, z ∈ colPerp σ J C Set.univ →
        (cT s (adMat F C) * JR (AF F) J) *ᵥ z = 0 := fun C hC => by
      rw [c3]
      funext i
      have := (Submodule.mem_iInf _).1 hC i
      simpa using this
    exact frameTorMat_mulVec (key X hz.1) (key Y hz.2) l

end Main

end GlobalTheory.IdTorus
