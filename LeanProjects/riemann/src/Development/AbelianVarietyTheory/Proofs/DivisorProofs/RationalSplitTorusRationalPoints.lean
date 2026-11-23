import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTerLast

noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct
open Formalism.UG (cT)

namespace GlobalTheory.IdTorus

theorem torusFrame_mul {R : Type} [CommRing R] {n r : ℕ} {X Y : Matrix (Fin n) (Fin r) R}
    {Xs Ys : Matrix (Fin r) (Fin n) R} (hxx : Xs * X = 0) (hyy : Ys * Y = 0) (hxy : Xs * Y = 1) (hyx : Ys * X = 1)
    (A B A' B' : Matrix (Fin r) (Fin r) R) :
    (1 + X * A * Ys + Y * B * Xs) * (1 + X * A' * Ys + Y * B' * Xs) =
      1 + X * (A + A' + A * A') * Ys + Y * (B + B' + B * B') * Xs := by
  first
  | exact @_root_.GlobalTheory.AbelianSumIdentitySecond.main
  | exact _root_.GlobalTheory.AbelianSumIdentitySecond.main
  | (apply _root_.GlobalTheory.AbelianSumIdentitySecond.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AbelianSumIdentitySecond.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AbelianSumIdentitySecond.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AbelianSumIdentitySecond.main ..)

section Rat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem cT_add' (σ : E →+* E) {m p : Type} (A B : Matrix m p E) : cT σ (A + B) = cT σ A + cT σ B := by
  ext i j; simp [cT]

private theorem cT_diagonal' (σ : E →+* E) {m : Type} [DecidableEq m] (d : m → E) :
    cT σ (diagonal d) = diagonal (fun k => σ (d k)) := by
  ext i j; by_cases h : i = j
  · subst h; simp [cT]
  · simp [cT, diagonal, h, Ne.symm h]

private theorem diagonal_sub_one_comb {R : Type} [CommRing R] {r : ℕ} (a b : Fin r → R) :
    diagonal (fun k => a k - 1) + diagonal (fun k => b k - 1) + diagonal (fun k => a k - 1) * diagonal (fun k => b k - 1) =
      diagonal (fun k => a k * b k - 1) := by
  rw [diagonal_mul_diagonal, diagonal_add, diagonal_add]; congr 1; funext k; ring

theorem torusFrame_mul_diag {R : Type} [CommRing R] {n r : ℕ} {X Y : Matrix (Fin n) (Fin r) R}
    {Xs Ys : Matrix (Fin r) (Fin n) R} (hxx : Xs * X = 0) (hyy : Ys * Y = 0) (hxy : Xs * Y = 1) (hyx : Ys * X = 1)
    (d d' c c' : Fin r → R) :
    (1 + X * diagonal (fun k => d k - 1) * Ys + Y * diagonal (fun k => d' k - 1) * Xs) *
      (1 + X * diagonal (fun k => c k - 1) * Ys + Y * diagonal (fun k => c' k - 1) * Xs) =
      1 + X * diagonal (fun k => d k * c k - 1) * Ys + Y * diagonal (fun k => d' k * c' k - 1) * Xs := by
  rw [torusFrame_mul hxx hyy hxy hyx, diagonal_sub_one_comb, diagonal_sub_one_comb]

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

example (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) : cT (σ : E →+* E) Y * J * X = 1 :=
  yx hσ hJ hW

theorem exists_UJ_torusMat (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (e : Fin r → Eˣ) :
    ∃ u ∈ Formalism.UG.UJ (σ : E →+* E) J, (u : Matrix (Fin n) (Fin n) E) =
      1 + X * diagonal (fun k => (e k : E) - 1) * (cT (σ : E →+* E) Y * J) +
        Y * diagonal (fun k => (σ (e k : E))⁻¹ - 1) * (cT (σ : E →+* E) X * J) := by
  have hxx := hW.xx
  have hyy := hW.yy
  have hxy := hW.xy
  have hyx := yx hσ hJ hW
  set Xs := cT (σ : E →+* E) X * J
  set Ys := cT (σ : E →+* E) Y * J
  let M : (Fin r → E) → (Fin r → E) → Matrix (Fin n) (Fin n) E := fun d d' =>
    1 + X * diagonal (fun k => d k - 1) * Ys + Y * diagonal (fun k => d' k - 1) * Xs
  have hM : ∀ d d' c c', M d d' * M c c' = M (fun k => d k * c k) (fun k => d' k * c' k) :=
    fun d d' c c' => torusFrame_mul_diag hxx hyy hxy hyx d d' c c'
  have h11 : M (fun _ => 1) (fun _ => 1) = 1 := by simp [M]
  have hs0 : ∀ k, σ (e k : E) ≠ 0 := fun k => (map_ne_zero σ).2 (e k).ne_zero
  let d : Fin r → E := fun k => (e k : E)
  let d' : Fin r → E := fun k => (σ (e k : E))⁻¹
  let c : Fin r → E := fun k => (e k : E)⁻¹
  let c' : Fin r → E := fun k => σ (e k : E)
  have e1 : M d d' * M c c' = 1 := by
    rw [hM, ← h11]; congr 1 <;> funext k <;> simp [d, d', c, c', hs0 k]
  have e2 : M c c' * M d d' = 1 := by
    rw [hM, ← h11]; congr 1 <;> funext k <;> simp [d, d', c, c', hs0 k]
  refine ⟨⟨M d d', M c c', e1, e2⟩, ?_, rfl⟩
  show cT (σ : E →+* E) (M d d') * J * M d d' = J
  have hcc : ∀ N : Matrix (Fin n) (Fin r) E, cT (σ : E →+* E) (cT (σ : E →+* E) N) = N := fun N =>
    Matrix.ext fun _ _ => sigma_sigma hσ _
  have hJJ : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
  have hc : cT (σ : E →+* E) (M d d') * J = J * M (fun k => σ (d' k)) (fun k => σ (d k)) := by
    simp only [M, cT_add', Formalism.UG.cT_mul, Formalism.UG.cT_one, cT_diagonal', Xs, Ys, hcc, hJJ, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, map_sub, map_one, RingHom.coe_coe]
    abel
  rw [hc, Matrix.mul_assoc, hM]
  convert Matrix.mul_one J using 2
  rw [← h11]; congr 1 <;> funext k <;> simp [d, d', hs0 k, sigma_sigma hσ]

theorem mem_ratPts_of_isIdTorusElt (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (e : Fin r → Eˣ)
    {a : GAd σ J} (ha : IsIdTorusElt σ J X Y (fun k => Units.map (inclR (F := F) (AF F)).toMonoidHom (e k)) a) :
    a ∈ ratPts σ J := by
  obtain ⟨u, hu, hue⟩ := exists_UJ_torusMat hσ hJ hW e
  have hyx := yx hσ hJ hW
  set ι : E →+* AF F ⊗[F] E := inclR (F := F) (AF F)
  set Xs := cT (σ : E →+* E) X * J
  set Ys := cT (σ : E →+* E) Y * J
  have hm : ∀ {p q s : ℕ} (A : Matrix (Fin p) (Fin q) E) (B : Matrix (Fin q) (Fin s) E),
      adMat F (A * B) = adMat F A * adMat F B := fun A B => Matrix.map_mul
  have hxx : adMat F Xs * adMat F X = 0 := by rw [← hm, hW.xx]; simp
  have hyy : adMat F Ys * adMat F Y = 0 := by rw [← hm, hW.yy]; simp
  have hxy : adMat F Xs * adMat F Y = 1 := by rw [← hm, hW.xy]; simp
  have hyx' : adMat F Ys * adMat F X = 1 := by rw [← hm, hyx]; simp
  set Ma := (matHom _ σ J a).1
  set P : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := 1 - adMat F X * adMat F Ys - adMat F Y * adMat F Xs
  have hXP : adMat F Xs * P = 0 := by
    simp only [P, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hxx, hxy, Matrix.zero_mul, Matrix.one_mul]; abel
  have hYP : adMat F Ys * P = 0 := by
    simp only [P, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hyy, hyx', Matrix.zero_mul, Matrix.one_mul]; abel
  have hMP : Ma * P = P := by
    ext i j
    have hz : (fun k => P k j) ∈ colPerp σ J X Set.univ ⊓ colPerp σ J Y Set.univ := by
      simp only [colPerp, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.proj_apply, Matrix.mulVecLin_apply]
      refine ⟨fun k _ => ?_, fun k _ => ?_⟩
      · have := congrFun (congrFun hXP k) j
        rw [Matrix.mul_apply] at this; simpa [Matrix.mulVec, dotProduct, Xs] using this
      · have := congrFun (congrFun hYP k) j
        rw [Matrix.mul_apply] at this; simpa [Matrix.mulVec, dotProduct, Ys] using this
    have := congrFun (ha.2.2 _ hz) i
    rw [Matrix.mul_apply]; simpa [Matrix.mulVec, dotProduct] using this
  have hD : diagonal (fun k => ((Units.map ι.toMonoidHom (e k) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) =
      (diagonal (fun k => (e k : E))).map ι := by rw [Matrix.diagonal_map (map_zero ι)]; rfl
  have hD' : diagonal (fun k => (((conjUnit σ (Units.map ι.toMonoidHom (e k)))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) =
      (diagonal (fun k => (σ (e k : E))⁻¹)).map ι := by
    rw [Matrix.diagonal_map (map_zero ι)]
    congr 1; funext k
    have hc : conjUnit σ (Units.map ι.toMonoidHom (e k)) = Units.map ι.toMonoidHom (Units.map (σ : E →+* E).toMonoidHom (e k)) :=
      Units.ext (by simp [conjUnit, sigR, inclR, ι])
    rw [hc, ← map_inv, ← map_inv]
    simp [Units.val_inv_eq_inv_val]
  have hsub : ∀ d : Fin r → E, diagonal (fun k => d k - 1) = diagonal d - 1 := by
    intro d; rw [← diagonal_one, diagonal_sub]
  rw [hsub, hsub] at hue
  have hMa : Ma = (u : Matrix (Fin n) (Fin n) E).map ι := by
    have h1 : Ma = Ma * (adMat F X * adMat F Ys + adMat F Y * adMat F Xs + P) := by
      rw [show adMat F X * adMat F Ys + adMat F Y * adMat F Xs + P = 1 by simp only [P]; abel, Matrix.mul_one]
    rw [h1, Matrix.mul_add, Matrix.mul_add, hMP, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ha.1, ha.2.1, hD, hD', hue]
    simp only [ι, P, adMat, Matrix.map_add, Matrix.map_sub, Matrix.map_one _ (map_zero ι) (map_one ι), Matrix.map_mul,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    simp only [Matrix.map_add _ (map_add (inclR (F := F) (AF F))), Matrix.map_sub _ (map_sub (inclR (F := F) (AF F))),
      Matrix.map_one _ (map_zero (inclR (F := F) (AF F))) (map_one (inclR (F := F) (AF F))), Matrix.map_mul]
    abel
  show a.1 ∈ HFin (AF F) σ J
  refine Subgroup.mem_map.2 ⟨u, hu, Units.ext ?_⟩
  exact hMa.symm

end Rat

end GlobalTheory.IdTorus
