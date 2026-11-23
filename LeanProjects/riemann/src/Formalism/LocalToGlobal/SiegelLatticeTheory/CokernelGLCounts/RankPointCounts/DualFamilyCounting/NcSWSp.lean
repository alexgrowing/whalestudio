import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSSplS
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSGLP

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.NcS.LT

namespace WSp

section Lin

variable {K : Type*} [Field K] {n : ℕ}

def dl (u : Fin n → K) : Module.Dual K (Fin n → K) where
  toFun w := u ⬝ᵥ w
  map_add' x y := dotProduct_add u x y
  map_smul' c x := by simp [dotProduct_smul]

theorem dl_apply (u w : Fin n → K) : dl u w = u ⬝ᵥ w := rfl

theorem eq_of_dot (u u' : Fin n → K) (h : ∀ w, u ⬝ᵥ w = u' ⬝ᵥ w) : u = u' := by
  funext i
  have e := h (Pi.single i 1)
  simpa [dotProduct_single] using e

end Lin

section Split

variable {K S : Type*} [Field K] [CommRing S] (π π' : S →+* K)

theorem indep_coord {n m : ℕ} (hinj : ∀ s t, π s = π t → π' s = π' t → s = t)
    (hsur : ∀ p : K, ∃ s, π s = p ∧ π' s = 0) (X : Fin m → Fin n → S) (hX : LinearIndependent S X) :
    LinearIndependent K (fun j i => π (X j i)) := by
  rw [Fintype.linearIndependent_iff] at hX ⊢
  intro c hc j
  choose s hs using hsur
  have hsum : ∑ k, s (c k) • X k = 0 := by
    funext i
    have e := congrFun hc i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e ⊢
    apply hinj
    · simp only [map_sum, map_mul, (hs _).1, map_zero]
      exact e
    · simp [map_sum, map_mul, (hs _).2]
  have e := hX _ hsum j
  rw [← (hs (c j)).1, e, map_zero]

theorem mat_ext {n : ℕ} (hinj : ∀ s t, π s = π t → π' s = π' t → s = t) (M N : Matrix (Fin n) (Fin n) S)
    (h1 : M.map π = N.map π) (h2 : M.map π' = N.map π') : M = N := by
  ext i j
  exact hinj _ _ (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

theorem map_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) S) (x : Fin n → S) (i : Fin n) :
    π ((M *ᵥ x) i) = (M.map π *ᵥ fun j => π (x j)) i := by
  simp [mulVec, dotProduct, map_sum, map_mul]

end Split

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem witt_split (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J)
    (v : HeightOneSpectrum (𝓞 F)) (π₁ π₂ : Fv F v ⊗[F] E →+* Fv F v)
    (hσ1 : ∀ s, π₁ (sigR (Fv F v) σ s) = π₂ s) (hσ2 : ∀ s, π₂ (sigR (Fv F v) σ s) = π₁ s)
    (hinj : ∀ s t, π₁ s = π₁ t → π₂ s = π₂ t → s = t)
    (hsur : ∀ p q : Fv F v, ∃ s, π₁ s = p ∧ π₂ s = q) {m : ℕ} (X Y : TupV (E := E) v n m)
    (hX : LinearIndependent (Fv F v ⊗[F] E) X) (hY : LinearIndependent (Fv F v ⊗[F] E) Y)
    (hG : gramR (Fv F v) σ J X = gramR (Fv F v) σ J Y) : ∃ g : HA (Fv F v) σ J, g • X = Y := by
  classical
  set J1 : Matrix (Fin n) (Fin n) (Fv F v) := (JR (F := F) (Fv F v) J).map π₁ with hJ1
  have hJ2 : (JR (F := F) (Fv F v) J).map π₂ = J1ᵀ := by
    ext i j
    simp only [Matrix.map_apply, transpose_apply, hJ1, JR]
    rw [← hσ1, (fun x => by simp [sigR, inclR] : ∀ x : E, sigR (Fv F v) σ (inclR (F := F) (Fv F v) x) =
      inclR (F := F) (Fv F v) (σ x)), hJ.1 j i]
  have hdetJ : IsUnit J1.det := by
    have e1 : J1.det = π₁ (JR (F := F) (Fv F v) J).det := (RingHom.map_det π₁ _).symm
    have e2 : (JR (F := F) (Fv F v) J).det = inclR (F := F) (Fv F v) J.det := (RingHom.map_det (inclR (F := F) (Fv F v)) J).symm
    rw [e1, e2]
    exact ((Ne.isUnit hJ.2).map (inclR (F := F) (Fv F v))).map π₁

  have hform : ∀ x y : Fin n → (Fv F v) ⊗[F] E,
      π₁ (hR (Fv F v) σ J x y) = (fun i => π₂ (x i)) ⬝ᵥ (J1 *ᵥ fun i => π₁ (y i)) := by
    intro x y
    simp only [hR, Formalism.UG.hform, map_sum, map_mul, hσ1, dotProduct, mulVec, Finset.mul_sum, hJ1,
      Matrix.map_apply, mul_assoc]
  set x1 : Fin m → Fin n → (Fv F v) := fun j i => π₁ (X j i)
  set y1 : Fin m → Fin n → (Fv F v) := fun j i => π₁ (Y j i)
  set x2 : Fin m → Fin n → (Fv F v) := fun j i => π₂ (X j i)
  set y2 : Fin m → Fin n → (Fv F v) := fun j i => π₂ (Y j i)
  have hsur1 : ∀ p : (Fv F v), ∃ s, π₁ s = p ∧ π₂ s = 0 := fun p => hsur p 0
  have hsur2 : ∀ p : (Fv F v), ∃ s, π₂ s = p ∧ π₁ s = 0 := fun p => (hsur 0 p).imp fun _ h => ⟨h.2, h.1⟩
  have hinj' : ∀ s t, π₂ s = π₂ t → π₁ s = π₁ t → s = t := fun s t h2 h1 => hinj s t h1 h2
  have hx1 : LinearIndependent (Fv F v) x1 := indep_coord π₁ π₂ hinj hsur1 X hX
  have hy1 : LinearIndependent (Fv F v) y1 := indep_coord π₁ π₂ hinj hsur1 Y hY
  have hx2 : LinearIndependent (Fv F v) x2 := indep_coord π₂ π₁ hinj' hsur2 X hX
  have hy2 : LinearIndependent (Fv F v) y2 := indep_coord π₂ π₁ hinj' hsur2 Y hY

  have hvecinj : ∀ u : Fin n → (Fv F v), u ᵥ* J1 = 0 → u = 0 := by
    intro u hu
    have : u = (u ᵥ* J1) ᵥ* J1⁻¹ := by rw [vecMul_vecMul, mul_nonsing_inv _ hdetJ, vecMul_one]
    rw [this, hu, zero_vecMul]
  have hforms : ∀ z : Fin m → Fin n → (Fv F v), LinearIndependent (Fv F v) z →
      LinearIndependent (Fv F v) (fun j => dl (z j ᵥ* J1)) := by
    intro z hz
    rw [Fintype.linearIndependent_iff] at hz ⊢
    intro c hc
    apply hz c
    apply hvecinj
    apply eq_of_dot
    intro w
    have e := LinearMap.congr_fun hc w
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, dl_apply, smul_eq_mul,
      LinearMap.zero_apply] at e
    have key : ∀ u, (u ᵥ* J1) ⬝ᵥ w = dl (J1 *ᵥ w) u := fun u => by
      rw [dl_apply, ← dotProduct_mulVec, dotProduct_comm]
    rw [key, zero_dotProduct, map_sum]
    refine (Finset.sum_congr rfl fun x _ => ?_).trans e
    rw [map_smul, ← key, smul_eq_mul]
  have hpair : ∀ i j, dl (x2 i ᵥ* J1) (x1 j) = dl (y2 i ᵥ* J1) (y1 j) := by
    intro i j
    rw [dl_apply, dl_apply, ← dotProduct_mulVec, ← dotProduct_mulVec]
    have e := congrFun (congrFun hG i) j
    simp only [gramR] at e
    have e1 := hform (X i) (X j)
    have e2 := hform (Y i) (Y j)
    rw [e] at e1
    exact e1.symm.trans e2
  obtain ⟨A, hAx, hAη⟩ := GLP.glPair x1 y1 (fun j => dl (x2 j ᵥ* J1)) (fun j => dl (y2 j ᵥ* J1)) hx1 hy1
    (hforms x2 hx2) (hforms y2 hy2) hpair
  set Am := LinearMap.toMatrix' (A : (Fin n → (Fv F v)) →ₗ[(Fv F v)] (Fin n → (Fv F v)))
  set Ai := LinearMap.toMatrix' (A.symm : (Fin n → (Fv F v)) →ₗ[(Fv F v)] (Fin n → (Fv F v)))
  have hAm : ∀ w, Am *ᵥ w = A w := fun w => LinearMap.toMatrix'_mulVec _ w
  have hAAi : Am * Ai = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext w
    simp
  have hAiA : Ai * Am = 1 := mul_eq_one_comm.mp hAAi
  have hJJ : J1 * J1⁻¹ = 1 := mul_nonsing_inv _ hdetJ
  have hJJ' : J1⁻¹ * J1 = 1 := nonsing_inv_mul _ hdetJ
  set B : Matrix (Fin n) (Fin n) (Fv F v) := (J1 * Ai * J1⁻¹)ᵀ
  set Bi : Matrix (Fin n) (Fin n) (Fv F v) := (J1 * Am * J1⁻¹)ᵀ
  have hBBi : B * Bi = 1 := by
    rw [← transpose_mul, ← transpose_one]
    congr 1
    calc J1 * Am * J1⁻¹ * (J1 * Ai * J1⁻¹) = J1 * Am * (J1⁻¹ * J1) * Ai * J1⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJJ', Matrix.mul_one, Matrix.mul_assoc J1, hAAi, Matrix.mul_one, hJJ]
  have hBiB : Bi * B = 1 := mul_eq_one_comm.mp hBBi
  have hU1 : Bᵀ * J1 * Am = J1 := by
    calc Bᵀ * J1 * Am = J1 * Ai * (J1⁻¹ * J1) * Am := by simp only [B, transpose_transpose, Matrix.mul_assoc]
      _ = J1 := by rw [hJJ', Matrix.mul_one, Matrix.mul_assoc, hAiA, Matrix.mul_one]
  have hU2 : Amᵀ * J1ᵀ * B = J1ᵀ := by
    have : Amᵀ * J1ᵀ * B = (Bᵀ * J1 * Am)ᵀ := by
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
    rw [this, hU1]

  choose mk hmk using hsur
  set gm : Matrix (Fin n) (Fin n) ((Fv F v) ⊗[F] E) := Matrix.of fun i j => mk (Am i j) (B i j)
  set gi : Matrix (Fin n) (Fin n) ((Fv F v) ⊗[F] E) := Matrix.of fun i j => mk (Ai i j) (Bi i j)
  have hg1 : gm.map π₁ = Am := by ext i j; simp [gm, (hmk _ _).1]
  have hg2 : gm.map π₂ = B := by ext i j; simp [gm, (hmk _ _).2]
  have hgi1 : gi.map π₁ = Ai := by ext i j; simp [gi, (hmk _ _).1]
  have hgi2 : gi.map π₂ = Bi := by ext i j; simp [gi, (hmk _ _).2]
  have hone1 : (1 : Matrix (Fin n) (Fin n) ((Fv F v) ⊗[F] E)).map π₁ = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hone2 : (1 : Matrix (Fin n) (Fin n) ((Fv F v) ⊗[F] E)).map π₂ = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hm1 : gm * gi = 1 := mat_ext π₁ π₂ hinj _ _ (by rw [Matrix.map_mul, hg1, hgi1, hAAi, hone1])
    (by rw [Matrix.map_mul, hg2, hgi2, hBBi, hone2])
  have hm2 : gi * gm = 1 := mat_ext π₁ π₂ hinj _ _ (by rw [Matrix.map_mul, hg1, hgi1, hAiA, hone1])
    (by rw [Matrix.map_mul, hg2, hgi2, hBiB, hone2])
  set u : GL (Fin n) ((Fv F v) ⊗[F] E) := ⟨gm, gi, hm1, hm2⟩
  have hcT1 : (Formalism.UG.cT (sigR (Fv F v) σ) gm).map π₁ = Bᵀ := by
    ext i j; simp [Formalism.UG.cT, hσ1, ← hg2]
  have hcT2 : (Formalism.UG.cT (sigR (Fv F v) σ) gm).map π₂ = Amᵀ := by
    ext i j; simp [Formalism.UG.cT, hσ2, ← hg1]
  have hu : u ∈ HR (Fv F v) σ J := by
    show Formalism.UG.cT (sigR (Fv F v) σ) gm * JR (F := F) (Fv F v) J * gm = JR (F := F) (Fv F v) J
    apply mat_ext π₁ π₂ hinj
    · rw [Matrix.map_mul, Matrix.map_mul, hcT1, hg1, ← hJ1, hU1]
    · rw [Matrix.map_mul, Matrix.map_mul, hcT2, hg2, hJ2, hU2]
  refine ⟨⟨u, hu⟩, ?_⟩
  have hmul : ∀ w : Fin n → (Fv F v) ⊗[F] E, (⟨u, hu⟩ : HA (Fv F v) σ J) • (fun _ : Fin 1 => w) = fun _ => gm *ᵥ w :=
    fun _ => rfl

  have hB2 : ∀ j, B *ᵥ x2 j = y2 j := by
    intro j
    have hdot : y2 j ᵥ* J1 ᵥ* Am = x2 j ᵥ* J1 := by
      apply eq_of_dot
      intro w
      have e := hAη j w
      simp only [dl_apply, ← hAm] at e
      rw [← dotProduct_mulVec, e]
    calc B *ᵥ x2 j = x2 j ᵥ* J1 ᵥ* Ai ᵥ* J1⁻¹ := by
          simp only [B, mulVec_transpose, vecMul_vecMul]
      _ = y2 j ᵥ* J1 ᵥ* Am ᵥ* Ai ᵥ* J1⁻¹ := by rw [hdot]
      _ = y2 j := by
          simp only [vecMul_vecMul, Matrix.mul_assoc, hAAi, Matrix.mul_one, hJJ, vecMul_one]
  funext j
  show gm *ᵥ X j = Y j
  funext i
  apply hinj
  · rw [map_mulVec, hg1]
    show (Am *ᵥ x1 j) i = y1 j i
    rw [hAm, hAx]
  · rw [map_mulVec, hg2]
    show (B *ᵥ x2 j) i = y2 j i
    rw [hB2]

end Main

end WSp

end Formalism.L2.SG.Pf.NcS.LT
