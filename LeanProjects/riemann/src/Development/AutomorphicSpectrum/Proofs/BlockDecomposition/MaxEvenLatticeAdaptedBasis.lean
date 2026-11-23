import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat

set_option linter.unusedSectionVars false

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin.GoodLocal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

theorem sigR_inclR (A : Type) [CommRing A] [Algebra F A] (e : E) :
    sigR A σ (inclR (F := F) A e) = inclR (F := F) A (σ e) := by
  simp [sigR, inclR]

theorem dual_mulVec (v : HeightOneSpectrum (𝓞 F)) (A : Matrix (Fin n) (Fin r) E)
    (z : Fin n → Fv F v ⊗[F] E) (i : Fin r) :
    ((cT (σ : E →+* E) A * J).map (inclR (F := F) (Fv F v)) *ᵥ z) i
      = hR (Fv F v) σ J (colV v A i) z := by
  simp only [hR, Formalism.UG.hform, colV, JR, sigR_inclR, mulVec, dotProduct, map_apply, Matrix.mul_apply,
    cT, transpose_apply, map_sum, map_mul, Finset.sum_mul, RingHom.coe_coe]
  rw [Finset.sum_comm]

theorem col_mulVec (v : HeightOneSpectrum (𝓞 F)) (A : Matrix (Fin n) (Fin r) E)
    (w : Fin r → Fv F v ⊗[F] E) :
    A.map (inclR (F := F) (Fv F v)) *ᵥ w = ∑ i, w i • colV v A i := by
  ext a
  simp [mulVec, dotProduct, colV, Finset.sum_apply, mul_comm]

theorem hR_colV (v : HeightOneSpectrum (𝓞 F)) (A : Matrix (Fin n) (Fin r) E)
    (B : Matrix (Fin n) (Fin r) E) (i j : Fin r) :
    hR (Fv F v) σ J (colV v A i) (colV v B j)
      = inclR (F := F) (Fv F v) ((cT (σ : E →+* E) A * J * B) i j) := by
  rw [← dual_mulVec]
  conv_rhs => rw [Matrix.mul_apply]
  simp only [mulVec, dotProduct, map_apply, colV, map_sum, map_mul]

theorem sigma_sigma (hCM : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hCM.2.2.2 τ, hCM.2.2.2 τ, star_star]

theorem cT_mul_rect (s : E →+* E) {a b c : Type} [Fintype b] (P : Matrix a b E) (Q : Matrix b c E) :
    cT s (P * Q) = cT s Q * cT s P := by
  simp [cT, Matrix.map_mul, transpose_mul]

theorem gram_yx (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin r) E}
    (hW : IsWittFrame σ J X Y) : cT (σ : E →+* E) Y * J * X = 1 := by
  have hcT : cT (σ : E →+* E) J = J := by
    ext i j
    exact hJ.1 i j
  have hcc : cT (σ : E →+* E) (cT (σ : E →+* E) X) = X := by
    ext i j
    exact sigma_sigma hCM _
  have h1 : cT (σ : E →+* E) (1 : Matrix (Fin r) (Fin r) E) = 1 := by
    ext i j
    simp [cT, Matrix.one_apply, eq_comm]
  have := congrArg (cT (σ : E →+* E)) hW.xy
  rw [cT_mul_rect, cT_mul_rect, hcT, hcc, h1, ← Matrix.mul_assoc] at this
  exact this

def projP (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (X Y : Matrix (Fin n) (Fin r) E) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
  1 - X.map (inclR (F := F) (Fv F v)) * (cT (σ : E →+* E) Y * J).map (inclR (F := F) (Fv F v))
    - Y.map (inclR (F := F) (Fv F v)) * (cT (σ : E →+* E) X * J).map (inclR (F := F) (Fv F v))

theorem projP_mulVec (v : HeightOneSpectrum (𝓞 F)) (X Y : Matrix (Fin n) (Fin r) E)
    (z : Fin n → Fv F v ⊗[F] E) :
    projP v σ J X Y *ᵥ z = z - ∑ i, hR (Fv F v) σ J (colV v Y i) z • colV v X i
      - ∑ i, hR (Fv F v) σ J (colV v X i) z • colV v Y i := by
  have hb : ∀ A B : Matrix (Fin n) (Fin r) E,
      (A.map (inclR (F := F) (Fv F v)) * (cT (σ : E →+* E) B * J).map (inclR (F := F) (Fv F v))) *ᵥ z
        = ∑ i, hR (Fv F v) σ J (colV v B i) z • colV v A i := by
    intro A B
    rw [← mulVec_mulVec, col_mulVec]
    simp only [dual_mulVec]
  simp only [projP, sub_mulVec, one_mulVec, hb]

theorem leviMat_mulVec (v : HeightOneSpectrum (𝓞 F)) (X Y : Matrix (Fin n) (Fin r) E)
    (M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (z : Fin n → Fv F v ⊗[F] E) :
    leviMat σ J (Fv F v) X Y M *ᵥ z =
      ∑ i, (hR (Fv F v) σ J (colV v Y i) (M *ᵥ colV v X i) * hR (Fv F v) σ J (colV v Y i) z) • colV v X i
      + ∑ i, (hR (Fv F v) σ J (colV v X i) (M *ᵥ colV v Y i) * hR (Fv F v) σ J (colV v X i) z) • colV v Y i
      + projP v σ J X Y *ᵥ (M *ᵥ (projP v σ J X Y *ᵥ z)) := by
  have hd : ∀ (A B : Matrix (Fin n) (Fin r) E) (i : Fin r),
      ((cT (σ : E →+* E) A * J).map (inclR (F := F) (Fv F v)) * M * B.map (inclR (F := F) (Fv F v))) i i
        = hR (Fv F v) σ J (colV v A i) (M *ᵥ colV v B i) := by
    intro A B i
    rw [← dual_mulVec, Matrix.mul_assoc]
    rfl
  have hmv : ∀ (A B : Matrix (Fin n) (Fin r) E) (d : Fin r → Fv F v ⊗[F] E),
      (A.map (inclR (F := F) (Fv F v)) * diagonal d * (cT (σ : E →+* E) B * J).map (inclR (F := F) (Fv F v))) *ᵥ z
        = ∑ i, (d i * hR (Fv F v) σ J (colV v B i) z) • colV v A i := by
    intro A B d
    rw [← mulVec_mulVec, ← mulVec_mulVec, col_mulVec]
    simp only [mulVec_diagonal, dual_mulVec]
  unfold leviMat
  simp only [add_mulVec]
  rw [hmv, hmv]
  simp only [hd]
  simp only [mulVec_mulVec, projP, Matrix.mul_assoc]

theorem hR_isom {v : HeightOneSpectrum (𝓞 F)} (g : GLoc σ J v) (a b : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J ((matHom _ σ J g).1 *ᵥ a) ((matHom _ σ J g).1 *ᵥ b) = hR (Fv F v) σ J a b := by
  have hg : cT (sigR (Fv F v) σ) (matHom _ σ J g).1 * JR (Fv F v) J * (matHom _ σ J g).1 = JR (Fv F v) J := g.2
  simp only [hR]
  rw [Formalism.UG.P.hform_mulVec, hg]

theorem levi_mem_stabLat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E)), IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) Λ → IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) Λ → ∀ (p m : GLoc σ J v), p ∈ stabLat σ J Λ → ∀ B : Matrix (Fin r) (Fin r) (Fv F v ⊗[F] E), B.BlockTriangular id → (matHom _ σ J p).1 * X.map (inclR (F := F) (Fv F v)) = X.map (inclR (F := F) (Fv F v)) * B → (matHom _ σ J m).1 = leviMat σ J (Fv F v) X Y (matHom _ σ J p).1 → m ∈ stabLat σ J Λ := by
  intro F E _ _ _ _ _ σ n J r X Y hCM hJ hW v Λ hΛ hA p m hp B _ _ hm
  obtain ⟨-, ⟨hint, heven⟩, hmax⟩ := hΛ
  have hxx : ∀ i j, hR (Fv F v) σ J (colV v X i) (colV v X j) = 0 := fun i j => by
    rw [hR_colV, hW.xx]; simp
  have hyy : ∀ i j, hR (Fv F v) σ J (colV v Y i) (colV v Y j) = 0 := fun i j => by
    rw [hR_colV, hW.yy]; simp
  have hxy : ∀ i j, hR (Fv F v) σ J (colV v X i) (colV v Y j) = if i = j then 1 else 0 := fun i j => by
    rw [hR_colV, hW.xy, Matrix.one_apply]; split_ifs <;> simp
  have hyx : ∀ i j, hR (Fv F v) σ J (colV v Y i) (colV v X j) = if i = j then 1 else 0 := fun i j => by
    rw [hR_colV, gram_yx hCM hJ hW, Matrix.one_apply]; split_ifs <;> simp
  have hδ : ∀ i j : Fin r, ((if i = j then 1 else 0 : Fv F v ⊗[F] E)) ∈ intLoc F E v := fun i j => by
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hx : ∀ i, colV v X i ∈ Λ := fun i => by
    refine (hA _).2 ⟨fun j => ?_, fun j => ?_, ?_⟩
    · rw [hxx]; exact zero_mem _
    · rw [hyx]; exact hδ _ _
    · simp [hxx, hyx]
  have hy : ∀ i, colV v Y i ∈ Λ := fun i => by
    refine (hA _).2 ⟨fun j => ?_, fun j => ?_, ?_⟩
    · rw [hxy]; exact hδ _ _
    · rw [hyy]; exact zero_mem _
    · simp [hxy, hyy]
  have hP : ∀ z ∈ Λ, projP v σ J X Y *ᵥ z ∈ Λ := fun z hz => by
    rw [projP_mulVec]
    exact ((hA z).1 hz).2.2
  have hsm : ∀ a ∈ intLoc F E v, ∀ z ∈ Λ, a • z ∈ Λ := fun a ha z hz => Λ.smul_mem ⟨a, ha⟩ hz
  have hpz : ∀ z ∈ Λ, (matHom _ σ J p).1 *ᵥ z ∈ Λ := fun z hz => (hp z).1 hz
  have hsub : ∀ z ∈ Λ, (matHom _ σ J m).1 *ᵥ z ∈ Λ := fun z hz => by
    rw [hm, leviMat_mulVec]
    refine add_mem (add_mem (sum_mem fun i _ => ?_) (sum_mem fun i _ => ?_)) (hP _ (hpz _ (hP z hz)))
    · exact hsm _ (mul_mem (hint _ (hy i) _ (hpz _ (hx i))) (hint _ (hy i) _ hz)) _ (hx i)
    · exact hsm _ (mul_mem (hint _ (hx i) _ (hpz _ (hy i))) (hint _ (hx i) _ hz)) _ (hy i)
  let L' : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E) :=
    { carrier := {z | (matHom _ σ J m).1 *ᵥ z ∈ Λ}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, mulVec_add] at ha hb ⊢
        exact add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun a z hz => by
        have e : (matHom _ σ J m).1 *ᵥ (a • z) = a • ((matHom _ σ J m).1 *ᵥ z) := by
          change (matHom _ σ J m).1 *ᵥ ((a : Fv F v ⊗[F] E) • z) = (a : Fv F v ⊗[F] E) • ((matHom _ σ J m).1 *ᵥ z)
          rw [mulVec_smul]
        change (matHom _ σ J m).1 *ᵥ (a • z) ∈ Λ
        rw [e]
        exact Λ.smul_mem a hz }
  have hL' : ∀ z, z ∈ L' ↔ (matHom _ σ J m).1 *ᵥ z ∈ Λ := fun z => Iff.rfl
  have hev : IsEvenInt (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) L' := by
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · rw [← hR_isom m a b]
      exact hint _ ha _ hb
    · rw [← hR_isom m a a]
      exact heven _ ha
  have hle : L' ≤ Λ := hmax L' hev hsub
  exact fun y => ⟨hsub y, fun h => hle h⟩

end GlobalTheory.CompanionTheory.KFin.GoodLocal

end
