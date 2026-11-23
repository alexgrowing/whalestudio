import Mathlib
import CompanionTheory.ThickeningEstimates.LieGroupReduction.SiegelCore
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsLevi
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet CompanionTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin.LeviPt

section Abstract

variable {K : Type} [CommRing K] (c : K →+* K)

theorem cT_add {m p : Type} (M N : Matrix m p K) : cT c (M + N) = cT c M + cT c N := by
  ext i j; simp [cT]

theorem cT_sub {m p : Type} (M N : Matrix m p K) : cT c (M - N) = cT c M - cT c N := by
  ext i j; simp [cT]

theorem cT_cT (hc : ∀ x, c (c x) = x) {m p : Type} (M : Matrix m p K) : cT c (cT c M) = M := by
  ext i j; simp [cT, hc]

theorem cT_diagonal {m : Type} [DecidableEq m] (d : m → K) :
    cT c (diagonal d) = diagonal (fun i => c (d i)) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [cT]
  · simp [cT, diagonal_apply_ne _ h, diagonal_apply_ne _ (Ne.symm h)]

theorem levi_core (hc : ∀ x, c (c x) = x) {n r : ℕ} {Jh : Matrix (Fin n) (Fin n) K}
    {Xa Ya : Matrix (Fin n) (Fin r) K} {Xd Yd : Matrix (Fin r) (Fin n) K}
    (hJ : cT c Jh = Jh) (hXd : Xd = cT c Xa * Jh) (hYd : Yd = cT c Ya * Jh)
    (hxx : Xd * Xa = 0) (hyy : Yd * Ya = 0) (hxy : Xd * Ya = 1)
    (g : GL (Fin n) K) (hg : cT c (g : Matrix (Fin n) (Fin n) K) * Jh * (g : Matrix (Fin n) (Fin n) K) = Jh)
    (B : Matrix (Fin r) (Fin r) K) (hBt : B.BlockTriangular id)
    (hB : (g : Matrix (Fin n) (Fin n) K) * Xa = Xa * B)
    (L : Matrix (Fin n) (Fin n) K)
    (hL : L = Xa * diagonal (fun i => (Yd * (g : Matrix (Fin n) (Fin n) K) * Xa) i i) * Yd
      + Ya * diagonal (fun i => (Xd * (g : Matrix (Fin n) (Fin n) K) * Ya) i i) * Xd
      + (1 - Xa * Yd - Ya * Xd) * (g : Matrix (Fin n) (Fin n) K) * (1 - Xa * Yd - Ya * Xd)) :
    ∃ u : GL (Fin n) K, (u : Matrix (Fin n) (Fin n) K) = L ∧ cT c L * Jh * L = Jh ∧
      (∃ d, L * Xa = Xa * diagonal d) ∧ (∃ d', L * Ya = Ya * diagonal d') ∧
      (∃ B' : Matrix (Fin r) (Fin r) K, B'.BlockTriangular id ∧ (∀ i, B' i i = 1) ∧
        ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) * Xa = Xa * B') ∧
      ∀ z : Fin n → K, Xd *ᵥ z = 0 → ∃ a : Fin r → K,
        (((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) - 1) *ᵥ z = Xa *ᵥ a := by
  classical
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin n) (Fin n) K, M = g := ⟨_, rfl⟩
  obtain ⟨Mi, hMi⟩ : ∃ Mi : Matrix (Fin n) (Fin n) K, Mi = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    ⟨_, rfl⟩
  have hMMi : M * Mi = 1 := by rw [hM, hMi]; exact Units.mul_inv g
  have hMiM : Mi * M = 1 := by rw [hM, hMi]; exact Units.inv_mul g
  rw [← hM] at hg hB hL
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin n) (Fin n) K, P = 1 - Xa * Yd - Ya * Xd := ⟨_, rfl⟩
  rw [← hP] at hL
  have hyx : Yd * Xa = 1 := by
    have h := congrArg (cT c) hxy
    rw [Formalism.UG.cT_mul, hXd, Formalism.UG.cT_mul, hJ, cT_cT c hc, Formalism.UG.cT_one] at h
    rw [hYd, Matrix.mul_assoc]; exact h
  have hcXd : cT c Xd = Jh * Xa := by rw [hXd, Formalism.UG.cT_mul, hJ, cT_cT c hc]
  have hcYd : cT c Yd = Jh * Ya := by rw [hYd, Formalism.UG.cT_mul, hJ, cT_cT c hc]
  have exx : ∀ {k : Type} (N : Matrix (Fin r) k K), Xd * (Xa * N) = 0 := fun N => by
    rw [← Matrix.mul_assoc, hxx, Matrix.zero_mul]
  have eyy : ∀ {k : Type} (N : Matrix (Fin r) k K), Yd * (Ya * N) = 0 := fun N => by
    rw [← Matrix.mul_assoc, hyy, Matrix.zero_mul]
  have exy : ∀ {k : Type} (N : Matrix (Fin r) k K), Xd * (Ya * N) = N := fun N => by
    rw [← Matrix.mul_assoc, hxy, Matrix.one_mul]
  have eyx : ∀ {k : Type} (N : Matrix (Fin r) k K), Yd * (Xa * N) = N := fun N => by
    rw [← Matrix.mul_assoc, hyx, Matrix.one_mul]
  have hPXa : P * Xa = 0 := by
    rw [hP]; simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hyx, hxx, Matrix.mul_one,
      Matrix.mul_zero, sub_self, sub_zero]
  have hPYa : P * Ya = 0 := by
    rw [hP]; simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hyy, hxy, Matrix.mul_one,
      Matrix.mul_zero, sub_self, sub_zero]
  have hXdP : Xd * P = 0 := by
    rw [hP]; simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hxx, hxy, Matrix.zero_mul,
      Matrix.one_mul, sub_self, sub_zero]
  have hYdP : Yd * P = 0 := by
    rw [hP]; simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hyy, hyx, Matrix.zero_mul,
      Matrix.one_mul, sub_self, sub_zero]
  have hPP : P * P = P := by
    have h : P * P = P * (1 - Xa * Yd - Ya * Xd) := by rw [← hP]
    rw [h, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPXa, ← Matrix.mul_assoc, hPYa,
      Matrix.zero_mul, Matrix.zero_mul, sub_zero, sub_zero]
  have ePP : ∀ {k : Type} (N : Matrix (Fin n) k K), P * (P * N) = P * N := fun N => by
    rw [← Matrix.mul_assoc, hPP]
  have ePx : ∀ {k : Type} (N : Matrix (Fin r) k K), P * (Xa * N) = 0 := fun N => by
    rw [← Matrix.mul_assoc, hPXa, Matrix.zero_mul]
  have ePy : ∀ {k : Type} (N : Matrix (Fin r) k K), P * (Ya * N) = 0 := fun N => by
    rw [← Matrix.mul_assoc, hPYa, Matrix.zero_mul]
  have exP : ∀ {k : Type} (N : Matrix (Fin n) k K), Xd * (P * N) = 0 := fun N => by
    rw [← Matrix.mul_assoc, hXdP, Matrix.zero_mul]
  have eyP : ∀ {k : Type} (N : Matrix (Fin n) k K), Yd * (P * N) = 0 := fun N => by
    rw [← Matrix.mul_assoc, hYdP, Matrix.zero_mul]
  have hMJ : cT c M * Jh = Jh * Mi := by
    calc cT c M * Jh = cT c M * Jh * (M * Mi) := by rw [hMMi, Matrix.mul_one]
      _ = (cT c M * Jh * M) * Mi := by simp only [Matrix.mul_assoc]
      _ = Jh * Mi := by rw [hg]
  have hBX : cT c B * Xd = Xd * Mi := by
    rw [hXd, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, ← hB, Formalism.UG.cT_mul]
    simp only [Matrix.mul_assoc, hMJ]
  have hBC : cT c B * (Xd * M * Ya) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hBX, Matrix.mul_assoc Xd Mi M, hMiM, Matrix.mul_one, hxy]
  have hCB : (Xd * M * Ya) * cT c B = 1 := mul_eq_one_comm.mp hBC
  have hBiB : cT c (Xd * M * Ya) * B = 1 := by
    have h := congrArg (cT c) hBC
    rwa [Formalism.UG.cT_mul, cT_cT c hc, Formalism.UG.cT_one] at h
  have hBBi : B * cT c (Xd * M * Ya) = 1 := mul_eq_one_comm.mp hBiB
  have hBit : (cT c (Xd * M * Ya)).BlockTriangular id := by
    haveI : Invertible B := invertibleOfRightInverse B _ hBBi
    have h := Matrix.blockTriangular_inv_of_blockTriangular hBt
    rwa [Matrix.inv_eq_right_inv hBBi] at h
  have hdiag : ∀ i, c ((Xd * M * Ya) i i) * B i i = 1 := by
    intro i
    have h := congrFun (congrFun hBiB i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h
    · rw [Matrix.one_apply_eq] at h; exact h
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h' | h'
      · rw [hBit h', zero_mul]
      · rw [hBt h', mul_zero]
    · intro h'; exact absurd (Finset.mem_univ i) h'

  have hYMX : Yd * M * Xa = B := by rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hyx, Matrix.one_mul]
  rw [hYMX] at hL
  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin r) (Fin r) K, D = diagonal (fun i => B i i) := ⟨_, rfl⟩
  obtain ⟨D', hD'⟩ : ∃ D' : Matrix (Fin r) (Fin r) K, D' = diagonal (fun i => (Xd * M * Ya) i i) := ⟨_, rfl⟩
  obtain ⟨Ds, hDs⟩ : ∃ Ds : Matrix (Fin r) (Fin r) K, Ds = diagonal (fun i => c (B i i)) := ⟨_, rfl⟩
  obtain ⟨D's, hD's⟩ : ∃ D's : Matrix (Fin r) (Fin r) K, D's = diagonal (fun i => c ((Xd * M * Ya) i i)) :=
    ⟨_, rfl⟩
  rw [← hD, ← hD'] at hL
  have hcD : cT c D = Ds := by rw [hD, hDs, cT_diagonal]
  have hcD' : cT c D' = D's := by rw [hD', hD's, cT_diagonal]
  have eDsD' : ∀ {k : Type} (N : Matrix (Fin r) k K), Ds * (D' * N) = N := fun N => by
    rw [← Matrix.mul_assoc, hDs, hD', diagonal_mul_diagonal]
    convert Matrix.one_mul N
    rw [← diagonal_one]; congr 1; funext i
    have h := congrArg c (hdiag i)
    rw [map_mul, hc, map_one, mul_comm] at h
    exact h
  have eD'sD : ∀ {k : Type} (N : Matrix (Fin r) k K), D's * (D * N) = N := fun N => by
    rw [← Matrix.mul_assoc, hD's, hD, diagonal_mul_diagonal]
    convert Matrix.one_mul N
    rw [← diagonal_one]; congr 1; funext i
    exact hdiag i
  have hXdMP : Xd * (M * P) = 0 := by
    have h1 : cT c B * (Xd * (M * P)) = 0 := by
      rw [← Matrix.mul_assoc, hBX, Matrix.mul_assoc, ← Matrix.mul_assoc Mi, hMiM, Matrix.one_mul, hXdP]
    calc Xd * (M * P) = (Xd * M * Ya * cT c B) * (Xd * (M * P)) := by rw [hCB, Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc _ (cT c B), h1, Matrix.mul_zero]
  have hMiXa : Mi * Xa = Xa * cT c (Xd * M * Ya) := by
    calc Mi * Xa = Mi * Xa * (B * cT c (Xd * M * Ya)) := by rw [hBBi, Matrix.mul_one]
      _ = Mi * (M * Xa) * cT c (Xd * M * Ya) := by rw [hB]; simp only [Matrix.mul_assoc]
      _ = Xa * cT c (Xd * M * Ya) := by rw [← Matrix.mul_assoc Mi, hMiM, Matrix.one_mul]
  have h1 : P * (M * P) = M * P - Xa * (Yd * (M * P)) := by
    rw [show P * (M * P) = (1 - Xa * Yd - Ya * Xd) * (M * P) by rw [← hP], Matrix.sub_mul, Matrix.sub_mul,
      Matrix.one_mul, Matrix.mul_assoc Xa, Matrix.mul_assoc Ya, hXdMP, Matrix.mul_zero, sub_zero]
  have hPMiPMP : P * (Mi * (P * (M * P))) = P := by
    rw [h1, Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc Mi M, hMiM, Matrix.one_mul, hPP,
      ← Matrix.mul_assoc Mi Xa, hMiXa, Matrix.mul_assoc Xa, ePx, sub_zero]
  obtain ⟨m', hm'⟩ : ∃ m' : Matrix (Fin n) (Fin n) K, m' = Ya * (Ds * Xd) + Xa * (D's * Yd) + P * (Mi * P) :=
    ⟨_, rfl⟩
  have hm'L : m' * L = 1 := by
    clear * - hm' hL exx eyy exy eyx exP eyP ePx ePy ePP eDsD' eD'sD hPMiPMP hP
    rw [hm', hL]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, exx, eyy, exy, eyx, exP, eyP, ePx, ePy,
      ePP, eDsD', eD'sD, hPMiPMP, Matrix.mul_zero, add_zero, zero_add]
    rw [hP]; abel
  have hLm' : L * m' = 1 := mul_eq_one_comm.mp hm'L
  have hPJ : cT c P * Jh = Jh * P := by
    rw [hP, cT_sub, cT_sub, Formalism.UG.cT_one, Formalism.UG.cT_mul, Formalism.UG.cT_mul, hcYd, hcXd]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, hXd.symm,
      hYd.symm]
    abel
  have ePJ : ∀ (N : Matrix (Fin n) (Fin n) K), cT c P * (Jh * N) = Jh * (P * N) := fun N => by
    rw [← Matrix.mul_assoc, hPJ, Matrix.mul_assoc]
  have eMJ : ∀ (N : Matrix (Fin n) (Fin n) K), cT c M * (Jh * N) = Jh * (Mi * N) := fun N => by
    rw [← Matrix.mul_assoc, hMJ, Matrix.mul_assoc]
  have hcL : cT c L * Jh = Jh * m' := by
    rw [hL, hm']
    simp only [cT_add, Formalism.UG.cT_mul, hcXd, hcYd, hcD, hcD', Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc,
      hXd.symm, hYd.symm, hPJ, eMJ, ePJ]
  have hunit : cT c L * Jh * L = Jh := by
    rw [hcL, Matrix.mul_assoc, hm'L, Matrix.mul_one]
  have hLXa : L * Xa = Xa * D := by
    rw [hL]
    simp only [Matrix.add_mul, Matrix.mul_assoc, hyx, hxx, hPXa, Matrix.mul_one, Matrix.mul_zero, add_zero]
  have hLYa : L * Ya = Ya * D' := by
    rw [hL]
    simp only [Matrix.add_mul, Matrix.mul_assoc, hyy, hxy, hPYa, Matrix.mul_one, Matrix.mul_zero, add_zero,
      zero_add]
  have em'Xa : ∀ {k : Type} (N : Matrix (Fin r) k K), m' * (Xa * N) = Xa * (D's * N) := fun N => by
    rw [hm']
    simp only [Matrix.add_mul, Matrix.mul_assoc, exx, eyx, ePx, Matrix.mul_zero, add_zero, zero_add]
  have hLP : L * P = P * (M * P) := by
    rw [hL]
    simp only [Matrix.add_mul, Matrix.mul_assoc, hYdP, hXdP, hPP, Matrix.mul_zero, zero_add]
  refine ⟨⟨L, m', hLm', hm'L⟩, rfl, hunit, ⟨_, hD ▸ hLXa⟩, ⟨_, hD' ▸ hLYa⟩, ?_, ?_⟩
  · refine ⟨D's * B, ?_, ?_, ?_⟩
    · intro i j h
      rw [hD's, diagonal_mul, hBt h, mul_zero]
    · intro i
      rw [hD's, diagonal_mul]
      exact hdiag i
    · change m' * (g : Matrix (Fin n) (Fin n) K) * Xa = Xa * (D's * B)
      rw [← hM, Matrix.mul_assoc, hB, em'Xa]
  · intro z hz
    refine ⟨(D's * B * Yd + D's * (Yd * (M * P)) - Yd) *ᵥ z, ?_⟩
    change (m' * (g : Matrix (Fin n) (Fin n) K) - 1) *ᵥ z = _
    rw [← hM]
    have hz' : z = (Xa * Yd + P) *ᵥ z := by
      rw [show Xa * Yd + P = 1 - Ya * Xd by rw [hP]; abel, Matrix.sub_mulVec, Matrix.one_mulVec,
        ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero, sub_zero]
    have h2 : m' * (M * P) = Xa * (D's * (Yd * (M * P))) + P := by
      conv_lhs => rw [show M * P = Xa * (Yd * (M * P)) + P * (M * P) by rw [h1]; abel]
      rw [Matrix.mul_add, em'Xa, ← hLP, ← Matrix.mul_assoc m' L P, hm'L, Matrix.one_mul]
    have key : (m' * M - 1) * (Xa * Yd + P) = Xa * (D's * B * Yd + D's * (Yd * (M * P)) - Yd) := by
      calc (m' * M - 1) * (Xa * Yd + P) = m' * (M * Xa) * Yd + m' * (M * P) - Xa * Yd - P := by
            simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_assoc]; abel
        _ = Xa * (D's * B) * Yd + (Xa * (D's * (Yd * (M * P))) + P) - Xa * Yd - P := by rw [hB, em'Xa, h2]
        _ = Xa * (D's * B * Yd + D's * (Yd * (M * P)) - Yd) := by
            simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_assoc]; abel
    conv_lhs => rw [hz']
    rw [Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec]

end Abstract

section Place

theorem sigma_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨_, _, _, hτ⟩ := h
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  apply w.embedding.injective
  rw [hτ, hτ, star_star]

theorem sigR_invol {F E : Type} [Field F] [Field E] [Algebra F E] (A : Type) [CommRing A] [Algebra F A]
    {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (x : A ⊗[F] E) : sigR A σ (sigR A σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, h]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem sigR_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (A : Type) [CommRing A] [Algebra F A]
    (σ : E →ₐ[F] E) (e : E) : sigR A σ (inclR A e) = inclR A (σ e) := by
  simp [sigR, inclR]

theorem cT_map_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (A : Type) [CommRing A] [Algebra F A]
    (σ : E →ₐ[F] E) {a b : ℕ} (N : Matrix (Fin a) (Fin b) E) :
    cT (sigR A σ) (N.map (inclR (F := F) A)) = (cT (σ : E →+* E) N).map (inclR (F := F) A) := by
  ext i j; simp [cT, sigR_inclR]

theorem exists_levi : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (A : Type) [CommRing A] [Algebra F A] [TopologicalSpace A] (p : HA A σ J) (B : Matrix (Fin r) (Fin r) (A ⊗[F] E)), B.BlockTriangular id → (matHom A σ J p).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * B → ∃ m : HA A σ J, (matHom A σ J m).1 = leviMat σ J A X Y (matHom A σ J p).1 ∧ (∃ d : Fin r → A ⊗[F] E, (matHom A σ J m).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * diagonal d) ∧ (∃ d' : Fin r → A ⊗[F] E, (matHom A σ J m).1 * Y.map (inclR (F := F) A) = Y.map (inclR (F := F) A) * diagonal d') ∧ (∃ B' : Matrix (Fin r) (Fin r) (A ⊗[F] E), B'.BlockTriangular id ∧ (∀ i, B' i i = 1) ∧ (matHom A σ J (m⁻¹ * p)).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * B') ∧ ∀ z : Fin n → A ⊗[F] E, ((cT (σ : E →+* E) X * J).map (inclR (F := F) A)) *ᵥ z = 0 → ∃ a : Fin r → A ⊗[F] E, ((matHom A σ J (m⁻¹ * p)).1 - 1) *ᵥ z = X.map (inclR (F := F) A) *ᵥ a :=
  _root_.UpperTheory.Reformulated.B.Gka3.exists_levi

end Place

end GlobalTheory.CompanionTheory.KFin.LeviPt
