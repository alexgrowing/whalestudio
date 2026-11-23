import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

noncomputable section

theorem reads_of_perC {D : D7} {r g : ℕ} (θ : InfFam D) (V W : HSp D) (hr : W.rank = r) (X : Data D.host.E r)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x x' : Frame X.Ψ r)
    (M : Matrix (Fin g) (Fin g) ℂ) (hM : IsUnit M.det)
    (h : ∀ u, (fun j => perC X x' u (idx j)) = M *ᵥ fun j => perC X x u (idx j))
    (f : WO V W → ℂ) (φ : TF V.rank g) (hf : Reads θ V W hr X bas idx f φ x) :
    Reads θ V W hr X bas idx f ((M.det ^ (V.rank / 2)) • φ) x' := by
  have hP : ∀ s, perMat X bas idx s x' = M * perMat X bas idx s x := by
    intro s
    ext i k
    have := congrFun (h fun τ => Data.emb τ.1 (bas (Pi.single (s k) 1))) i
    exact this
  have hH : hMat X bas idx x' = hMat X bas idx x * M⁻¹ := by
    rw [hMat, hP, Matrix.mul_inv_rev, hMat]
  have hT : tauMat X bas idx x' = tauMat X bas idx x := by
    rw [tauMat, hH, hP, Matrix.mul_assoc, ← Matrix.mul_assoc M⁻¹, nonsing_inv_mul _ hM, Matrix.one_mul, tauMat]
  have hI : imInv X bas idx x' = imInv X bas idx x := by rw [imInv, imInv, hT]
  obtain ⟨⟨R, hR, h1, h2⟩, h3⟩ := hf
  refine ⟨⟨R, hR, fun y hy => h1 y fun e => hy (by simp [e]), fun y z hz => by simp [h2 y z hz]⟩, fun w hw => ?_⟩
  have hz : ∀ b, hMat X bas idx x' *ᵥ zOf θ V W hr X idx x' w b = hMat X bas idx x *ᵥ zOf θ V W hr X idx x w b := by
    intro b
    have : zOf θ V W hr X idx x' w b = M *ᵥ zOf θ V W hr X idx x w b := h _
    rw [this, hH, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hM, Matrix.mul_one]
  have hS : ∀ (c : ℂ) t z, thS (c • φ) t z = c * thS φ t z := by
    intro c t z
    simp only [thS, Pi.smul_apply, smul_eq_mul, mul_assoc, tsum_mul_left]
  rw [h3 w hw]
  simp only [hx, thA, hz, hT, hI, hS]
  have hd : (hMat X bas idx x).det = (hMat X bas idx x').det * M.det := by
    rw [hH, ← det_mul, Matrix.mul_assoc, nonsing_inv_mul _ hM, Matrix.mul_one]
  rw [hd, mul_pow]
  ring

theorem det_tr_inv_block {r : ℕ} (P Q b : Matrix (Fin r) (Fin r) ℂ) (hb : IsUnit b.det) (hPQ : P + Q = 1)
    (hPP : P * P = P) (hc : b * P = P * b) (hs : Pᵀ = P) :
    (P * bᵀ + Q * b⁻¹).det ≠ 0 ∧ (P * bᵀ + Q * b⁻¹).det = (P * b + Q).det / (Q * b + P).det := by
  have hQ : Q = 1 - P := by rw [← hPQ]; abel
  have h1 : b * b⁻¹ = 1 := mul_nonsing_inv _ hb
  have h2 : b⁻¹ * b = 1 := nonsing_inv_mul _ hb
  generalize b⁻¹ = c at h1 h2 ⊢
  have hc' : c * P = P * c := by
    calc c * P = c * P * (b * c) := by rw [h1, Matrix.mul_one]
      _ = c * (P * b) * c := by simp only [Matrix.mul_assoc]
      _ = P * c := by rw [← hc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hct : bᵀ * P = P * bᵀ := by
    have := congrArg transpose hc
    rw [transpose_mul, transpose_mul, hs] at this
    exact this.symm
  have hPP' : ∀ y : Matrix (Fin r) (Fin r) ℂ, P * (P * y) = P * y := fun y => by rw [← Matrix.mul_assoc, hPP]
  have e1 : (Q * c + P) * (Q * b + P) = 1 := by
    have : c * (P * b) = P := by rw [← hc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    subst hQ
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc, h2, this, hc', hPP, hPP']
    abel
  have e2 : (P * c + Q) * (P * b + Q) = 1 := by
    have : c * (P * b) = P := by rw [← hc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    subst hQ
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc, h2, this, hc', hPP, hPP']
    abel
  have e3 : P * bᵀ + Q * c = (P * b + Q)ᵀ * (Q * c + P) := by
    have : ∀ y : Matrix (Fin r) (Fin r) ℂ, bᵀ * (P * y) = P * (bᵀ * y) := fun y => by
      rw [← Matrix.mul_assoc, hct, Matrix.mul_assoc]
    subst hQ
    simp only [transpose_add, transpose_mul, transpose_sub, transpose_one, hs,
      Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc, this, hct, hPP, hPP']
    abel
  have d1 := congrArg det e1
  have d2 := congrArg det e2
  rw [det_mul, det_one] at d1 d2
  rw [e3, det_mul, det_transpose]
  refine ⟨mul_ne_zero (right_ne_zero_of_mul_eq_one d2) (left_ne_zero_of_mul_eq_one d1), ?_⟩
  rw [div_eq_mul_inv, eq_inv_of_mul_eq_one_left d1]

theorem isUnit_det_of_isONFr {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x : Frame X.Ψ r) (h : IsONFr X x) (τ : X.Ψ) : IsUnit (mat x τ).det := by
  have e : FD.gram τ.1 X.Gm (mat x τ) = (mat x τ)ᵀ * (X.Gm.map τ.1 * (mat x τ).map conj) := by
    ext a b
    simp only [FD.gram, hermC, FD.col, of_apply, mul_apply, transpose_apply, map_apply, Finset.mul_sum, mul_assoc]
  have d := congrArg det (e.symm.trans (h τ))
  rw [det_mul, det_transpose, sgnM, det_diagonal] at d
  refine isUnit_iff_ne_zero.2 (left_ne_zero_of_mul (d ▸ Finset.prod_ne_zero_iff.2 fun a _ => ?_))
  unfold sgn
  split_ifs <;> simp

def prFst (r p : ℕ) : Matrix (Fin r) (Fin r) ℂ := diagonal fun a => if (a : ℕ) < p then 1 else 0

theorem prFst_block_zero {r p : ℕ} {b : Matrix (Fin r) (Fin r) ℂ} (h : b * prFst r p = prFst r p * b) {a c : Fin r}
    (hac : ¬ ((a : ℕ) < p ↔ (c : ℕ) < p)) : b a c = 0 := by
  have := congrFun (congrFun h a) c
  simp only [prFst, mul_diagonal, diagonal_mul] at this
  by_cases ha : (a : ℕ) < p <;> by_cases hc : (c : ℕ) < p <;> simp_all

theorem perC_block {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x x' : Frame X.Ψ r) (τ : X.Ψ) (b : Matrix (Fin r) (Fin r) ℂ) (hb : IsUnit b.det)
    (hx' : mat x' τ = mat x τ * b) (hc : b * prFst r X.p0 = prFst r X.p0 * b) (u : X.Ψ → Fin r → ℂ) (a : Fin r) :
    perC X x' u (τ, a) = ∑ c, (prFst r X.p0 * bᵀ + (1 - prFst r X.p0) * b⁻¹) a c * perC X x u (τ, c) := by
  have hc' : b⁻¹ * prFst r X.p0 = prFst r X.p0 * b⁻¹ := by
    calc b⁻¹ * prFst r X.p0 = b⁻¹ * prFst r X.p0 * (b * b⁻¹) := by rw [mul_nonsing_inv _ hb, Matrix.mul_one]
      _ = b⁻¹ * (prFst r X.p0 * b) * b⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [← hc, ← Matrix.mul_assoc, nonsing_inv_mul _ hb, Matrix.one_mul]
  have hN : ∀ c, (prFst r X.p0 * bᵀ + (1 - prFst r X.p0) * b⁻¹) a c = if (a : ℕ) < X.p0 then b c a else b⁻¹ a c := by
    intro c
    simp only [Matrix.sub_mul, Matrix.one_mul, prFst, Matrix.add_apply, Matrix.sub_apply, diagonal_mul, transpose_apply]
    split_ifs <;> simp
  simp only [hN, perC, hx']
  by_cases ha : (a : ℕ) < X.p0
  · simp only [ha, if_true]
    have : hermC τ.1 X.Gm (FD.col (mat x τ * b) a) (u τ) =
        ∑ c, b c a * hermC τ.1 X.Gm (FD.col (mat x τ) c) (u τ) := by
      simp only [hermC, FD.col, mul_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [this]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc0 : (c : ℕ) < X.p0
    · simp only [hc0, if_true]
    · rw [prFst_block_zero hc (by tauto), zero_mul, zero_mul]
  · simp only [ha, if_false]
    rw [Matrix.mul_inv_rev, ← mulVec_mulVec]
    change ∑ c, b⁻¹ a c * _ = _
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc0 : (c : ℕ) < X.p0
    · rw [prFst_block_zero hc' (by tauto), zero_mul, zero_mul]
    · simp only [hc0, if_false]

theorem sgnM_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) :
    sgnM X = (2 : ℂ) • prFst r X.p0 - 1 := by
  ext a c
  by_cases h : a = c
  · subst h
    simp only [sgnM, prFst, sgn, diagonal_apply_eq, Matrix.sub_apply, Matrix.smul_apply, one_apply_eq]
    split_ifs <;> norm_num
  · simp [sgnM, prFst, h]

theorem block_of_inv {r : ℕ} (P x k s : Matrix (Fin r) (Fin r) ℂ) (hx : IsUnit x.det)
    (h1 : s * x = -(x * ((2 : ℂ) • P - 1))) (h2 : s * (k * x) = -(k * x * ((2 : ℂ) • P - 1))) :
    (x⁻¹ * (k * x)) * P = P * (x⁻¹ * (k * x)) ∧
      ((1 / 2 : ℂ) • (1 - s) * k + (1 / 2 : ℂ) • (1 + s)).det = (P * (x⁻¹ * (k * x)) + (1 - P)).det ∧
      ((1 / 2 : ℂ) • (1 + s) * k + (1 / 2 : ℂ) • (1 - s)).det = ((1 - P) * (x⁻¹ * (k * x)) + P).det := by
  have i1 : x * x⁻¹ = 1 := mul_nonsing_inv _ hx
  have i2 : x⁻¹ * x = 1 := nonsing_inv_mul _ hx
  generalize x⁻¹ = y at i1 i2 ⊢
  have i2' : ∀ z : Matrix (Fin r) (Fin r) ℂ, y * (x * z) = z := fun z => by rw [← Matrix.mul_assoc, i2, Matrix.one_mul]
  have hs : s = 1 - (2 : ℂ) • (x * (P * y)) := by
    calc s = s * x * y := by rw [Matrix.mul_assoc, i1, Matrix.mul_one]
      _ = _ := by
        rw [h1]
        simp only [Matrix.neg_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
          Matrix.mul_assoc, i1, neg_sub]
  have hconj : ∀ A : Matrix (Fin r) (Fin r) ℂ, A.det = (y * (A * x)).det := by
    intro A
    rw [det_mul, det_mul, mul_comm A.det, ← mul_assoc, ← det_mul, i2, det_one, one_mul]
  have a1 : (1 / 2 : ℂ) • (1 - s) = x * (P * y) := by rw [hs]; module
  have a2 : (1 / 2 : ℂ) • (1 + s) = 1 - x * (P * y) := by rw [hs]; module
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (fun z => y * z) h2
    simp only [hs, Matrix.mul_neg, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc, i2', neg_sub, sub_right_inj] at this
    simpa only [Matrix.mul_assoc] using (smul_right_injective _ (two_ne_zero (α := ℂ)) this).symm
  · rw [a1, a2, hconj]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc, i2', i2]
  · rw [a1, a2, hconj]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc, i2', i2]

theorem reads_two_frames : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (x x' : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsONFr X x' → IsInvOf W hr X x s → IsInvOf W hr X x' s → ∀ k : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ, (∀ (ρ : D.what₂.Tau) (τ : X.Ψ), τ.1 = tauE D ρ → mat x' τ = Matrix.reindex (finCongr hr) (finCongr hr) (k ρ) * mat x τ) → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), Reads θ V W hr X bas idx f φ x → Reads θ V W hr X bas idx f ((∏ ρ, (((1 / 2 : ℂ) • (1 - s ρ) * k ρ + (1 / 2 : ℂ) • (1 + s ρ)).det / ((1 / 2 : ℂ) • (1 + s ρ) * k ρ + (1 / 2 : ℂ) • (1 - s ρ)).det) ^ (V.rank / 2)) • φ) x' := by
  intro D ψ θ V W r g hr X bas idx _ _ _ _ hmod _ x x' s hx hx' hs hs' k hk f φ hf
  subst hr
  have hinj : Function.Injective (tauE D) := fun _ _ h =>
    D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))
  let t : D.what₂.Tau → X.Ψ := fun ρ => ⟨tauE D ρ, (hmod.psi _).2 ⟨ρ, rfl⟩⟩
  have ht : Function.Bijective t := ⟨fun a b h => hinj (congrArg Subtype.val h), fun τ => by
    obtain ⟨ρ, h⟩ := (hmod.psi τ.1).1 τ.2
    exact ⟨ρ, Subtype.ext h.symm⟩⟩
  have hu := isUnit_det_of_isONFr X x hx
  have hu' := isUnit_det_of_isONFr X x' hx'
  let b : X.Ψ → Matrix (Fin W.rank) (Fin W.rank) ℂ := fun τ => (mat x τ)⁻¹ * mat x' τ
  have hb : ∀ τ, IsUnit (b τ).det := fun τ => by
    rw [det_mul]; exact (isUnit_nonsing_inv_det _ (hu τ)).mul (hu' τ)
  have hxb : ∀ τ, mat x' τ = mat x τ * b τ := fun τ => by
    rw [← Matrix.mul_assoc, mul_nonsing_inv _ (hu τ), Matrix.one_mul]
  set P := prFst W.rank X.p0 with hP
  have key : ∀ ρ, b (t ρ) * P = P * b (t ρ) ∧
      ((1 / 2 : ℂ) • (1 - s ρ) * k ρ + (1 / 2 : ℂ) • (1 + s ρ)).det = (P * b (t ρ) + (1 - P)).det ∧
      ((1 / 2 : ℂ) • (1 + s ρ) * k ρ + (1 / 2 : ℂ) • (1 - s ρ)).det = ((1 - P) * b (t ρ) + P).det := by
    intro ρ
    have e0 : mat x' (t ρ) = k ρ * mat x (t ρ) := hk ρ (t ρ) rfl
    have e1 : s ρ * mat x (t ρ) = -(mat x (t ρ) * sgnM X) := hs ρ (t ρ) rfl
    have e2 : s ρ * mat x' (t ρ) = -(mat x' (t ρ) * sgnM X) := hs' ρ (t ρ) rfl
    rw [sgnM_eq] at e1 e2
    rw [e0] at e2
    have := block_of_inv P _ _ _ (hu _) e1 e2
    rw [← e0] at this
    exact this
  have hc : ∀ τ, b τ * P = P * b τ := fun τ => by
    obtain ⟨ρ, rfl⟩ := ht.2 τ
    exact (key ρ).1
  let N : X.Ψ → Matrix (Fin W.rank) (Fin W.rank) ℂ := fun τ => P * (b τ)ᵀ + (1 - P) * (b τ)⁻¹
  have hN : ∀ τ, (N τ).det ≠ 0 ∧ (N τ).det = (P * b τ + (1 - P)).det / ((1 - P) * b τ + P).det := fun τ =>
    det_tr_inv_block P (1 - P) (b τ) (hb τ) (by abel) (by
      rw [hP, prFst, diagonal_mul_diagonal]; congr 1; funext a; split_ifs <;> simp) (hc τ) (by
      rw [hP, prFst, diagonal_transpose])
  let e : Fin g ≃ Fin W.rank × X.Ψ := idx.trans (Equiv.prodComm _ _)
  have hdet : ((blockDiagonal N).submatrix e e).det = ∏ τ, (N τ).det := by
    rw [det_submatrix_equiv_self, det_blockDiagonal]
  have main := reads_of_perC θ V W rfl X bas idx x x' ((blockDiagonal N).submatrix e e)
    (by rw [hdet]; exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun τ _ => (hN τ).1)) (fun u => by
      funext j
      have h1 : ((blockDiagonal N).submatrix e e *ᵥ fun j => perC X x u (idx j)) j =
          ∑ p : Fin W.rank × X.Ψ, blockDiagonal N (e j) p * perC X x u p.swap := by
        rw [← e.sum_comp]
        rfl
      rw [h1, Fintype.sum_prod_type]
      refine (perC_block X x x' (idx j).1 (b _) (hb _) (hxb _) (hc _) u (idx j).2).trans ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_eq_single (idx j).1]
      · exact congrArg (· * _) (blockDiagonal_apply_eq N (idx j).2 c (idx j).1).symm
      · intro τ _ hτ
        have : blockDiagonal N (e j) (c, τ) = 0 := blockDiagonal_apply_ne N (idx j).2 c hτ.symm
        rw [this, zero_mul]
      · simp) f φ hf
  convert main using 2
  rw [hdet, Finset.prod_pow, ← ht.prod_comp]
  congr 1
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [(hN _).2, (key ρ).2.1, (key ρ).2.2]

end

end GlobalTheory.AdTh
