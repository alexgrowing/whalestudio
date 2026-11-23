import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasWitness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsONFr
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUnique

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdTh
open GlobalTheory.SW hiding Level
open GlobalTheory.IndefiniteRowSideFullHecke.VacuumCharacterDeterminant (detPos detNeg vacChar)
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameEquiv.CompactMove

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)

theorem thR_of_perC (x x' : Frame X.Ψ r) (M : Matrix (Fin g) (Fin g) ℂ) (hM : IsUnit M.det)
    (h : ∀ u, (fun j => perC X x' u (idx j)) = M *ᵥ fun j => perC X x u (idx j))
    (φ : TF n g) (v : WR X n) :
    thR X bas idx φ x' v = (M.det⁻¹) ^ (n / 2) * thR X bas idx φ x v := by
  have hP : ∀ s, perMat X bas idx s x' = M * perMat X bas idx s x := by
    intro s
    ext i k
    exact congrFun (h fun τ => Data.emb τ.1 (bas (Pi.single (s k) 1))) i
  have hH : hMat X bas idx x' = hMat X bas idx x * M⁻¹ := by
    rw [hMat, hP, Matrix.mul_inv_rev, hMat]
  have hT : tauMat X bas idx x' = tauMat X bas idx x := by
    rw [tauMat, hH, hP, Matrix.mul_assoc, ← Matrix.mul_assoc M⁻¹, nonsing_inv_mul _ hM, Matrix.one_mul, tauMat]
  have hI : imInv X bas idx x' = imInv X bas idx x := by rw [imInv, imInv, hT]
  have hz : ∀ b, hMat X bas idx x' *ᵥ zR X idx x' v b = hMat X bas idx x *ᵥ zR X idx x v b := by
    intro b
    have : zR X idx x' v b = M *ᵥ zR X idx x v b := h fun τ => v τ b
    rw [this, hH, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hM, Matrix.mul_one]
  simp only [thR, gaussR, GlobalTheory.Dict.hx, thA, hz, hT, hI]
  rw [hH, det_mul, det_nonsing_inv, Ring.inverse_eq_inv', mul_pow]
  ring

theorem thR_block (x x' : Frame X.Ψ r) (b : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (hb : ∀ τ, IsUnit (b τ).det)
    (hxb : ∀ τ, mat x' τ = mat x τ * b τ) (hc : ∀ τ, b τ * prFst r X.p0 = prFst r X.p0 * b τ)
    (φ : TF n g) (v : WR X n) :
    thR X bas idx φ x' v = (∏ τ, (((1 - prFst r X.p0) * b τ + prFst r X.p0).det /
      (prFst r X.p0 * b τ + (1 - prFst r X.p0)).det) ^ (n / 2)) * thR X bas idx φ x v := by
  classical
  set P := prFst r X.p0 with hP
  let N : X.Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => P * (b τ)ᵀ + (1 - P) * (b τ)⁻¹
  have hN : ∀ τ, (N τ).det ≠ 0 ∧ (N τ).det = (P * b τ + (1 - P)).det / ((1 - P) * b τ + P).det := fun τ =>
    det_tr_inv_block P (1 - P) (b τ) (hb τ) (by abel) (by
      rw [hP, prFst, diagonal_mul_diagonal]; congr 1; funext a; split_ifs <;> simp) (hc τ) (by
      rw [hP, prFst, diagonal_transpose])
  let e : Fin g ≃ Fin r × X.Ψ := idx.trans (Equiv.prodComm _ _)
  have hdet : ((blockDiagonal N).submatrix e e).det = ∏ τ, (N τ).det := by
    rw [det_submatrix_equiv_self, det_blockDiagonal]
  have main := thR_of_perC X bas idx x x' ((blockDiagonal N).submatrix e e)
    (by rw [hdet]; exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun τ _ => (hN τ).1)) (fun u => by
      funext j
      have h1 : ((blockDiagonal N).submatrix e e *ᵥ fun j => perC X x u (idx j)) j =
          ∑ p : Fin r × X.Ψ, blockDiagonal N (e j) p * perC X x u p.swap := by
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
      · simp) φ v
  rw [main, hdet, Finset.prod_pow, ← Finset.prod_inv_distrib]
  congr 2
  exact Finset.prod_congr rfl fun τ _ => by rw [(hN τ).2, inv_div]

end Classical

theorem det_block_conj {r : ℕ} (P m : Matrix (Fin r) (Fin r) ℂ) (hPP : P * P = P) (hP : Pᴴ = P)
    (hP' : P.map conj = P) (hc : m * P = P * m) (hm : mᴴ * m = 1) :
    (P * m.map conj + (1 - P)).det = (P * m + (1 - P)).det⁻¹ := by
  have h1 : (P * m + (1 - P))ᴴ * (P * m + (1 - P)) = 1 := by
    have a1 : mᴴ * (P * m) = P := by rw [← hc, ← Matrix.mul_assoc, hm, Matrix.one_mul]
    have a2 : ∀ y : Matrix (Fin r) (Fin r) ℂ, P * (P * y) = P * y := fun y => by rw [← Matrix.mul_assoc, hPP]
    simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hP,
      Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc, a1, a2, hPP]
    abel
  have h2 : P * m.map conj + (1 - P) = (starRingEnd ℂ).mapMatrix (P * m + (1 - P)) := by
    rw [map_add, map_mul, map_sub, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hP']
  have h3 := congrArg det h1
  rw [det_mul, det_conjTranspose, det_one] at h3
  rw [h2, ← RingHom.map_det]
  exact eq_inv_of_mul_eq_one_left h3

theorem blocks {r p : ℕ} (G B k : Matrix (Fin r) (Fin r) ℂ) (S : Matrix (Fin r) (Fin r) ℂ)
    (hS : S = (2 : ℂ) • prFst r p - 1) (hSS : S * S = 1) (hB : Bᴴ * G * B = S) (hk : kᴴ * G * k = G)
    (hc : k * (B * S * B⁻¹) = B * S * B⁻¹ * k) :
    ∃ m : Matrix (Fin r) (Fin r) ℂ, IsUnit (m.map conj).det ∧ k * B = B * m ∧
      m.map conj * prFst r p = prFst r p * m.map conj ∧
      ((1 - prFst r p) * m.map conj + prFst r p).det / (prFst r p * m.map conj + (1 - prFst r p)).det =
        detPos (B * S * B⁻¹) k * (detNeg (B * S * B⁻¹) k)⁻¹ := by
  have hu := GlobalTheory.Ker.ONBasis.isUnit_det hSS hB
  have hPP : prFst r p * prFst r p = prFst r p := by
    rw [prFst, diagonal_mul_diagonal]; congr 1; funext a; split_ifs <;> simp
  have hPc : (prFst r p).map conj = prFst r p := by
    ext a c
    simp only [prFst, map_apply, diagonal_apply]
    split_ifs <;> simp
  have hPH : (prFst r p)ᴴ = prFst r p := by
    rw [prFst, diagonal_conjTranspose]; congr 1; funext a; simp only [Pi.star_apply]; split_ifs <;> simp
  generalize prFst r p = P at *
  have e0 : B * S * B⁻¹ * B = B * S := by rw [Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
  generalize B * S * B⁻¹ = s at *
  obtain ⟨h1, h2, h3⟩ := block_of_inv P B k (-s) hu (by rw [Matrix.neg_mul, e0, hS])
    (by rw [Matrix.neg_mul, ← Matrix.mul_assoc, ← hc, Matrix.mul_assoc, e0, hS, Matrix.mul_assoc])
  have hkB : k * B = B * (B⁻¹ * (k * B)) := (mul_nonsing_inv_cancel_left _ _ hu).symm
  generalize B⁻¹ * (k * B) = m at *
  have hmS : m * S = S * m := by
    rw [hS, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, h1, Matrix.mul_one, Matrix.one_mul]
  have hm1 : mᴴ * S * m = S := by
    calc mᴴ * S * m = (B * m)ᴴ * G * (B * m) := by
          rw [← hB, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Bᴴ * (kᴴ * G * k) * B := by rw [← hkB, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = S := by rw [hk, hB]
  have hm : mᴴ * m = 1 := by
    calc mᴴ * m = mᴴ * S * m * S := by
          rw [Matrix.mul_assoc, hmS, Matrix.mul_assoc, ← Matrix.mul_assoc S, hSS, Matrix.one_mul]
      _ = 1 := by rw [hm1, hSS]
  have d1 := det_block_conj P m hPP hPH hPc h1 hm
  have d2 := det_block_conj (1 - P) m
    (by rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hPP]; abel)
    (by rw [conjTranspose_sub, conjTranspose_one, hPH])
    (by
      change (starRingEnd ℂ).mapMatrix (1 - P) = _
      rw [map_sub, map_one, RingHom.mapMatrix_apply, hPc])
    (by rw [Matrix.mul_sub, Matrix.sub_mul, h1, Matrix.mul_one, Matrix.one_mul]) hm
  rw [sub_sub_cancel] at d2
  refine ⟨m, ?_, hkB, ?_, ?_⟩
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (Matrix.isUnit_det_of_left_inverse hm).map _
  · rw [← hPc, ← Matrix.map_mul, ← Matrix.map_mul, h1]
  · rw [d1, d2, ← h2, ← h3, detNeg, detPos, detPos]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_neg,
      Matrix.neg_mul, Matrix.mul_one, Matrix.one_mul, hc, sub_neg_eq_add, ← sub_eq_add_neg]
    rw [div_eq_mul_inv, inv_inv, mul_comm]

theorem Th_mvB (D : D7) (S T : HSp D) (C : GlobalTheory.Ker.Ctx S T) (B : C.Bas) (hB : C.IsB B) (k : GA D T)
    (_hk : k ∈ GinfC T)
    (hc : ∀ τ, compAt C.θ τ (Formalism.L2.Theta.mt T k) * C.sB B τ = C.sB B τ * compAt C.θ τ (Formalism.L2.Theta.mt T k))
    (φ : TF S.rank C.g) (hφ : GlobalTheory.SW.IsSB φ) :
    C.Th (C.xB (C.mvB k B)) φ = vacChar C.θ T (C.sB B) S.rank (fun _ => 0) k • C.Th (C.xB B) φ := by
  have hdom : ∀ A, C.IsB A → C.xB A ∈ C.X.dom := fun A hA =>
    GlobalTheory.Ker.ONBasis.mem_dom C.X (GlobalTheory.Ker.ONBasis.isONFr_xB C hA)
  have z1 := (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ (hdom _ hB) φ hφ).1
  have z2 := (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ (hdom _ (GlobalTheory.Ker.ONBasis.isB_mvB C hB k)) φ hφ).1
  obtain ⟨-, l1, l2⟩ := GlobalTheory.ThetaSpace.theta_space_laws D S T C
  refine (l1 _ _ z2.1 ((l2 _ z1.1).1 _)).2 fun w hw => ?_
  choose m m1 m2 m3 m4 using fun τ => blocks (p := C.X.p0) (gramAt D T τ) (B τ)
    (compAt C.θ τ (Formalism.L2.Theta.mt T k)) (sgnM C.X) (sgnM_eq C.X) (GlobalTheory.Ker.ONBasis.sgnM_sq C.X) (hB τ)
    (GlobalTheory.Ker.ONBasis.compAt_unitary C τ k) (hc τ)
  rw [z2.2 w hw, Pi.smul_apply, z1.2 w hw, smul_eq_mul,
    thR_block C.X C.bas C.idx (C.xB B) (C.xB (C.mvB k B)) (fun σ => (m (C.m.e.symm σ)).map conj)
      (fun σ => m1 _) (fun σ => ?_) (fun σ => m3 _)]
  · congr 1
    rw [← C.m.e.prod_comp, vacChar]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Equiv.symm_apply_apply, m4, zero_add, zero_sub, _root_.zpow_neg, zpow_natCast, zpow_natCast, mul_pow, inv_pow]
    rfl
  · obtain ⟨τ, rfl⟩ := C.m.e.surjective σ
    rw [GlobalTheory.Ker.ONBasis.mat_xB, GlobalTheory.Ker.ONBasis.mat_xB, Equiv.symm_apply_apply, ← Matrix.map_mul, ← m2]
    rfl

end GlobalTheory.FrameEquiv.CompactMove

end
