import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CovGrp
open Formalism.QuantumDeterminants Formalism.L2.SG.PoincareInHH.PoincareSetting

section Gen
variable {n k r : ℕ}

theorem coord_span_zero (Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ) (Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ)
    (hQ1 : Qi * Q = 1) (lam : ℂ) (e : Fin r → Fin n → ℂ)
    (he : ∀ a : Fin r, Q *ᵥ Pi.single (eI k r a) 1 = lam ^ (r - (a : ℕ)) • e a)
    (c : ℕ) (y : Fin n → ℂ) (hy : y ∈ Formalism.L2.SG.HidaSetting.spanLt e c) (i : Fin (2 * r + k + 1)) (hi : c ≤ i.val) :
    (Qi *ᵥ y) i = 0 := by
  let f : (Fin n → ℂ) →ₗ[ℂ] ℂ := (LinearMap.proj i).comp (Matrix.mulVecLin Qi)
  have hle : Formalism.L2.SG.HidaSetting.spanLt e c ≤ LinearMap.ker f := by
    unfold Formalism.L2.SG.HidaSetting.spanLt
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    simp only [Set.mem_setOf_eq] at hb
    have hne : lam ^ (r - (b : ℕ)) ≠ 0 := by
      intro h0
      have h1 := congrArg (fun w => Qi *ᵥ w) (he b)
      simp only [Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec, h0, zero_smul, Matrix.mulVec_zero] at h1
      have h2 := congrFun h1 (eI k r b)
      simp at h2
    have h1 := congrArg (fun w => Qi *ᵥ w) (he b)
    simp only [Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec, Matrix.mulVec_smul] at h1
    have h3 : Qi *ᵥ e b = (lam ^ (r - (b : ℕ)))⁻¹ • Pi.single (eI k r b) 1 := by
      rw [h1, smul_smul, inv_mul_cancel₀ hne, one_smul]
    show f (e b) = 0
    simp only [f, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply, LinearMap.coe_proj,
      Function.eval, h3, Pi.smul_apply, smul_eq_mul]
    have : i ≠ eI k r b := by
      intro h; rw [h] at hi; simp [eI] at hi; omega
    simp [Pi.single_apply, this]
  exact hle hy

theorem mem_nset (J : Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ)
    (Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ) (hQ1 : Qi * Q = 1) (hQ2 : Q * Qi = 1)
    (hH : Qᴴ * J * Q = Hpk k r) (lam : ℂ) (e : Fin r → Fin n → ℂ)
    (he : ∀ a : Fin r, Q *ᵥ Pi.single (eI k r a) 1 = lam ^ (r - (a : ℕ)) • e a)
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : Mᴴ * J * M = J)
    (hS : ∀ a : Fin r, (M - 1) *ᵥ e a ∈ Formalism.L2.SG.HidaSetting.spanLt e a.1)
    (hX : ∀ y, (∀ a, star (e a) ⬝ᵥ (J *ᵥ y) = 0) → (M - 1) *ᵥ y ∈ Formalism.L2.SG.HidaSetting.spanLt e r) :
    Qi * M * Q ∈ Nset k r := by
  have hcol : ∀ (j i : Fin (2 * r + k + 1)), (Qi * M * Q) i j = (Qi *ᵥ (M *ᵥ (Q *ᵥ Pi.single j 1))) i := by
    intro j i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
    rfl
  have hsplit : ∀ w : Fin n → ℂ, Qi *ᵥ (M *ᵥ w) = Qi *ᵥ w + Qi *ᵥ ((M - 1) *ᵥ w) := by
    intro w
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
    abel
  refine ⟨?_, ?_, ?_⟩
  · show (Qi * M * Q)ᴴ * Hpk k r * (Qi * M * Q) = Hpk k r
    have hQ2' : Qiᴴ * Qᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQ2, Matrix.conjTranspose_one]
    rw [← hH]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    calc Qᴴ * (Mᴴ * (Qiᴴ * (Qᴴ * (J * (Q * (Qi * (M * Q)))))))
        = Qᴴ * (Mᴴ * ((Qiᴴ * Qᴴ) * (J * ((Q * Qi) * (M * Q))))) := by simp only [Matrix.mul_assoc]
      _ = Qᴴ * ((Mᴴ * J * M) * Q) := by rw [hQ2', hQ2]; simp only [Matrix.one_mul, Matrix.mul_assoc]
      _ = Qᴴ * (J * Q) := by rw [hM]
  · intro a i hai
    have hne : lam ^ (r - (a : ℕ)) ≠ 0 := by
      intro h0
      have h1 := congrArg (fun w => Qi *ᵥ w) (he a)
      simp only [Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec, h0, zero_smul, Matrix.mulVec_zero] at h1
      have h2 := congrFun h1 (eI k r a)
      simp at h2
    have h1 := congrArg (fun w => Qi *ᵥ w) (he a)
    simp only [Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec, Matrix.mulVec_smul] at h1
    have hv : Qi *ᵥ (M *ᵥ (Q *ᵥ Pi.single (eI k r a) 1)) =
        Pi.single (eI k r a) 1 + lam ^ (r - (a : ℕ)) • (Qi *ᵥ ((M - 1) *ᵥ e a)) := by
      rw [he a, Matrix.mulVec_smul, Matrix.mulVec_smul, hsplit, smul_add, ← h1]
    rw [hcol, hv, Pi.add_apply, Pi.smul_apply,
      coord_span_zero Q Qi hQ1 lam e he a.1 _ (hS a) i (by simpa [eI] using hai), smul_zero, add_zero,
      Pi.single_apply]
  · intro i j hj1 hj2 hi
    have horth : ∀ a, star (e a) ⬝ᵥ (J *ᵥ (Q *ᵥ Pi.single j 1)) = 0 := by
      intro a
      have hne : lam ^ (r - (a : ℕ)) ≠ 0 := by
        intro h0
        have h1 := congrArg (fun w => Qi *ᵥ w) (he a)
        simp only [Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec, h0, zero_smul, Matrix.mulVec_zero] at h1
        have h2 := congrFun h1 (eI k r a)
        simp at h2
      have key : star (Q *ᵥ Pi.single (eI k r a) 1) ⬝ᵥ (J *ᵥ (Q *ᵥ Pi.single j 1)) = 0 := by
        rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hH]
        have hz : Hpk k r (eI k r a) j = 0 := by
          have ha := a.isLt
          unfold Hpk
          simp only [eI, Fin.ext_iff]
          split_ifs <;> first | rfl | (exfalso; omega)
        simp [Matrix.mulVec, dotProduct, Pi.single_apply, hz]
      rw [he a, star_smul, smul_dotProduct] at key
      exact (smul_eq_zero.1 key).resolve_left (by simpa using hne)
    rw [hcol, hsplit, Pi.add_apply, coord_span_zero Q Qi hQ1 lam e he r _ (hX _ horth) i hi, add_zero,
      Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec]
    simp [Pi.single_apply]

end Gen

section Main
open GlobalTheory.TypeAsm

theorem trI_one {D : D7} {X : HidaSetting D} (C : Choice X 1) : trI C 1 = fun _ => Matrix.of.symm 1 := by
  funext τ
  show Matrix.of.symm (C.Qi τ * Formalism.MainNotions.S.uMat ((1 : X.B.I.Ginf) (vOf X τ)) * C.Q τ) = Matrix.of.symm 1
  have hu : Formalism.MainNotions.S.uMat ((1 : X.B.I.Ginf) (vOf X τ)) = 1 := rfl
  rw [hu, Matrix.mul_one, (C.isT τ).1]

theorem trI_mul {D : D7} {X : HidaSetting D} (C : Choice X 1) (s t : X.B.I.Ginf) :
    trI C (s * t) = GlobalTheory.DegVol.mulP (trI C s) (trI C t) := by
  funext τ
  have h2 := (C.isT τ).2.1
  have e : C.Qi τ * Formalism.MainNotions.S.uMat ((s * t) (vOf X τ)) * C.Q τ =
      (C.Qi τ * Formalism.MainNotions.S.uMat (s (vOf X τ)) * C.Q τ) * (C.Qi τ * Formalism.MainNotions.S.uMat (t (vOf X τ)) * C.Q τ) := by
    have : Formalism.MainNotions.S.uMat ((s * t) (vOf X τ)) = Formalism.MainNotions.S.uMat (s (vOf X τ)) * Formalism.MainNotions.S.uMat (t (vOf X τ)) := by
      simp [Formalism.MainNotions.S.uMat]
    rw [this]
    calc C.Qi τ * (Formalism.MainNotions.S.uMat (s (vOf X τ)) * Formalism.MainNotions.S.uMat (t (vOf X τ))) * C.Q τ
        = C.Qi τ * Formalism.MainNotions.S.uMat (s (vOf X τ)) * (C.Q τ * C.Qi τ) * Formalism.MainNotions.S.uMat (t (vOf X τ)) * C.Q τ := by
          rw [h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  simp only [trI, GlobalTheory.DegVol.mulP, Formalism.QuantumDeterminants.lmulM, Formalism.L2.SG.RealObj.trG, Equiv.apply_symm_apply]
  rw [e]
  rfl

theorem trI_inv {D : D7} {X : HidaSetting D} (C : Choice X 1) (s : X.B.I.Ginf) :
    (fun τ => Matrix.of.symm (Matrix.of (trI C s τ))⁻¹) = trI C s⁻¹ := by
  funext τ
  have h1 := (C.isT τ).1
  have h2 := (C.isT τ).2.1
  simp only [trI, Equiv.apply_symm_apply, Formalism.L2.SG.RealObj.trG]
  congr 1
  apply Matrix.inv_eq_right_inv
  have hu : Formalism.MainNotions.S.uMat (s (vOf X τ)) * Formalism.MainNotions.S.uMat (s⁻¹ (vOf X τ)) = 1 := by
    simp [Formalism.MainNotions.S.uMat]
  calc C.Qi τ * Formalism.MainNotions.S.uMat (s (vOf X τ)) * C.Q τ * (C.Qi τ * Formalism.MainNotions.S.uMat (s⁻¹ (vOf X τ)) * C.Q τ)
      = C.Qi τ * Formalism.MainNotions.S.uMat (s (vOf X τ)) * (C.Q τ * C.Qi τ) * Formalism.MainNotions.S.uMat (s⁻¹ (vOf X τ)) * C.Q τ := by
        simp only [Matrix.mul_assoc]
    _ = C.Qi τ * C.Q τ := by
        rw [h2, Matrix.mul_one, Matrix.mul_assoc (C.Qi τ), hu, Matrix.mul_one]
    _ = 1 := h1

theorem cov_grp : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1),
    (trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u).Countable ∧
    (fun _ => Matrix.of.symm 1) ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ∧
    (∀ m ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, ∀ m' ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u,
      GlobalTheory.DegVol.mulP m m' ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) ∧
    (∀ m ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u,
      (fun τ => Matrix.of.symm (Matrix.of (m τ))⁻¹) ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) ∧
    ∀ m ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, ∀ τ, Matrix.of (m τ) ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS := by
  intro D X Y u C
  have hS := Formalism.L2.SG.Pf.NOsub_coe X u Y.hK
  have mem : ∀ s, s ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ↔ s ∈ Formalism.L2.SG.Pf.NOsub X u Y.hK := by
    intro s; rw [← hS]; rfl
  refine ⟨(Formalism.L2.SG.Pf.noCount_holds X u).image _, ⟨1, (mem 1).2 (Subgroup.one_mem _), trI_one C⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    exact ⟨s * t, (mem _).2 (Subgroup.mul_mem _ ((mem _).1 hs) ((mem _).1 ht)), trI_mul C s t⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact ⟨s⁻¹, (mem _).2 (Subgroup.inv_mem _ ((mem _).1 hs)), (trI_inv C s).symm⟩
  · rintro _ ⟨s, hs, rfl⟩ τ
    obtain ⟨γ, -, hγ1, hγN, -⟩ := hs
    have hN : s ∈ X.NinfU u := hγ1 ▸ hγN
    have hNv := hN (vOf X τ)
    obtain ⟨hQ1, hQ2, hH, he⟩ := C.isT τ
    simp only [trI, Equiv.apply_symm_apply, Formalism.L2.SG.RealObj.trG]
    exact mem_nset (Formalism.REAL.Jm (X.B.I.ε (vOf X τ))) (C.Q τ) (C.Qi τ) hQ1 hQ2 hH (frS D) _
      (fun a => (he a a rfl).1) _ (s (vOf X τ)).2 hNv.1.1 hNv.2

end Main

end GlobalTheory.CovGrp
