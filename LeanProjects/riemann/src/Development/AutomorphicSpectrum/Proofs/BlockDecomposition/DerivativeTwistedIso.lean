import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd.DerivTw

section gen

variable {G M V W : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem equiv_of_eq {ρ σ : Representation ℂ G V} (h : ρ = σ) : Nonempty (ρ.Equiv σ) :=
  h ▸ ⟨Representation.Equiv.refl _⟩

theorem twAct_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) (e : ρ.Equiv σ) :
    Nonempty ((twAct ρ N θ s hs).Equiv (twAct σ N θ s hs)) := by
  let f := twMap ρ σ N θ e.toLinearEquiv.toLinearMap (fun g v => eint e g v)
  let f' := twMap σ ρ N θ e.symm.toLinearEquiv.toLinearMap (fun g v => eint e.symm g v)
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofLinear f f' ?_ ?_) fun x => ?_⟩
  · refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    show Submodule.Quotient.mk (e (e.symm v)) = Submodule.Quotient.mk v
    simp
  · refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    show Submodule.Quotient.mk (e.symm (e v)) = Submodule.Quotient.mk v
    simp
  · refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    show Submodule.Quotient.mk (e (ρ (s x) v)) = Submodule.Quotient.mk (σ (s x) (e v))
    rw [eint e]

theorem twKer_twist (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) (χ : G →* ℂˣ) (hN : ∀ n : N, χ n = 1) :
    twKer (twist ρ χ) N θ = twKer ρ N θ := by
  unfold twKer
  congr 1
  ext w
  simp only [twist_apply, hN, Units.val_one, one_smul, Set.mem_setOf_eq]

theorem twAct_twist (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) (χ : G →* ℂˣ) (χ' : M →* ℂˣ)
    (hN : ∀ n : N, χ n = 1) (hχ : ∀ m, χ (s m) = χ' m) :
    Nonempty ((twAct (twist ρ χ) N θ s hs).Equiv (twist (twAct ρ N θ s hs) χ')) := by
  refine ⟨Representation.Equiv.mk (Submodule.quotEquivOfEq (twKer (twist ρ χ) N θ) (twKer ρ N θ) (twKer_twist ρ N θ χ hN)) fun x => ?_⟩
  refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
  show Submodule.Quotient.mk (p := twKer ρ N θ) ((χ (s x) : ℂ) • ρ (s x) v) =
    (χ' x : ℂ) • Submodule.Quotient.mk (p := twKer ρ N θ) (ρ (s x) v)
  rw [hχ]
  rfl

end gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_of_last {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (h : A (Fin.last n) = eLast k n) :
    A.det = (blockMat k n A).det := by
  have h0 : ∀ j : Fin n, A (Fin.last n) (Fin.castSucc j) = 0 := fun j => by
    rw [h]; simp [eLast, Pi.single_apply, Fin.castSucc_ne_last]
  have h1 : A (Fin.last n) (Fin.last n) = 1 := by
    rw [h]; simp [eLast]
  rw [Matrix.det_succ_row A (Fin.last n), Fin.sum_univ_castSucc]
  simp only [h0, h1, Fin.succAbove_last]
  simp [blockMat, ← two_mul, Matrix.submatrix]
  rfl

theorem det_uin {n : ℕ} (u : MirUin k n) :
    Matrix.GeneralLinearGroup.det ((u : Mir k n) : GL (Fin (n + 1)) k) = 1 := by
  obtain ⟨v, hv⟩ := (u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hb : blockMat k n (((u : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = 1 := by
    rw [show ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v from hv.symm]
    ext i j
    show (1 + colMat k n v.toAdd) (Fin.castSucc i) (Fin.castSucc j) = _
    simp [colMat, one_apply, Fin.castSucc_ne_last]
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, det_of_last _ ((mem_Mir_iff k _).1 (u : Mir k n).2), hb]
  simp

theorem det_levi {n : ℕ} (m : GL (Fin n) k) :
    Matrix.GeneralLinearGroup.det ((levi k n m : Mir k n) : GL (Fin (n + 1)) k) = Matrix.GeneralLinearGroup.det m := by
  have hb : blockMat k n (((levi k n m : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      (m : Matrix (Fin n) (Fin n) k) := by
    ext i j
    show glEmbMat k n (m : Matrix (Fin n) (Fin n) k) (Fin.castSucc i) (Fin.castSucc j) = _
    simp [glEmbMat]
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    det_of_last _ ((mem_Mir_iff k _).1 (levi k n m : Mir k n).2), hb]

theorem dpow_add (n : ℕ) (s t : ℝ) : dpow (k := k) n (s + t) = dpow n t * dpow n s := by
  ext g
  simp only [dpow, detChar_apply, MonoidHom.mul_apply, Complex.ofReal_add, absPow_add, Units.val_mul]
  exact mul_comm _ _

theorem dpow_zero (n : ℕ) : dpow (k := k) n 0 = 1 := by
  ext g
  simp [dpow]

theorem dpowM_add (n : ℕ) (s t : ℝ) : dpowM (k := k) n (s + t) = dpowM n t * dpowM n s := by
  ext g
  simp [dpowM, dpow_add]

theorem dpowM_zero (n : ℕ) : dpowM (k := k) n 0 = 1 := by
  ext g
  simp [dpowM, dpow_zero]

theorem dpowM_uin {n : ℕ} (s : ℝ) (u : MirUin k n) : dpowM n s (u : Mir k n) = 1 := by
  show detChar (Fin (n + 1)) (absPow k (s : ℂ)) ((u : Mir k n) : GL (Fin (n + 1)) k) = 1
  rw [detChar_apply, det_uin, map_one]

theorem dpowM_levi {n : ℕ} (s : ℝ) (m : GL (Fin n) k) : dpowM n s (levi k n m) = dpow n s m := by
  show detChar (Fin (n + 1)) (absPow k (s : ℂ)) ((levi k n m : Mir k n) : GL (Fin (n + 1)) k) = _
  rw [detChar_apply, det_levi]
  rfl

theorem tw_tw {n : ℕ} (π : GRep k n) (s t : ℝ) : GIso ((π.tw s).tw t) (π.tw (s + t)) := by
  show Nonempty ((twist (twist π.ρ (dpow n s)) (dpow n t)).Equiv (twist π.ρ (dpow n (s + t))))
  exact equiv_of_eq (by rw [twist_twist, dpow_add])

theorem tw_zero {n : ℕ} (π : GRep k n) : GIso (π.tw 0) π := by
  show Nonempty ((twist π.ρ (dpow n 0)).Equiv π.ρ)
  exact equiv_of_eq (by rw [dpow_zero, twist_one])

theorem mtw_mtw {n : ℕ} (τ : MRep k n) (s t : ℝ) : MIso (mtw (mtw τ s) t) (mtw τ (s + t)) := by
  show Nonempty ((twist (twist τ.ρ (dpowM n s)) (dpowM n t)).Equiv (twist τ.ρ (dpowM n (s + t))))
  exact equiv_of_eq (by rw [twist_twist, dpowM_add])

theorem mtw_zero {n : ℕ} (τ : MRep k n) : MIso (mtw τ 0) τ := by
  show Nonempty ((twist τ.ρ (dpowM n 0)).Equiv τ.ρ)
  exact equiv_of_eq (by rw [dpowM_zero, twist_one])

theorem miso_mtw {n : ℕ} {A B : MRep k n} (s : ℝ) (h : MIso A B) : MIso (mtw A s) (mtw B s) := by
  obtain ⟨e⟩ := h
  exact ⟨Representation.Equiv.mk e.toLinearEquiv fun x => by
    ext v
    show e (((dpowM n s x : ℂˣ) : ℂ) • A.ρ x v) = ((dpowM n s x : ℂˣ) : ℂ) • B.ρ x (e v)
    rw [map_smul]
    exact congrArg _ (eint e x v)⟩

def psiG {n : ℕ} (τ : MRep k n) : GRep k n := ⟨_, psiMinus k τ.ρ⟩

theorem miso_phiM (ψ : AddChar k Circle) {n : ℕ} {A B : MRep k (n + 1)} (h : MIso A B) :
    MIso (MRep.phiM k ψ A) (MRep.phiM k ψ B) := by
  obtain ⟨e⟩ := h
  exact twAct_equiv _ _ _ (levi_stab ψ n) e

theorem giso_psiG {n : ℕ} {A B : MRep k n} (h : MIso A B) : GIso (psiG A) (psiG B) := by
  obtain ⟨e⟩ := h
  exact twAct_equiv _ _ _ (levi_normalises n) e

theorem phiM_mtw (ψ : AddChar k Circle) {n : ℕ} (τ : MRep k (n + 1)) (s : ℝ) :
    MIso (MRep.phiM k ψ (mtw τ s)) (mtw (MRep.phiM k ψ τ) s) :=
  twAct_twist τ.ρ _ _ _ (levi_stab ψ n) (dpowM (n + 1) s) (dpowM n s) (dpowM_uin s) fun m => by
    show dpowM (n + 1) s (levi k (n + 1) (m : GL (Fin (n + 1)) k)) = _
    rw [dpowM_levi]
    rfl

theorem psiG_mtw {n : ℕ} (τ : MRep k n) (s : ℝ) : GIso (psiG (mtw τ s)) ((psiG τ).tw s) :=
  twAct_twist τ.ρ _ _ _ (levi_normalises n) (dpowM n s) (dpow n s) (dpowM_uin s) (dpowM_levi s)

theorem miso_iterPhi (ψ : AddChar k Circle) {n : ℕ} : ∀ (j : ℕ) {A B : MRep k (n + j)}, MIso A B →
    MIso (iterPhi k ψ j A) (iterPhi k ψ j B)
  | 0, _, _, h => h
  | j + 1, _, _, h => miso_iterPhi ψ j (miso_phiM ψ h)

theorem iterPhi_mtw (ψ : AddChar k Circle) {n : ℕ} (s : ℝ) : ∀ (j : ℕ) (X : MRep k (n + j)),
    MIso (iterPhi k ψ j (mtw X s)) (mtw (iterPhi k ψ j X) s)
  | 0, _ => miso_refl _
  | j + 1, X => miso_trans (miso_iterPhi ψ j (phiM_mtw ψ X s)) (iterPhi_mtw ψ s j (MRep.phiM k ψ X))

theorem iterN_iso (ψ : AddChar k Circle) {n : ℕ} : ∀ (j : ℕ) (τ : MRep k (n + j)),
    MIso (iterN ψ j τ) (mtw (iterPhi k ψ j τ) (-(j : ℝ) / 2))
  | 0, τ => by
    rw [show -((0 : ℕ) : ℝ) / 2 = 0 by simp]
    exact miso_symm (mtw_zero τ)
  | j + 1, τ => by
    have h1 := iterN_iso ψ j (phiN ψ τ)
    have h2 := iterPhi_mtw ψ (-1 / 2) j (MRep.phiM k ψ τ)
    have h3 := mtw_mtw (iterPhi k ψ j (MRep.phiM k ψ τ)) (-1 / 2) (-(j : ℝ) / 2)
    rw [show (-1 / 2 : ℝ) + -(j : ℝ) / 2 = -((j + 1 : ℕ) : ℝ) / 2 by push_cast; ring] at h3
    exact miso_trans h1 (miso_trans (miso_mtw _ h2) h3)

theorem derivB_iso_tw : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (j n : ℕ) (π : GRep k (n + j)), GIso (derivB ψ j π) ((dG ψ j π).tw ((j : ℝ) / 2)) := by
  intro k _ _ _ _ ψ j n π
  cases j with
  | zero =>
    rw [show ((0 : ℕ) : ℝ) / 2 = 0 by simp]
    exact giso_symm (tw_zero π)
  | succ j =>
    have h1 : MIso (iterN ψ j (gres π)) (mtw (iterPhi k ψ j (resM k π.ρ)) (-(j : ℝ) / 2)) := iterN_iso ψ j (gres π)
    have h2 : GIso (psiN (iterN ψ j (gres π))) ((psiG (mtw (iterPhi k ψ j (resM k π.ρ)) (-(j : ℝ) / 2))).tw (-1 / 2)) :=
      giso_tw _ (giso_psiG h1)
    have h3 := giso_tw (-1 / 2) (psiG_mtw (iterPhi k ψ j (resM k π.ρ)) (-(j : ℝ) / 2))
    have h4 := tw_tw (psiG (iterPhi k ψ j (resM k π.ρ))) (-(j : ℝ) / 2) (-1 / 2)
    have h5 : GIso ((dG ψ (j + 1) π).tw (((j + 1 : ℕ) : ℝ) / 2))
        (((psiG (iterPhi k ψ j (resM k π.ρ))).tw (-(j : ℝ) / 2 + -1 / 2)).tw (((j + 1 : ℕ) : ℝ) / 2)) :=
      giso_tw _ (giso_trans h2 (giso_trans h3 h4))
    have h6 := tw_tw (psiG (iterPhi k ψ j (resM k π.ρ))) (-(j : ℝ) / 2 + -1 / 2) (((j + 1 : ℕ) : ℝ) / 2)
    rw [show -(j : ℝ) / 2 + -1 / 2 + ((j + 1 : ℕ) : ℝ) / 2 = 0 by push_cast; ring] at h6
    exact giso_symm (giso_trans h5 (giso_trans h6 (tw_zero _)))

end GlobalTheory.CompanionTheory.LeibOrd.DerivTw

end
