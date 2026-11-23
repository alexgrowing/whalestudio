import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCellStructureData
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectionToTwistedEigenfunctionSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFourierExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfEigOfMemTwKer

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.MirFourier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.LocO

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def vEl (i t : ℕ) (v : Fin ((i + 1) + t + 1) → k) : Mir k ((i + 1) + t + 1) :=
  unipIn k ((i + 1) + t + 1) (Multiplicative.ofAdd v)

def ap (i t : ℕ) (c : Fin (i + 1) → k) (d : Fin (t + 1) → k) : Fin ((i + 1) + t + 1) → k :=
  Fin.append (m := i + 1) (n := t + 1) c d

variable (k) in

def cEl (i t : ℕ) (c : Fin (i + 1) → k) : Mir k ((i + 1) + t + 1) := vEl k i t (ap i t c 0)

theorem vEl_add (i t : ℕ) (v w : Fin ((i + 1) + t + 1) → k) : vEl k i t (v + w) = vEl k i t v * vEl k i t w :=
  map_mul (unipIn k ((i + 1) + t + 1)) (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)

theorem dEmb_eq (i t : ℕ) (d : Fin (t + 1) → k) : dEmb k i t d = vEl k i t (ap i t 0 d) := rfl

theorem ap_add (i t : ℕ) (c c' : Fin (i + 1) → k) (d d' : Fin (t + 1) → k) :
    ap i t (c + c') (d + d') = ap i t c d + ap i t c' d' := by
  funext x
  refine Fin.addCases (m := i + 1) (n := t + 1) (fun j => ?_) (fun j => ?_) x <;> simp [ap]

theorem vEl_ap (i t : ℕ) (c : Fin (i + 1) → k) (d : Fin (t + 1) → k) :
    vEl k i t (ap i t c d) = cEl k i t c * dEmb k i t d := by
  rw [cEl, dEmb_eq, ← vEl_add, ← ap_add, add_zero, zero_add]

theorem vEl_mem (i t : ℕ) (v : Fin ((i + 1) + t + 1) → k) : vEl k i t v ∈ MirUin k ((i + 1) + t + 1) :=
  Subgroup.mem_subgroupOf.2 ⟨Multiplicative.ofAdd v, rfl⟩

theorem exists_vEl (i t : ℕ) (u : Mir k ((i + 1) + t + 1)) (hu : u ∈ MirUin k ((i + 1) + t + 1)) :
    ∃ v, u = vEl k i t v := by
  obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.1 hu
  exact ⟨v.toAdd, Subtype.ext hv.symm⟩

theorem ePG_true_eq (i t : ℕ) (b : Fin (t + 1)) :
    ePG (i + 1) (t + 1) ⟨true, b⟩ = Fin.castSucc (Fin.natAdd (i + 1) b) :=
  Fin.ext (by simpa using Fib.ePG_true_val (i + 1) (t + 1) b)

theorem ePG_false_eq (i t : ℕ) (a : Fin (i + 1)) :
    ePG (i + 1) (t + 1) ⟨false, Fin.castSucc a⟩ = Fin.castSucc (Fin.castAdd (t + 1) a) := by
  apply Fin.ext
  simp [ePG, finSumFinEquiv_symm_apply_castSucc]

theorem vEl_castSucc_last (i t : ℕ) (v : Fin ((i + 1) + t + 1) → k) (r : Fin ((i + 1) + t + 1)) :
    (((vEl k i t v : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
      Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc r) (Fin.last _) = v r :=
  unip_apply_castSucc_last k _ (Multiplicative.ofAdd v) r

theorem vEl_of_ne (i t : ℕ) (v : Fin ((i + 1) + t + 1) → k) (r s : Fin ((i + 1) + t + 2)) (h : r ≠ s)
    (hs : s ≠ Fin.last _) :
    (((vEl k i t v : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
      Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k) r s = 0 := by
  show (1 + colMat k _ v) r s = 0
  simp [colMat, one_apply, h, hs]

theorem vEl_diag (i t : ℕ) (v : Fin ((i + 1) + t + 1) → k) (r : Fin ((i + 1) + t + 1)) :
    (((vEl k i t v : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
      Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc r) (Fin.castSucc r) = 1 := by
  show (1 + colMat k _ v) _ _ = 1
  simp [colMat, one_apply, Fin.castSucc_ne_last]

theorem cEl_mem (i t : ℕ) (c : Fin (i + 1) → k) : cEl k i t c ∈ HPG k (i + 1) (t + 1) := by
  show ((cEl k i t c : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) ∈ parab k (ePG (i + 1) (t + 1))
  rw [mem_parab_iff]
  intro a b r s hab
  obtain ⟨rfl, rfl⟩ : a = true ∧ b = false := by
    revert hab; cases a <;> cases b <;> simp
  rw [ePG_true_eq]
  induction s using Fin.lastCases with
  | last =>
    rw [ePG_false_last]
    refine (vEl_castSucc_last i t _ _).trans ?_
    exact Fin.append_right _ _ _
  | cast s =>
    rw [ePG_false_eq]
    refine vEl_of_ne i t _ _ _ ?_ (Fin.castSucc_ne_last _)
    intro e
    have := congrArg Fin.val e
    simp at this
    omega

theorem det_unip (n : ℕ) (v : Multiplicative (Fin n → k)) :
    ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k).det = 1 := by
  have h : BlockTriangular ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) id := by
    intro a b hab
    have hab' : b < a := hab
    have hb : b ≠ Fin.last n := fun e => by
      rw [e] at hab'
      exact absurd hab' (not_lt.2 (Fin.le_last _))
    show (1 + colMat k n v.toAdd) a b = 0
    simp [colMat, one_apply, hb, hab'.ne']
  rw [det_of_upperTriangular h]
  refine Finset.prod_eq_one fun a _ => ?_
  show (1 + colMat k n v.toAdd) a a = 1
  induction a using Fin.lastCases with
  | last => simp [colMat]
  | cast a => simp [colMat, Fin.castSucc_ne_last]

theorem dpowM_unipIn (n : ℕ) (s : ℝ) (v : Multiplicative (Fin n → k)) : dpowM n s (unipIn k n v) = 1 := by
  have h : Matrix.GeneralLinearGroup.det (unip k n v) = 1 := Units.ext (det_unip n v)
  show (absPow k (s : ℂ)) (Matrix.GeneralLinearGroup.det (unip k n v)) = 1
  rw [h, map_one]

theorem pgProj_cEl (i t : ℕ) (c : Fin (i + 1) → k) :
    pgProj k (i + 1) (t + 1) ⟨cEl k i t c, cEl_mem i t c⟩ = (unipIn k (i + 1) (Multiplicative.ofAdd c), 1) := by
  refine Prod.ext (Subtype.ext (Units.ext ?_)) (Units.ext ?_)
  · ext a b
    show (((cEl k i t c : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
      Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k) (ePG (i + 1) (t + 1) ⟨false, a⟩) (ePG (i + 1) (t + 1) ⟨false, b⟩) =
        (1 + colMat k (i + 1) c) a b
    induction b using Fin.lastCases with
    | last =>
      rw [ePG_false_last]
      induction a using Fin.lastCases with
      | last =>
        rw [ePG_false_last]
        have h1 := congrFun ((mem_Mir_iff k _).1 (cEl k i t c).2) (Fin.last _)
        refine h1.trans ?_
        simp [eLast, colMat]
      | cast a =>
        rw [ePG_false_eq]
        refine (vEl_castSucc_last i t _ _).trans ?_
        refine (Fin.append_left _ _ _).trans ?_
        simp [colMat, one_apply, Fin.castSucc_ne_last]
    | cast b =>
      rw [ePG_false_eq]
      induction a using Fin.lastCases with
      | last =>
        rw [ePG_false_last]
        refine (vEl_of_ne i t _ _ _ (Fin.castSucc_ne_last _).symm (Fin.castSucc_ne_last _)).trans ?_
        simp [colMat, one_apply, (Fin.castSucc_ne_last _).symm]
      | cast a =>
        rw [ePG_false_eq]
        by_cases h : a = b
        · subst h
          refine (vEl_diag i t _ _).trans ?_
          simp [colMat, Fin.castSucc_ne_last]
        · refine (vEl_of_ne i t _ _ _ ?_ (Fin.castSucc_ne_last _)).trans ?_
          · intro e
            apply h
            have := congrArg Fin.val e
            simp at this
            exact Fin.ext this
          · simp [colMat, one_apply, h, Fin.castSucc_ne_last]
  · ext a b
    show (((cEl k i t c : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
      Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k) (ePG (i + 1) (t + 1) ⟨true, a⟩) (ePG (i + 1) (t + 1) ⟨true, b⟩) =
        (1 : Matrix (Fin (t + 1)) (Fin (t + 1)) k) a b
    rw [ePG_true_eq, ePG_true_eq]
    by_cases h : a = b
    · subst h
      rw [one_apply_eq]
      exact vEl_diag i t _ _
    · rw [one_apply_ne h]
      refine vEl_of_ne i t _ _ _ ?_ (Fin.castSucc_ne_last _)
      intro e
      apply h
      have := congrArg Fin.val e
      simp at this
      exact Fin.ext this

def rho1 {i : ℕ} (τ : MRep k (i + 1)) (W : Type) [AddCommGroup W] [Module ℂ W] :
    Representation ℂ (Multiplicative (Fin (i + 1) → k)) (τ.V ⊗[ℂ] W) where
  toFun x := LinearMap.rTensor W (τ.ρ (unipIn k (i + 1) x))
  map_one' := by
    rw [map_one, map_one]
    exact LinearMap.rTensor_id _ _
  map_mul' a b := by
    rw [map_mul, map_mul]
    exact LinearMap.rTensor_mul W _ _

theorem sigX_cEl {i t : ℕ} (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (c : Fin (i + 1) → k) (w : τ.V ⊗[ℂ] σ.V) :
    sigX τ σ ⟨cEl k i t c, cEl_mem i t c⟩ w = rho1 τ σ.V (Multiplicative.ofAdd c) w := by
  show extTensor _ _ (pgProj k (i + 1) (t + 1) ⟨cEl k i t c, cEl_mem i t c⟩) w = _
  rw [pgProj_cEl]
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a b =>
    refine (extTensor_tmul _ _ _ a b).trans ?_
    have h1 : (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ 1 b = b := by rw [map_one]; rfl
    have h2 : (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (unipIn k (i + 1) (Multiplicative.ofAdd c)) a =
        τ.ρ (unipIn k (i + 1) (Multiplicative.ofAdd c)) a := by
      show ((dpowM (i + 1) _ (unipIn k (i + 1) (Multiplicative.ofAdd c)) : ℂˣ) : ℂ) • τ.ρ _ a = _
      rw [dpowM_unipIn, Units.val_one, one_smul]
    exact congrArg₂ (fun x y => TensorProduct.tmul ℂ x y) h2 h1

theorem levi_conj_vEl (i t : ℕ) (g : GL (Fin ((i + 1) + t + 1)) k) (v : Fin ((i + 1) + t + 1) → k) :
    levi k _ g * vEl k i t v * (levi k _ g)⁻¹ =
      vEl k i t ((g : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k).mulVec v) := by
  apply Subtype.ext
  show glEmb k _ g * unip k _ (Multiplicative.ofAdd v) * (glEmb k _ g)⁻¹ = unip k _ _
  rw [glEmb_mul_unip', mul_inv_cancel_right]
  rfl

theorem wEl_mul_sEmb (i t : ℕ) (m : Mir k ((i + 1) + t)) :
    wEl k i t * sEmb k ((i + 1) + t) m = levi k _ (wGL k i t * (m : GL (Fin ((i + 1) + t + 1)) k)) :=
  (map_mul (levi k ((i + 1) + t + 1)) _ _).symm

theorem piPerm_last (i t : ℕ) : piPerm i t (Fin.last _) = Fin.castAdd (t + 1) (Fin.last i) := by
  have h1 : (finCongr (by omega : (i + 1) + t + 1 = i + (t + 1) + 1)) (Fin.last ((i + 1) + t)) = Fin.last (i + (t + 1)) :=
    Fin.ext (by simp)
  have h2 : (ePG i (t + 1)).symm (Fin.last (i + (t + 1))) = ⟨false, Fin.last i⟩ := by
    rw [Equiv.symm_apply_eq, ePG_false_last]
  show eGP (i + 1) t ((ePG i (t + 1)).symm (finCongr _ (Fin.last ((i + 1) + t)))) = _
  rw [h1, h2]
  apply Fin.ext
  simp [eGP, stdSum]

theorem inv_mulVec_last (i t : ℕ) (m : Mir k ((i + 1) + t)) (w : Fin ((i + 1) + t + 1) → k) :
    ((((wGL k i t * (m : GL (Fin ((i + 1) + t + 1)) k))⁻¹ : GL (Fin ((i + 1) + t + 1)) k) :
      Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k).mulVec w) (Fin.last _) =
      w (Fin.castAdd (t + 1) (Fin.last i)) := by
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  have hm : ((m : GL (Fin ((i + 1) + t + 1)) k))⁻¹ ∈ Mir k ((i + 1) + t) := inv_mem m.2
  rw [mulVec_last_of_mem k _ hm]
  show ((Equiv.Perm.permMatrix k (piPerm i t)).mulVec w) (Fin.last _) = _
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mulVec, Function.comp, piPerm_last]

theorem mirChar_conj (ψ : AddChar k Circle) (i t : ℕ) (m : Mir k ((i + 1) + t)) (c : Fin (i + 1) → k) (d : Fin (t + 1) → k)
    (l : MirUin k ((i + 1) + t + 1))
    (hl : (l : Mir k ((i + 1) + t + 1)) = (wEl k i t * sEmb k ((i + 1) + t) m)⁻¹ * vEl k i t (ap i t c d) *
      (wEl k i t * sEmb k ((i + 1) + t) m)) :
    mirChar k ψ ((i + 1) + t) l = Circle.toUnits (ψ (c (Fin.last i))) := by
  set g := wGL k i t * (m : GL (Fin ((i + 1) + t + 1)) k) with hg
  have h1 : (l : Mir k ((i + 1) + t + 1)) = vEl k i t
      (((g⁻¹ : GL (Fin ((i + 1) + t + 1)) k) : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k).mulVec (ap i t c d)) := by
    rw [hl, wEl_mul_sEmb, ← levi_conj_vEl, map_inv, inv_inv]
  have h2 : (((l : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k)) = unip k ((i + 1) + t + 1)
      (Multiplicative.ofAdd (((g⁻¹ : GL (Fin ((i + 1) + t + 1)) k) : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k).mulVec (ap i t c d))) := by
    rw [h1]; rfl
  rw [mirChar_eq k ψ _ l _ h2]
  simp only [toAdd_ofAdd]
  rw [hg, inv_mulVec_last]
  congr 2
  exact Fin.append_left _ _ _

theorem thetaA_single (ψ : AddChar k Circle) (i : ℕ) :
    thetaA k ψ (Pi.single (Fin.last i) 1 : Fin (i + 1) → k) = mirChar k ψ i := by
  ext x
  simp [thetaA, mirChar, chrA, chrV]

theorem isSmooth_rho1 {i : ℕ} (τ : MRep k (i + 1)) (hτ : IsSmooth τ.ρ) (W : Type) [AddCommGroup W] [Module ℂ W] :
    IsSmooth (rho1 τ W) := by
  intro z
  show z ∈ smoothPart (rho1 τ W)
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul a b =>
    let T : Subgroup (Multiplicative (Fin (i + 1) → k)) :=
      { carrier := {g | rho1 τ W g (a ⊗ₜ b) = a ⊗ₜ b}
        mul_mem' := by
          intro x y hx hy
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hy, hx]
        one_mem' := by simp
        inv_mem' := by
          intro x hx
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← hx]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    have h0 : IsOpen {x : Multiplicative (Fin (i + 1) → k) | τ.ρ (unipIn k (i + 1) x) a = a} :=
      (hτ a).preimage (continuous_unipIn (i + 1))
    refine T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (h0.mem_nhds (by simp)) ?_)
    intro x hx
    show LinearMap.rTensor W _ (a ⊗ₜ b) = a ⊗ₜ b
    rw [LinearMap.rTensor_tmul, show τ.ρ (unipIn k (i + 1) x) a = a from hx]

theorem mem_twKer_of_qO {i t : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (z : τ.V ⊗[ℂ] σ.V)
    (hz : qO τ σ ψ z = 0) :
    z ∈ twKer (rho1 τ σ.V) ⊤ (resChr ψ (Pi.single (Fin.last i) 1 : Fin (i + 1) → k) ⊤) := by
  set K := twKer τ.ρ (MirUin k (i + 1)) (mirChar k ψ i) with hK
  have hex : Function.Exact (LinearMap.rTensor σ.V K.subtype) (LinearMap.rTensor σ.V K.mkQ) :=
    rTensor_exact σ.V (LinearMap.exact_subtype_mkQ K) (Submodule.mkQ_surjective K)
  set χ := resChr ψ (Pi.single (Fin.last i) 1 : Fin (i + 1) → k) ⊤ with hχ
  have hle : K ≤ twKer (τ.ρ.comp (unipIn k (i + 1)) : Representation ℂ (Multiplicative (Fin (i + 1) → k)) τ.V) ⊤ χ := by
    have := twKer_le_top ψ τ.ρ (Pi.single (Fin.last i) 1 : Fin (i + 1) → k)
    rwa [thetaA_single] at this
  have hmap : ∀ b : σ.V, twKer (τ.ρ.comp (unipIn k (i + 1)) : Representation ℂ (Multiplicative (Fin (i + 1) → k)) τ.V) ⊤ χ ≤
      (twKer (rho1 τ σ.V) ⊤ χ).comap ((TensorProduct.mk ℂ τ.V σ.V).flip b) := by
    intro b
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, v, rfl⟩
    show (_ - _) ⊗ₜ[ℂ] b ∈ twKer (rho1 τ σ.V) ⊤ χ
    rw [TensorProduct.sub_tmul, ← TensorProduct.smul_tmul']
    exact Submodule.subset_span ⟨n, v ⊗ₜ b, rfl⟩
  have key : ∀ x : K ⊗[ℂ] σ.V, LinearMap.rTensor σ.V K.subtype x ∈ twKer (rho1 τ σ.V) ⊤ χ := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    | tmul w b =>
      rw [LinearMap.rTensor_tmul]
      exact hmap b (hle w.2)
  obtain ⟨x, rfl⟩ := (hex z).1 hz
  exact key x

theorem ap_zero (i t : ℕ) : ap i t (0 : Fin (i + 1) → k) (0 : Fin (t + 1) → k) = 0 := by
  funext x
  refine Fin.addCases (m := i + 1) (n := t + 1) (fun j => ?_) (fun j => ?_) x <;> simp [ap]

theorem vEl_zero (i t : ℕ) : vEl k i t 0 = 1 := map_one (unipIn k ((i + 1) + t + 1))

theorem continuous_ap (i t : ℕ) :
    Continuous (fun p : (Fin (i + 1) → k) × (Fin (t + 1) → k) => ap i t p.1 p.2) := by
  refine continuous_pi fun x => ?_
  refine Fin.addCases (m := i + 1) (n := t + 1) (fun j => ?_) (fun j => ?_) x
  · simp only [ap, Fin.append_left]
    fun_prop
  · simp only [ap, Fin.append_right]
    fun_prop

def psiHom (i t : ℕ) (y : Mir k ((i + 1) + t + 1)) :
    Multiplicative (Fin (i + 1) → k) × Multiplicative (Fin (t + 1) → k) →* Mir k ((i + 1) + t + 1) where
  toFun p := y⁻¹ * vEl k i t (ap i t p.1.toAdd p.2.toAdd) * y
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, toAdd_one]
    rw [ap_zero, vEl_zero]
    group
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul]
    rw [ap_add, vEl_add]
    group

theorem continuous_psiHom (i t : ℕ) (y : Mir k ((i + 1) + t + 1)) : Continuous (psiHom i t y) := by
  have h1 : Continuous (fun p : Multiplicative (Fin (i + 1) → k) × Multiplicative (Fin (t + 1) → k) =>
      vEl k i t (ap i t p.1.toAdd p.2.toAdd)) :=
    (continuous_unipIn _).comp (continuous_ofAdd.comp ((continuous_ap i t).comp
      ((continuous_toAdd.comp continuous_fst).prodMk (continuous_toAdd.comp continuous_snd))))
  exact (continuous_const.mul h1).mul continuous_const

theorem resChr_last (ψ : AddChar k Circle) (i : ℕ) (C : Subgroup (Multiplicative (Fin (i + 1) → k))) (x : C) :
    resChr ψ (Pi.single (Fin.last i) 1 : Fin (i + 1) → k) C x =
      Circle.toUnits (ψ ((x : Multiplicative (Fin (i + 1) → k)).toAdd (Fin.last i))) := by
  simp [resChr, chrA]

theorem isOpen_resChr_ker (ψ : AddChar k Circle) (hψ : Continuous ψ) (i : ℕ) (C : Subgroup (Multiplicative (Fin (i + 1) → k))) :
    IsOpen ((resChr ψ (Pi.single (Fin.last i) 1 : Fin (i + 1) → k) C).ker : Set C) := by
  have h : ((resChr ψ (Pi.single (Fin.last i) 1 : Fin (i + 1) → k) C).ker : Set C) =
      (fun x : C => (x : Multiplicative (Fin (i + 1) → k)).toAdd (Fin.last i)) ⁻¹' {z | ψ z = 1} := by
    ext x
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, resChr_last, Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · intro h
      apply Circle.ext
      simpa using congrArg Units.val h
    · intro h
      rw [h, map_one]
  rw [h]
  refine (GlobalTheory.CompanionTheory.BZFun.isOpen_addChar_eq_one k ψ hψ).preimage ?_
  exact (continuous_apply _).comp (continuous_toAdd.comp continuous_subtype_val)

theorem exists_polyBall_of_isCompact (n : ℕ) {K : Set (Fin n → k)} (hK : IsCompact K) :
    ∃ s : kˣ, ∀ a ∈ K, Multiplicative.ofAdd a ∈ polyBall (k := k) n s := by
  have hcov : K ⊆ ⋃ s : kˣ, {a | Multiplicative.ofAdd a ∈ polyBall (k := k) n s} := fun a _ => by
    obtain ⟨s, hs⟩ := exists_mem_polyBall (k := k) (Multiplicative.ofAdd a)
    exact Set.mem_iUnion.2 ⟨s, hs⟩
  obtain ⟨s, hs⟩ := hK.elim_directed_cover _
    (fun s => (isOpen_polyBall n s).preimage continuous_ofAdd) hcov (by
      intro s₁ s₂
      rcases le_total (ValuativeRel.valuation k (s₁ : k)) (ValuativeRel.valuation k (s₂ : k)) with h | h
      · exact ⟨s₂, fun a ha => polyBall_mono n h ha, fun a ha => ha⟩
      · exact ⟨s₁, fun a ha => ha, fun a ha => polyBall_mono n h ha⟩)
  exact ⟨s, hs⟩

theorem avgVanish_translate {G Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup Z] [Module ℂ Z]
    (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (θ : U →* ℂˣ) (f : cIndSpace H σ) (y h e : G) (hh : h ∈ H)
    (he : y⁻¹ * e * y ∈ U) (hv : AvgVanish H σ U θ f y) : AvgVanish H σ U θ f (h * e * y) := by
  obtain ⟨L, hL, hc, g, h1, h2, h3⟩ := hv
  refine ⟨L, hL, hc, g, h1, h2, fun u hu => ?_⟩
  have e1 : h * e * y * u = (⟨h, hh⟩ : H) * (y * (y⁻¹ * e * y * u)) := by
    show _ = h * _
    group
  rw [e1, (g : smoothPart (ind H σ)).1.2 ⟨h, hh⟩ _, h3 _ (U.mul_mem he hu), map_zero]

theorem avgVanish_of_fibre' {G Z Γ A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup Z] [Module ℂ Z] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A]
    (μ : MeasureTheory.Measure A) [μ.IsAddHaarMeasure]
    (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (θ : U →* ℂˣ)
    (ρ₁ : Representation ℂ Γ Z) (hρ₁ : IsSmooth ρ₁)
    (C : Subgroup Γ) (hC : IsCompact (C : Set Γ)) (χ : C →* ℂˣ) (hχ : IsOpen (χ.ker : Set C))
    (c : C → H) (hc : ∀ (b : C) (w : Z), σ (c b) w = ρ₁ (b : Γ) w)
    (e : A → G) (he : ∀ a a', e (a + a') = e a * e a')
    (hce : ∀ (b : C) (a : A), ((c b : H) : G) * e a = e a * ((c b : H) : G))
    (y : G) (D : Set A) (hD0 : (0 : A) ∈ D) (hDs : ∀ a a', a ∈ D → a' ∈ D → a - a' ∈ D)
    (hDc : IsCompact D) (hDo : IsOpen D)
    (L : Subgroup G) (hLU : L ≤ U) (hLc : IsCompact (L : Set G))
    (hθ : IsOpen ((θ.comp (Subgroup.inclusion hLU)).ker : Set L))
    (hL1 : ∀ l : L, ∃ (b : C) (a : A), a ∈ D ∧ y * (l : G) * y⁻¹ = ((c b : H) : G) * e a ∧
      θ (Subgroup.inclusion hLU l) = χ b)
    (hL2 : ∀ b : C, ∃ l : L, y * (l : G) * y⁻¹ = ((c b : H) : G) ∧ θ (Subgroup.inclusion hLU l) = χ b)
    (hL3 : ∀ a ∈ D, ∃ l : L, y * (l : G) * y⁻¹ = e a ∧ θ (Subgroup.inclusion hLU l) = 1)
    (hU : ∀ u ∈ U, ∃ h ∈ H, ∃ a : A, y * u * y⁻¹ = h * e a)
    (hfib : ∀ f' : cIndSpace H σ, IsLocallyConstant (fun a => (f' : smoothPart (ind H σ)).1.1 (e a * y)) ∧
      HasCompactSupport (fun a => (f' : smoothPart (ind H σ)).1.1 (e a * y)))
    (f : cIndSpace H σ) (hsupp : ∀ a, (f : smoothPart (ind H σ)).1.1 (e a * y) ≠ 0 → a ∈ D)
    (hz : GlobalTheory.CompanionTheory.Rodier.smInt μ (fun a => (f : smoothPart (ind H σ)).1.1 (e a * y)) ∈ twKer ρ₁ C χ) :
    AvgVanish H σ U θ f y :=
  avgVanish_of_fibre μ H σ U θ ρ₁ hρ₁ C hC χ hχ c hc e he hce y D hD0 hDs hDc hDo L hLU hLc hθ hL1 hL2 hL3 hU hfib f hsupp hz

theorem avgVanish_at {i t : ℕ} (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1))
    (hτ : IsSmooth τ.ρ) (f : XS τ σ) (m : Mir k ((i + 1) + t)) (y : Mir k ((i + 1) + t + 1))
    (hy : y = wEl k i t * sEmb k ((i + 1) + t) m) (hq : qO τ σ ψ (intO f y) = 0) :
    AvgVanish (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t)) f y := by
  letI : MeasurableSpace (Fin (t + 1) → k) := borel _
  haveI : BorelSpace (Fin (t + 1) → k) := ⟨rfl⟩
  haveI : (muD k (t + 1)).IsAddHaarMeasure := by
    unfold muD
    infer_instance
  have hnorm := Grp.mirUin_normal (k := k) ((i + 1) + t + 1)
  obtain ⟨s₁, hs₁⟩ := exists_mem_twKer_polyBall ψ (rho1 τ σ.V) _ _ (mem_twKer_of_qO ψ τ σ _ hq)
  have hfib := fun f' : XS τ σ => Fib.fibre_isLocallyConstant_hasCompactSupport k i t τ σ f' y
  obtain ⟨s₂, hs₂⟩ := exists_polyBall_of_isCompact (t + 1) (hfib f).2
  obtain ⟨L, hL⟩ : ∃ L : Subgroup (Mir k ((i + 1) + t + 1)), L = ((polyBall (k := k) (i + 1) s₁).prod (polyBall (k := k) (t + 1) s₂)).map (psiHom i t y) := ⟨_, rfl⟩
  have hLU : L ≤ MirUin k ((i + 1) + t + 1) := by
    rw [hL]
    rintro _ ⟨p, -, rfl⟩
    exact hnorm.conj_mem' _ (vEl_mem i t _) y
  have hLc : IsCompact (L : Set (Mir k ((i + 1) + t + 1))) := by
    rw [hL, Subgroup.coe_map, Subgroup.coe_prod]
    exact ((isCompact_polyBall _ _).prod (isCompact_polyBall _ _)).image (continuous_psiHom i t y)
  have hθ : IsOpen (((mirChar k ψ ((i + 1) + t)).comp (Subgroup.inclusion hLU)).ker : Set L) := by
    have h1 := Grp.mirChar_ker_open (k := k) ψ hψ ((i + 1) + t)
    exact h1.preimage (Continuous.subtype_mk continuous_subtype_val _)
  have hmem : ∀ l ∈ L, ∃ p ∈ (polyBall (k := k) (i + 1) s₁).prod (polyBall (k := k) (t + 1) s₂), psiHom i t y p = l := by
    rw [hL]
    exact fun l hl => hl
  have hmem' : ∀ p ∈ (polyBall (k := k) (i + 1) s₁).prod (polyBall (k := k) (t + 1) s₂), psiHom i t y p ∈ L := by
    rw [hL]
    exact fun p hp => ⟨p, hp, rfl⟩
  have hcj : ∀ W : Mir k ((i + 1) + t + 1), y * (y⁻¹ * W * y) * y⁻¹ = W := fun W => by group
  have hch : ∀ (p : Multiplicative (Fin (i + 1) → k) × Multiplicative (Fin (t + 1) → k)) (hp : psiHom i t y p ∈ L),
      mirChar k ψ ((i + 1) + t) (Subgroup.inclusion hLU ⟨psiHom i t y p, hp⟩) = Circle.toUnits (ψ (p.1.toAdd (Fin.last i))) := by
    intro p hp
    refine mirChar_conj ψ i t m _ p.2.toAdd _ ?_
    rw [← hy]
    rfl
  have hce : ∀ (b : polyBall (k := k) (i + 1) s₁) (a : Fin (t + 1) → k),
      cEl k i t (b : Multiplicative (Fin (i + 1) → k)).toAdd * dEmb k i t a =
        dEmb k i t a * cEl k i t (b : Multiplicative (Fin (i + 1) → k)).toAdd := fun b a =>
    Grp.mirUin_comm (vEl_mem i t _) (vEl_mem i t _)
  have hL1 : ∀ l : L, ∃ (b : polyBall (k := k) (i + 1) s₁) (a : Fin (t + 1) → k), a ∈ {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (t + 1) s₂} ∧
      y * (l : Mir k ((i + 1) + t + 1)) * y⁻¹ = cEl k i t (b : Multiplicative (Fin (i + 1) → k)).toAdd * dEmb k i t a ∧
      mirChar k ψ ((i + 1) + t) (Subgroup.inclusion hLU l) = resChr ψ (Pi.single (Fin.last i) 1) (polyBall (k := k) (i + 1) s₁) b := by
    rintro ⟨l, hl⟩
    obtain ⟨p, ⟨hp1, hp2⟩, rfl⟩ := hmem l hl
    refine ⟨⟨p.1, hp1⟩, p.2.toAdd, hp2, ?_, ?_⟩
    · rw [← vEl_ap]
      exact hcj _
    · rw [resChr_last]
      exact hch p hl
  have hL2 : ∀ b : polyBall (k := k) (i + 1) s₁, ∃ l : L, y * (l : Mir k ((i + 1) + t + 1)) * y⁻¹ = cEl k i t (b : Multiplicative (Fin (i + 1) → k)).toAdd ∧
      mirChar k ψ ((i + 1) + t) (Subgroup.inclusion hLU l) = resChr ψ (Pi.single (Fin.last i) 1) (polyBall (k := k) (i + 1) s₁) b := by
    intro b
    have hp := hmem' ((b : Multiplicative (Fin (i + 1) → k)), 1) ⟨b.2, Subgroup.one_mem _⟩
    refine ⟨⟨_, hp⟩, hcj _, ?_⟩
    rw [resChr_last]
    exact hch _ hp
  have hL3 : ∀ a ∈ {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (t + 1) s₂}, ∃ l : L, y * (l : Mir k ((i + 1) + t + 1)) * y⁻¹ = dEmb k i t a ∧
      mirChar k ψ ((i + 1) + t) (Subgroup.inclusion hLU l) = 1 := by
    intro a ha
    have hp := hmem' (1, Multiplicative.ofAdd a) ⟨Subgroup.one_mem _, ha⟩
    refine ⟨⟨_, hp⟩, hcj _, ?_⟩
    rw [hch _ hp]
    simp

  have hU : ∀ u ∈ MirUin k ((i + 1) + t + 1), ∃ h ∈ HPG k (i + 1) (t + 1), ∃ a : Fin (t + 1) → k, y * u * y⁻¹ = h * dEmb k i t a := by
    intro u hu
    obtain ⟨v, rfl⟩ := exists_vEl i t u hu
    rw [hy, wEl_mul_sEmb, levi_conj_vEl]
    obtain ⟨w, hw⟩ : ∃ w : Fin ((i + 1) + t + 1) → k, w = ((wGL k i t * (m : GL (Fin ((i + 1) + t + 1)) k) : GL (Fin ((i + 1) + t + 1)) k) :
      Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k).mulVec v := ⟨_, rfl⟩
    rw [← hw]
    refine ⟨cEl k i t fun j => w (Fin.castAdd (t + 1) j), cEl_mem i t _, fun j => w (Fin.natAdd (i + 1) j), ?_⟩
    rw [← vEl_ap]
    congr 1
    exact (Fin.append_castAdd_natAdd (m := i + 1) (n := t + 1)).symm
  have hsupp : ∀ a, evX f (dEmb k i t a * y) ≠ 0 → a ∈ {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (t + 1) s₂} :=
    fun a ha => hs₂ a (subset_tsupport _ ha)
  have hD0 : (0 : Fin (t + 1) → k) ∈ {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (t + 1) s₂} := (polyBall (k := k) (t + 1) s₂).one_mem
  have hDs : ∀ a a', a ∈ {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (t + 1) s₂} → a' ∈ {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (t + 1) s₂} → a - a' ∈ {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (t + 1) s₂} :=
    fun a a' h h' => (polyBall (k := k) (t + 1) s₂).div_mem h h'
  have hDc : IsCompact {a : Fin (t + 1) → k | Multiplicative.ofAdd a ∈ polyBall (k := k) (t + 1) s₂} :=
    by
      have h : {a : Fin (t + 1) → k | Multiplicative.ofAdd a ∈ polyBall (k := k) (t + 1) s₂} =
          Multiplicative.toAdd '' (polyBall (k := k) (t + 1) s₂ : Set (Multiplicative (Fin (t + 1) → k))) := by
        ext a
        exact ⟨fun h => ⟨Multiplicative.ofAdd a, h, rfl⟩, by rintro ⟨x, hx, rfl⟩; exact hx⟩
      rw [h]
      exact (isCompact_polyBall (t + 1) s₂).image continuous_toAdd
  have hDo : IsOpen {a : Fin (t + 1) → k | Multiplicative.ofAdd a ∈ polyBall (k := k) (t + 1) s₂} :=
    (isOpen_polyBall (t + 1) s₂).preimage continuous_ofAdd
  exact avgVanish_of_fibre' (muD k (t + 1)) (HPG k (i + 1) (t + 1)) (sigX τ σ) _ _ (rho1 τ σ.V) (isSmooth_rho1 τ hτ σ.V) (polyBall (k := k) (i + 1) s₁) (isCompact_polyBall _ _)
    (resChr ψ _ (polyBall (k := k) (i + 1) s₁)) (isOpen_resChr_ker ψ hψ i _) (fun b => ⟨cEl k i t (b : Multiplicative (Fin (i + 1) → k)).toAdd, cEl_mem i t _⟩)
    (fun b w => sigX_cEl τ σ _ w) (dEmb k i t) (Fib.dEmb_add i t) hce y _ hD0 hDs hDc hDo L hLU hLc hθ
    hL1 hL2 hL3 hU hfib f hsupp hs₁

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (h0 : eO ψ f = 0)
    (p : Mir k ((i + 1) + t + 1)) (hp : p ∉ Cl k i t),
  AvgVanish (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t)) f p := by
  intro k _ _ _ _ i t ψ hψ τ σ hτ _ f h0 p hp
  obtain ⟨h, hh, d, m, rfl⟩ := (GlobalTheory.T.mirabolic_double_coset_decomposition k i t).2 p hp
  rw [mul_assoc _ (wEl k i t)]
  have hq : qO τ σ ψ (intO f (wEl k i t * sEmb k ((i + 1) + t) m)) = 0 := by
    have hc : i + (t + 1) = (i + 1) + t := by omega
    have h1 := congrFun h0 ((castM k hc).symm m)
    have h2 : ((dpowM (i + (t + 1)) (-1 / 2) ((castM k hc).symm m) : ℂˣ) : ℂ) •
        qO τ σ ψ (intO f (wEl k i t * sEmb k _ (castM k hc ((castM k hc).symm m)))) = 0 := h1
    rw [MulEquiv.apply_symm_apply] at h2
    exact (smul_eq_zero.1 h2).resolve_left (Units.ne_zero _)
  refine avgVanish_translate _ _ _ _ f _ h _ hh ?_ (avgVanish_at ψ hψ τ σ hτ f m _ rfl hq)
  exact (Grp.mirUin_normal (k := k) ((i + 1) + t + 1)).conj_mem' _ (vEl_mem i t _) _

end GlobalTheory.CompanionTheory.BZPhiPG.LocO

end
