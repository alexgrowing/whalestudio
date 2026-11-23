import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingMirabolicVanishing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductTwoRepsEquivTwoBlockInduction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.Norm

section Generic

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def twistEquivOf {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (χ : G →* ℂˣ) :
    (twist ρ χ).Equiv (twist σ χ) :=
  .mk φ.toLinearEquiv fun g => LinearMap.ext fun v => by
    show φ.toLinearEquiv ((χ g : ℂ) • ρ g v) = (χ g : ℂ) • σ g (φ.toLinearEquiv v)
    rw [map_smul]
    exact congrArg _ (LinearMap.congr_fun (φ.isIntertwining' g) v)

def pairT (a : V) (y : W) : ∀ x : Bool, TwoT V W x
  | false => a
  | true => y

theorem bool_tprod_pairT (a : V) (y : W) :
    Exponents.boolTensorEquiv (X := TwoT V W) (PiTensorProduct.tprod ℂ (pairT a y)) = (a ⊗ₜ[ℂ] y : V ⊗[ℂ] W) :=
  Exponents.boolTensorEquiv_tprod _

theorem tprod_pairT_smul (a : V) (c d : ℂ) (y : W) :
    PiTensorProduct.tprod ℂ (pairT (c • a) (d • y)) = (c * d) • PiTensorProduct.tprod ℂ (pairT a y) := by
  apply (Exponents.boolTensorEquiv (X := TwoT V W)).injective
  rw [map_smul, bool_tprod_pairT, bool_tprod_pairT]
  exact TensorProduct.smul_tmul_smul c d a y

end Generic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Chars

theorem det_levi' (n : ℕ) (g : GL (Fin n) k) :
    GeneralLinearGroup.det ((levi k n g : Mir k n) : GL (Fin (n + 1)) k) = GeneralLinearGroup.det g := by
  ext
  exact GlobalTheory.CompanionTheory.MirPsiPair.det_glEmbMat n _

theorem det_unip' (n : ℕ) (v : Multiplicative (Fin n → k)) : GeneralLinearGroup.det (unip k n v) = 1 := by
  ext
  show (1 + colMat k n v.toAdd : Matrix (Fin (n + 1)) (Fin (n + 1)) k).det = 1
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    by_cases hi : i = Fin.last n
    · subst hi
      simp [colMat]
    · simp [colMat, hi]
  · intro a b hab
    have hb : b ≠ Fin.last n := fun h => by
      subst h
      exact absurd (Fin.le_last a) (not_le.2 hab)
    have hne : a ≠ b := fun h => by
      subst h
      exact lt_irrefl _ hab
    simp [colMat, hb, Matrix.one_apply, hne]

theorem dpowM_levi' (n : ℕ) (s : ℝ) (g : GL (Fin n) k) : dpowM n s (levi k n g) = dpow n s g := by
  show absPow k (s : ℂ) (GeneralLinearGroup.det ((levi k n g : Mir k n) : GL (Fin (n + 1)) k)) = absPow k (s : ℂ) _
  rw [det_levi']

theorem dpowM_of_mem' (n : ℕ) (s : ℝ) (u : Mir k n) (hu : u ∈ MirUin k n) : dpowM n s u = 1 := by
  obtain ⟨v, hv⟩ := (hu : (u : GL (Fin (n + 1)) k) ∈ MirU k n)
  show absPow k (s : ℂ) (GeneralLinearGroup.det (u : GL (Fin (n + 1)) k)) = 1
  have hv' : (u : GL (Fin (n + 1)) k) = unip k n v := hv.symm
  rw [hv', det_unip', map_one]

theorem scalar_sum (i t : ℕ) (a b : kˣ) :
    absPow k ((-1 / 2 : ℝ) : ℂ) (a * b) * (absPow k 1 b * (absPow k ((((t : ℕ) : ℝ) / 2 : ℝ) : ℂ) a *
        absPow k ((-((i + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) b)) =
      absPow k ((t : ℂ) / 2) a * absPow k (-(i : ℂ) / 2) b * absPow k ((-1 / 2 : ℝ) : ℂ) a := by
  have e0 : absPow k 1 = absPow k (1 / 2) * absPow k (1 / 2) := by
    rw [← absPow_add]
    congr 1
    ring
  have e1 : absPow k ((-((i + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) = absPow k (-(i : ℂ) / 2) * (absPow k (1 / 2))⁻¹ := by
    rw [← absPow_neg, ← absPow_add]
    congr 1
    push_cast
    ring
  have e2 : absPow k ((-1 / 2 : ℝ) : ℂ) = (absPow k (1 / 2))⁻¹ := by
    rw [← absPow_neg]
    congr 1
    push_cast
    ring
  have e3 : absPow k ((((t : ℕ) : ℝ) / 2 : ℝ) : ℂ) = absPow k ((t : ℂ) / 2) := by
    congr 1
    push_cast
    ring
  rw [e0, e1, e2, e3]
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, mul_inv]
  generalize absPow k (1 / 2) a = A
  generalize absPow k (1 / 2) b = B
  generalize absPow k ((t : ℂ) / 2) a = T
  generalize absPow k (-(i : ℂ) / 2) b = R
  calc A⁻¹ * B⁻¹ * (B * B * (T * (R * B⁻¹))) = (B⁻¹ * B) * (B * B⁻¹) * (T * R * A⁻¹) := by ac_rfl
    _ = T * R * A⁻¹ := by rw [inv_mul_cancel, mul_inv_cancel, one_mul, one_mul]

theorem isSmoothChar_dpow (n : ℕ) (s : ℝ) : IsSmoothChar (dpow (k := k) n s) :=
  (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar

theorem twKer_twist_dpowM {V : Type} [AddCommGroup V] [Module ℂ V] (n : ℕ) (τ : Representation ℂ (Mir k n) V) (s : ℝ) :
    twKer (twist τ (dpowM n s)) (MirUin k n) 1 = twKer τ (MirUin k n) 1 := by
  unfold twKer
  congr 1
  ext w
  refine exists_congr fun u => exists_congr fun v => ?_
  have hu : dpowM n s (u : Mir k n) = 1 := dpowM_of_mem' n s u.1 u.2
  rw [twist_apply, hu, Units.val_one, one_smul]

end Chars

section Main

variable {i t : ℕ} (τ : MRep k i) (σ : GRep k t)

abbrev eIT (i t : ℕ) : (Σ x, Two (Fin i) (Fin t) x) ≃ Fin (i + t) := two (stdSum (rfl : i + t = i + t))

abbrev sigT : Representation ℂ (Qp k i t) (PiTensorProduct ℂ (TwoT (psiN τ).V σ.V)) :=
  (twist (piTensor (twoRep (psiN τ).ρ σ.ρ)) (deltaHalf k (Two (Fin i) (Fin t)))).comp (leviProj k (eIT i t))

abbrev mkT (s : ℝ) : τ.V →ₗ[ℂ] Jacquet (mtw τ s).ρ (MirUin k i) := (twKer (mtw τ s).ρ (MirUin k i) 1).mkQ

abbrev mkY : τ.V →ₗ[ℂ] (psiN τ).V := (twKer τ.ρ (MirUin k i) 1).mkQ

def Lq (s : ℝ) : (Jacquet (mtw τ s).ρ (MirUin k i) ⊗[ℂ] σ.V) ≃ₗ[ℂ] PiTensorProduct ℂ (TwoT (psiN τ).V σ.V) :=
  (TensorProduct.congr (Submodule.quotEquivOfEq _ _ (twKer_twist_dpowM i τ.ρ s)) (LinearEquiv.refl ℂ σ.V)).trans
    (Exponents.boolTensorEquiv (X := TwoT (psiN τ).V σ.V)).symm

theorem Lq_tmul (s : ℝ) (y : τ.V) (w : σ.V) :
    Lq τ σ s (mkT τ s y ⊗ₜ[ℂ] w) = PiTensorProduct.tprod ℂ (pairT (mkY τ y) w) := by
  apply (Exponents.boolTensorEquiv (X := TwoT (psiN τ).V σ.V)).injective
  rw [bool_tprod_pairT]
  refine (LinearEquiv.apply_symm_apply (Exponents.boolTensorEquiv (X := TwoT (psiN τ).V σ.V)) _).trans ?_
  rfl

theorem qRep_tmul (s₁ s₂ : ℝ) (q : Qp k i t) (y : τ.V) (w : σ.V) :
    qRep (mtw τ s₁).ρ (σ.tw s₂).ρ q (mkT τ s₁ y ⊗ₜ[ℂ] w) =
      ((absPow k 1 (GeneralLinearGroup.det (qBlocks k i t q).2) : ℂˣ) : ℂ) •
        (mkT τ s₁ (((dpow i s₁ (qBlocks k i t q).1 : ℂˣ) : ℂ) • τ.ρ (levi k i (qBlocks k i t q).1) y) ⊗ₜ[ℂ]
          (((dpow t s₂ (qBlocks k i t q).2 : ℂˣ) : ℂ) • σ.ρ (qBlocks k i t q).2 w : σ.V)) := by
  have h : extTensor (psiMinus k (mtw τ s₁).ρ) (σ.tw s₂).ρ (qBlocks k i t q) (mkT τ s₁ y ⊗ₜ[ℂ] w) =
      mkT τ s₁ (((dpow i s₁ (qBlocks k i t q).1 : ℂˣ) : ℂ) • τ.ρ (levi k i (qBlocks k i t q).1) y) ⊗ₜ[ℂ]
          (((dpow t s₂ (qBlocks k i t q).2 : ℂˣ) : ℂ) • σ.ρ (qBlocks k i t q).2 w : σ.V) := by
    refine (extTensor_tmul _ _ _ _ _).trans ?_
    show mkT τ s₁ (((dpowM i s₁ (levi k i (qBlocks k i t q).1) : ℂˣ) : ℂ) • τ.ρ (levi k i (qBlocks k i t q).1) y) ⊗ₜ[ℂ] _ = _
    rw [dpowM_levi']
    rfl
  exact congrArg (fun z => ((absPow k 1 (GeneralLinearGroup.det (qBlocks k i t q).2) : ℂˣ) : ℂ) • z) h

theorem Lq_tmul_smul (s : ℝ) (c d : ℂ) (y : τ.V) (w : σ.V) :
    Lq τ σ s (mkT τ s (c • y) ⊗ₜ[ℂ] (d • w : σ.V)) = (c * d) • PiTensorProduct.tprod ℂ (pairT (mkY τ y) w) := by
  rw [Lq_tmul, map_smul, tprod_pairT_smul]

theorem scalar_q (i t : ℕ) (q : Qp k i t) :
    ((dpow (i + t) (-1 / 2) (q : GL (Fin (i + t)) k) : ℂˣ) : ℂ) *
        (((absPow k 1 (GeneralLinearGroup.det (qBlocks k i t q).2) : ℂˣ) : ℂ) *
          (((dpow i (((t : ℕ) : ℝ) / 2) (qBlocks k i t q).1 : ℂˣ) : ℂ) *
            ((dpow t (-((i + 1 : ℕ) : ℝ) / 2) (qBlocks k i t q).2 : ℂˣ) : ℂ))) =
      ((deltaHalf k (Two (Fin i) (Fin t)) (leviProj k (eIT i t) q) : ℂˣ) : ℂ) *
        ((dpow i (-1 / 2) (qBlocks k i t q).1 : ℂˣ) : ℂ) := by
  have hlev : leviProj k (eIT i t) q = leviTwo k (Fin i) (Fin t) (qBlocks k i t q) := by
    funext x
    cases x
    · rfl
    · rfl
  have hdet : GeneralLinearGroup.det (q : GL (Fin (i + t)) k) =
      GeneralLinearGroup.det (qBlocks k i t q).1 * GeneralLinearGroup.det (qBlocks k i t q).2 := by
    rw [det_parab, Fintype.prod_bool, mul_comm]
    rfl
  rw [hlev, deltaHalf_two]
  simp only [← Units.val_mul]
  congr 1
  have := scalar_sum (k := k) i t (GeneralLinearGroup.det (qBlocks k i t q).1)
    (GeneralLinearGroup.det (qBlocks k i t q).2)
  simp only [dpow, detChar_apply, hdet, Fintype.card_fin]
  exact this

def qEnd (s₁ s₂ : ℝ) (q : Qp k i t) :
    (Jacquet (mtw τ s₁).ρ (MirUin k i) ⊗[ℂ] σ.V) →ₗ[ℂ] (Jacquet (mtw τ s₁).ρ (MirUin k i) ⊗[ℂ] σ.V) :=
  qRep (mtw τ s₁).ρ (σ.tw s₂).ρ q

theorem sigT_Lq (q : Qp k i t) (v : Jacquet (mtw τ (((t : ℕ) : ℝ) / 2)).ρ (MirUin k i) ⊗[ℂ] σ.V) :
    sigT τ σ q (Lq τ σ (((t : ℕ) : ℝ) / 2) v) =
      ((dpow (i + t) (-1 / 2) (q : GL (Fin (i + t)) k) : ℂˣ) : ℂ) •
        Lq τ σ (((t : ℕ) : ℝ) / 2) (qEnd τ σ (((t : ℕ) : ℝ) / 2) (-((i + 1 : ℕ) : ℝ) / 2) q v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul x w =>
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h2 : (fun x => twoRep (psiN τ).ρ σ.ρ x (leviProj k (eIT i t) q x) (pairT (mkY τ y) w x)) =
        pairT (((dpow i (-1 / 2) (qBlocks k i t q).1 : ℂˣ) : ℂ) • mkY τ (τ.ρ (levi k i (qBlocks k i t q).1) y))
          ((1 : ℂ) • σ.ρ (qBlocks k i t q).2 w) := by
      funext x
      cases x
      · rfl
      · exact (one_smul ℂ _).symm
    have hL : sigT τ σ q (PiTensorProduct.tprod ℂ (pairT (mkY τ y) w)) =
        ((deltaHalf k (Two (Fin i) (Fin t)) (leviProj k (eIT i t) q) : ℂˣ) : ℂ) •
          (((dpow i (-1 / 2) (qBlocks k i t q).1 : ℂˣ) : ℂ) * 1) •
            PiTensorProduct.tprod ℂ (pairT (mkY τ (τ.ρ (levi k i (qBlocks k i t q).1) y)) (σ.ρ (qBlocks k i t q).2 w)) := by
      show ((deltaHalf k (Two (Fin i) (Fin t)) (leviProj k (eIT i t) q) : ℂˣ) : ℂ) •
        piTensor (twoRep (psiN τ).ρ σ.ρ) (leviProj k (eIT i t) q) (PiTensorProduct.tprod ℂ (pairT (mkY τ y) w)) = _
      rw [piTensor_tprod]
      exact congrArg _ ((congrArg (PiTensorProduct.tprod ℂ) h2).trans (tprod_pairT_smul _ _ _ _))
    have hR := qRep_tmul τ σ (((t : ℕ) : ℝ) / 2) (-((i + 1 : ℕ) : ℝ) / 2) q y w
    refine (congrArg (sigT τ σ q) (Lq_tmul τ σ _ y w)).trans (hL.trans ?_)
    refine Eq.trans ?_ (congrArg (fun z => ((dpow (i + t) (-1 / 2) (q : GL (Fin (i + t)) k) : ℂˣ) : ℂ) • Lq τ σ (((t : ℕ) : ℝ) / 2) z) hR.symm)
    show _ = ((dpow (i + t) (-1 / 2) (q : GL (Fin (i + t)) k) : ℂˣ) : ℂ) • Lq τ σ (((t : ℕ) : ℝ) / 2) (_ • _)
    rw [map_smul, Lq_tmul_smul, smul_smul, smul_smul, smul_smul, mul_one]
    congr 1
    rw [← scalar_q i t q]
    ring

end Main

theorem psiN_prodPGn_of_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k i) (σ : GRep k t), IsSmooth τ.ρ → IsSmooth σ.ρ → Nonempty ((psiMinus k (prodPGn τ σ).ρ).Equiv (smInd (Qp k i t) (qRep (mtw τ (((t : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ))) → GIso (psiN (prodPGn τ σ)) ((psiN τ).prod σ) := by
  intro k _ _ _ _ i t τ σ _ _ hE
  obtain ⟨E⟩ := hE
  exact ⟨(twistEquivOf E (dpow (i + t) (-1 / 2))).trans
    (GlobalTheory.LocGL.smIndTwistEquiv le_rfl le_rfl (isSmoothChar_dpow _ _) (Lq τ σ _) fun q v => sigT_Lq τ σ q v)⟩

end GlobalTheory.CompanionTheory.BZPsiPG.Norm

end
