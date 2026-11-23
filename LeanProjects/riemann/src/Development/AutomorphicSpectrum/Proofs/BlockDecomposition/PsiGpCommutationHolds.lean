import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoFunSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirProjEqOneOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPsiMinus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingMirabolicVanishing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductTwoRepsEquivTwoBlockInduction
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjContinuousStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HGPClosedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemHGPIffParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjLeviFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjUnipotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjUnipotentSurjectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionTwistedKernelStatement

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.RgGu.PsiGP

section Tensor

variable {V₁ V Z Y : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V] [Module ℂ V] [AddCommGroup Z] [Module ℂ Z]
  [AddCommGroup Y] [Module ℂ Y]

def pair (a : V) (y : Y) : ∀ x : Bool, TwoT V Y x
  | false => a
  | true => y

def cMap (i : V₁ ≃ₗ[ℂ] V) (mk : Z →ₗ[ℂ] Y) : V₁ ⊗[ℂ] Z →ₗ[ℂ] PiTensorProduct ℂ (TwoT V Y) :=
  (Exponents.boolTensorEquiv (X := TwoT V Y)).symm.toLinearMap ∘ₗ TensorProduct.map i.toLinearMap mk

theorem bool_tprod_pair (a : V) (y : Y) :
    Exponents.boolTensorEquiv (X := TwoT V Y) (PiTensorProduct.tprod ℂ (pair a y)) = (a ⊗ₜ[ℂ] y : V ⊗[ℂ] Y) :=
  Exponents.boolTensorEquiv_tprod _

theorem cMap_tmul (i : V₁ ≃ₗ[ℂ] V) (mk : Z →ₗ[ℂ] Y) (a : V₁) (b : Z) :
    cMap i mk (a ⊗ₜ[ℂ] b) = PiTensorProduct.tprod ℂ (pair (i a) (mk b)) := by
  apply (Exponents.boolTensorEquiv (X := TwoT V Y)).injective
  rw [bool_tprod_pair]
  show (Exponents.boolTensorEquiv (X := TwoT V Y)) ((Exponents.boolTensorEquiv (X := TwoT V Y)).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem tprod_pair_smul (a : V) (d : ℂ) (y : Y) :
    PiTensorProduct.tprod ℂ (pair a (d • y)) = d • PiTensorProduct.tprod ℂ (pair a y) := by
  apply (Exponents.boolTensorEquiv (X := TwoT V Y)).injective
  rw [map_smul, bool_tprod_pair, bool_tprod_pair]
  exact TensorProduct.tmul_smul d a y

theorem cMap_surjective (i : V₁ ≃ₗ[ℂ] V) (mk : Z →ₗ[ℂ] Y) (h : Function.Surjective mk) :
    Function.Surjective (cMap i mk) :=
  (Exponents.boolTensorEquiv (X := TwoT V Y)).symm.surjective.comp (TensorProduct.map_surjective i.surjective h)

theorem cMap_eq_zero (i : V₁ ≃ₗ[ℂ] V) (mk : Z →ₗ[ℂ] Y) (h : Function.Surjective mk) (w : V₁ ⊗[ℂ] Z)
    (hw : cMap i mk w = 0) : w ∈ LinearMap.range (LinearMap.lTensor V₁ (LinearMap.ker mk).subtype) := by
  have h0 : TensorProduct.map i.toLinearMap mk w = 0 := by
    have : (Exponents.boolTensorEquiv (X := TwoT V Y)).symm (TensorProduct.map i.toLinearMap mk w) = 0 := hw
    simpa using this
  have h1 : LinearMap.lTensor V₁ mk w = 0 := by
    have e : ∀ w : V₁ ⊗[ℂ] Z, TensorProduct.map i.symm.toLinearMap LinearMap.id (TensorProduct.map i.toLinearMap mk w) =
        LinearMap.lTensor V₁ mk w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a b => simp
    rw [← e, h0, map_zero]
  have hex : Function.Exact (LinearMap.ker mk).subtype mk := LinearMap.exact_subtype_ker_map mk
  exact (lTensor_exact V₁ hex h w).1 h1

end Tensor

section Intertwine

variable {G M W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
  [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem coinv_intertwine (H U : Subgroup G) (Q : Subgroup M) (s : M →* G) (χ : M →* ℂˣ)
    (σ : Representation ℂ H W) (σ' : Representation ℂ Q W') (c : W →ₗ[ℂ] W')
    (E : (cIndSpace H σ ⧸ twKer (cInd H σ) U 1) ≃ₗ[ℂ] smoothPart (ind Q σ'))
    (hE : ∀ (f : cIndSpace H σ) (x : M), (E (Submodule.Quotient.mk f)).1.1 x = (χ x : ℂ) • c (f.1.1.1 (s x)))
    (g : M) (f : cIndSpace H σ) :
    E ((χ g : ℂ) • Submodule.Quotient.mk (cInd H σ (s g) f)) = smInd Q σ' g (E (Submodule.Quotient.mk f)) := by
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  rw [map_smul]
  show (χ g : ℂ) • (E (Submodule.Quotient.mk (cInd H σ (s g) f))).1.1 x = (E (Submodule.Quotient.mk f)).1.1 (x * g)
  rw [hE, hE, map_mul, smul_smul, Units.val_mul, mul_comm]
  show _ • c (f.1.1.1 (s x * s g)) = _ • c (f.1.1.1 (s (x * g)))
  rw [map_mul]

end Intertwine

section Concrete

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem parab_mul_KO {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) :
    ∀ g : GL n k, ∃ p ∈ parab k e, ∃ x ∈ GlobalTheory.SplitWeil.KO k n, g = p * x := by
  obtain ⟨-, -, -, -, -, -, -, -, h⟩ := GlobalTheory.SmGL.LeviInt.levi_integral_facts k α n m e
  exact h

theorem det_levi (n : ℕ) (g : GL (Fin n) k) :
    GeneralLinearGroup.det ((levi k n g : Mir k n) : GL (Fin (n + 1)) k) = GeneralLinearGroup.det g := by
  ext
  exact GlobalTheory.CompanionTheory.MirPsiPair.det_glEmbMat n _

theorem det_unip (n : ℕ) (v : Multiplicative (Fin n → k)) : GeneralLinearGroup.det (unip k n v) = 1 := by
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

theorem dpowM_levi (n : ℕ) (s : ℝ) (g : GL (Fin n) k) :
    dpowM n s (levi k n g) = dpow n s g := by
  show absPow k (s : ℂ) (GeneralLinearGroup.det ((levi k n g : Mir k n) : GL (Fin (n + 1)) k)) = absPow k (s : ℂ) _
  rw [det_levi]

theorem dpowM_of_mem (n : ℕ) (s : ℝ) (u : Mir k n) (hu : u ∈ MirUin k n) : dpowM n s u = 1 := by
  obtain ⟨v, hv⟩ := (hu : (u : GL (Fin (n + 1)) k) ∈ MirU k n)
  show absPow k (s : ℂ) (GeneralLinearGroup.det (u : GL (Fin (n + 1)) k)) = 1
  have hv' : (u : GL (Fin (n + 1)) k) = unip k n v := hv.symm
  rw [hv', det_unip, map_one]

theorem scalar_id (m j : ℕ) (a b : kˣ) :
    absPow k ((-1 / 2 : ℝ) : ℂ) (a * b) * absPow k (((((j + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) a *
        absPow k (((-((m : ℕ) : ℝ) / 2 : ℝ)) : ℂ) b =
      absPow k ((j : ℂ) / 2) a * absPow k (-(m : ℂ) / 2) b * absPow k ((-1 / 2 : ℝ) : ℂ) b := by
  have e1 : absPow k (((((j + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) = absPow k ((j : ℂ) / 2) * absPow k (1 / 2) := by
    rw [← absPow_add]
    congr 1
    push_cast
    ring
  have e2 : absPow k ((-1 / 2 : ℝ) : ℂ) = (absPow k (1 / 2))⁻¹ := by
    rw [← absPow_neg]
    congr 1
    push_cast
    ring
  have e3 : absPow k (((-((m : ℕ) : ℝ) / 2 : ℝ)) : ℂ) = absPow k (-(m : ℂ) / 2) := by
    congr 1
    push_cast
    ring
  rw [e1, e2, e3]
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, mul_inv]
  generalize absPow k (1 / 2) a = A
  generalize absPow k (1 / 2) b = B
  generalize absPow k ((j : ℂ) / 2) a = P
  generalize absPow k (-(m : ℂ) / 2) b = R
  calc A⁻¹ * B⁻¹ * (P * A) * R = (A⁻¹ * A) * (P * R * B⁻¹) := by ac_rfl
    _ = P * R * B⁻¹ := by rw [inv_mul_cancel, one_mul]

end Concrete

section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev eMJ (m j : ℕ) : (Σ x, Two (Fin m) (Fin j) x) ≃ Fin (m + j) := two (stdSum (rfl : m + j = m + j))

variable {m j : ℕ} (ρ : GRep k m) (τ : MRep k j)

abbrev Vt : Type := (ρ.tw (((j + 1 : ℕ) : ℝ) / 2)).V

abbrev Zt (m : ℕ) : Type := (mtw τ (-((m : ℕ) : ℝ) / 2)).V

abbrev sig := (extTensor (ρ.tw (((j + 1 : ℕ) : ℝ) / 2)).ρ (mtw τ (-((m : ℕ) : ℝ) / 2)).ρ).comp (gpProj k m j)

abbrev sigP : Representation ℂ (parab k (eMJ m j)) (PiTensorProduct ℂ (TwoT ρ.V (psiN τ).V)) :=
  (twist (piTensor (twoRep ρ.ρ (psiN τ).ρ)) (deltaHalf k (Two (Fin m) (Fin j)))).comp (leviProj k (eMJ m j))

abbrev mkY : τ.V →ₗ[ℂ] (psiN τ).V := (twKer τ.ρ (MirUin k j) 1).mkQ

abbrev mkZ (m : ℕ) : Zt τ m →ₗ[ℂ] (psiN τ).V := (twKer τ.ρ (MirUin k j) 1).mkQ

abbrev iV (j : ℕ) : Vt (j := j) ρ ≃ₗ[ℂ] ρ.V := LinearEquiv.refl ℂ ρ.V

abbrev cc : Vt (j := j) ρ ⊗[ℂ] Zt τ m →ₗ[ℂ] PiTensorProduct ℂ (TwoT ρ.V (psiN τ).V) := cMap (iV ρ j) (mkZ τ m)

theorem cc_tmul (a : ρ.V) (b : τ.V) : cc ρ τ ((a : Vt (j := j) ρ) ⊗ₜ[ℂ] (b : Zt τ m)) =
    PiTensorProduct.tprod ℂ (pair a (mkY τ b)) :=
  cMap_tmul _ _ _ _

theorem levi_mem_HGP (p : GL (Fin (m + j)) k) (hp : p ∈ parab k (eMJ m j)) : levi k (m + j) p ∈ MirabolicParabolic k m j :=
  (GlobalTheory.T.mem_mirabolicParabolic_iff_parabolic k m j _).2 (by rwa [GlobalTheory.CompanionTheory.BZMirAdj.mirProj_levi])

theorem hcomp (p : parab k (eMJ m j)) (w : Vt (j := j) ρ ⊗[ℂ] Zt τ m) :
    ((dpow (m + j) (-1 / 2) (p : GL (Fin (m + j)) k) : ℂˣ) : ℂ) •
        cc ρ τ (sig ρ τ ⟨levi k (m + j) p, levi_mem_HGP _ p.2⟩ w) = sigP ρ τ p (cc ρ τ w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul a b =>
    set g₁ : GL (Fin m) k := leviProj k (eMJ m j) p false with hg₁
    set g₂ : GL (Fin j) k := leviProj k (eMJ m j) p true with hg₂
    have hgp := GlobalTheory.T.gpProj_levi_formula k m j (p : GL (Fin (m + j)) k) p.2 (levi_mem_HGP _ p.2)
    have h1 : sig ρ τ ⟨levi k (m + j) p, levi_mem_HGP _ p.2⟩ (a ⊗ₜ[ℂ] b) =
        (((dpow m (((j + 1 : ℕ) : ℝ) / 2) g₁ : ℂˣ) : ℂ) • ρ.ρ g₁ a : Vt (j := j) ρ) ⊗ₜ[ℂ]
          (((dpow j (-((m : ℕ) : ℝ) / 2) g₂ : ℂˣ) : ℂ) • τ.ρ (levi k j g₂) b : Zt τ m) := by
      show extTensor _ _ (gpProj k m j _) _ = _
      rw [hgp]
      refine (extTensor_tmul _ _ _ a b).trans ?_
      show (((dpow m (((j + 1 : ℕ) : ℝ) / 2) g₁ : ℂˣ) : ℂ) • ρ.ρ g₁ a : Vt (j := j) ρ) ⊗ₜ[ℂ]
        (((dpowM j (-((m : ℕ) : ℝ) / 2) (levi k j g₂) : ℂˣ) : ℂ) • τ.ρ (levi k j g₂) b : Zt τ m) = _
      rw [dpowM_levi]
    have h2 : (fun x => twoRep ρ.ρ (psiN τ).ρ x (leviProj k (eMJ m j) p x) (pair a (mkY τ b) x)) =
        pair (ρ.ρ g₁ a) (((dpow j (-1 / 2) g₂ : ℂˣ) : ℂ) • mkY τ (τ.ρ (levi k j g₂) b)) := by
      funext x
      cases x
      · rfl
      · rfl
    have hlev : leviProj k (eMJ m j) p = leviTwo k (Fin m) (Fin j) (g₁, g₂) := by
      funext x
      cases x
      · rfl
      · rfl
    have hdet : GeneralLinearGroup.det (p : GL (Fin (m + j)) k) =
        GeneralLinearGroup.det g₁ * GeneralLinearGroup.det g₂ := by
      rw [det_parab, Fintype.prod_bool, mul_comm]
    have hs : ((dpow (m + j) (-1 / 2) (p : GL (Fin (m + j)) k) : ℂˣ) : ℂ) *
        (((dpow m (((j + 1 : ℕ) : ℝ) / 2) g₁ : ℂˣ) : ℂ) * ((dpow j (-((m : ℕ) : ℝ) / 2) g₂ : ℂˣ) : ℂ)) =
        ((deltaHalf k (Two (Fin m) (Fin j)) (leviProj k (eMJ m j) p) : ℂˣ) : ℂ) * ((dpow j (-1 / 2) g₂ : ℂˣ) : ℂ) := by
      rw [hlev, deltaHalf_two, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
      congr 1
      have := scalar_id (k := k) m j (GeneralLinearGroup.det g₁) (GeneralLinearGroup.det g₂)
      simp only [dpow, detChar_apply, hdet, Fintype.card_fin]
      rw [← mul_assoc]
      exact this
    have h3 : cc ρ τ (sig ρ τ ⟨levi k (m + j) p, levi_mem_HGP _ p.2⟩ (a ⊗ₜ[ℂ] b)) =
        (((dpow m (((j + 1 : ℕ) : ℝ) / 2) g₁ : ℂˣ) : ℂ) * ((dpow j (-((m : ℕ) : ℝ) / 2) g₂ : ℂˣ) : ℂ)) •
          PiTensorProduct.tprod ℂ (pair (ρ.ρ g₁ a) (mkY τ (τ.ρ (levi k j g₂) b))) := by
      rw [h1, TensorProduct.smul_tmul_smul]
      exact (LinearMap.map_smul (cc ρ τ) _ _).trans (congrArg _ (cc_tmul ρ τ _ _))
    have h4 : cc ρ τ (a ⊗ₜ[ℂ] b) = PiTensorProduct.tprod ℂ (pair a (mkY τ b)) := cc_tmul ρ τ a b
    rw [h3, h4, smul_smul, hs, ← smul_smul]
    show _ = ((deltaHalf k (Two (Fin m) (Fin j)) (leviProj k (eMJ m j) p) : ℂˣ) : ℂ) •
      piTensor (twoRep ρ.ρ (psiN τ).ρ) (leviProj k (eMJ m j) p) (PiTensorProduct.tprod ℂ (pair a (mkY τ b)))
    rw [piTensor_tprod]
    exact congrArg _ ((tprod_pair_smul _ _ _).symm.trans (congrArg (PiTensorProduct.tprod ℂ) h2.symm))

theorem mkZ_surjective : Function.Surjective (mkZ τ m) :=
  Submodule.mkQ_surjective (twKer τ.ρ (MirUin k j) 1)

theorem mkY_unip (u : Mir k j) (hu : u ∈ MirUin k j) (b : τ.V) : mkY τ (τ.ρ u b) = mkY τ b := by
  refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨u, hu⟩, b, ?_⟩)
  simp

theorem sig_tmul (v : MirabolicParabolic k m j) (a : Vt (j := j) ρ) (b : Zt τ m) (hv : (gpProj k m j v).1 = 1)
    (hv2 : (gpProj k m j v).2 ∈ MirUin k j) :
    sig ρ τ v (a ⊗ₜ[ℂ] b) = a ⊗ₜ[ℂ] (τ.ρ (gpProj k m j v).2 b : Zt τ m) := by
  refine (extTensor_tmul _ _ _ a b).trans ?_
  rw [hv]
  show (((dpow m (((j + 1 : ℕ) : ℝ) / 2) 1 : ℂˣ) : ℂ) • ρ.ρ 1 a : Vt (j := j) ρ) ⊗ₜ[ℂ]
    (((dpowM j (-((m : ℕ) : ℝ) / 2) (gpProj k m j v).2 : ℂˣ) : ℂ) • τ.ρ (gpProj k m j v).2 b : Zt τ m) = _
  rw [dpowM_of_mem _ _ _ hv2, map_one, map_one]
  simp
  rfl

theorem tmul_mem_twKer (a : Vt (j := j) ρ) (t : Zt τ m) (ht : t ∈ twKer τ.ρ (MirUin k j) 1) :
    a ⊗ₜ[ℂ] t ∈ twKer (sig ρ τ) ((MirUin k (m + j)).subgroupOf (MirabolicParabolic k m j)) 1 := by
  refine Submodule.span_induction (p := fun t _ => a ⊗ₜ[ℂ] (t : Zt τ m) ∈ twKer (sig ρ τ) ((MirUin k (m + j)).subgroupOf (MirabolicParabolic k m j)) 1)
    ?_ ?_ ?_ ?_ ht
  · rintro _ ⟨n, b, rfl⟩
    obtain ⟨v, hv, hv2⟩ := GlobalTheory.T.gpProj_unipotent_surjective k m j (n : Mir k j) n.2
    refine Submodule.subset_span ⟨⟨v, hv⟩, a ⊗ₜ[ℂ] b, ?_⟩
    have h1 := sig_tmul ρ τ v a b (by rw [hv2]) (by rw [hv2]; exact n.2)
    rw [hv2] at h1
    show _ = sig ρ τ v _ - _
    rw [h1]
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    exact TensorProduct.tmul_sub _ _ _
  · show a ⊗ₜ[ℂ] (0 : Zt τ m) ∈ _
    rw [TensorProduct.tmul_zero]
    exact zero_mem _
  · intro x y _ _ hx hy
    show a ⊗ₜ[ℂ] ((x : Zt τ m) + (y : Zt τ m)) ∈ _
    rw [TensorProduct.tmul_add]
    exact add_mem hx hy
  · intro c x _ hx
    show a ⊗ₜ[ℂ] (c • (x : Zt τ m)) ∈ _
    rw [TensorProduct.tmul_smul]
    exact Submodule.smul_mem _ _ hx

theorem hck (w : Vt (j := j) ρ ⊗[ℂ] Zt τ m) :
    cc ρ τ w = 0 ↔ w ∈ twKer (sig ρ τ) ((MirUin k (m + j)).subgroupOf (MirabolicParabolic k m j)) 1 := by
  constructor
  · intro hw
    obtain ⟨y, rfl⟩ := cMap_eq_zero (iV ρ j) (mkZ τ m) (mkZ_surjective τ) w hw
    clear hw
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    | tmul a t =>
      exact tmul_mem_twKer ρ τ a _ ((Submodule.Quotient.mk_eq_zero _).1 t.2)
  · intro hw
    have hle : twKer (sig ρ τ) ((MirUin k (m + j)).subgroupOf (MirabolicParabolic k m j)) 1 ≤ LinearMap.ker (cc ρ τ) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, w, rfl⟩
      have hu : ((u : MirabolicParabolic k m j) : Mir k (m + j)) ∈ MirUin k (m + j) := u.2
      obtain ⟨h1, h2⟩ := GlobalTheory.T.gpProj_unipotent k m j u hu
      have key : ∀ w, cc ρ τ (sig ρ τ (u : MirabolicParabolic k m j) w) = cc ρ τ w := by
        intro w
        induction w using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul a b =>
          rw [sig_tmul ρ τ _ a b h1 h2]
          exact (cc_tmul ρ τ _ _).trans ((congrArg (fun y => PiTensorProduct.tprod ℂ (pair (V := ρ.V) a y)) (mkY_unip τ _ h2 b)).trans
            (cc_tmul ρ τ a b).symm)
      show cc ρ τ (sig ρ τ (u : MirabolicParabolic k m j) w - (((1 : ((MirUin k (m + j)).subgroupOf (MirabolicParabolic k m j)) →* ℂˣ) u : ℂˣ) : ℂ) • w) = 0
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
      exact sub_eq_zero.2 (key w)
    exact hle hw

theorem isOpen_dpow_ker (n : ℕ) (s : ℝ) : IsOpen ((dpow (k := k) n s).ker : Set (GL (Fin n) k)) :=
  (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar

theorem isSmooth_sig (hρ : IsSmooth ρ.ρ) (hτ : IsSmooth τ.ρ) : IsSmooth (sig ρ τ) := by
  refine isSmooth_comp (isSmooth_extTensor (isSmooth_twist hρ (isOpen_dpow_ker _ _)) ?_) _ (GlobalTheory.T.gpProj_continuous k m j)
  exact isSmooth_twist hτ (IsSmoothChar.comp (χ := dpow (j + 1) (-((m : ℕ) : ℝ) / 2)) (isOpen_dpow_ker _ _) (Mir k j).subtype
    continuous_subtype_val)

theorem exE (hρ : IsSmooth ρ.ρ) (hτ : IsSmooth τ.ρ) :
    ∃ E : (cIndSpace (MirabolicParabolic k m j) (sig ρ τ) ⧸ twKer (cInd (MirabolicParabolic k m j) (sig ρ τ)) (MirUin k (m + j)) 1) ≃ₗ[ℂ]
        smoothPart (ind (parab k (eMJ m j)) (sigP ρ τ)),
      ∀ (f : cIndSpace (MirabolicParabolic k m j) (sig ρ τ)) (x : GL (Fin (m + j)) k), (E (Submodule.Quotient.mk f)).1.1 x =
        ((dpow (m + j) (-1 / 2) x : ℂˣ) : ℂ) • cc ρ τ (f.1.1.1 (levi k (m + j) x)) := by
  have hPK := parab_mul_KO (k := k) (eMJ m j)
  have hker : ∀ g, mirabolicProjection k (m + j) g = 1 ↔ g ∈ MirUin k (m + j) := fun g =>
    ⟨GlobalTheory.CompanionTheory.BZMirAdj.mem_of_mirProj_eq_one k _ g, GlobalTheory.CompanionTheory.BZMirAdj.mirProj_eq_one_of_mem k _ g⟩
  have hUH : MirUin k (m + j) ≤ MirabolicParabolic k m j := fun g hg => by
    refine (GlobalTheory.T.mem_mirabolicParabolic_iff_parabolic k m j g).2 ?_
    rw [GlobalTheory.CompanionTheory.BZMirAdj.mirProj_eq_one_of_mem k _ g hg]
    exact one_mem _
  have hN : (MirUin k (m + j)).Normal := by
    have : MirUin k (m + j) = (mirabolicProjection k (m + j)).ker := by
      ext g
      rw [MonoidHom.mem_ker, hker]
    rw [this]
    infer_instance
  exact GlobalTheory.CompanionTheory.CIndCoinv.coinv_equiv (MirabolicParabolic k m j) (MirUin k (m + j)) (parab k (eMJ m j)) (levi k (m + j))
    (mirabolicProjection k (m + j)) (GlobalTheory.T.isClosed_mirabolicParabolic k m j) (GlobalTheory.CompanionTheory.BZMirOnto.exists_compactOpen k (m + j))
    (GlobalTheory.CompanionTheory.BZMirFun.continuous_levi k (m + j)) (GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k (m + j))
    (GlobalTheory.CompanionTheory.BZMirAdj.mirProj_levi k (m + j)) hker hUH (fun g hg => (GlobalTheory.T.mem_mirabolicParabolic_iff_parabolic k m j g).1 hg)
    (fun p hp => levi_mem_HGP p hp) (GlobalTheory.SplitWeil.KO k (Fin (m + j))) GlobalTheory.SplitFlip.isCompact_KO hPK
    (dpow (m + j) (-1 / 2)) (isOpen_dpow_ker _ _) (sig ρ τ) (isSmooth_sig ρ τ hρ hτ) (sigP ρ τ)
    (cc ρ τ) (cMap_surjective _ _ (mkZ_surjective τ)) (hck ρ τ) (hcomp ρ τ)
    (GlobalTheory.T.compact_induction_twisted_kernel _ _ hUH (GlobalTheory.CompanionTheory.BZMirOnto.exists_compactOpen k (m + j)) _ (isSmooth_sig ρ τ hρ hτ))

theorem psiMinus_cInd_equiv_smInd (hρ : IsSmooth ρ.ρ) (hτ : IsSmooth τ.ρ) :
    Nonempty ((twist (psiMinus k (cInd (MirabolicParabolic k m j) (sig ρ τ))) (dpow (m + j) (-1 / 2))).Equiv
      (smInd (parab k (eMJ m j)) (sigP ρ τ))) := by
  refine (exE ρ τ hρ hτ).elim fun E hE => ?_
  have key := coinv_intertwine _ _ _ (levi k (m + j)) (dpow (m + j) (-1 / 2)) _ _ _ E hE
  refine ⟨Representation.Equiv.mk E ?_⟩
  intro g
  refine LinearMap.ext fun y => ?_
  refine Submodule.Quotient.induction_on _ y fun f => ?_
  have h1 : twist (psiMinus k (cInd (MirabolicParabolic k m j) (sig ρ τ))) (dpow (m + j) (-1 / 2)) g (Submodule.Quotient.mk f) =
      ((dpow (m + j) (-1 / 2) g : ℂˣ) : ℂ) • Submodule.Quotient.mk (cInd (MirabolicParabolic k m j) (sig ρ τ) (levi k (m + j) g) f) := rfl
  have h2 : E (twist (psiMinus k (cInd (MirabolicParabolic k m j) (sig ρ τ))) (dpow (m + j) (-1 / 2)) g (Submodule.Quotient.mk f)) =
      smInd (parab k (eMJ m j)) (sigP ρ τ) g (E (Submodule.Quotient.mk f)) := (congrArg E h1).trans (key g f)
  exact h2

end Main

theorem psiGP : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PsiGP k := by
  intro k _ _ _ _ m j ρ τ hρ hτ
  exact psiMinus_cInd_equiv_smInd ρ τ hρ hτ

end GlobalTheory.CompanionTheory.RgGu.PsiGP
