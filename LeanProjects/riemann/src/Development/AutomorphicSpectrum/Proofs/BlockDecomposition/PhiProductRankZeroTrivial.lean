import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemHGPIffParabolic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjUnipotent

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.PhiGpZero

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mir_zero_eq_one (p : Mir k 0) : p = 1 := by
  have hp := (mem_Mir_iff k (p : GL (Fin 1) k)).1 p.2
  apply Subtype.ext
  apply Units.ext
  ext a b
  obtain rfl : a = Fin.last 0 := Fin.ext (by simp)
  obtain rfl : b = Fin.last 0 := Fin.ext (by simp)
  have := congrFun hp (Fin.last 0)
  simpa [eLast] using this

theorem mirProj_of_mem (n : ℕ) (u : Mir k n) (hu : u ∈ MirUin k n) : mirabolicProjection k n u = 1 := by
  apply Units.ext
  ext a b
  show ((u : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.castSucc b) = _
  rw [GlobalTheory.CompanionTheory.GpUnip.mirUin_entry k n u hu _ _ (Fin.castSucc_ne_last b)]
  simp [one_apply]

theorem conj_mem (n : ℕ) (g u : Mir k n) (hu : u ∈ MirUin k n) : g * u * g⁻¹ ∈ MirUin k n := by
  apply GlobalTheory.CompanionTheory.BZMirAdj.mem_of_mirProj_eq_one
  rw [map_mul, map_mul, mirProj_of_mem n u hu, mul_one, map_inv, mul_inv_cancel]

theorem mem_mirabolicParabolic_zero (m : ℕ) (g : Mir k (m + 1 + 0)) : g ∈ MirabolicParabolic k (m + 1) 0 := by
  rw [GlobalTheory.CompanionTheory.GPMem.mem_mirabolicParabolic_iff_mirabolicProj_mem_parabolic, mem_parab_two]
  intro b
  exact b.elim0

theorem cInd_apply_of_conj {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (σ : Representation ℂ H W) (u : G)
    (hu : ∀ g : G, ∃ h : g * u * g⁻¹ ∈ H, σ ⟨_, h⟩ = 1) (f : cIndSpace H σ) : cInd H σ u f = f := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext g
  show f.1.1.1 (g * u) = f.1.1.1 g
  obtain ⟨h, hσ⟩ := hu g
  have hf : f.1.1.1 (g * u * g⁻¹ * g) = σ ⟨_, h⟩ (f.1.1.1 g) := f.1.1.2 ⟨_, h⟩ g
  have e : (g * u * g⁻¹) * g = g * u := by group
  rw [e, hσ] at hf
  exact hf

theorem prodGP_unipotent_apply {m : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ₁ : Representation ℂ (GL (Fin (m + 1)) k) V) (τ₁ : Representation ℂ (Mir k 0) W)
    (u : Mir k (m + 1 + 0)) (hu : u ∈ MirUin k (m + 1 + 0))
    (f : cIndSpace (MirabolicParabolic k (m + 1) 0) ((extTensor ρ₁ τ₁).comp (gpProj k (m + 1) 0))) :
    prodGP ρ₁ τ₁ u f = f := by
  refine cInd_apply_of_conj _ _ u (fun g => ⟨mem_mirabolicParabolic_zero m _, ?_⟩) f
  have hc := conj_mem (m + 1 + 0) g u hu
  have hp : gpProj k (m + 1) 0 ⟨_, mem_mirabolicParabolic_zero m (g * u * g⁻¹)⟩ = 1 :=
    Prod.ext (GlobalTheory.CompanionTheory.GpUnip.gpProj_unip k (m + 1) 0 ⟨_, mem_mirabolicParabolic_zero m _⟩ hc).1 (mir_zero_eq_one _)
  show (extTensor ρ₁ τ₁) (gpProj k (m + 1) 0 ⟨_, mem_mirabolicParabolic_zero m (g * u * g⁻¹)⟩) = 1
  rw [hp, map_one]

theorem exists_mirChar_ne (ψ : AddChar k Circle) (hψ : ψ ≠ 1) (n : ℕ) :
    ∃ u : MirUin k (n + 1), mirChar k ψ n u ≠ 1 := by
  obtain ⟨x, hx⟩ := (AddChar.ne_one_iff).1 hψ
  let w : Multiplicative (Fin (n + 1) → k) := Multiplicative.ofAdd (Pi.single (Fin.last n) x)
  let u : MirUin k (n + 1) := ⟨⟨unip k (n + 1) w, MirU_le_Mir k (n + 1) ⟨w, rfl⟩⟩, ⟨w, rfl⟩⟩
  refine ⟨u, ?_⟩
  rw [mirChar_eq k ψ n u w rfl]
  intro h
  apply hx
  have h2 : Circle.toUnits (ψ x) = 1 := by simpa [w] using h
  have h3 : ((Circle.toUnits (ψ x) : ℂˣ) : ℂ) = 1 := by rw [h2]; rfl
  exact Circle.ext (by simpa using h3)

theorem phiN_subsingleton_of_fixed (ψ : AddChar k Circle) {n : ℕ} (X : MRep k (n + 1)) (u : MirUin k (n + 1))
    (hθ : mirChar k ψ n u ≠ 1) (hu : ∀ v, X.ρ (u : Mir k (n + 1)) v = v) : Subsingleton (phiN ψ X).V := by
  have hne : (1 : ℂ) - ((mirChar k ψ n u : ℂˣ) : ℂ) ≠ 0 := by
    intro h
    apply hθ
    apply Units.ext
    rw [Units.val_one]
    exact (sub_eq_zero.1 h).symm
  have top : twKer X.ρ (MirUin k (n + 1)) (mirChar k ψ n) = ⊤ := by
    refine eq_top_iff.2 fun v _ => ?_
    have hmem : X.ρ (u : Mir k (n + 1)) v - ((mirChar k ψ n u : ℂˣ) : ℂ) • v ∈
        twKer X.ρ (MirUin k (n + 1)) (mirChar k ψ n) := Submodule.subset_span ⟨u, v, rfl⟩
    rw [hu] at hmem
    have e : v = ((1 : ℂ) - ((mirChar k ψ n u : ℂˣ) : ℂ))⁻¹ • (v - ((mirChar k ψ n u : ℂˣ) : ℂ) • v) := by
      conv_rhs => rw [show v - ((mirChar k ψ n u : ℂˣ) : ℂ) • v = ((1 : ℂ) - ((mirChar k ψ n u : ℂˣ) : ℂ)) • v by
        rw [sub_smul, one_smul]]
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ hmem
  show Subsingleton (X.V ⧸ twKer X.ρ (MirUin k (n + 1)) (mirChar k ψ n))
  refine ⟨fun a b => ?_⟩
  induction a using Submodule.Quotient.induction_on with
  | H a =>
    induction b using Submodule.Quotient.induction_on with
    | H b => exact (Submodule.Quotient.eq _).2 (top ▸ Submodule.mem_top)

theorem phiN_prodGPn_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (ρ : GRep k (m + 1)) (τ : MRep k 0)
    (h : (m + 1) + 0 = (m + 0) + 1), IsSmooth ρ.ρ → IsSmooth τ.ρ →
    Subsingleton (phiN ψ (mcast h (prodGPn ρ τ))).V := by
  intro k _ _ _ _ ψ _ hψ m ρ τ h _ _
  obtain ⟨u, hu⟩ := exists_mirChar_ne ψ hψ (m + 0)
  refine phiN_subsingleton_of_fixed ψ (mcast h (prodGPn ρ τ)) u hu ?_
  intro v
  exact prodGP_unipotent_apply _ _ _ u.2 v

end GlobalTheory.CompanionTheory.PhiGpZero

end
