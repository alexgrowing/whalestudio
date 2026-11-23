import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FrameStab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

local infixl:70 " ⋆ₘ " => HMul.hMul

theorem incA_injective (D : D7) : Function.Injective (incA D) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem mt_mul (W : HSp D) (g h : GA D W) : Formalism.L2.Theta.mt W (g * h) = Formalism.L2.Theta.mt W g * Formalism.L2.Theta.mt W h := by
  simp [Formalism.L2.Theta.mt]

theorem mt_inv_mul (W : HSp D) (g : GA D W) : Formalism.L2.Theta.mt W g⁻¹ * Formalism.L2.Theta.mt W g = 1 := by
  rw [← mt_mul]; simp [Formalism.L2.Theta.mt]

theorem mt_mul_inv (W : HSp D) (g : GA D W) : Formalism.L2.Theta.mt W g * Formalism.L2.Theta.mt W g⁻¹ = 1 := by
  rw [← mt_mul]; simp [Formalism.L2.Theta.mt]

theorem mt_mul_frame (W : HSp D) {s : ℕ} (L : Matrix (Fin W.rank) (Fin s) D.host.E) (n : GA D W) (hn : n ∈ NI W L) :
    Formalism.L2.Theta.mt W n ⋆ₘ L.map (incA D) = L.map (incA D) := by
  induction hn using Subgroup.closure_induction with
  | mem g hg =>
    have h1 : (Formalism.L2.Theta.mt W g - 1) ⋆ₘ L.map (incA D) = 0 := hg.1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
    exact h1
  | one => simp [Formalism.L2.Theta.mt]
  | mul x y _ _ hx hy => rw [mt_mul, Matrix.mul_assoc, hy, hx]
  | inv x _ hx =>
    calc Formalism.L2.Theta.mt W x⁻¹ ⋆ₘ L.map (incA D)
        = Formalism.L2.Theta.mt W x⁻¹ ⋆ₘ (Formalism.L2.Theta.mt W x ⋆ₘ L.map (incA D)) := by rw [hx]
      _ = L.map (incA D) := by rw [← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]

theorem mt_conj_sub_one (W : HSp D) (γ m : GA D W) : Formalism.L2.Theta.mt W (γ * m * γ⁻¹) - 1 =
    Formalism.L2.Theta.mt W γ * (Formalism.L2.Theta.mt W m - 1) * Formalism.L2.Theta.mt W γ⁻¹ := by
  rw [mt_mul, mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mt_mul_inv]

theorem conj_sub_one_kills_frame_of_fixed (W : HSp D) {s : ℕ} (L : Matrix (Fin W.rank) (Fin s) D.host.E) (γ m : GA D W)
    (hΓiL : Formalism.L2.Theta.mt W γ⁻¹ ⋆ₘ L.map (incA D) = L.map (incA D))
    (h1 : (Formalism.L2.Theta.mt W m - 1) ⋆ₘ L.map (incA D) = 0) :
    (Formalism.L2.Theta.mt W (γ * m * γ⁻¹) - 1) ⋆ₘ L.map (incA D) = 0 := by
  rw [mt_conj_sub_one, Matrix.mul_assoc, hΓiL, Matrix.mul_assoc, h1, Matrix.mul_zero]

theorem rowFrame_mul_conj_sub_one_eq_zero_of_fixed (W : HSp D) {s : ℕ} (P : Matrix (Fin s) (Fin W.rank) D.host.E) (γ m : GA D W)
    (hPΓ : P.map (incA D) ⋆ₘ Formalism.L2.Theta.mt W γ = P.map (incA D))
    (h2 : P.map (incA D) ⋆ₘ (Formalism.L2.Theta.mt W m - 1) = 0) :
    P.map (incA D) ⋆ₘ (Formalism.L2.Theta.mt W (γ * m * γ⁻¹) - 1) = 0 := by
  rw [mt_conj_sub_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPΓ, h2, Matrix.zero_mul]

theorem conj_unipotentRadical_kernelCondition_of_rationalFixed (W : HSp D) {s : ℕ} (L : Matrix (Fin W.rank) (Fin s) D.host.E) (P : Matrix (Fin s) (Fin W.rank) D.host.E)
    (γ m : GA D W) (γ₀ γi : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (hγ₀ : Formalism.L2.Theta.mt W γ = γ₀.map (incA D)) (hγγi : γ₀ * γi = 1) (hPγi : P * γi = P)
    (hΓL : Formalism.L2.Theta.mt W γ ⋆ₘ L.map (incA D) = L.map (incA D))
    (h3 : ∀ x : Fin W.rank → D.host.E, P *ᵥ x = 0 → ∃ a : Fin s → AE D,
        (Formalism.L2.Theta.mt W m - 1) *ᵥ (fun i => incA D (x i)) = L.map (incA D) *ᵥ a)
    (x : Fin W.rank → D.host.E) (hx : P *ᵥ x = 0) : ∃ a : Fin s → AE D,
        (Formalism.L2.Theta.mt W (γ * m * γ⁻¹) - 1) *ᵥ (fun i => incA D (x i)) = L.map (incA D) *ᵥ a := by
  have hy : P *ᵥ (γi *ᵥ x) = 0 := by
    rw [Matrix.mulVec_mulVec, hPγi]; exact hx
  obtain ⟨a, ha⟩ := h3 _ hy
  refine ⟨a, ?_⟩
  have hyb : (fun i => incA D ((γi *ᵥ x) i)) = γi.map (incA D) *ᵥ (fun i => incA D (x i)) := by
    funext i; exact RingHom.map_mulVec (incA D) γi x i
  have hxb : Formalism.L2.Theta.mt W γ *ᵥ (fun i => incA D ((γi *ᵥ x) i)) = fun i => incA D (x i) := by
    rw [hyb, Matrix.mulVec_mulVec, hγ₀, ← Matrix.map_mul, hγγi, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mulVec]
  have hxi : Formalism.L2.Theta.mt W γ⁻¹ *ᵥ (fun i => incA D (x i)) = fun i => incA D ((γi *ᵥ x) i) := by
    rw [← hxb, Matrix.mulVec_mulVec, mt_inv_mul, Matrix.one_mulVec]
  rw [mt_conj_sub_one, ← Matrix.mulVec_mulVec, hxi, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_mulVec, hΓL]

theorem stab : ∀ (D : D7) (W : HSp D) (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W L →
    (∀ γ ∈ GQ W, ∀ γ₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E, Formalism.L2.Theta.mt W γ = γ₀.map (incA D) →
      γ₀ * L = L → ∀ n ∈ NI W L, γ * n * γ⁻¹ ∈ NI W L) ∧
    (∀ n ∈ NI W L, ∀ n₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E, Formalism.L2.Theta.mt W n = n₀.map (incA D) →
      n₀ * L = L) := by
  intro D W s L _
  refine ⟨?_, fun n hn n₀ hn₀ => ?_⟩
  swap
  · apply Matrix.map_injective (incA_injective D)
    show (n₀ * L).map (incA D) = L.map (incA D)
    rw [Matrix.map_mul, ← hn₀]
    exact mt_mul_frame W L n hn
  intro γ hγ γ₀ hγ₀ hL
  obtain ⟨g, hg, e⟩ := hγ
  have hg0 : (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) = γ₀ := by
    apply Matrix.map_injective (incA_injective D)
    show (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D) = γ₀.map (incA D)
    rw [← hγ₀]
    exact congrArg Units.val e

  obtain ⟨σ, hσ⟩ : ∃ σ : D.host.E →+* D.host.E, σ = (D.sp.cm.sig : D.host.E →+* D.host.E) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = W.gram := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin s) (Fin W.rank) D.host.E, P = Formalism.UG.cT σ L * G := ⟨_, rfl⟩
  obtain ⟨γi, hγi⟩ : ∃ γi : Matrix (Fin W.rank) (Fin W.rank) D.host.E, γi = (g⁻¹ : GL (Fin W.rank) D.host.E).1 :=
    ⟨_, rfl⟩
  have hγγi : γ₀ * γi = 1 := by rw [← hg0, hγi]; exact Units.mul_inv g
  have hU : Formalism.UG.cT σ γ₀ * G * γ₀ = G := by rw [← hg0, hσ, hG]; exact hg
  have hPγ : P * γ₀ = P := by
    calc P * γ₀ = Formalism.UG.cT σ (γ₀ * L) * G * γ₀ := by rw [hL, hP]
      _ = Formalism.UG.cT σ L * (Formalism.UG.cT σ γ₀ * G * γ₀) := by
        rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = P := by rw [hU, hP]
  have hPγi : P * γi = P := by
    calc P * γi = P * γ₀ * γi := by rw [hPγ]
      _ = P := by rw [Matrix.mul_assoc, hγγi, Matrix.mul_one]

  have hΓL : Formalism.L2.Theta.mt W γ ⋆ₘ L.map (incA D) = L.map (incA D) := by
    rw [hγ₀, ← Matrix.map_mul, hL]
  have hΓiL : Formalism.L2.Theta.mt W γ⁻¹ ⋆ₘ L.map (incA D) = L.map (incA D) := by
    calc Formalism.L2.Theta.mt W γ⁻¹ ⋆ₘ L.map (incA D)
        = Formalism.L2.Theta.mt W γ⁻¹ ⋆ₘ (Formalism.L2.Theta.mt W γ ⋆ₘ L.map (incA D)) := by rw [hΓL]
      _ = L.map (incA D) := by rw [← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
  have hPΓ : P.map (incA D) ⋆ₘ Formalism.L2.Theta.mt W γ = P.map (incA D) := by
    rw [hγ₀, ← Matrix.map_mul, hPγ]
  have hPΓi : P.map (incA D) ⋆ₘ Formalism.L2.Theta.mt W γ⁻¹ = P.map (incA D) := by
    calc P.map (incA D) ⋆ₘ Formalism.L2.Theta.mt W γ⁻¹
        = P.map (incA D) ⋆ₘ Formalism.L2.Theta.mt W γ ⋆ₘ Formalism.L2.Theta.mt W γ⁻¹ := by rw [hPΓ]
      _ = P.map (incA D) := by rw [Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one]

  have key : NI W L ≤ (NI W L).comap (MulAut.conj γ).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun m hm => ?_
    have h1 : (Formalism.L2.Theta.mt W m - 1) ⋆ₘ L.map (incA D) = 0 := hm.1
    have h2 : P.map (incA D) ⋆ₘ (Formalism.L2.Theta.mt W m - 1) = 0 := by
      have := hm.2.1
      rw [hP, hσ, hG]; exact this
    have h3 : ∀ x : Fin W.rank → D.host.E, P *ᵥ x = 0 → ∃ a : Fin s → AE D,
        (Formalism.L2.Theta.mt W m - 1) *ᵥ (fun i => incA D (x i)) = L.map (incA D) *ᵥ a := by
      rw [hP, hσ, hG]; exact hm.2.2
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine Subgroup.subset_closure ⟨conj_sub_one_kills_frame_of_fixed W L γ m hΓiL h1, ?_, ?_⟩
    · have := rowFrame_mul_conj_sub_one_eq_zero_of_fixed W P γ m hPΓ h2
      rw [hP, hσ, hG] at this; exact this
    · intro x hx
      rw [← hG, ← hσ, ← hP] at hx
      exact conj_unipotentRadical_kernelCondition_of_rationalFixed W L P γ m γ₀ γi hγ₀ hγγi hPγi hΓL h3 x hx
  intro n hn
  exact key hn

end GlobalTheory.FrameStab
