import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormNonvanishing
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped Matrix TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 800000

namespace GlobalTheory.LevelLatticeCong

theorem cong_add {R : Type} [CommRing R] {n : ℕ} (K : Matrix (Fin n) (Fin n) R) (t : R) (M : ℕ)
    {u₁ u₂ y₁ y₂ : Fin n → R} (f₁ : t • (K *ᵥ u₁ - u₁) = M • y₁) (f₂ : t • (K *ᵥ u₂ - u₂) = M • y₂) :
    t • (K *ᵥ (u₁ + u₂) - (u₁ + u₂)) = M • (y₁ + y₂) := by
  rw [smul_add, ← f₁, ← f₂, Matrix.mulVec_add, ← smul_add]
  congr 1
  abel

theorem cong_smul {R : Type} [CommRing R] {n : ℕ} (K : Matrix (Fin n) (Fin n) R) (t s : R) (M : ℕ)
    {u w : Fin n → R} (f : t • (K *ᵥ u - u) = M • w) :
    t • (K *ᵥ (s • u) - s • u) = M • (s • w) := by
  rw [Matrix.mulVec_smul, ← smul_sub, smul_comm t, f, smul_comm]

end GlobalTheory.LevelLatticeCong

namespace GlobalTheory.LevelLatticeCong

theorem cong_on_sdLattice : ∀ {D : D7} (V : HSp D) {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}, IsSDFrame V β Λ 1 → ∀ {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)}, LatEmb V ι → ∀ (K : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) (t : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) (M : ℕ), (∀ a : La, ∃ w ∈ latGHat V 1, t • (K *ᵥ finVec V (ι a) - finVec V (ι a)) = M • w) → ∀ x ∈ Λ, ∃ y ∈ latHat V, t • (K *ᵥ finVec V x - finVec V x) = M • y := by
  intro D V β Λ hβ La _ _ ι hι K t M h
  have hl : latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [← GlobalTheory.OneMapRef.Lift.hatV_eq hβ]; rfl

  have hfv : ∀ (e : D.host.E) (v : Fin V.rank → D.host.E),
      finVec V (e • v) = ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] e) • finVec V v := by
    intro e v; funext i
    simp only [finVec, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

  have hint : ∀ c : 𝓞 D.host.E, ∀ z ∈ latHat V,
      ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • z ∈ latHat V := by
    intro c z hz
    rw [hl] at hz ⊢
    exact GlobalTheory.Member.AALev.hat_smul_int Λ c hz

  have hinv : ∀ b ∈ ((D.host.AA)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E),
      ∀ w ∈ latGHat V 1, ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b) • w ∈ latHat V := by
    intro b hb
    let s : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E :=
      (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b
    let H : AddSubgroup (Fin V.rank → FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) :=
      (latHat V).comap (DistribMulAction.toAddMonoidHom _ s)
    suffices hle : latGHat V 1 ≤ H from fun w hw => hle hw
    rw [GlobalTheory.LevelActionPinned.latGHat_one, AddSubgroup.closure_le]
    · rintro _ ⟨_, ⟨a, ha, rfl⟩, z, hz, rfl⟩
      have hba : b * a ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
        rw [← inv_mul_cancel₀ (GlobalTheory.MarkCoset.AA_ne_zero D)]
        exact FractionalIdeal.mul_mem_mul hb ha
      obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hba
      have e : ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b) •
          (((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] a) • z) =
          ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • z := by
        rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        congr 2
        exact hc.symm
      show s • _ ∈ latHat V
      rw [e]; exact hint c z hz
  let P : D.host.E → Prop := fun e => ∀ x ∈ Λ, ∃ y ∈ latHat V,
    t • (K *ᵥ finVec V (e • x) - finVec V (e • x)) = M • y
  have hadd : ∀ e₁ e₂ : D.host.E, P e₁ → P e₂ → P (e₁ + e₂) := by
    intro e₁ e₂ h₁ h₂ x hx
    obtain ⟨y₁, hy₁, f₁⟩ := h₁ x hx
    obtain ⟨y₂, hy₂, f₂⟩ := h₂ x hx
    refine ⟨y₁ + y₂, add_mem hy₁ hy₂, ?_⟩
    have e0 : finVec V ((e₁ + e₂) • x) = finVec V (e₁ • x) + finVec V (e₂ • x) := by
      rw [add_smul]; funext i; exact TensorProduct.tmul_add _ _ _
    rw [e0]
    exact cong_add K t M f₁ f₂
  have hmul : ∀ a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E),
      ∀ b ∈ (((D.host.AA)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E), P (a * b) := by
    intro a ha b hb x hx
    have hxL : finVec V x ∈ latHat V := by
      rw [hl]; exact GlobalTheory.Member.AALev.fv_mem_hat _ hx
    have hax : a • x ∈ latG V 1 := by
      refine Submodule.subset_span ⟨a, ha, x, ?_, rfl⟩
      refine ⟨finVec V x, hxL, ?_⟩
      simp only [map_one, Units.val_one, Matrix.one_mulVec]
    rw [← hι.2] at hax
    obtain ⟨a', ha'⟩ := hax
    obtain ⟨w, hw, e⟩ := h a'
    rw [ha'] at e
    refine ⟨((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b) • w, hinv b hb w hw, ?_⟩
    have e1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
    rw [e1, hfv b]
    exact cong_smul K t _ M e
  have h1 : (1 : D.host.E) ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) *
      (((D.host.AA)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E) := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ (GlobalTheory.MarkCoset.AA_ne_zero D)]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  have hP : P 1 := Submodule.mul_induction_on h1 hmul hadd
  intro x hx
  simpa only [one_smul] using hP x hx

end GlobalTheory.LevelLatticeCong
