import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMapHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPhiDivNsmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsSide
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SurjectiveOfFiniteLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolOfFiniteSurjective

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TorRef.Unif

theorem isTwInv_comb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {ψ φ : InvFun (𝓞 E)} (a b : ℕ)
    (h₁ : IsTwInv H ψ) (h₂ : IsTwInv H φ) : IsTwInv H (comb a ψ b φ) := by
  intro σ hσ n B
  simp only [comb]
  rw [h₁ σ hσ n B, h₂ σ hσ n B]

theorem exists_common_pair {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l₁ l₂ : Level H} {Xo₁ : Moduli D l₁} {Xo₂ : Moduli D l₂} {c₁ : Coeff l₁} {c₂ : Coeff l₂}
    (Z₁ : GMod Xo₁ c₁) (Z₂ : GMod Xo₂ c₂) {ψ φ : InvFun (𝓞 E)} {k : ℕ} (hψ : IsTwInv H ψ) (hφ : IsTwInv H φ)
    (h₁ : PolRay ψ φ k Z₁) (d₁ : ∀ a b, ∃ BD, IsPhiDiv (comb a ψ b φ) Z₁ BD)
    (h₂ : PolRay ψ φ k Z₂) (d₂ : ∀ a b, ∃ BD, IsPhiDiv (comb a ψ b φ) Z₂ BD) :
    ∃ A B : ℕ, 0 < A ∧ 0 < B ∧ (∃ BD, IsPol (comb A ψ B φ) (A * k) Z₁ BD) ∧
      (∃ BD, IsPol (comb A ψ B φ) (A * k) Z₂ BD) := by
  obtain ⟨b₁, N₁, T₁, hb₁, hN₁, r₁⟩ := h₁
  obtain ⟨b₂, N₂, T₂, hb₂, hN₂, r₂⟩ := h₂
  set s := T₁ + T₂ + 1 with hs
  have hT₁ : T₁ ≤ N₂ * b₁ * s := le_trans (by omega) (Nat.le_mul_of_pos_left s (Nat.mul_pos hN₂ hb₁))
  have hT₂ : T₂ ≤ N₁ * b₂ * s := le_trans (by omega) (Nat.le_mul_of_pos_left s (Nat.mul_pos hN₁ hb₂))
  obtain ⟨P₁, hP₁⟩ := r₁ _ hT₁
  obtain ⟨P₂, hP₂⟩ := r₂ _ hT₂
  obtain ⟨Q₁, hQ₁⟩ := d₁ (b₂ * (N₁ * (N₂ * b₁ * s))) (b₂ * b₁)
  obtain ⟨Q₂, hQ₂⟩ := d₂ (b₁ * (N₂ * (N₁ * b₂ * s))) (b₁ * b₂)
  have k₁ := GlobalTheory.PolScale.isPol_scale _ H D _ Xo₁ c₁ Z₁ ψ φ _ _ b₂ _ P₁ Q₁ hψ hφ hb₂ hP₁ hQ₁
  have k₂ := GlobalTheory.PolScale.isPol_scale _ H D _ Xo₂ c₂ Z₂ ψ φ _ _ b₁ _ P₂ Q₂ hψ hφ hb₁ hP₂ hQ₂
  have e₁ : b₁ * (N₂ * (N₁ * b₂ * s)) = b₂ * (N₁ * (N₂ * b₁ * s)) := by ring
  have e₂ : b₁ * b₂ = b₂ * b₁ := by ring
  have e₃ : b₂ * (N₁ * (N₂ * b₁ * s) * k) = b₂ * (N₁ * (N₂ * b₁ * s)) * k := by ring
  have e₄ : b₁ * (N₂ * (N₁ * b₂ * s) * k) = b₂ * (N₁ * (N₂ * b₁ * s)) * k := by ring
  rw [e₃] at k₁
  rw [e₄, e₁, e₂] at k₂
  exact ⟨_, _, Nat.mul_pos hb₂ (Nat.mul_pos hN₁ (Nat.mul_pos (Nat.mul_pos hN₂ hb₁) (by omega))), Nat.mul_pos hb₂ hb₁,
    ⟨Q₁, k₁⟩, ⟨Q₂, k₂⟩⟩

theorem uniformSt : UniformSt := by
  have hM : PolMapSt := GlobalTheory.TorRef.polMapSt
  intro E _ _ _ H D _ Xo ψ φ k Z hψ hφ hZ
  by_cases h : ∃ (l : Level H) (c : Coeff l), ∀ p : ℕ, p.Prime → l.GoodAt p
  swap
  · exact ⟨1, 1, one_pos, one_pos, fun l c hg => (h ⟨l, c, hg⟩).elim⟩
  obtain ⟨l₀, c₀, h₀⟩ := h
  obtain ⟨b₀, N₀, T₀, hb₀, hN₀, hr₀⟩ := (hZ l₀ c₀ h₀).1
  refine ⟨N₀ * (T₀ + 1), b₀, Nat.mul_pos hN₀ (Nat.succ_pos _), hb₀, fun l c hg => ?_⟩
  obtain ⟨BD₀, hBD₀⟩ := hr₀ (T₀ + 1) (Nat.le_succ _)
  have hβ : ∀ (l : Level H) (c : Coeff l), IsDedFrac (algebraMap (𝓞 c.F) c.F) ∧ Algebra.FiniteType ℤ (𝓞 c.F) :=
    fun l c => ⟨(GlobalTheory.CoeffRings.coeff_isDedFrac E H l c).1, (GlobalTheory.CoeffRings.coeff_isDedFrac E H l c).2.1⟩
  obtain ⟨l', c', hg', b₁, b₂, r₁, r₂, ν₁, ν₂, hb₁, hb₂, hr₁, hr₂, hc₁, hc₂⟩ := GlobalTheory.LvCover.exists_cover E H D Xo Z l c hg l₀ c₀ h₀

  obtain ⟨A, B, -, -, ⟨P', hP'⟩, ⟨P₀, hP₀⟩⟩ := exists_common_pair (Z l' c' hg') (Z l₀ c₀ h₀) hψ hφ (hZ l' c' hg').1
    (hZ l' c' hg').2 (hZ l₀ c₀ h₀).1 (hZ l₀ c₀ h₀).2
  obtain ⟨π₂, hπ₂, mu₂, hf₂, hj₂, -, -⟩ := hM E H D l₀ l' (Xo l₀) (Xo l') c₀ c' _ _ _ _ (Z l₀ c₀ h₀) (Z l' c' hg') P₀ P'
    (comb A ψ B φ) (A * k) b₂ (RingEquiv.refl _) r₂ ν₂ (hβ l₀ c₀).1 (hβ l' c').1 (hβ l' c').2 (isTwInv_comb A B hψ hφ) rfl
    hP₀ hP' hc₂
  obtain ⟨BD', hBD'⟩ := (hZ l' c' hg').2 (N₀ * (T₀ + 1)) b₀
  have k' := GlobalTheory.PolPull.isPol_pull E H D l₀ l' (Xo l₀) (Xo l') c₀ c' (Z l₀ c₀ h₀) (Z l' c' hg') BD₀ BD' _ _ b₂ _ r₂ ν₂ π₂ hπ₂ mu₂
    (isTwInv_comb _ _ hψ hφ) rfl hf₂ hj₂ hBD₀ hBD'

  obtain ⟨A', B', -, -, ⟨Q, hQ⟩, ⟨Q', hQ'⟩⟩ := exists_common_pair (Z l c hg) (Z l' c' hg') hψ hφ (hZ l c hg).1
    (hZ l c hg).2 (hZ l' c' hg').1 (hZ l' c' hg').2
  obtain ⟨π₁, hπ₁, mu₁, hf₁, hj₁, -, -⟩ := hM E H D l l' (Xo l) (Xo l') c c' _ _ _ _ (Z l c hg) (Z l' c' hg') Q Q'
    (comb A' ψ B' φ) (A' * k) b₁ (RingEquiv.refl _) r₁ ν₁ (hβ l c).1 (hβ l' c').1 (hβ l' c').2 (isTwInv_comb A' B' hψ hφ)
    rfl hQ hQ' hc₁
  have hs := GlobalTheory.ModelSurj.surjective_of_finite_lift E H D l l' (Xo l) (Xo l') c c' (Z l c hg) (Z l' c' hg') b₁ r₁ π₁ hπ₁ hb₁ hf₁ hj₁ hr₁
  obtain ⟨BD, hBD⟩ := (hZ l c hg).2 (N₀ * (T₀ + 1)) b₀
  exact ⟨BD, GlobalTheory.AmpleDown.isPol_of_finite_surjective E H D l l' (Xo l) (Xo l') c c' (Z l c hg) (Z l' c' hg') BD BD' _ _ b₁ _ r₁ ν₁ π₁ hπ₁ mu₁
    (isTwInv_comb _ _ hψ hφ) rfl hb₁ hf₁ hj₁ hs
    (CechPic.isLB_tens (isLB_lbPow (CechPic.isLB_dual (PolFin.isLB_detLie_of_polOf hQ.2.isLB)) _)
      (CechPic.isLB_dual BD.isLB_lb)) k' hBD⟩

end GlobalTheory.TorRef.Unif
