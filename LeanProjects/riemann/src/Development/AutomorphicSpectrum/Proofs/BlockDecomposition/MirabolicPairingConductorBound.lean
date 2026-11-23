import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCoefficientContinuousStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingDepthVanishingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedSmallShearStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearPreservesBoxMembershipStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedBoxIntegralIdentityStatement

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem JJ_preimage_box_eq_JJ_box : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (g : GL (Fin (n + 1)) k) (v : V) (v' : V'), ∃ r : kˣ, ∀ t : kˣ, valuation k ((c * t⁻¹ : kˣ) : k) ≤ valuation k (r : k) → ∀ t' : kˣ, (∀ x ∈ box (n + 1) t, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t') → JJ ν ψ T B {x | (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t'} v v' = JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' := by
  intro k _ _ _ _ _ _ ν _ ψ c n V V' _ _ _ _ T T' B s hψ hc hT hT' hB g v v'
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hmono : ∀ {a a' : kˣ}, valuation k (a : k) ≤ valuation k (a' : k) →
      ∀ b ∈ GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) a, b ∈ GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) a' := by
    intro a a' haa' b hb
    have hb' : ∀ j, valuation k (b j) ≤ valuation k (a : k) := hb
    show ∀ j, valuation k (b j) ≤ valuation k (a' : k)
    exact fun j => le_trans (hb' j) haa'
  have hmin : ∀ a a' : kˣ, ∃ r : kˣ,
      valuation k (r : k) ≤ valuation k (a : k) ∧ valuation k (r : k) ≤ valuation k (a' : k) := by
    intro a a'
    rcases le_total (valuation k (a : k)) (valuation k (a' : k)) with h | h
    exacts [⟨a, le_rfl, h⟩, ⟨a', h, le_rfl⟩]
  obtain ⟨r₁, hr₁, h₁⟩ := GlobalTheory.T.shear_preserves_box_membership g
  obtain ⟨r₂, -, h₂⟩ := GlobalTheory.T.smooth_vector_fixed_small_shear T hT v
  obtain ⟨r₃, -, h₃⟩ := GlobalTheory.T.smooth_vector_fixed_small_shear T' hT' v'
  obtain ⟨r₄, h₄₁, h₄₂⟩ := hmin r₁ r₂
  obtain ⟨r, hr₄, hr₃⟩ := hmin r₄ r₃
  refine ⟨r, fun t ht t' hgt => ?_⟩
  set M : Set (Fin (n + 1) → k) :=
    {x | (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) t'} with hM
  have hMimage : M = (fun y => ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
      *ᵥ y) '' (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) t' : Set (Fin (n + 1) → k)) := by
    ext x
    constructor
    · intro hx
      refine ⟨_, hx, ?_⟩
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    · rintro ⟨y, hy, rfl⟩
      show (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ
        (((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ y) ∈
          GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) t'
      simpa only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, SetLike.mem_coe] using hy
  have hMc : IsCompact M := by
    rw [hMimage]
    exact (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.isCompact_box (n + 1) t').image
      (Continuous.matrix_mulVec continuous_const continuous_id)
  have hMm : MeasurableSet M := hMc.isClosed.measurableSet
  have hw : Continuous (GlobalTheory.CompanionTheory.MirPair.wt ψ n) := by
    unfold GlobalTheory.CompanionTheory.MirPair.wt
    exact continuous_subtype_val.comp (hψ.comp (continuous_apply (Fin.last n)).neg)
  have hf : Continuous fun x =>
      GlobalTheory.CompanionTheory.MirPair.wt ψ n x * GlobalTheory.CompanionTheory.MirPair.coef T B v v' x :=
    hw.mul (GlobalTheory.T.mirabolic_coefficient_continuous T B hT v v')
  have hsub : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) t : Set (Fin (n + 1) → k)) ⊆ M :=
    fun x hx => hgt x hx
  have key := GlobalTheory.T.fourier_box_integral_vanishing ν ψ c hψ hc (n + 1) t M
    (fun x => GlobalTheory.CompanionTheory.MirPair.wt ψ n x * GlobalTheory.CompanionTheory.MirPair.coef T B v v' x)
    (GlobalTheory.CompanionTheory.MirPair.JJ ν ψ T B M v v') hMc hMm hf (by
      intro b hb
      have hbv : ∀ j, valuation k (b j) ≤ valuation k ((c * t⁻¹ : kˣ) : k) := hb
      have hb₁ := hmono (le_trans ht (le_trans hr₄ h₄₁)) b hb
      have hb₂ := hmono (le_trans ht (le_trans hr₄ h₄₂)) b hb
      have hb₃ := hmono (le_trans ht hr₃) b hb
      have hlast : valuation k (b (Fin.last n)) < 1 :=
        lt_of_le_of_lt (le_trans (hbv (Fin.last n)) (le_trans ht (le_trans hr₄ h₄₁))) hr₁
      have hinv : ∀ x, ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ M ↔ x ∈ M :=
        fun x => h₁ b hb₁ t' x
      have h := GlobalTheory.T.mirabolic_pairing_depth_vanishing ν ψ T T' B s hψ hT hB b M v v'
        hlast (h₂ b hb₂) hinv
      rw [h₃ b hb₃] at h
      exact h)
  rw [Set.inter_eq_right.2 hsub] at key
  exact key.symm

end GlobalTheory.CompanionTheory.MirPair
