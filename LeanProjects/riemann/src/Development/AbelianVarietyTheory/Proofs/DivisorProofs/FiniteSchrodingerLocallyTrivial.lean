import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicSchwartzSpaceOfLevelCompactSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerIntegralBound

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.SchrFixSmall

open GlobalTheory.HeisSchA

variable {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ]

theorem schr_add (ψ : AddChar R ℂ) (w : (κ → R) × (κ → R)) (Φ Ψ : (κ → R) → ℂ) :
    schr ψ w (Φ + Ψ) = schr ψ w Φ + schr ψ w Ψ := by
  funext x; simp only [schr, Pi.add_apply, mul_add]

theorem schr_smul (ψ : AddChar R ℂ) (w : (κ → R) × (κ → R)) (c : ℂ) (Φ : (κ → R) → ℂ) :
    schr ψ w (c • Φ) = c • schr ψ w Φ := by
  funext x; simp only [schr, Pi.smul_apply, smul_eq_mul]; ring

theorem schr_zero (ψ : AddChar R ℂ) (w : (κ → R) × (κ → R)) :
    schr ψ w (0 : (κ → R) → ℂ) = 0 := by
  funext x; simp only [schr, Pi.zero_apply, mul_zero]

theorem schr_fixed_small : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ (κ : Type) [Fintype κ], ∀ Ψ ∈ schA F κ, ∃ N ∈ 𝓝 (0 : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)),
      ∀ p ∈ N, schr ψ (fun i => pairA F 0 (p.1 i), fun i => pairA F 0 (p.2 i)) Ψ = Ψ := by
  intro F _ _ ψ hψ κ _ Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | zero => exact ⟨Set.univ, Filter.univ_mem, fun p _ => schr_zero ψ _⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨N₁, hN₁, e₁⟩ := h1
    obtain ⟨N₂, hN₂, e₂⟩ := h2
    exact ⟨N₁ ∩ N₂, Filter.inter_mem hN₁ hN₂, fun p hp => by rw [schr_add, e₁ p hp.1, e₂ p hp.2]⟩
  | smul c Φ _ h =>
    obtain ⟨N, hN, e⟩ := h
    exact ⟨N, hN, fun p hp => by rw [schr_smul, e p hp]⟩
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    let fe : (κ → FiniteAdeleRing (𝓞 F) F) → κ → AF F := fun a i => pairA F 0 (a i)
    have cfe : Continuous fe := continuous_pi fun i =>
      (show Continuous fun y : FiniteAdeleRing (𝓞 F) F => ((0 : InfiniteAdeleRing F), y) from
        continuous_const.prodMk continuous_id).comp (continuous_apply i)
    let w' : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) →
        (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) × FiniteAdeleRing (𝓞 F) F :=
      fun p => (p.2, p.1, p2 (⅟(2 : AF F) * (fe p.1 ⬝ᵥ fe p.2)))
    have cw : Continuous w' :=
      continuous_snd.prodMk (continuous_fst.prodMk (continuous_snd.comp
        (continuous_const.mul ((cfe.comp continuous_fst).dotProduct (cfe.comp continuous_snd)))))
    have w0 : w' 0 = 0 := by
      have : fe 0 = 0 := funext fun i => rfl
      simp only [w', Prod.fst_zero, Prod.snd_zero, this, zero_dotProduct, mul_zero, map_zero]
      rfl
    have hev := (cw.tendsto' 0 0 w0).eventually (GlobalTheory.ConeMeasSmall.eventually_fixed (finChar ψ) (finChar_isLocallyConstant ψ hψ) hg)
    refine ⟨_, hev, fun p hp => ?_⟩
    have hp' := fun z => (hp : ∀ z, finChar ψ (z ⬝ᵥ (w' p).1 + (w' p).2.2) * g (z + (w' p).2.1) = g z) z
    funext x
    have hp1 : ∀ a : κ → FiniteAdeleRing (𝓞 F) F, (⇑p1 ∘ fe a) = 0 := fun a => funext fun i => rfl
    have harch : p1 (x ⬝ᵥ fe p.2 + ⅟(2 : AF F) * (fe p.1 ⬝ᵥ fe p.2)) = 0 := by
      rw [map_add, map_mul, RingHom.map_dotProduct, RingHom.map_dotProduct, hp1, hp1]
      simp
    have hfin : p2 (x ⬝ᵥ fe p.2 + ⅟(2 : AF F) * (fe p.1 ⬝ᵥ fe p.2)) =
        (fun i => (x i).2) ⬝ᵥ p.2 + p2 (⅟(2 : AF F) * (fe p.1 ⬝ᵥ fe p.2)) := by
      rw [map_add, RingHom.map_dotProduct]
      rfl
    have hx1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + fe p.1) i).1) =
        fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + 0) = _
      rw [add_zero]
    have hx2 : (fun i => ((x + fe p.1) i).2) = (fun i => (x i).2) + p.1 := funext fun i => rfl
    show ψ (x ⬝ᵥ fe p.2 + ⅟(2 : AF F) * (fe p.1 ⬝ᵥ fe p.2)) * (f _ * g _) = f _ * g _
    rw [map_eq_mul ψ, harch, hfin, hx1, hx2, ← hp' (fun i => (x i).2)]
    have h0 : ψ (mk 0 0) = 1 := by
      rw [show (mk 0 0 : AF F) = 0 from rfl, AddChar.map_zero_eq_one]
    rw [h0]
    ring

end GlobalTheory.SchrFixSmall
