import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

noncomputable section

namespace GlobalTheory.ConeSmallSumBd

open GlobalTheory.ConeSmallSer GlobalTheory.ConeSmallCT

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem stabLn_mul_inv {x : Fin n → E} {p q : UA σ J} (hp : StabLn x p) (hq : StabLn x q) : StabLn x (p * q⁻¹) := by
  obtain ⟨l, hl⟩ := hp
  obtain ⟨m, hm⟩ := hq
  have e : ∀ a b : UA σ J, mat (a * b) = mat a * mat b := fun _ _ => rfl
  have e1 : mat (1 : UA σ J) = 1 := rfl
  have key : mat q⁻¹ *ᵥ (mat q *ᵥ incV F x) = incV F x := by
    rw [Matrix.mulVec_mulVec, ← e, inv_mul_cancel, e1, Matrix.one_mulVec]
  rw [hm, Matrix.mulVec_smul] at key
  have h2 : mat q⁻¹ *ᵥ incV F x = (m⁻¹).1 • incV F x :=
    calc mat q⁻¹ *ᵥ incV F x = (m⁻¹).1 • (m.1 • mat q⁻¹ *ᵥ incV F x) := by
          rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
      _ = (m⁻¹).1 • incV F x := by rw [key]
  refine ⟨l * m⁻¹, ?_⟩
  rw [e, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul, hl, smul_smul, Units.val_mul, mul_comm]

theorem tsum_norm_le {x : Fin n → E} {T : Set (UA σ J)} (hT : IsReps T x) {f : UA σ J → ℂ}
    (hinv : ∀ p ∈ ratU σ J, StabLn x p → ∀ h, f (p * h) = f h) {b : T → ℝ} (hb : Summable b)
    {γ g : UA σ J} (hγ : γ ∈ ratU σ J) (hbd : ∀ t : T, ‖f (t.1 * (γ * g))‖ ≤ b t) :
    Summable (fun t : T => ‖f (t.1 * g)‖) ∧ ∑' t : T, ‖f (t.1 * g)‖ ≤ ∑' t, b t := by
  have hr : ∀ t : T, t.1 * γ⁻¹ ∈ ratU σ J := fun t => mul_mem (hT.1 t.2) (inv_mem hγ)
  choose r hrT hrs using fun t : T => (hT.2 _ (hr t)).exists
  let ρ : T → T := fun t => ⟨r t, hrT t⟩
  have hinj : Function.Injective ρ := by
    intro t₁ t₂ h
    have h' : r t₁ = r t₂ := congrArg Subtype.val h
    have h1 : StabLn x (t₁.1 * γ⁻¹ * (r t₁)⁻¹) := hrs t₁
    have h2 : StabLn x (t₂.1 * γ⁻¹ * (r t₂)⁻¹) := hrs t₂
    have h3 := stabLn_mul_inv h1 h2
    have e : t₁.1 * γ⁻¹ * (r t₁)⁻¹ * (t₂.1 * γ⁻¹ * (r t₂)⁻¹)⁻¹ = t₁.1 * t₂.1⁻¹ := by rw [h']; group
    rw [e] at h3
    refine Subtype.ext ((hT.2 t₁.1 (hT.1 t₁.2)).unique ⟨t₁.2, 1, ?_⟩ ⟨t₂.2, h3⟩)
    rw [mul_inv_cancel]
    simp [mat]
  have hle : ∀ t : T, ‖f (t.1 * g)‖ ≤ b (ρ t) := fun t => by
    have e : t.1 * g = (t.1 * γ⁻¹ * (r t)⁻¹) * (r t * (γ * g)) := by group
    rw [e, hinv _ (mul_mem (hr t) (inv_mem (hT.1 (hrT t)))) (hrs t)]
    exact hbd (ρ t)
  have hs : Summable (b ∘ ρ) := hb.comp_injective hinj
  have hs' : Summable (fun t : T => ‖f (t.1 * g)‖) := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs
  exact ⟨hs', hs'.tsum_le_tsum_of_inj ρ hinj (fun c _ => (norm_nonneg _).trans (hbd c)) hle hb⟩

theorem isCompact_ht_le (c : ℝ≥0) : IsCompact {g : UA σ J | ht g ≤ c} := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  have hcA : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hc : IsClosed (UG (cA σ) (incM F J) : Set (GL (Fin n) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin n) (AE F E) => (g : Matrix (Fin n) (Fin n) (AE F E)) := Units.continuous_val
    exact isClosed_eq (((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul (hv.matrix_map hcA))) continuous_const
  exact hc.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_heightGL_le F c)

theorem sum_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d d₁ : ℕ)
    (W : Spc F E d) (H' : Plane E d d₁) (R : ℝ≥0), (∀ u ∈ unip σ W H', ∃ γ ∈ ratU σ W.J ⊓ unip σ W H', ht (γ * u) ≤ R) →
    ∀ T : Set (UA σ W.J), GlobalTheory.ConeSmallCT.IsReps T H'.x → ∀ f : UA σ W.J → ℂ,
    (∀ p ∈ ratU σ W.J, GlobalTheory.ConeSmallSer.StabLn H'.x p → ∀ h, f (p * h) = f h) → GlobalTheory.ConeSmallCT.LocUnifSum f T →
    ∀ h, ∃ C : ℝ, ∀ u ∈ unip σ W H', Summable (fun t : T => ‖f (t.1 * (u * h))‖) ∧ ∑' t : T, ‖f (t.1 * (u * h))‖ ≤ C := by
  intro F E _ _ _ _ _ σ d d₁ W H' R hR T hT f hinv hL h
  obtain ⟨b, hb, hbd⟩ := hL _ (isCompact_ht_le (σ := σ) (J := W.J) (R * ht h))
  refine ⟨∑' t, b t, fun u hu => ?_⟩
  obtain ⟨γ, hγ, hγR⟩ := hR u hu
  refine tsum_norm_le hT hinv hb hγ.1 fun t => hbd t _ ?_
  rw [← mul_assoc]
  exact (heightGL_mul_le F (γ * u).1 h.1).trans (mul_le_mul_left hγR _)

end GlobalTheory.ConeSmallSumBd

end
