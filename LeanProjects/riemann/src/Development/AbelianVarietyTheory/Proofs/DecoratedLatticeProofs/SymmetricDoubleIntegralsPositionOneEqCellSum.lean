import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PositionOneOfSymmetricDoubleIntegralFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneDblIffSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilSourceActionAndSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSelfDualOfHasConductor
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeUnipotentHaarIntegralPointsEqOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMulMatrixVolumeOpenSubgroupIntegralGL
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.PosOne
open scoped ENNReal

attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace

section Scale
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k]

theorem isQuotInt_smul_measure {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {ν : Measure k} {μX : Measure (GL n k)}
    {μG : Measure (GL (n ⊕ Fin c) k)} {p : ℕ} {f : GL (n ⊕ Fin c) k → ℂ} {z : ℂ} (a : ℝ≥0∞)
    (h : IsQuotInt ν μX μG p f z) : IsQuotInt ν μX (a • μG) p f ((a.toReal : ℂ) * z) := by
  obtain ⟨F, hF, hf, hz⟩ := h
  refine ⟨F, hF, hf, ?_⟩
  rw [integral_smul_measure, hz, Complex.real_smul]

theorem isQuotInt_const_mul {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {ν : Measure k} {μX : Measure (GL n k)}
    {μG : Measure (GL (n ⊕ Fin c) k)} {p : ℕ} {f : GL (n ⊕ Fin c) k → ℂ} {z : ℂ} (b : ℂ)
    (h : IsQuotInt ν μX μG p f z) : IsQuotInt ν μX μG p (fun x => b * f x) (b * z) := by
  obtain ⟨F, hF, hf, hz⟩ := h
  refine ⟨fun x => b * F x, (SB _).smul_mem b hF, fun x => ?_, ?_⟩
  · dsimp only
    rw [hf x, ← integral_const_mul]
    congr 1
    funext g
    exact (integral_const_mul _ _).symm
  · rw [hz, integral_const_mul]

theorem app_smul {X V : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℂ V] (b : ℂ) (l : SB X →ₗ[ℂ] V)
    (f : X → ℂ) : app (b • l) f = b • app l f := by
  unfold app
  split_ifs <;> simp

theorem oneDbl_smul {n₀ n₁ n₂ : Type} [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂]
    [DecidableEq n₂] {c : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A] {ψ : AddChar k Circle} {ν : Measure k}
    {m₁ : Measure (GL n₁ k)} {G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)} {m₂ : Measure (GL n₂ k)}
    {G₂ : Measure (GL (n₂ ⊕ Fin c) k)} {μ₁ μ₂ : kˣ →* ℂˣ} {ρ : ℕ} {σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A}
    {T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ} {F : A}
    {Φ₁ : Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ}
    {Φ₂ : Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k → ℂ} {z : ℂ} (a b : ℝ≥0∞)
    (h : OneDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ σ T F Φ₁ Φ₂ z) :
    OneDbl ψ ν m₁ (a • G₁) m₂ (b • G₂) μ₁ μ₂ ρ σ T F Φ₁ Φ₂ ((a.toReal : ℂ) * ((b.toReal : ℂ) * z)) := by
  obtain ⟨w, hw, hz⟩ := h
  refine ⟨fun x => (b.toReal : ℂ) • w x, fun x Ψ => ?_, ?_⟩
  · exact isQuotInt_smul_measure b (hw x Ψ)
  · have := isQuotInt_smul_measure a (isQuotInt_const_mul (b.toReal : ℂ) hz)
    convert this using 2 with x
    rw [app_smul, smul_eq_mul]

theorem relIndex_mul_measure_KO {Y : Type} [Fintype Y] [DecidableEq Y] (G : Measure (GL Y k)) [G.IsHaarMeasure]
    (hK : G (KO k Y) = 1) (J : Subgroup (GL Y k)) (hJ : IsCO J) (hle : J ≤ KO k Y) :
    (J.relIndex (KO k Y) : ℝ≥0∞) * G J = 1 ∧ J.relIndex (KO k Y) ≠ 0 := by
  haveI : BorelSpace (GL Y k) := GlobalTheory.SplitFlip.borel_GL
  have hc : IsCompact (KO k Y : Set (GL Y k)) := GlobalTheory.SplitFlip.isCompact_KO
  haveI : CompactSpace (KO k Y) := isCompact_iff_compactSpace.1 hc
  have ho : IsOpen ((J.subgroupOf (KO k Y) : Subgroup (KO k Y)) : Set (KO k Y)) :=
    hJ.1.preimage continuous_subtype_val
  haveI : Finite (KO k Y ⧸ J.subgroupOf (KO k Y)) := Subgroup.quotient_finite_of_isOpen _ ho
  haveI : (J.subgroupOf (KO k Y)).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine ⟨?_, Subgroup.FiniteIndex.index_ne_zero⟩
  rw [GlobalTheory.IndexVolume.relIndex_mul_measure_subgroup J (KO k Y) hle hJ.1.measurableSet G, hK]

theorem rescale_one_eq {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (hc : 1 ≤ c) {ν : Measure k} (hν : IsUnitVol ν)
    (m : Measure (GL n k)) : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν (1 : GL (n ⊕ Fin c) k) m = m := by
  have h := GlobalTheory.T.rootExchangeUnipotentHaar_integralPoints_eq_one k n c 1 le_rfl hc ν hν
  have e : (((stabLat (1 : GL (n ⊕ Fin c) k)).subgroupOf (N k n c 1) : Subgroup (N k n c 1)) : Set (N k n c 1)) =
      {u : N k n c 1 | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} := by
    ext u
    simp [Subgroup.mem_subgroupOf, mem_stabLat]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale
  rw [e, h, inv_one, one_smul]

end Scale

set_option maxHeartbeats 4000000 in

theorem comb_eq_sum_cells : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ),
    c + 1 = 2 * ρ → ∀ (ψ : AddChar k Circle), Continuous ψ → HasConductor ψ 1 → ∀ (ν : Measure k), IsUnitVol ν →
  ∀ (μ₁ μ₂ : kˣ →* ℂˣ), IsOpen (μ₁.ker : Set kˣ) → IsOpen (μ₂.ker : Set kˣ) →
  ∀ (m₁ : Measure (GL n₁ k)) (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) (m₂ : Measure (GL n₂ k))
    (G₂ : Measure (GL (n₂ ⊕ Fin c) k)), m₁.IsHaarMeasure → G₁.IsHaarMeasure → m₂.IsHaarMeasure → G₂.IsHaarMeasure →
    G₁ (KO k (n₁ ⊕ Fin (c + 1))) = 1 → G₂ (KO k (n₂ ⊕ Fin c)) = 1 →
  ∀ (L₀ : Level (GL (n₀ ⊕ Fin (c + 1 + 1)) k)) (L₁ : Level (GL (n₁ ⊕ Fin (c + 1)) k)) (L₂ : Level (GL (n₂ ⊕ Fin c) k)),
    IsCO L₁.J → IsCO L₂.J → L₁.J ≤ KO k _ → L₂.J ≤ KO k _ →
  ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (τ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A), IsSmoothRep τ →
  ∀ (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), TriPos ψ μ₁ μ₂ ρ τ T →
  ∀ (F : A), (∀ j : L₂.J, τ (j : GL (n₂ ⊕ Fin c) k) F = (L₂.lam j : ℂ) • F) →
  ∀ (P₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (P₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)),
    HasTypes μ₁ L₀ L₁ P₁.1 → HasTypes μ₂ L₁ L₂ P₂.1 →
  ∀ (α : GL (n₀ ⊕ Fin (c + 1 + 1)) k) (A₁ : Finset (GL (n₁ ⊕ Fin (c + 1)) k)) (A₂ : Finset (GL (n₂ ⊕ Fin c) k)),
    Covers 1 L₁.J A₁ (fun h => GlobalTheory.StepData.flat ψ ν μ₁ P₁.1 α h) → (∀ γ ∈ A₁, Covers 1 L₂.J A₂ fun h => GlobalTheory.StepData.flat ψ ν μ₂ P₂.1 γ h) →
  ∀ (e₀ : GL (n₀ ⊕ Fin (c + 1 + 1)) k →₀ ℂ), IsOneComb ψ ν (ρ + 1) L₀ α e₀ →
  ∀ (e₂ : GL (n₂ ⊕ Fin c) k → (GL (n₂ ⊕ Fin c) k →₀ ℂ)), (∀ β ∈ A₂, IsOneComb ψ ν ρ L₂ β (e₂ β)) →
  ∀ (z : GL (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ),
    (∀ a ∈ e₀.support, SymDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ τ T F (om μ₁ a 1 P₁.1) P₂.1 (z a)) →
    comb e₀ z = ((L₁.J.relIndex (KO k _) : ℂ) * (L₂.J.relIndex (KO k _) : ℂ))⁻¹ *
      ∑ γ ∈ A₁, ∑ β ∈ A₂, ((((m₁ (prX (Cgrp L₁.J γ))).toReal⁻¹ * (m₂ (prX (Cgrp L₂.J β))).toReal⁻¹ : ℝ) : ℂ) *
        comb (e₂ β) fun b => app (app T (xi ψ ν μ₁ P₁.1 L₁.J 1 α γ)) (xi ψ ν μ₂ P₂.1 L₂.J 1 γ β) (τ b F)) := by
  intro k _ _ _ _ _ _ n₀ n₁ n₂ _ _ _ _ _ _ c ρ hcρ ψ hψ hcond ν hν μ₁ μ₂ ho₁ ho₂ m₁ G₁ m₂ G₂ hm₁ hG₁ hm₂ hG₂ hK₁ hK₂
    L₀ L₁ L₂ hco₁ hco₂ hle₁ hle₂ A _ _ τ hτ T hT F hF P₁ P₂ hty₁ hty₂ α A₁ A₂ hcov₁ hcov₂ e₀ he₀ e₂ he₂ z hz
  haveI := hm₁
  haveI := hG₁
  haveI := hm₂
  haveI := hG₂
  have hne : ψ ≠ 1 := hcond.ne_one
  have hsd : IsSelfDual ψ ν := ((GlobalTheory.SplitWeil.selfDual_measure k ψ hψ hne).2.1 hcond ν).1 hν
  obtain ⟨⟨ρ₀, hρ₀⟩, hsm⟩ := GlobalTheory.PosOne.isSrc_exists_isSmoothRep k (n₀ ⊕ Fin (c + 1 + 1)) (n₁ ⊕ Fin (c + 1)) μ₁ ho₁
  have hsm₀ := hsm ρ₀ hρ₀

  have hcomb : ∀ f : GL (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ,
      comb (e₀.mapDomain (· * α⁻¹)) (fun g => f (g * α)) = comb e₀ f := by
    intro f
    unfold comb
    rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
    simp only [inv_mul_cancel_right]
  have hsrc : SrcComb ψ ν (ρ + 1) ρ₀ (ρ₀ α P₁) (e₀.mapDomain (· * α⁻¹)) := by
    intro L hL
    have hP : ∀ j : L₀.J, ρ₀ (j : GL (n₀ ⊕ Fin (c + 1 + 1)) k) P₁ = (L₀.lam j : ℂ) • P₁ := fun j =>
      Subtype.ext ((hρ₀ _ _).trans (hty₁.1 j))
    rw [he₀ _ ρ₀ hsm₀ L hL P₁ hP, ← hcomb]
    congr 1
    funext g
    rw [map_mul, Module.End.mul_apply]
  have hsym : ∀ g ∈ (e₀.mapDomain (· * α⁻¹)).support,
      SymDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ τ T F (om μ₁ g 1 (ρ₀ α P₁).1) P₂.1 (z (g * α)) := by
    intro g hg
    classical
    rw [Finsupp.mapDomain_support_of_injective (mul_left_injective α⁻¹)] at hg
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hg
    have e : om μ₁ (a * α⁻¹) 1 (ρ₀ α P₁).1 = om μ₁ (a * α⁻¹ * α) 1 P₁.1 := by
      rw [← hρ₀, ← hρ₀, map_mul ρ₀ (a * α⁻¹) α, Module.End.mul_apply]
    rw [e]
    simpa only [inv_mul_cancel_right] using hz a ha
  have h1 := GlobalTheory.T.positionOne_of_symmetricDoubleIntegral_finite k n₀ n₁ n₂ c ρ hcρ ψ hψ hne ν hsd μ₁ μ₂ ho₁ ho₂ m₁ G₁ m₂ G₂ A τ hτ T hT F ρ₀ hρ₀ (ρ₀ α P₁) P₂
    (e₀.mapDomain (· * α⁻¹)) hsrc (fun g => z (g * α)) hsym
  rw [hcomb, hρ₀] at h1

  obtain ⟨hi₁, hn₁⟩ := relIndex_mul_measure_KO G₁ hK₁ L₁.J hco₁ hle₁
  obtain ⟨hi₂, hn₂⟩ := relIndex_mul_measure_KO G₂ hK₂ L₂.J hco₂ hle₂
  set r₁ : ℝ≥0∞ := (L₁.J.relIndex (KO k (n₁ ⊕ Fin (c + 1))) : ℝ≥0∞) with hr₁
  set r₂ : ℝ≥0∞ := (L₂.J.relIndex (KO k (n₂ ⊕ Fin c)) : ℝ≥0∞) with hr₂
  haveI : (r₁ • G₁).IsHaarMeasure := Measure.IsHaarMeasure.smul G₁ (by simpa [hr₁] using hn₁) (by simp [hr₁])
  haveI : (r₂ • G₂).IsHaarMeasure := Measure.IsHaarMeasure.smul G₂ (by simpa [hr₂] using hn₂) (by simp [hr₂])
  have h2 := oneDbl_smul r₁ r₂ h1
  have hc : 1 ≤ c := by omega
  rw [← rescale_one_eq (n := n₁) (c := c + 1) (by omega) hν m₁, ← rescale_one_eq (n := n₂) hc hν m₂] at h2
  have h3 := (GlobalTheory.PosOne.oneDbl_iff_sum k n₀ n₁ n₂ c ρ hcρ ψ hψ hcond ν hν μ₁ μ₂ ho₁ ho₂ m₁ (r₁ • G₁) m₂ (r₂ • G₂) L₁ L₂
    hco₁ hco₂ (by rw [Measure.smul_apply, smul_eq_mul, hi₁]) (by rw [Measure.smul_apply, smul_eq_mul, hi₂]) 1 1 A τ hτ T hT F hF
    P₁ P₂ hty₁.2 hty₂ α A₁ A₂ hcov₁ hcov₂ _).1 h2

  have hex : ∀ γ ∈ A₁, ∀ β ∈ A₂, toOne ν τ ρ (fun v => app (app T (xi ψ ν μ₁ P₁.1 L₁.J 1 α γ)) (xi ψ ν μ₂ P₂.1 L₂.J 1 γ β) v)
      (τ β F) = comb (e₂ β) fun b => app (app T (xi ψ ν μ₁ P₁.1 L₁.J 1 α γ)) (xi ψ ν μ₂ P₂.1 L₂.J 1 γ β) (τ b F) := by
    intro γ _ β hβ
    refine he₂ β hβ A τ hτ _ ?_ F hF
    intro g hg v
    unfold app
    split_ifs with h₁ h₂
    · exact (hT.1 _).1 _ g hg v
    · simp
    · simp
  have hr : ((r₁.toReal : ℂ) * (r₂.toReal : ℂ)) = ((L₁.J.relIndex (KO k _) : ℂ) * (L₂.J.relIndex (KO k _) : ℂ)) := by
    simp [hr₁, hr₂]
  have hr0 : ((L₁.J.relIndex (KO k (n₁ ⊕ Fin (c + 1))) : ℂ) * (L₂.J.relIndex (KO k (n₂ ⊕ Fin c)) : ℂ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 hn₁) (Nat.cast_ne_zero.2 hn₂)
  rw [← mul_assoc, hr] at h3
  rw [eq_inv_mul_iff_mul_eq₀ hr0, h3]
  refine Finset.sum_congr rfl fun γ hγ => Finset.sum_congr rfl fun β hβ => ?_
  rw [hex γ hγ β hβ]

end GlobalTheory.PosOne
