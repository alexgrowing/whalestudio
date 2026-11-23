import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolyBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier ValuativeRel
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.FiniteFourier

open GlobalTheory.CompanionTheory.TwistedAverage

theorem sum_twOrbit_eq_zero {G V : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (L : Subgroup G)
    (hL : IsCompact (L : Set G)) (L₁ : Subgroup L) (hL₁ : IsOpen (L₁ : Set L)) (v : V)
    (hv : ∀ x ∈ L₁, ρ (x : G) v = v) (θ : L →* ℂˣ) (hθ : ∀ x ∈ L₁, θ x = 1)
    (hk : v ∈ twKer ρ L θ) [L₁.Normal] [Fintype (L ⧸ L₁)] :
    ∑ q : L ⧸ L₁, twOrbit ρ L θ v q.out = 0 := by
  classical
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hle : L₁ ≤ θ.ker := fun x hx => hθ x hx
  have hopen : IsOpen (θ.ker : Set L) := Subgroup.isOpen_mono hle hL₁
  obtain ⟨M, hM, hsum⟩ := exists_sum_eq_zero hρ hL θ hopen hk
  haveI : L₁.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  set C : Subgroup L := (M ⊓ L₁).normalCore with hC
  haveI : C.Normal := Subgroup.normalCore_normal _
  haveI : C.FiniteIndex := inferInstance
  haveI : Fintype (L ⧸ C) := Fintype.ofFinite _
  have hCM : C ≤ M ⊓ L₁ := Subgroup.normalCore_le _
  haveI : Finite (L₁ ⧸ C.subgroupOf L₁) := inferInstance
  haveI : Fintype (L₁ ⧸ C.subgroupOf L₁) := Fintype.ofFinite _
  have h0 := hsum C (hCM.trans inf_le_left)
  rw [sum_out_refine (hCM.trans inf_le_right) (twOrbit ρ L θ v)
    (fun x k hk => twOrbit_mul_right ρ L θ v x k ⟨hv k hk, hθ k hk⟩)] at h0
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact absurd h0 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  · exact h0

theorem eq_zero_of_twKer :
    ∀ {G V : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ → ∀ (L : Subgroup G), IsCompact (L : Set G) → ∀ (L₁ : Subgroup L), IsOpen (L₁ : Set L) → ∀ (v : V), (∀ x ∈ L₁, ρ (x : G) v = v) → ∀ {ι : Type} (R : Finset ι), R.Nonempty → ∀ (χ : ι → (L →* ℂˣ)), (∀ a ∈ R, ∀ x ∈ L₁, χ a x = 1) → (∀ a ∈ R, v ∈ twKer ρ L (χ a)) → (∀ x : L, x ∉ L₁ → ∑ a ∈ R, (((χ a x)⁻¹ : ℂˣ) : ℂ) = 0) → v = 0 := by
  intro G V _ _ _ _ _ ρ hρ L hL L₁ hL₁ v hv ι R hR χ hχ hker hsum
  classical
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  haveI : Finite (L ⧸ L₁) := Subgroup.quotient_finite_of_isOpen _ hL₁
  haveI : L₁.Normal := Subgroup.normal_of_comm L₁
  haveI : Fintype (L ⧸ L₁) := Fintype.ofFinite _
  have key : ∀ a ∈ R, ∑ q : L ⧸ L₁, twOrbit ρ L (χ a) v q.out = 0 := fun a ha =>
    sum_twOrbit_eq_zero ρ hρ L hL L₁ hL₁ v hv (χ a) (hχ a ha) (hker a ha)
  have h0 : ∑ q : L ⧸ L₁, ∑ a ∈ R, twOrbit ρ L (χ a) v q.out = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero key
  have hoff : ∀ q : L ⧸ L₁, q ≠ 1 → ∑ a ∈ R, twOrbit ρ L (χ a) v q.out = 0 := by
    intro q hq
    have hnot : q.out ∉ L₁ := by
      intro hmem
      apply hq
      rw [← QuotientGroup.out_eq' q]
      exact (QuotientGroup.eq_one_iff _).2 hmem
    simp only [twOrbit]
    rw [← Finset.sum_smul, hsum _ hnot, zero_smul]
  have hone : ((1 : L ⧸ L₁).out : L) ∈ L₁ := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.out_eq']
  have hmain : ∑ a ∈ R, twOrbit ρ L (χ a) v (1 : L ⧸ L₁).out = R.card • v := by
    rw [Finset.card_eq_sum_ones, Finset.sum_smul]
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [twOrbit]
    rw [hχ a ha _ hone, hv _ hone]
    simp
  rw [Finset.sum_eq_single (1 : L ⧸ L₁) (fun q _ hq => hoff q hq)
    (fun h => absurd (Finset.mem_univ _) h), hmain] at h0
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact absurd h0 (Nat.cast_ne_zero.2 hR.card_pos.ne')
  · exact h0

end GlobalTheory.CompanionTheory.FiniteFourier
