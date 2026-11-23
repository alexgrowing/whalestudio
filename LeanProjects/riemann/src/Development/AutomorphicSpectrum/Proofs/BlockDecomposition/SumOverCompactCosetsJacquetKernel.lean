import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.TwistedAverage

theorem sum_reps_eq_sum_out {H V : Type} [Group H] [AddCommGroup V] (K : Subgroup H)
    [Fintype (H ⧸ K)] (T : Finset H) (hT : ∀ x : H, ∃! t, t ∈ T ∧ t⁻¹ * x ∈ K) (f : H → V)
    (hf : ∀ x, ∀ k ∈ K, f (x * k) = f x) :
    ∑ t ∈ T, f t = ∑ q : H ⧸ K, f q.out := by
  refine Finset.sum_bij (fun t _ => (QuotientGroup.mk t : H ⧸ K)) (fun _ _ => Finset.mem_univ _)
    ?_ ?_ ?_
  · intro a ha b hb hab
    exact (hT b).unique ⟨ha, QuotientGroup.eq.1 hab⟩ ⟨hb, by simp⟩
  · intro q _
    obtain ⟨t, ⟨ht, hx⟩, -⟩ := hT q.out
    refine ⟨t, ht, ?_⟩
    rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.2 hx
  · intro t _
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K t
    rw [hh, hf _ _ h.2]

theorem sum_reps_eq_zero_of_mem_twKer :
    ∀ {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G Z), IsSmooth ρ → ∀ (L : Subgroup G), IsCompact (L : Set G) → ∀ v : Z, v ∈ twKer ρ L 1 → ∀ (K : Subgroup L) (T : Finset L), IsOpen (K : Set L) → (∀ x ∈ K, ρ (x : G) v = v) → (∀ x : L, ∃! t, t ∈ T ∧ t⁻¹ * x ∈ K) → ∑ t ∈ T, ρ (t : G) v = 0 := by
  intro G Z _ _ _ _ _ ρ hρ L hL v hv K T hKo hKv hT
  classical
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hθ : IsOpen (((1 : L →* ℂˣ).ker : Subgroup L) : Set L) := by
    rw [MonoidHom.ker_one]
    exact isOpen_univ
  obtain ⟨M, hM, hsum⟩ := exists_sum_eq_zero hρ hL (1 : L →* ℂˣ) hθ hv
  haveI : Finite (L ⧸ K) := Subgroup.quotient_finite_of_isOpen _ hKo
  haveI hKf : K.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI : Fintype (L ⧸ K) := Fintype.ofFinite _
  set C : Subgroup L := (M ⊓ K).normalCore with hC
  haveI : C.Normal := Subgroup.normalCore_normal _
  haveI : C.FiniteIndex := inferInstance
  haveI : Fintype (L ⧸ C) := Fintype.ofFinite _
  have hCM : C ≤ M ⊓ K := Subgroup.normalCore_le _
  haveI : Finite (K ⧸ C.subgroupOf K) := inferInstance
  haveI : Fintype (K ⧸ C.subgroupOf K) := Fintype.ofFinite _
  have hf : ∀ x : L, ∀ k ∈ K, twOrbit ρ L 1 v (x * k) = twOrbit ρ L 1 v x := by
    intro x k hk
    simp only [twOrbit, MonoidHom.one_apply, mul_one, inv_one, Units.val_one, one_smul,
      Subgroup.coe_mul, map_mul, Module.End.mul_apply, hKv k hk]
  have h0 := hsum C (hCM.trans inf_le_left)
  rw [sum_out_refine (hCM.trans inf_le_right) (twOrbit ρ L 1 v) hf] at h0
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h0
  have h1 : ∑ q : L ⧸ K, twOrbit ρ L 1 v q.out = 0 := by
    rcases h0 with h0 | h0
    · exact absurd h0 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
    · exact h0
  have h2 := sum_reps_eq_sum_out K T hT (twOrbit ρ L 1 v) hf
  rw [h1] at h2
  simpa [twOrbit] using h2

end GlobalTheory.CompanionTheory.TwistedAverage
