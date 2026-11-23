import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.CvGelfandAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.CvHecke
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HeckeGelfandPair

open GlobalTheory.BCT UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Th

private theorem sum_reindex {G : Type} [Group G] (K : Subgroup G) (φ ψ : G → G)
    (hφ : ∀ z, ∀ k ∈ K, (φ z)⁻¹ * φ (z * k) ∈ K) (hψ : ∀ z, ∀ k ∈ K, (ψ z)⁻¹ * ψ (z * k) ∈ K)
    (hψφ : ∀ z, ψ (φ z) = z) (hφψ : ∀ z, φ (ψ z) = z) (u : G → ℂ)
    (hu : ∀ k ∈ K, ∀ x, u (x * k) = u x) :
    ∑ᶠ q : G ⧸ K, u (φ q.out) = ∑ᶠ q : G ⧸ K, u q.out := by
  have back : ∀ (a b : G → G), (∀ z, ∀ k ∈ K, (b z)⁻¹ * b (z * k) ∈ K) → (∀ z, b (a z) = z) →
      ∀ q : G ⧸ K, ((b (((a q.out : G) : G ⧸ K)).out : G) : G ⧸ K) = q := by
    intro a b hb hba q
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (a q.out)
    rw [hk, ← QuotientGroup.eq.2 (hb (a q.out) k k.2), hba, QuotientGroup.out_eq']
  let e : G ⧸ K ≃ G ⧸ K :=
    { toFun := fun q => ((φ q.out : G) : G ⧸ K)
      invFun := fun q => ((ψ q.out : G) : G ⧸ K)
      left_inv := back φ ψ hψ hψφ
      right_inv := back ψ φ hφ hφψ }
  rw [← finsum_comp_equiv e (f := fun q : G ⧸ K => u q.out)]
  refine finsum_congr fun q => ?_
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (φ q.out)
  change u (φ q.out) = u (((φ q.out : G) : G ⧸ K)).out
  rw [hk, hu k k.2]

theorem cvGelfand : CvGelfand :=
  _root_.UpperTheory.Reformulated.B.HeckeGelfandPair.cvGelfand

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Th
