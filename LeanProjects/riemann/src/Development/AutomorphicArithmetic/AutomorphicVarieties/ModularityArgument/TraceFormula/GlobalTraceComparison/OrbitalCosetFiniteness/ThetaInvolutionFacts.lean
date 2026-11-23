import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.CvGelfandAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularTwistedOrbitLocalFinitenessStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralPropertiesStatement

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8 UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open scoped Classical Pointwise

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Th

private lemma out_orbit {G : Type} [Group G] (θ : G →* G) (K : Subgroup G) (hθ : ∀ k ∈ K, θ k ∈ K) (δ x : G) :
    ∃ k ∈ K, ∃ k' ∈ K,
      (Quotient.out (DoubleCoset.mk (twCent θ δ) K x))⁻¹ * δ * θ (Quotient.out (DoubleCoset.mk (twCent θ δ) K x)) =
        k * (x⁻¹ * δ * θ x) * k' := by
  obtain ⟨h, hh, k, hk, e⟩ := (DoubleCoset.eq (twCent θ δ) K _ _).1
    (DoubleCoset.out_eq' (twCent θ δ) K (DoubleCoset.mk (twCent θ δ) K x))
  generalize Quotient.out (DoubleCoset.mk (twCent θ δ) K x) = o at e
  have hc : h * δ = δ * θ h := hh
  refine ⟨k, hk, (θ k)⁻¹, K.inv_mem (hθ k hk), ?_⟩
  subst e
  simp only [_root_.mul_inv_rev, map_mul, mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right]
  rw [← mul_assoc δ (θ h), ← hc]
  simp [mul_assoc]

private theorem orbFin_prod {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [ContinuousMul G] [ContinuousMul H] (θ : G →* G) (θ' : H →* H) (K : Subgroup G) (K' : Subgroup H)
    (hK : IsCompact (K : Set G)) (hK' : IsCompact (K' : Set H))
    (hθ : ∀ k ∈ K, θ k ∈ K) (hθ' : ∀ k ∈ K', θ' k ∈ K') (δ : G) (δ' : H)
    (h1 : OrbFin θ K δ) (h2 : OrbFin θ' K' δ') : OrbFin (θ.prodMap θ') (K.prod K') (δ, δ') := by
  intro C hC
  have c1 : IsCompact ((K : Set G) * (Prod.fst '' C) * (K : Set G)) := (hK.mul (hC.image continuous_fst)).mul hK
  have c2 : IsCompact ((K' : Set H) * (Prod.snd '' C) * (K' : Set H)) := (hK'.mul (hC.image continuous_snd)).mul hK'
  let φ : DoubleCoset.Quotient (twCent (θ.prodMap θ') (δ, δ') : Set (G × H)) ((K.prod K' : Subgroup (G × H)) : Set (G × H)) →
      DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G) × DoubleCoset.Quotient (twCent θ' δ' : Set H) (K' : Set H) :=
    fun q => (DoubleCoset.mk _ _ (Quotient.out q).1, DoubleCoset.mk _ _ (Quotient.out q).2)
  have hφ : Function.Injective φ := by
    intro q q' e
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    obtain ⟨a, ha, k, hk, f1⟩ := (DoubleCoset.eq _ _ _ _).1 e1
    obtain ⟨b, hb, l, hl, f2⟩ := (DoubleCoset.eq _ _ _ _).1 e2
    have hab : (a, b) ∈ twCent (θ.prodMap θ') (δ, δ') :=
      Prod.ext (show a * δ = δ * θ a from ha) (show b * δ' = δ' * θ' b from hb)
    have key : DoubleCoset.mk (twCent (θ.prodMap θ') (δ, δ')) (K.prod K') (Quotient.out q) =
        DoubleCoset.mk (twCent (θ.prodMap θ') (δ, δ')) (K.prod K') (Quotient.out q') :=
      (DoubleCoset.eq _ _ _ _).2 ⟨(a, b), hab, (k, l), ⟨hk, hl⟩, Prod.ext f1 f2⟩
    rwa [DoubleCoset.out_eq', DoubleCoset.out_eq'] at key
  refine (Set.Finite.preimage hφ.injOn ((h1 _ c1).prod (h2 _ c2))).subset ?_
  intro q hq
  refine ⟨?_, ?_⟩
  · obtain ⟨k, hk, k', hk', e⟩ := out_orbit θ K hθ δ (Quotient.out q).1
    show (Quotient.out (DoubleCoset.mk (twCent θ δ) K (Quotient.out q).1))⁻¹ * δ *
      θ (Quotient.out (DoubleCoset.mk (twCent θ δ) K (Quotient.out q).1)) ∈ (K : Set G) * (Prod.fst '' C) * (K : Set G)
    rw [e]
    exact Set.mul_mem_mul (Set.mul_mem_mul hk ⟨_, hq, rfl⟩) hk'
  · obtain ⟨k, hk, k', hk', e⟩ := out_orbit θ' K' hθ' δ' (Quotient.out q).2
    show (Quotient.out (DoubleCoset.mk (twCent θ' δ') K' (Quotient.out q).2))⁻¹ * δ' *
      θ' (Quotient.out (DoubleCoset.mk (twCent θ' δ') K' (Quotient.out q).2)) ∈ (K' : Set H) * (Prod.snd '' C) * (K' : Set H)
    rw [e]
    exact Set.mul_mem_mul (Set.mul_mem_mul hk ⟨_, hq, rfl⟩) hk'

theorem theta_involution_facts : Th2 := by
  intro E _ _ _ hE a b w _
  have ta := GlobalTheory.T.localTwist_continuous_involution_integral_properties E hE a w
  have tb := GlobalTheory.T.localTwist_continuous_involution_integral_properties E hE b w
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (ta.1.comp continuous_fst).prodMk (tb.1.comp continuous_snd)
  · intro x
    exact Prod.ext (ta.2.1 x.1) (tb.2.1 x.2)
  · intro k hk
    exact ⟨ta.2.2.1 _ hk.1, tb.2.2.1 _ hk.2⟩
  · rintro ⟨y₁, y₂⟩ h₁ h₂
    exact orbFin_prod (thL a w) (thL b w) _ _ ta.2.2.2.2.2.1 tb.2.2.2.2.2.1 ta.2.2.1 tb.2.2.1 y₁ y₂
      ((GlobalTheory.T.regularTwistedOrbit_local_finiteness E hE a w y₁ h₁ _ ⟨ta.2.2.2.2.1, le_rfl, ta.2.2.1⟩).2)
      ((GlobalTheory.T.regularTwistedOrbit_local_finiteness E hE b w y₂ h₂ _ ⟨tb.2.2.2.2.1, le_rfl, tb.2.2.1⟩).2)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Th
