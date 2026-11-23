import Development.AutomorphicSpectrum.Definitions.TwistedFlags.BlockDoubleCosetFunctionsExist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeDeterminesSphericalHeckeCharacterGL

namespace CompanionTheory.D.Upq.DoubleCosetLemmas

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.LFun GlobalTheory.CompanionTheory.Ipf.Val

theorem dosetInd_mem_hecke {G : Type} [Group G] (K : Subgroup G) (m : G) :
    dosetInd ℂ K m ∈ Hecke ℂ K := by
  classical
  refine ⟨fun a b g => ?_, {m}, fun g hg => ?_⟩
  · have : (a : G) * g * b ∈ DoubleCoset.doubleCoset m (K : Set G) K ↔
        g ∈ DoubleCoset.doubleCoset m (K : Set G) K := by
      simp only [DoubleCoset.mem_doubleCoset]
      constructor
      · rintro ⟨x, hx, y, hy, e⟩
        exact ⟨(a : G)⁻¹ * x, K.mul_mem (K.inv_mem a.2) hx, y * (b : G)⁻¹, K.mul_mem hy (K.inv_mem b.2), by
          rw [show g = (a : G)⁻¹ * ((a : G) * g * b) * (b : G)⁻¹ by group, e]; group⟩
      · rintro ⟨x, hx, y, hy, rfl⟩
        exact ⟨a * x, K.mul_mem a.2 hx, y * b, K.mul_mem hy b.2, by group⟩
    simp only [dosetInd, Set.indicator_apply, this, Pi.one_apply]
  · obtain ⟨x, hx, y, hy, e⟩ := DoubleCoset.mem_doubleCoset.1 (Set.mem_of_indicator_ne_zero hg)
    exact ⟨m, Finset.mem_singleton_self m, ⟨x, hx⟩, ⟨y, hy⟩, e⟩

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)} {c : ℕ}

theorem IsSphEig.apply {B : Multiset ℂˣ} {m : GL (Fin c) (Cv v)} {lam : ℂ} (h : IsSphEig v B m lam)
    {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin c) (Cv v)) V} {x : V}
    (hx : IsSatVecGL v ρ x B) : heckeVec ρ (KGL v c) (dosetInd ℂ (KGL v c) m) x = lam • x := by
  obtain ⟨z, hz⟩ := GlobalTheory.ChainOnto.SatHeckeChar.heckeVec_eq_smul_of_isSatVecGL K v c B _
    (dosetInd_mem_hecke (KGL v c) m)
  obtain ⟨V₀, _, _, ρ₀, x₀, h₀, h₁⟩ := h
  rw [hz V ρ x hx, smul_left_injective ℂ h₀.1 ((hz V₀ ρ₀ x₀ h₀).symm.trans h₁)]

end CompanionTheory.D.Upq.DoubleCosetLemmas
