import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatGal

theorem map_mem_sub_of_mul {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)
    (g : B →+* B) (s : W → W) (hs : ∀ w, g (f w) = f (s w)) (u : W) (hu : s ξ = u * ξ) :
    ∀ x ∈ sub f ξ l M, g x ∈ sub f ξ l M := by
  have hle : sub f ξ l M ≤ (sub f ξ l M).comap g := by
    refine Subring.closure_le.2 ?_
    rintro z (⟨w, rfl⟩ | ⟨i, rfl⟩)
    · show g (f w) ∈ sub f ξ l M
      rw [hs]
      exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
    · show g (dpE f ξ l M i) ∈ sub f ξ l M
      have hη : g (η f ξ l M) = f u * η f ξ l M := by
        rw [η, map_rat_smul, hs, hu, map_mul, mul_smul_comm]
      have hd : g (dpE f ξ l M i) = f u ^ i * dpE f ξ l M i := by
        rw [dpE, map_rat_smul, map_pow, hη, mul_pow, mul_smul_comm]
      rw [hd]
      have h1 : f u ∈ sub f ξ l M := Subring.subset_closure (Or.inl ⟨u, rfl⟩)
      have h2 : dpE f ξ l M i ∈ sub f ξ l M := Subring.subset_closure (Or.inr ⟨i, rfl⟩)
      exact (sub f ξ l M).mul_mem ((sub f ξ l M).pow_mem h1 i) h2
  exact fun x hx => hle hx

theorem gal_mem_sub : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (M k : ℕ)
    (g : K.fixingSubgroup) (hT : Ideal.span {tBdR l ^ k} ≤ (Ideal.span {tBdR l ^ k}).comap (Lat.gP l g)),
    ∀ x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M,
      Ideal.quotientMap _ (Lat.gP l g) hT x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  intro l _ K M k g hT
  have hmem : toBot g.1 • xi0 l ∈ RingHom.ker (theta0 l) :=
    gal_smul_mem_ker_fontaineTheta (toBot g.1) (by
      rw [ker_theta0]; exact Ideal.mem_span_singleton_self _)
  rw [ker_theta0, Ideal.mem_span_singleton'] at hmem
  obtain ⟨u, hu⟩ := hmem
  refine map_mem_sub_of_mul (fk l k) (xi0 l) l M _ (fun w => toBot g.1 • w) (fun w => ?_) u hu.symm
  show Ideal.quotientMap _ (gP l g) hT (Ideal.Quotient.mk _ (wittToBDeRhamPlus (normInteger ℂ_[l]) l w)) =
    Ideal.Quotient.mk _ (wittToBDeRhamPlus (normInteger ℂ_[l]) l (toBot g.1 • w))
  rw [Ideal.quotientMap_mk, ← gal_smul_wittToBDeRhamPlus]
  rfl

end GlobalTheory.CompanionTheory.LatGal
