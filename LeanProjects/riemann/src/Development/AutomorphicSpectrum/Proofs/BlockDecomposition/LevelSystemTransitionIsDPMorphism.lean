import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

section Gen
variable {W B W' B' : Type} [CommRing W] [CommRing B] [Algebra ℚ B] [CommRing W'] [CommRing B'] [Algebra ℚ B']
  (f : W →+* B) (ξ : W) (f' : W' →+* B') (ξ' : W') (l M : ℕ)

theorem map_isDPMorphism (g : B →+* B') (h : ∀ x ∈ Lat.sub f ξ l M, g x ∈ Lat.sub f' ξ' l M)
    (hg : g (f ξ) = f' ξ')
    (hc : DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ)) (hc' : DPClosed (Lat.ι f' ξ' l M) (Lat.γB f' ξ')) :
    IsDPMorphism (Lat.γ f ξ l M hc) (Lat.γ f' ξ' l M hc') (Lat.map f ξ f' ξ' l M g h) := by
  have hIB : ∀ x ∈ Lat.IB f ξ, g x ∈ Lat.IB f' ξ' := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, hg]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  refine ⟨?_, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    show Lat.ι f' ξ' l M (Lat.map f ξ f' ξ' l M g h a) ∈ Lat.IB f' ξ'
    rw [Lat.ι_map]
    exact hIB _ ha
  · intro n a ha
    have ha' : Lat.ι f ξ l M a ∈ Lat.IB f ξ := ha
    have hb : Lat.map f ξ f' ξ' l M g h a ∈ Lat.I f' ξ' l M := by
      show Lat.ι f' ξ' l M (Lat.map f ξ f' ξ' l M g h a) ∈ Lat.IB f' ξ'
      rw [Lat.ι_map]
      exact hIB _ ha'
    apply Lat.ι_injective f' ξ' l M
    rw [Lat.ι_γ _ _ _ _ _ hb, Lat.ι_map, Lat.ι_map, Lat.ι_γ _ _ _ _ _ ha, DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul _ _ ha',
      DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul _ _ (hIB _ ha'), map_rat_smul, map_pow]

end Gen

variable {l : ℕ} [Fact l.Prime]

theorem dk_fk (k : ℕ) (w : Ainf l) : dk l k (fk l (k + 1) w) = fk l k w := by
  rfl

theorem levSys_ddp {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (m : ℕ) :
    IsDPMorphism ((levSys h).L (m + 1)).γ ((levSys h).L m).γ ((levSys h).dA m) := by
  exact map_isDPMorphism (fk l (m + 2)) (xi0 l) (fk l (m + 1)) (xi0 l) l M (dk l (m + 1))
    (fun x hx => h.dIn (m + 1) x hx) (dk_fk (m + 1) (xi0 l)) (h.hc (m + 2)) (h.hc (m + 1))

end GlobalTheory.CompanionTheory.LatC
