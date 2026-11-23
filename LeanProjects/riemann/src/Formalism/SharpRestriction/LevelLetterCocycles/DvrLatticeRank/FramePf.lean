import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfRec
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfAB
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfBA
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfBeta

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O}
    (Bs : FramepfBas W T) (π' : LetA O n) (c : ZMod n)
    (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))
    (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))

theorem framepf_back (hT : IsCrys PD T.ρ) (Eπ : LetA O n) (h' M : ℕ)
    (huE : IsUnit (algebraMap (LetA O n) W.EE Eπ)) (hEΔ : Eπ ∈ W.AΔ) (u : LetA O n) (huΔ : u ∈ W.AΔ)
    (hφ : W.φA π' ^ M = π' ^ M * Eπ ^ (4 * h') * u) :
    FramepfBack Bs π' c hπ0 hΔπ hR2 γ0 hu Eπ h' M := by
  intro H H' K₁ K₂ lam h₁ h₂
  obtain ⟨βφ, hβφ⟩ := framepf_phiBasis Bs hT
  let eb : Module.Basis (Fin Bs.r) O (LcQ W T π' c) :=
    Module.Basis.ofEquivFun (framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu)
  have heb : ∀ j, eb j = framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu j := fun j => by
    simp only [eb, Module.Basis.coe_ofEquivFun, framepf_ebar]
  have hΨ : ∀ (e : W.EE) j, framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H (e ⊗ₜ eb j) =
      e • ∑ m, W.φA (framepf_ι π' (c - 1) (H m j)) • W.φD T (Bs.b m) := fun e j => by
    rw [heb, framepf_Ψα_tmul, framepf_hh_ebar, framepf_φD_vec]
  have hΦ : ∀ a : Fin Bs.r → LetA O n,
      framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ H' (∑ k, a k • W.φD T (Bs.b k)) =
        ∑ j, algebraMap (LetA O n) W.EE (∑ k, a k * W.φA (framepf_ι π' (c - 1) (H' j k))) ⊗ₜ eb j :=
    fun a => by simp only [heb]; exact framepf_Ψβ_sum Bs π' c hπ0 hΔπ hR2 γ0 hu βφ hβφ H' a
  have hS : ∀ (Km : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) m k,
      u * W.φA (framepf_ι π' (c - 1) (Km m k)) ∈ W.AΔ := fun Km m k =>
    W.AΔ.mul_mem huΔ (framepf_φA_ι_mem π' c hπ0 hΔπ γ0 _)
  refine ⟨framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ H',
    framepf_Ψβ_Lam Bs π' c hπ0 hΔπ hR2 γ0 hu βφ hβφ Eπ hEΔ h' hT H',
    framepf_Ψβ_J Bs π' c hπ0 hΔπ hR2 γ0 hu βφ hβφ Eπ h' M hT H',
    framepf_βα_core Bs π' Eπ h' M c huE eb (fun j k => W.φA (framepf_ι π' (c - 1) (H' j k)))
      (fun j k => W.φA (framepf_ι π' (c - 1) (H j k))) _ (hS K₁) lam (fun j k => ?_) _ _ hΨ hΦ,
    framepf_αβ_core Bs hT π' Eπ h' M c huE hEΔ eb (fun j k => W.φA (framepf_ι π' (c - 1) (H' j k)))
      (fun j k => W.φA (framepf_ι π' (c - 1) (H j k))) _ (hS K₂) lam (fun j k => ?_) _ _ hΨ hΦ⟩
  · rw [framepf_φA_ι_matmul Bs π' c hπ0, h₁, framepf_φA_ι_entry Bs π' c hπ0, hφ, mul_assoc _ u]
  · rw [framepf_φA_ι_matmul Bs π' c hπ0, h₂, framepf_φA_ι_entry Bs π' c hπ0, hφ, mul_assoc _ u]

end Local

set_option maxHeartbeats 1000000 in

theorem frame_pf : FrameStep := by
  intro D HW F Cm CA CB CK hA l _ hl K LL hG π' E hR h' hh' c
  exact framepf_rec D HW F Cm hA.1 l hl K LL hG π' E hR h' hh' c
    fun T hT Bs hπ0 hΔπ hR2 γ0 hu huE hEΔ u huΔ hφ =>
      framepf_back Bs π' c hπ0 hΔπ hR2 γ0 hu hT _ h' _ huE hEΔ u huΔ hφ

end Formalism.MainNotions.N.Ln34

end
