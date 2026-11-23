import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Clause3Asc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverse
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanContragredient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransposeInverseInvolutionApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsSpehOne

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL Zc Zc.Cos

namespace PositivityTheory.Rg.Rs

namespace PLocDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem basis (N : ℕ) : ∀ U ∈ nhds (1 : GL (Fin N) k), ∃ K : Subgroup (GL (Fin N) k),
    IsOpen (K : Set (GL (Fin N) k)) ∧ IsCompact (K : Set (GL (Fin N) k)) ∧ (K : Set (GL (Fin N) k)) ⊆ U :=
  fun U hU => by
    obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k (Fin N) U hU
    exact ⟨J, h1, GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩

theorem contraMap_surjective {N : ℕ} {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {σ : Representation ℂ (GL (Fin N) k) X} {τ : Representation ℂ (GL (Fin N) k) Y} (hσ : IsSmooth σ)
    (hτ : IsSmooth τ) (f : σ.IntertwiningMap τ) (hf : Function.Injective f) :
    Function.Surjective (GlobalTheory.ContraRefl.contraMap f) := by
  intro l
  obtain ⟨K, ho, hc, hKs⟩ := basis N _ ((isSmooth_contra σ l).mem_nhds (by simp))
  have hlK : l ∈ fixed (contra σ) K := GlobalTheory.ContraRefl.mem_fix.2 fun h hh => hKs hh
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f.toLinearMap (LinearMap.ker_eq_bot.2 hf)
  obtain ⟨l', h1, h2⟩ := GlobalTheory.ContraRefl.exists_fixed_contra hτ ho hc
    (((l : Module.Dual ℂ X) ∘ₗ g) ∘ₗ (fixed τ K).subtype)
  have hl'K : l' ∈ fixed (contra τ) K := GlobalTheory.ContraRefl.mem_fix.2 h1
  refine ⟨l', Subtype.ext (GlobalTheory.ContraRefl.form_ext hσ hc (fun h hh w => ?_) (fun h hh w => ?_) fun w hw => ?_)⟩
  · show (l' : Module.Dual ℂ Y) (f (σ h w)) = (l' : Module.Dual ℂ Y) (f w)
    rw [f.isIntertwining]
    exact GlobalTheory.ContraRefl.invariant_of_fixed ⟨l', hl'K⟩ h hh (f w)
  · exact GlobalTheory.ContraRefl.invariant_of_fixed ⟨l, hlK⟩ h hh w
  · have hfw : f w ∈ fixed τ K := GlobalTheory.ContraRefl.mem_fix.2 fun h hh => by
      rw [← f.isIntertwining]
      exact congrArg f (GlobalTheory.ContraRefl.mem_fix.1 hw h hh)
    show (l' : Module.Dual ℂ Y) (f w) = (l : Module.Dual ℂ X) w
    have e1 := h2 ⟨f w, hfw⟩
    have e2 := LinearMap.congr_fun hg w
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at e2
    rw [show f w = ((⟨f w, hfw⟩ : fixed τ K) : Y) from rfl, e1]
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    exact congrArg _ e2

def untwist {N : ℕ} {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {π : Representation ℂ (GL (Fin N) k) X} {σ : Representation ℂ (GL (Fin N) k) Y}
    (q : π.IntertwiningMap (σ.comp (thetaW k N))) : Representation.IntertwiningMap (π.comp (thetaW k N)) σ where
  toLinearMap := q.toLinearMap
  isIntertwining' g := by
    ext x
    have h := q.isIntertwining _ _ (thetaW k N g) x
    simp only [MonoidHom.comp_apply, GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW] at h
    exact h

theorem prodIrr_congr {h N : ℕ} {x y : Fin h → IrrGL k} (e : x = y) (hx : ∑ a, (x a).1 = N)
    (hy : ∑ a, (y a).1 = N) : Nonempty ((prodIrr x hx).Equiv (prodIrr y hy)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

set_option maxHeartbeats 2000000 in

theorem exists_surjective_rev {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N)
    (σ : GlobalTheory.CuspRep.SmIrr (GL (Fin N) k)) (f : σ.ρ.IntertwiningMap (prodIrr x hd)) (hf : f ≠ 0) :
    ∃ hd' : ∑ a, (x (Fin.rev a)).1 = N,
      ∃ g : (prodIrr (fun a => x (Fin.rev a)) hd').IntertwiningMap σ.ρ, Function.Surjective g := by
  have hA : GlobalTheory.Published.IrreducibleAdmissibleGL := GlobalTheory.CompanionTheory.BZCuspPair.irrAdm
  have hGK : GKLocal k := GlobalTheory.CompanionTheory.GKLocalProof.gkLocal hA
  have hinj : Function.Injective f := GlobalTheory.DiscreteSpectrumCM.injective_of_irreducible σ.irred f fun e =>
    hf (Representation.IntertwiningMap.ext e)
  obtain ⟨hd1, ⟨E1⟩⟩ := GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr hA x hd
  have hs := contraMap_surjective σ.smooth (isSmooth_prodIrr x hd) f hinj
  obtain ⟨E2⟩ := GlobalTheory.CompanionTheory.ThetaW.comp_thetaW_equiv_contra hGK N σ.ρ σ.smooth σ.irred
  let q : (prodIrr (fun a => dualCl (x a)) hd1).IntertwiningMap (σ.ρ.comp (thetaW k N)) :=
    (E2.symm.toIntertwiningMap.comp (GlobalTheory.ContraRefl.contraMap f)).comp E1.symm.toIntertwiningMap
  have hq : Function.Surjective q :=
    E2.symm.toLinearEquiv.surjective.comp (hs.comp E1.symm.toLinearEquiv.surjective)
  obtain ⟨hd2, ⟨E3⟩⟩ := GlobalTheory.CompanionTheory.ThetaProd.prodIrr_comp_thetaW hA hGK (fun a => dualCl (x a)) hd1
  have e : (fun a => dualCl (dualCl (x (Fin.rev a)))) = fun a => x (Fin.rev a) :=
    funext fun a => GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl hA _
  have hd' : ∑ a, (x (Fin.rev a)).1 = N := by
    rw [← hd]; exact Equiv.sum_comp Fin.revPerm (fun a => (x a).1)
  obtain ⟨E4⟩ := prodIrr_congr e hd2 hd'
  exact ⟨hd', ((untwist q).comp E3.symm.toIntertwiningMap).comp E4.symm.toIntertwiningMap,
    (hq.comp E3.symm.toLinearEquiv.surjective).comp E4.symm.toLinearEquiv.surjective⟩

end PLocDual

set_option maxHeartbeats 2000000 in
open PLocDual in
theorem locDual_holds : LocDual := by
  intro k _ _ _ _ _ N d x σ' _ _ hd f hf
  obtain ⟨hd', g, hg⟩ := exists_surjective_rev (fun i : Fin d => spehFactor x d i.rev) hd σ' f hf
  have e : (fun a : Fin d => spehFactor x d (Fin.rev (Fin.rev a))) = spehFactor x d :=
    funext fun a => by rw [Fin.rev_rev]
  have hd'' : ∑ i, (spehFactor x d i).1 = N := by simpa only [Fin.rev_rev] using hd'
  obtain ⟨E⟩ := prodIrr_congr e hd' hd''
  exact ⟨hd'', g.comp E.symm.toIntertwiningMap, hg.comp E.symm.toLinearEquiv.surjective⟩

end PositivityTheory.Rg.Rs

end
