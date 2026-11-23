import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.ArchBaseChangeOfHyp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatakeOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatakeGLOfHasSatakeParametersPrincipalSeries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import GroundTheory.AutomorphicForms.FiniteLengthJacquet

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.OnePart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem hasSat_iff {π : CuspSub E n} {w : HeightOneSpectrum (𝓞 E)} {τ : SmIrr (GL (Fin n) (w.adicCompletion E))}
    (hτ : π.IsLocComp w τ) (B : Multiset ℂˣ) : (CG.mk π).HasSat w B ↔ GlobalTheory.LFun.HasSatGL w τ.ρ B := by
  refine ⟨fun h => ?_, fun h => GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hτ h⟩
  obtain ⟨α, hαB, hα⟩ := GlobalTheory.LFun.SphComp.hasSatake_of_isLocComp π h hτ
  rw [← hαB]
  exact GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake E w n _ _ _ hα

theorem isSubquotient_iff {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {π : Representation ℂ G W} [ρ.IsIrreducible] [π.IsIrreducible] :
    GlobalTheory.SmGL.IsSubquotient π ρ ↔ Nonempty (π.Equiv ρ) := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := GroundTheory.Automorphic.IsSubquotient.exists_bijective (π := π) (ρ := ρ) h
    exact ⟨GlobalTheory.LocGL.equivOfBijective e he⟩
  · rintro ⟨e⟩
    exact .of_surjective e.symm.toIntertwiningMap e.symm.toLinearEquiv.surjective

theorem oneRead : OneRead := by
  intro E _ _ _ n hn π D hD
  obtain ⟨c, N, h, V, σ, m, pos, disc, loc, inf⟩ := D
  obtain ⟨hc, hv⟩ := hD
  dsimp only at hc hv
  subst hc
  obtain ⟨e, he⟩ := hv 0
  obtain ⟨M, rfl⟩ : ∃ M, N = fun _ => M := ⟨N 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  have e' : M = n := e
  subst e'
  have he' : V 0 = π.V := he
  obtain ⟨s, rfl⟩ : ∃ s : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin M) (w.adicCompletion E)), σ = fun _ => s :=
    ⟨σ 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  have hl : ∀ w, π.IsLocComp w (s w) := fun w => ((cuspSub_iff π).2.1 w _).1 (he' ▸ loc 0 w)
  refine ⟨fun w B => ?_, fun w => ⟨_, hl w⟩, fun w τ hτ P => ?_⟩
  · rw [hasSat_iff (hl w)]
    constructor
    · intro hB
      exact ⟨fun _ => B, fun _ => ⟨hB.1, hB⟩, by simp⟩
    · rintro ⟨b, hb, rfl⟩
      simpa using (hb 0).2
  · obtain ⟨φ⟩ := GlobalTheory.LocGL.nonempty_equiv_multiProd_one (s w).smooth (GlobalTheory.SmGL.stdBlocks (fun _ : Fin 1 => M) h)
      fun a i => Fin.ext (by rw [GlobalTheory.SmGL.stdBlocks_val, Subsingleton.elim a 0]; simp)
    obtain ⟨u⟩ := LocUniq.isLocComp_unique π w _ _ (hl w) hτ
    have := (s w).irred
    have := P.irred
    have hφ : ∀ {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GL (Fin M) (w.adicCompletion E)) X),
        GlobalTheory.SmGL.IsSubquotient ρ (s w).ρ → GlobalTheory.SmGL.IsSubquotient ρ (GlobalTheory.UnitaryBC.locProd h w fun _ => s w) := fun ρ hρ =>
      hρ.trans (.of_surjective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.surjective)
    constructor
    · intro hP
      have h1 : GlobalTheory.SmGL.IsSubquotient P.ρ (s w).ρ :=
        hP.trans (.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective)
      obtain ⟨e₁⟩ := isSubquotient_iff.1 h1
      exact ⟨e₁.trans u⟩
    · rintro ⟨e₁⟩
      exact hφ _ (isSubquotient_iff.2 ⟨e₁.trans u.symm⟩)

end GlobalTheory.CompanionTheory.OnePart

end
